% Forward Simulation for Kirchhoff Rods
%
% Based on a piecewise-linear discretization. The simulation state consists
% of an edge vector and a normal vector per segment.
% Per segment, there are three equality constraints: 1) the length of an
% edge vector is equal to its initial length, 2) the normal vector is
% unit-length, 3) the edge vector and normal vector are orthogonal.
% The endpoint clamps are enforced with equality constraints.
% The Kirchhoff energy is computed using a finite difference approximation.
% Constrained local energy minima are computed using Matlab's interior
% point algorithm, specifying the analytical gradient and Hessian of the
% Lagrangian.

classdef KirchhoffRodSimulation < handle
    properties
        E
        mu
        Ixx
        Ixy
        Iyy
        J
        seg_lengths
        
        vertex_masses
        cum_vertex_masses
        gravity = [0;0;9.8]
        
        gamma_0
        gamma_l
        tangent_0
        tangent_l
        normal_0
        normal_l
        
        binormal_0
        binormal_l
        
        vertex_weights
        num_segments
        total_length
        endpoint_position_constraint_enabled = true
        
        state
    end
    
    methods
        function obj = KirchhoffRodSimulation(seg_lengths)
            obj.seg_lengths = seg_lengths(:)';
            obj.total_length = sum(obj.seg_lengths);
            obj.num_segments = length(obj.seg_lengths);
            obj.vertex_weights = 0.5 * [obj.seg_lengths(1), ...
                obj.seg_lengths(1:end-1)+obj.seg_lengths(2:end), ...
                obj.seg_lengths(end)];
            obj.vertex_masses = zeros(1, obj.num_segments+1);
            obj.cum_vertex_masses = zeros(1, obj.num_segments);
            
            obj.gamma_0 = [0;0;0];
            obj.gamma_l = [0;0;obj.total_length];
            obj.tangent_0 = [0;0;1];
            obj.tangent_l = [0;0;1];
            obj.normal_0 = [1;0;0];
            obj.normal_l = [1;0;0];
            
            obj.binormal_0 = cross(obj.tangent_0, obj.normal_0);
            obj.binormal_l = cross(obj.tangent_l, obj.normal_l);
            
            obj.state = KirchhoffRodState([zeros(2,obj.num_segments); ones(1,obj.num_segments)], ...
                [ones(1,obj.num_segments); zeros(2,obj.num_segments)]);
        end

        function setStiffness(obj, E, mu, Ixx, Ixy, Iyy, J)
            obj.E = E;
            obj.mu = mu;
            obj.Ixx = Ixx(:)';
            obj.Ixy = Ixy(:)';
            obj.Iyy = Iyy(:)';
            if nargin < 7
                obj.J = 4*(obj.Ixx.*obj.Iyy - obj.Ixy.^2)./(obj.Ixx + obj.Iyy);
            else
                obj.J = J(:)';
            end
        end
        
        function setVertexMasses(obj, vertex_masses)
            obj.vertex_masses = vertex_masses;
            obj.cum_vertex_masses = cumsum(vertex_masses(2:end), 'reverse');
        end
        
        function ret = computeDeadloadVertexMasses(obj,density)
            detI = obj.Ixx .* obj.Iyy - obj.Ixy.^2;
            area = 2*sqrt(pi) * detI.^(1/4);
            ret = density*area.*obj.vertex_weights;
        end
        
        function setEndpointPositionConstraintEnabled(obj, enabled)
            obj.endpoint_position_constraint_enabled = enabled;
        end

        function setBoundaryConditions(obj,gamma_0,tangent_0,normal_0,gamma_l,tangent_l,normal_l)
            obj.gamma_0 = gamma_0(:);
            obj.gamma_l = gamma_l(:);
            obj.tangent_0 = tangent_0(:);
            obj.tangent_l = tangent_l(:);
            obj.normal_0 = normal_0(:);
            obj.normal_l = normal_l(:);
            
            obj.binormal_0 = cross(obj.tangent_0, obj.normal_0);
            obj.binormal_l = cross(obj.tangent_l, obj.normal_l);
        end
        
        function setInitialGuessFromVertexFrames(obj, frames)
            vt = permute(frames(:,3,:), [1 3 2]);
            vn = permute(frames(:,1,:), [1 3 2]);
            
            t = 0.5*(vt(:,1:end-1)+vt(:,2:end));
            t = t ./ sqrt(sum(t.^2,1));
            n = 0.5*(vn(:,1:end-1)+vn(:,2:end));
            n = n - sum(t.*n,1).*t;
            n = n ./ sqrt(sum(n.^2,1));
            
            obj.state.tangents = t;
            obj.state.normals = n;
        end
        
        function generateInitialGuess(obj, extra_turns)
            if nargin < 2
                extra_turns = 0;
            end
            dt = max(min(dot(obj.tangent_0,obj.tangent_l),1),-1);
            angle = acos(dt);
            ax = cross(obj.tangent_0,obj.tangent_l);
            ax_norm = norm(ax);
            if ax_norm>1.e-8
                ax = ax/ax_norm;
            else
                ax = cross(obj.tangent_0,[0;0;1]);
                ax_norm = norm(ax);
                if ax_norm>1.e-8
                    ax = ax/ax_norm;
                else
                    ax = cross(obj.tangent_0,[1;0;0]);
                    ax = ax/norm(ax);
                end
            end
            
            w = obj.vertex_weights / sum(obj.vertex_weights);
            tangents = [obj.tangent_0, zeros(3,obj.num_segments+1)];
            normals = [obj.normal_0, zeros(3,obj.num_segments+1)];
            for i=1:obj.num_segments+1
                R = rodrigues_rotation(ax,angle*w(i));
                tangents(:,i+1) = R*tangents(:,i);
                n = normals(:,i) - dot(normals(:,i), tangents(:,i+1))*tangents(:,i+1);
                normals(:,i+1) = n/norm(n);
            end
            dt = max(min(dot(normals(:,end),obj.normal_l),1),-1);
            detsign = sign(det([obj.tangent_l, normals(:,end), obj.normal_l]));
            if detsign==0
                detsign=1;
            end
            angle = (extra_turns*2*pi+acos(dt)) * detsign;
            cw = cumsum(w);
            for i=1:obj.num_segments+1
                R = rodrigues_rotation(tangents(:,i+1),angle*cw(i));
                normals(:,i+1) = R*normals(:,i+1);
            end
            
            obj.state.tangents = tangents(:,2:end-1);
            obj.state.normals = normals(:,2:end-1);
        end
        
        function solve(obj, show_vis)
            if nargin < 2
                show_vis = true;
            end
            plot_fcn = [];
            if show_vis
                plot_fcn = @(x,o,s)obj.plotfcn(x,o,s);
            end
            opts = optimoptions('fmincon',...
                'Algorithm','interior-point',...
                'Display','iter-detailed',...
                'SpecifyConstraintGradient',true,...
                'SpecifyObjectiveGradient',true,...
                'HessianFcn',@(x,lambda) obj.hessianfcn(x,lambda),...
                'PlotFcn', plot_fcn...
                );
            
            x0 = [obj.state.tangents;obj.state.normals];
            x0 = x0(:);
            
            Aeq = [];
            beq = [];
            if obj.endpoint_position_constraint_enabled
                rows = repmat([1;2;3],obj.num_segments,1);
                cols = repmat([1;2;3],1,obj.num_segments)+(0:6:6*obj.num_segments-1);
                vals = repmat(obj.seg_lengths,3,1);
                Aeq = sparse(rows(:),cols(:),vals(:),3,6*obj.num_segments);
                beq = obj.gamma_l - obj.gamma_0;
            end
            
            [x,fval,exitflag] = fmincon(@(x)obj.objfcn(x),x0,[],[],Aeq,beq,[],[],@(x)obj.nonlconfcn(x),opts);
            x = reshape(x,6,[]);
            obj.state.tangents = x(1:3,:);
            obj.state.normals = x(4:6,:);
        end
        
        function stop = plotfcn(obj,x,optimValues,state)
            ns = obj.num_segments;
            x = reshape(x,6,[]);
            t = x(1:3,:);
            n = x(4:6,:);
            avg_sl = max(mean(obj.seg_lengths),obj.total_length*0.02);
            
            if strcmp(state, 'init')
                patch('Vertices',[obj.gamma_0, obj.gamma_l]','Faces',[1;2],...
                    'Marker','.','MarkerSize',12,'MarkerEdgeColor','k');
                patch('Vertices',[obj.gamma_0, obj.gamma_0-obj.tangent_0*avg_sl, ...
                    obj.gamma_l, obj.gamma_l+obj.tangent_l*avg_sl]','Faces',[1 2;3 4],...
                    'EdgeColor',[0.7 0.7 0.7],'LineWidth',2);
                p_normal = [obj.gamma_0,obj.gamma_l]+0.5*avg_sl*[-obj.tangent_0,obj.tangent_l];
                patch('Vertices',[p_normal, p_normal+0.5*avg_sl*[obj.normal_0, obj.normal_l]]','Faces',[1 3;2 4],...
                    'EdgeColor',[1 0.5 0.5],'LineWidth',2);
            end
            
            t_color = [0.5 0.5 0.5];
            n_color = [1 0.7 0.7];
            if strcmp(state, 'done')
                t_color = [0 0 0];
                n_color = [1 0 0];
            end
            
            p = cumsum([obj.gamma_0, obj.seg_lengths .* t], 2);
            patch('Vertices',p','Faces',[1:ns;2:ns+1]','EdgeColor',t_color,'LineWidth',1,...
                'Marker','.','MarkerEdgeColor',t_color);
            p_normal = 0.5*(p(:,1:end-1)+p(:,2:end));
            patch('Vertices',[p_normal, p_normal+0.5*avg_sl*n]','Faces',[1:ns;ns+1:2*ns]',...
                'EdgeColor',n_color,'LineWidth',1);
            view(87,15);
            axis equal tight vis3d;
            
            stop = false;
        end

        function ret = hessianfcn(obj,x,lambda)
            x = reshape(x,6,[]);
            st = KirchhoffRodState(x(1:3,:), x(4:6,:));
            [~, ~, hess_W_rows, hess_W_cols, hess_W_vals] = obj.computeEnergy(st, true);
            [c_rows,c_cols,c_vals] = obj.computeConstraintHessian(lambda.eqnonlin(:));
            ret = sparse([hess_W_rows;c_rows],[hess_W_cols;c_cols],[hess_W_vals;c_vals],6*obj.num_segments,6*obj.num_segments);
        end
        
        function [c,ceq,gc,gceq] = nonlconfcn(obj,x)
            c=[];
            gc=[];
            x = reshape(x,6,[]);
            st = KirchhoffRodState(x(1:3,:), x(4:6,:));
            [ceq,gceq] = obj.computeNonlinearConstraints(st);
        end
        
        function [E, grad_E] = objfcn(obj,x)
            x = reshape(x,6,[]);
            st = KirchhoffRodState(x(1:3,:), x(4:6,:));
            [E, grad_E] = obj.computeEnergy(st);
            grad_E = grad_E(:);
        end
        
        function [gamma, frames] = getFramedCurve(obj)
            t = [obj.tangent_0, ...
                0.5*(obj.state.tangents(:,1:end-1) + obj.state.tangents(:,2:end)), ...
                obj.tangent_l];
            t = t ./ sqrt(sum(t.^2,1));
            n = [obj.normal_0, ...
                0.5*(obj.state.normals(:,1:end-1) + obj.state.normals(:,2:end)), ...
                obj.normal_l];
            n = n - sum(t.*n,1).*t;
            n = n ./ sqrt(sum(n.^2,1));
            b = cross(t,n,1);
            frames = reshape([n;b;t],3,3,[]);
            
            gamma = [obj.gamma_0, obj.gamma_0 + cumsum(obj.seg_lengths .* obj.state.tangents,2)];
        end
        
        function [k, grad_k1, grad_k2, grad_tau] = computeCurvatureVector(obj, st)
            if nargin < 2
                st = obj.state;
            end
            t = [obj.tangent_0, st.tangents, obj.tangent_l];            
            n = [obj.normal_0, st.normals, obj.normal_l];
            b = [obj.binormal_0, st.computeBinormals(), obj.binormal_l];
            nprime = (n(:,2:end) - n(:,1:end-1)) ./ obj.vertex_weights;
            bprime = (b(:,2:end) - b(:,1:end-1)) ./ obj.vertex_weights;
            
            k1 = sum(t(:,2:end).*bprime, 1);
            k2 = -sum(t(:,2:end).*nprime, 1);
            tau = sum(n(:,2:end).*bprime, 1);
            
            k = [k1;k2;tau];
            
            if nargout > 1
                grad_k1 = [cross(t(:,2:end), n(:,1:end-1), 1); ...
                    cross(t(:,1:end-1), t(:,2:end), 1); ...
                    -b(:,1:end-1); ...
                    zeros(3, obj.num_segments+1)] ./ obj.vertex_weights;
                grad_k2 = [zeros(3, obj.num_segments+1); ...
                    t(:,2:end); ...
                    n(:,1:end-1) - n(:,2:end); ...
                    -t(:,2:end)] ./ obj.vertex_weights;
                grad_tau = [cross(n(:,2:end), n(:,1:end-1), 1); ...
                    cross(t(:,1:end-1), n(:,2:end), 1); ...
                    zeros(3, obj.num_segments+1); ...
                    -b(:,1:end-1)] ./ obj.vertex_weights;
            end
        end
        
        function [W, grad_W, hess_W_rows, hess_W_cols, hess_W_vals] = computeEnergy(obj, st, skip_gradient)
            if nargin < 2
                st = obj.state;
            end
            if nargin < 3
                skip_gradient = false;
            end
            ns = obj.num_segments;
            
            if nargout > 1
                [k, grad_k1, grad_k2, grad_tau] = obj.computeCurvatureVector(st);
            else
                k = obj.computeCurvatureVector(st);
            end
            
            W_bend_xx = 0.5 * obj.E * sum(obj.vertex_weights .* obj.Ixx .* k(1,:).^2);
            W_bend_xy = obj.E * sum(obj.vertex_weights .* obj.Ixy .* k(1,:) .* k(2,:));
            W_bend_yy = 0.5 * obj.E * sum(obj.vertex_weights .* obj.Iyy .* k(2,:).^2);
            W_twist = 0.5 * obj.mu * sum(obj.vertex_weights .* obj.J .* k(3,:).^2);
            
            gamma = [obj.gamma_0, obj.gamma_0 + cumsum(obj.seg_lengths .* st.tangents,2)];
            vertex_gravity_potentials = sum(gamma.*obj.gravity,1) .* obj.vertex_masses;
            
            W = W_bend_xx + W_bend_xy + W_bend_yy + W_twist + sum(vertex_gravity_potentials);
            
            if nargout > 1
                if skip_gradient
                    grad_W = 0;
                else
                    grad_W_bend_xx = obj.E * (obj.vertex_weights(1:end-1).*obj.Ixx(1:end-1).*k(1,1:end-1).*grad_k1(7:12,1:end-1) ...
                        + obj.vertex_weights(2:end).*obj.Ixx(2:end).*k(1,2:end).*grad_k1(1:6,2:end));
                    grad_W_bend_xy = obj.E * (...
                        obj.vertex_weights(1:end-1).*obj.Ixy(1:end-1) .*(k(1,1:end-1).*grad_k2(7:12,1:end-1) + k(2,1:end-1).*grad_k1(7:12,1:end-1)) ...
                        + obj.vertex_weights(2:end).*obj.Ixy(2:end).*(k(1,2:end).*grad_k2(1:6,2:end) + k(2,2:end).*grad_k1(1:6,2:end)));
                    grad_W_bend_yy = obj.E * (obj.vertex_weights(1:end-1).*obj.Iyy(1:end-1).*k(2,1:end-1).*grad_k2(7:12,1:end-1) ...
                        + obj.vertex_weights(2:end).*obj.Iyy(2:end).*k(2,2:end).*grad_k2(1:6,2:end));
                    grad_W_twist = obj.mu * (obj.vertex_weights(1:end-1).*obj.J(1:end-1).*k(3,1:end-1).*grad_tau(7:12,1:end-1) ...
                        + obj.vertex_weights(2:end).*obj.J(2:end).*k(3,2:end).*grad_tau(1:6,2:end));
                    
                    grad_gravity = (obj.seg_lengths.*obj.cum_vertex_masses) .* obj.gravity;
                    
                    grad_W = grad_W_bend_xx + grad_W_bend_xy + grad_W_bend_yy + grad_W_twist;
                    grad_W(1:3,:) = grad_W(1:3,:) + grad_gravity;
                end
                
                if nargout > 2
                    t = [obj.tangent_0, st.tangents, obj.tangent_l];
                    n = [obj.normal_0, st.normals, obj.normal_l];
                    
                    EwIxx = obj.E*obj.Ixx.*obj.vertex_weights;
                    EwIxy = obj.E*obj.Ixy.*obj.vertex_weights;
                    EwIyy = obj.E*obj.Iyy.*obj.vertex_weights;
                    muwJ = obj.mu*obj.J .* obj.vertex_weights;
                    [r_Hk1, c_Hk1, v_Hk1] = obj.wHk1(t,n);
                    v_Hk1 = obj.E*(obj.Ixx.*k(1,:) + obj.Ixy.*k(2,:)).*v_Hk1;
                    [r_Hk2, c_Hk2, v_Hk2] = obj.wHk2();
                    v_Hk2 = obj.E*(obj.Iyy.*k(2,:) + obj.Ixy.*k(1,:)).*v_Hk2;
                    [r_Htau, c_Htau, v_Htau] = obj.wHtau(t,n);
                    v_tauHtau = obj.mu*obj.J.*k(3,:).*v_Htau;
                    
                    gk1 = permute(grad_k1(1:9,:),[1 3 2]);
                    gk1t = permute(gk1, [2 1 3]);
                    v_outer1 = (permute(EwIxx,[1 3 2]) .* gk1) .* gk1t;
                    r_outer1 = kron((1:9)',ones(9,1)) + (0:6:6*(ns+1)-1);
                    c_outer1 = repmat((1:9)',9,1) + (0:6:6*(ns+1)-1);
                    
                    gk2 = permute(grad_k2(4:12,:),[1 3 2]);
                    gk2t = permute(gk2, [2 1 3]);
                    v_outer2 = (permute(EwIyy,[1 3 2]) .* gk2) .* gk2t;
                    r_outer2 = kron((4:12)',ones(9,1)) + (0:6:6*(ns+1)-1);
                    c_outer2 = repmat((4:12)',9,1) + (0:6:6*(ns+1)-1);
                    
                    v_outer12 = (permute(EwIxy,[1 3 2]) .* gk1) .* gk2t;
                    r_outer12 = repmat((1:9)',9,1) + (0:6:6*(ns+1)-1);
                    c_outer12 = kron((4:12)',ones(9,1)) + (0:6:6*(ns+1)-1);
                    
                    gtau = permute(grad_tau([1:6 10:12],:),[1 3 2]);
                    gtaut = permute(gtau, [2 1 3]);
                    v_outertau = (permute(muwJ,[1 3 2]) .* gtau) .* gtaut;
                    r_outertau = kron([1:6 10:12]',ones(9,1)) + (0:6:6*(ns+1)-1);
                    c_outertau = repmat([1:6 10:12]',9,1) + (0:6:6*(ns+1)-1);
                    
                    r_all = [r_Hk1(:);r_outer1(:);r_Hk2(:);r_outer2(:);r_Htau(:);r_outertau(:);r_outer12(:);c_outer12(:)];
                    c_all = [c_Hk1(:);c_outer1(:);c_Hk2(:);c_outer2(:);c_Htau(:);c_outertau(:);c_outer12(:);r_outer12(:)];
                    v_all = [v_Hk1(:);v_outer1(:);v_Hk2(:);v_outer2(:);v_tauHtau(:);v_outertau(:);v_outer12(:);v_outer12(:)];
                    keep = r_all>6 & r_all<=6*(ns+1) & c_all>6 & c_all<=6*(ns+1);
                    hess_W_rows = r_all(keep)-6;
                    hess_W_cols = c_all(keep)-6;
                    hess_W_vals = v_all(keep);
                end
            end
        end
        
        function [c, grad_c] = computeNonlinearConstraints(obj, st)
            if nargin < 2
                st = obj.state;
            end
            
            c_unit_tangent = 0.5*sum(st.tangents.^2, 1) - 0.5;
            c_unit_normal = 0.5*sum(st.normals.^2, 1) - 0.5;
            c_orth = sum(st.tangents .* st.normals, 1);
            
            c = [c_unit_tangent'; c_unit_normal'; c_orth'];
            
            if nargout > 1
                r1 = repmat([1;2;3],1,obj.num_segments)+(0:6:6*obj.num_segments-1);
                c1 = repmat(1:obj.num_segments,3,1);
                v1 = st.tangents;
                
                r2 = repmat([4;5;6],1,obj.num_segments)+(0:6:6*obj.num_segments-1);
                c2 = repmat(obj.num_segments+1:2*obj.num_segments,3,1);
                v2 = st.normals;
                
                r3 = 1:6*obj.num_segments;
                c3 = repmat(2*obj.num_segments+1:3*obj.num_segments,6,1);
                v3 = [st.normals; st.tangents];
                
                grad_c = sparse([r1(:);r2(:);r3(:)], ...
                    [c1(:);c2(:);c3(:)], ...
                    [v1(:);v2(:);v3(:)], ...
                    6*obj.num_segments,3*obj.num_segments);
            end
        end
        
        function [rows,cols,vals] = computeConstraintHessian(obj, lambda)
            ns = obj.num_segments;
            r1 = repmat([1;2;3],1,obj.num_segments)+(0:6:6*obj.num_segments-1);
            v1 = kron(lambda(1:ns), ones(3,1));
            r2 = repmat([4;5;6],1,obj.num_segments)+(0:6:6*obj.num_segments-1);
            v2 = kron(lambda(ns+1:2*ns), ones(3,1));
            r3 = 1:6*obj.num_segments;
            c3 = repmat([4;5;6;1;2;3],1,obj.num_segments)+(0:6:6*obj.num_segments-1);
            v3 = kron(lambda(2*ns+1:3*ns), ones(6,1));
            
            rows = [r1(:);r2(:);r3(:)];
            cols = [r1(:);r2(:);c3(:)];
            vals = [v1(:);v2(:);v3(:)];
        end
        
        function [R,C,V] = wHk1(obj,t,n)
            r0 = [3;1;2;2;3;1];
            c0 = [2;3;1;3;1;2];
            r = [r0;r0;repmat(r0+3,2,1);repmat(r0+6,2,1)];
            c = [c0+3;c0+6;c0;c0+6;c0;c0+3];
            R = repmat(r,1,obj.num_segments+1) + (0:6:6*(obj.num_segments+1)-1);
            C = repmat(c,1,obj.num_segments+1) + (0:6:6*(obj.num_segments+1)-1);
            V = [...
                t(:,2:end);-t(:,2:end);-n(:,1:end-1);n(:,1:end-1);...
                -t(:,2:end);t(:,2:end);t(:,1:end-1);-t(:,1:end-1);...
                n(:,1:end-1);-n(:,1:end-1);-t(:,1:end-1);t(:,1:end-1)];
        end
        
        function [R,C,V] = wHk2(obj)
            r = [4;5;6;7;8;9;7;8;9;10;11;12];
            c = [7;8;9;4;5;6;10;11;12;7;8;9];
            R = repmat(r,1,obj.num_segments+1) + (0:6:6*(obj.num_segments+1)-1);
            C = repmat(c,1,obj.num_segments+1) + (0:6:6*(obj.num_segments+1)-1);
            V = [ones(6,obj.num_segments+1); -ones(6,obj.num_segments+1)];
        end
        
        function [R,C,V] = wHtau(obj,t,n)
            r0 = [3;1;2;2;3;1];
            c0 = [2;3;1;3;1;2];
            r = [r0;r0;repmat(r0+3,2,1);repmat(r0+9,2,1)];
            c = [c0+3;c0+9;c0;c0+9;c0;c0+3];
            R = repmat(r,1,obj.num_segments+1) + (0:6:6*(obj.num_segments+1)-1);
            C = repmat(c,1,obj.num_segments+1) + (0:6:6*(obj.num_segments+1)-1);
            V = [...
                n(:,2:end);-n(:,2:end);-n(:,1:end-1);n(:,1:end-1);...
                -n(:,2:end);n(:,2:end);t(:,1:end-1);-t(:,1:end-1);...
                n(:,1:end-1);-n(:,1:end-1);-t(:,1:end-1);t(:,1:end-1)];
        end
    end
end
classdef CurveHelper < handle
    methods(Static)
        function [output_fcn, l, t_fcn] = parametrizeByArcLength(input_fcn, t_range, rel_tol, abs_tol)
            if nargin < 3
                rel_tol = 1.e-5;
            end
            if nargin < 4
                abs_tol = 1.e-7;
            end
            
            ode_options = odeset('RelTol',rel_tol,'AbsTol',abs_tol, ...
                'Events', @(s,t) CurveHelper.inv_arc_length_event_fcn(s,t,t_range(2)));
            t_sol = ode45(@(s,t) CurveHelper.inv_arc_length_ode_fcn(s,t,input_fcn), [0 inf], t_range(1), ode_options);
            
            l = t_sol.xe;
            output_fcn = @(s) CurveHelper.evaluateCurve(s, t_sol, input_fcn);
            t_fcn = @(s) deval(t_sol, s);
        end
        
        function [position, isterminal, direction] = inv_arc_length_event_fcn(~,t,t_end)
            position = t_end - t;
            isterminal = 1;
            direction = -1;
        end
        
        function dt = inv_arc_length_ode_fcn(~,t,input_fcn)
            [~,dp] = input_fcn(t);
            dt = 1/norm(dp);
        end
        
        function [g,dg,ddg] = evaluateCurve(s, t_sol, input_fcn)
            t = deval(t_sol, s);
            switch nargout
                case 1
                    g = input_fcn(t);
                case 2
                    [g,dp] = input_fcn(t);
                    norm_dp = sqrt(sum(dp.^2,1));
                    dg = dp ./ norm_dp;
                case 3
                    [g,dp,ddp] = input_fcn(t);
                    norm_dp = sqrt(sum(dp.^2,1));
                    dg = dp ./ norm_dp;
                    sqr_norm_dp = norm_dp.*norm_dp;
                    ddg = ddp./sqr_norm_dp - sum(dp.*ddp,1)./(sqr_norm_dp.*sqr_norm_dp).*dp;
            end
        end
        
        function framed_curve_fcn = computeParallelFrame(curve_fcn, l, n2_0, rel_tol, abs_tol)
            if nargin < 4
                rel_tol = 1.e-5;
            end
            if nargin < 5
                abs_tol = 1.e-7;
            end
            
            [~,dg] = curve_fcn(0);
            n2_0 = n2_0 - dot(n2_0,dg)*dg;
            n2_0 = n2_0/norm(n2_0);
            
            ode_options = odeset('RelTol',rel_tol,'AbsTol',abs_tol);
            n2_sol = ode45(@(s,n) CurveHelper.parallel_normal_ode_fcn(s,n,curve_fcn), [0 l], n2_0, ode_options);
            
            framed_curve_fcn = @(s) CurveHelper.evaluateFramedCurve(s, curve_fcn, n2_sol);
        end
        
        function dn = parallel_normal_ode_fcn(s,n,curve_fcn)
            [~,dg,ddg] = curve_fcn(s);
            dn = -sum(n.*ddg,1).*dg;
        end
        
        function [g, dg, n2, k] = evaluateFramedCurve(s, curve_fcn, n2_sol)
            switch nargout
                case 1
                    g = curve_fcn(s);
                case 2
                    [g,dg] = curve_fcn(s);
                case 3
                    [g,dg] = curve_fcn(s);
                    n2 = deval(n2_sol, s);
                case 4
                    [g,dg,ddg] = curve_fcn(s);
                    n2 = deval(n2_sol, s);
                    n1 = cross(n2,dg,1);
                    k1 = -sum(n2.*ddg,1);
                    k2 = sum(n1.*ddg,1);
                    dn1 = -k2.*dg;
                    tau = sum(n2.*dn1,1);
                    k = [k1;k2;tau];
            end
        end
        
        function [which_converged, r_final, t_final] = computeSeparatingPoint(p1, n1, curve2_fcn, curve2_length, t0)
            p20 = curve2_fcn(t0);
            to_vec = p20-p1;
            r0 = 0.5*sqrt(sum(to_vec.^2,1));
            
            [g20, dg20, ddg20] = curve2_fcn(0);
            [g2l, dg2l, ddg2l] = curve2_fcn(curve2_length);
            
            ext_curve2_fcn = @(t) CurveHelper.extended_curve_fcn(t, curve2_length, curve2_fcn, g20,dg20,ddg20, g2l,dg2l,ddg2l);
            
            num_samples = size(p1,2);
            which_converged = false(1,num_samples);
            r_final = ones(1,num_samples);
            t_final = ones(1,num_samples);
            
            for i=1:num_samples
                f_fcn = @(x) CurveHelper.separating_point_function(x(1), x(2), p1(:,i), n1(:,i), ext_curve2_fcn);
                df_fcn = @(x) CurveHelper.separating_point_gradient(x(1), x(2), p1(:,i), n1(:,i), ext_curve2_fcn);

                [x_final, which_converged(i)] = NumOpt.newtonsMethod(f_fcn, df_fcn, [t0(i);r0(i)], 1.e-12, 20);
                r_final(i) = x_final(2);
                t_final(i) = x_final(1);
            end
        end
        
        function [g,dg,ddg] = extended_curve_fcn(t, l, curve_fcn, g0,dg0,ddg0,gl,dgl,ddgl)
            if t>=0
                if t<=l
                    [g,dg,ddg]=curve_fcn(t);
                else
                    g = gl + dgl*(t-l)+0.5*ddgl*(t-l).^2;
                    dg = dgl + ddgl*(t-l);
                    ddg = ddgl;
                end
            else
                g = g0 + dg0*t + 0.5*ddg0*t.^2;
                dg = dg0 + ddg0*t;
                ddg = ddg0;
            end
        end
        
        function f = separating_point_function(t,r,g1,n1,curve2_fcn)
            [g2, dg2] = curve2_fcn(t);
            f = [dot(g1-g2+2*r*n1, g1-g2); dot(g1-g2+r*n1, dg2)];
        end
        
        function df = separating_point_gradient(t,r,g1,n1,curve2_fcn)
            [g2, dg2, ddg2] = curve2_fcn(t);
            df = [-2*dot(dg2, g1-g2+r*n1), 2*dot(n1,g1-g2); ...
                dot(g1-g2+r*n1,ddg2)-dot(dg2,dg2), dot(n1,dg2)];
        end
        
        function [q,t] = findApproximatelyClosestPoint(p, curve_fcn, curve_length, num_samples)
            if nargin < 4
                num_samples = 41;
            end
            s = linspace(1,curve_length,num_samples);
            g = curve_fcn(s);
            [~,i] = min(sum((p-g).^2,1));
            q = g(i);
            t = s(i);
        end
        
        function [dg1,ddg1,kappa] = makeCurveSamplesArcLength(dg,ddg)
            % Make arc-length
            ddg1 = ddg./sum(dg.^2,1);
            dg1 = dg./sqrt(sum(dg.^2,1));
            ddg1 = ddg1 - sum(ddg1.*dg1,1).*dg1;
            kappa = sqrt(sum(ddg1.^2,1));
        end
        
        function normals = parallelTransportNormal(g,n0)
            nv = size(g,2);
            normals = zeros(3,nv-1);
            normals(:,1) = n0;
            to = g(:,2:end)-g(:,1:end-1);
            tangents = to ./ sqrt(sum(to.^2,1));
            for i=2:nv-1
                n_prev = normals(:,i-1);
                n = n_prev - dot(n_prev, tangents(:,i)) * tangents(:,i);
                n = n./norm(n);
                normals(:,i) = n;
            end
        end
        
        function [gamma, F, s] = computeFramedCurveFromCurvatureVector(k_func, length, num_segments, gamma0, F0)
            if nargin < 4
                gamma0 = zeros(3,1);
            end
            if nargin < 5
                F0 = eye(3);
            end
            nv = num_segments + 1;
            gamma = [gamma0 zeros(3,num_segments)];
            F = cat(3, F0, zeros(3,3,num_segments));
            ds = length / num_segments;
            s = linspace(0,length,nv);
            for i=1:num_segments
                Fi = F(:,:,i);
                gamma(:,i+1) = gamma(:,i) + ds*Fi(:,3);
                
                ki = k_func(s(i));
                norm_ki = norm(ki);
                theta = norm_ki * ds;
                dir = zeros(3,1);
                if norm_ki > 1.e-12
                    dir = ki/norm_ki;
                end
                K = cross_product_matrix(dir);
                R = eye(3) + sin(theta)*K + (1-cos(theta))*K*K;
                F(:,:,i+1) = Fi * R;
            end
        end
    end
end
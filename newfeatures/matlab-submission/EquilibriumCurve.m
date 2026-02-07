classdef EquilibriumCurve < handle
    methods(Static)
        function [c,cbar,rod_fcn] = solve(curve_fcn, l, nu, a_max, weight_normal, n_samples, rel_tol, abs_tol)
            if nargin < 3 || isempty(nu)
                nu = 0.3;
            end
            if nargin < 4 || isempty(a_max)
                a_max = inf;
            end
            if nargin < 5 || isempty(weight_normal)
                weight_normal = 1;
            end
            if nargin < 6 || isempty(n_samples)
                n_samples = 401;
            end
            
            if weight_normal == 0
                weight_normal = 1.e-10;
            elseif weight_normal == inf
                weight_normal = 1.e10;
            end
            
            s = linspace(0,l,n_samples);
            [g,dg,ddg] = curve_fcn(s);
            
            v1a = dg;
            a1a = [cross(g,v1a,1);v1a];
            v1b = ddg./sqrt(sum(ddg.^2,1));
            a1b = [cross(g,v1b,1);v1b];
            
            v2 = cross(dg,ddg,1);
            a2 = [cross(g,v2,1);v2];
            
            a2_upper = double(a_max < inf);
            
            A = [[a1a',  ones(n_samples,1)]; ... % -E <= <a1a,c>
                 [a1a', -ones(n_samples,1)]; ... % <a1a,c> <= E
                 [a1b',  repmat(1/weight_normal, n_samples,1)]; ... % -E <= <a1b,c>
                 [a1b', repmat(-1/weight_normal, n_samples,1)]; ... % <a1b,c> <= E
                 [repmat(a2',1+a2_upper,1), zeros((1+a2_upper)*n_samples,1)]]; ... % 1 <= <a2,c> <= a_max
            
            sense = [repmat('>',n_samples,1); repmat('<',n_samples,1); ... % 1a
                repmat('>',n_samples,1); repmat('<',n_samples,1); ... % 1b
                repmat('>',n_samples,1); repmat('<',a2_upper*n_samples,1)]; % 2
            rhs = [zeros(4*n_samples,1); ones(n_samples,1); repmat(a_max,a2_upper*n_samples,1)];
            objective = [zeros(6,1); 1];
            
%             [Aineq,bineq,Aeq,beq] = LPHelper.gurobiToMatlab(A,rhs,sense);
%             x = linprog(objective,Aineq,bineq,Aeq,beq);
%             sln = struct('x',x);
            
            model = struct('A',sparse(A),'sense',sense,'rhs',rhs,'lb',[-inf(6,1);0],'obj',objective);
            params = struct('OutputFlag', 0);
            sln = gurobi2linprog(model, params);
            
            if ~strcmp(sln.status, 'OPTIMAL')
                rod_fcn = [];
                c = [];
                cbar = [];
                return;
            end
            
            c = sln.x(1:3);
            cbar = sln.x(4:6);
            
            if nargout < 3
                return;
            end
            
            if nargin < 7 || isempty(rel_tol)
                rel_tol = 1.e-6;
            end
            if nargin < 8 || isempty(abs_tol)
                abs_tol = 1.e-8;
            end
            ode_options = odeset('RelTol',rel_tol,'AbsTol',abs_tol);
            
            
            n2_start = GeometryHelper.generateBasis(dg(:,1));
            framed_curve_fcn = CurveHelper.computeParallelFrame(curve_fcn, l, n2_start, ...
                ode_options.RelTol,ode_options.AbsTol);
            
            muOverE = 1/(2*(1+nu));
            beta_sol = ode45(@(s,beta) EquilibriumCurve.beta_ode_fcn(s,beta,framed_curve_fcn,c,cbar,muOverE), ...
                [0 l], 0, ode_options);
            
            rod_fcn = @(s) EquilibriumCurve.evaluateRod(s, beta_sol, framed_curve_fcn, c, cbar, muOverE);
            
%             [Fbeta, kbeta, I, J] = EquilibriumCurve.evaluateRod(s, beta_sol, framed_curve_fcn, c, cbar, muOverE);
%             
%             beta = deval(beta_sol, s);
%             dbeta = zeros(1,n_samples);
%             for i=1:n_samples
%                 dbeta(i) = EquilibriumCurve.beta_ode_fcn(s(i),beta(i),framed_curve_fcn,c,cbar,muOverE);
%             end
%             figure;
%             plot(s,beta);
        end
        
        function [c,cbar] = solveWithIntegratedLoad(g,dg,ddg,A,Abar,lb,reg_weight)
            if isempty(A)
                A = zeros(size(g));
            end
            if isempty(Abar)
                Abar = zeros(size(g));
            end
            n = size(g,2);
            v = cross(dg,ddg,1);
            c_coeff = cross(g,v,1)';
            cbar_coeff = v';
            a_term = sum(v .* (cross(A,g,1) - Abar), 1)';
            rhs_dgdgg = lb-a_term;
            A_dgdgg = [c_coeff cbar_coeff zeros(n,1)];
            sense_dgdgg = repmat('>',n,1);
            
            kappa = sqrt(sum(ddg.^2,1));
            v_twist = {dg, reg_weight*ddg./kappa};
            rhs_twist = cell(2,1);
            A_twist = cell(2,1);
            sense_twist = cell(2,1);
            for i=1:2
                c_coeff = cross(g,v_twist{i},1)';
                cbar_coeff = v_twist{i}';
                a_term = sum(v .* (cross(A,g,1) - Abar), 1)';
                A_twist{i} = [c_coeff cbar_coeff ones(n,1); ...
                    c_coeff cbar_coeff -ones(n,1)];
                rhs_twist{i} = [-a_term; -a_term];
                sense_twist{i} = [repmat('>',n,1); repmat('<',n,1)];
            end
            
            A = [A_dgdgg; A_twist{1}; A_twist{2}];
            rhs = [rhs_dgdgg; rhs_twist{1}; rhs_twist{2}];
            sense = [sense_dgdgg; sense_twist{1}; sense_twist{2}];
%             A = [A_dgdgg; A_twist{1}; A_twist{2}; A_twist{3}];
%             rhs = [rhs_dgdgg; rhs_twist{1}; rhs_twist{2}; rhs_twist{3}];
%             sense = [sense_dgdgg; sense_twist{1}; sense_twist{2}; sense_twist{3}];
            objective = [zeros(6,1); 1];
            
            model = struct('A',sparse(A),'sense',sense,'rhs',rhs,'lb',[-inf(6,1);0],'obj',objective);
            params = struct('OutputFlag', 0);
            sln = gurobi2linprog(model, params);
            
            if ~strcmp(sln.status, 'OPTIMAL')
                c = [];
                cbar = [];
                return;
            end
            
            c = sln.x(1:3);
            cbar = sln.x(4:6);
        end
        
        function [c,cbar] = solveWithoutLoad(g,dg,ddg,lb,reg_weight)
            [c,cbar] = EquilibriumCurve.solveWithIntegratedLoad(g,dg,ddg,[],[],lb,reg_weight);
        end
        
        function [c,cbar] = solveWithLineLoad(s,g,dg,ddg,a,lb,reg_weight)
            seg_lengths = s(2:end) - s(1:end-1);
            a_mid = 0.5 * (a(:,1:end-1) + a(:,2:end));
            A = [zeros(3,1), cumsum(seg_lengths.*a_mid,2)];
            abar = cross(a,g,1);
            abar_mid = 0.5 * (abar(:,1:end-1) + abar(:,2:end));
            Abar = [zeros(3,1), cumsum(seg_lengths.*abar_mid,2)];
            
            [c,cbar] = EquilibriumCurve.solveWithIntegratedLoad(g,dg,ddg,A,Abar,lb,reg_weight);
        end
        
        function [c,cbar] = solveWithWeight(g,dg,ddg, i_last_before_mass, g_mass, mg, reg_weight)
            n = size(g,2);
            
            % v = gamma' x gamma''
            v = cross(dg,ddg,1);
            c_coeff = cross(g,v,1)';
            cbar_coeff = v';
            mass_moment = cross(repmat(mg,1,n), g-g_mass, 1);
            weight_term = 0.5*sum(v.*mass_moment, 1)';
            weight_term(1:i_last_before_mass) = -weight_term(1:i_last_before_mass);
            rhs_dgdgg = 1-weight_term;
            A_dgdgg = [c_coeff cbar_coeff zeros(n,1)];
            sense_dgdgg = repmat('>',n,1);
            
            % Twist couple constraints: v1 = gamma', v2 = gamma''/kappa
            v_twist = {dg, ddg./sqrt(sum(ddg.^2,1))};
            rhs_twist = cell(2,1);
            A_twist = cell(2,1);
            sense_twist = cell(2,1);
            for i=1:2
                c_coeff = cross(g,v_twist{i},1)';
                cbar_coeff = v_twist{i}';
                weight_term = 0.5*sum(v.*mass_moment, 1)';
                weight_term(1:i_last_before_mass) = -weight_term(1:i_last_before_mass);
                
                A_twist{i} = [c_coeff cbar_coeff ones(n,1); ...
                    c_coeff cbar_coeff -ones(n,1)];
                rhs_twist{i} = [-weight_term; -weight_term];
                sense_twist{i} = [repmat('>',n,1); repmat('<',n,1)];
            end
            A_twist{2}(:,7) = A_twist{2}(:,7) / reg_weight;
            
            % Assemble
            A = [A_dgdgg; A_twist{1}; A_twist{2}];
            rhs = [rhs_dgdgg; rhs_twist{1}; rhs_twist{2}];
            sense = [sense_dgdgg; sense_twist{1}; sense_twist{2}];
            objective = [zeros(6,1); 1];
            
%             [Aineq,bineq] = LPHelper.gurobiToMatlab(A,rhs,sense);
%             [x,~,exitflag] = linprog(objective,Aineq,bineq);
%             if exitflag == 1
%                 c = x(1:3);
%                 cbar = x(4:6);
%             else
%                 c = [];
%                 cbar = [];
%             end
            
            model = struct('A',sparse(A),'sense',sense,'rhs',rhs,'lb',[-inf(6,1);0],'obj',objective);
            params = struct('OutputFlag', 0);
            sln = gurobi2linprog(model, params);
            
            if ~strcmp(sln.status, 'OPTIMAL')
                c = [];
                cbar = [];
                return;
            end
            
            c = sln.x(1:3);
            cbar = sln.x(4:6);
        end
        
        function ret = testFeasibilityWithWeight(g,dg,ddg,i_last_before_mass, g_mass, mg,c,cbar)
            cs = [c - 0.5*mg, c + 0.5*mg];
            cbars = [cbar + 0.5*cross(mg,g_mass), cbar - 0.5*cross(mg,g_mass)];
            
            n = size(g,2);
            seg_i = 2 - double((1:n) <= i_last_before_mass);
            c = cs(:,seg_i);
            cbar = cbars(:,seg_i);
            hel = cross(c,g,1) + cbar;
            dgcddg = cross(dg,ddg,1);
            ind = sum(dgcddg.*hel, 1);
            ret = all(ind > 0);
%             
%             for i=1:n
%                 seg_i = 2 - double(i<=i_last_before_mass);
%                 c = cs(:,seg_i);
%                 cbar = cbars(:,seg_i);
%                 
%                 hel = cross(c,g(:,i)) + cbar;
%                 ind = dot(cross(dg(:,i), ddg(:,i)), hel);
%             end
        end
        
        function rod_fcn = solveWithFixedCoefficients(curve_fcn, c, cbar, l, nu, rel_tol, abs_tol)
            [~, dg_start] = curve_fcn(0);
            
            if nargin < 6 || isempty(rel_tol)
                rel_tol = 1.e-6;
            end
            if nargin < 7 || isempty(abs_tol)
                abs_tol = 1.e-8;
            end
            ode_options = odeset('RelTol',rel_tol,'AbsTol',abs_tol);
            
            n2_start = GeometryHelper.generateBasis(dg_start);
            framed_curve_fcn = CurveHelper.computeParallelFrame(curve_fcn, l, n2_start, ...
                ode_options.RelTol,ode_options.AbsTol);
            
            muOverE = 1/(2*(1+nu));
            beta_sol = ode45(@(s,beta) EquilibriumCurve.beta_ode_fcn(s,beta,framed_curve_fcn,c,cbar,muOverE), ...
                [0 l], 0, ode_options);
            
            rod_fcn = @(s) EquilibriumCurve.evaluateRod(s, beta_sol, framed_curve_fcn, c, cbar, muOverE);
        end
        
        function max_err = verifyEquilibrium(rod_fcn, c, cbar, l, nu, num_samples)
            if nargin < 4
                num_samples = 401;
            end
            muOverE = 1/(2*(1+nu));
            s = linspace(0,l,num_samples);
            [g,Fbeta, kbeta, I, J] = rod_fcn(s);
            
            hel = cross(repmat(c,1,num_samples), g, 1) + cbar;
            Ikn = permute(I(:,1,:),[1 3 2]) .* kbeta(1,:) + permute(I(:,2,:),[1 3 2]) .* kbeta(2,:);
            FnIkn = permute(Fbeta(:,1,:),[1 3 2]) .* Ikn(1,:) + permute(Fbeta(:,2,:),[1 3 2]) .* Ikn(2,:);
            lhs = FnIkn + muOverE * J .* kbeta(3,:) .* permute(Fbeta(:,3,:),[1 3 2]);
            dif = hel - lhs;
            max_err = max(abs(dif(:)));
        end
    end
    
    methods(Static)
        function dbeta = beta_ode_fcn(s, beta, framed_curve_fcn, c, cbar, muOverE)
            [g,dg,n2,k] = framed_curve_fcn(s);
            n1 = cross(n2,dg);
            hel = cross(c,g)+cbar;
            
            kn = k([1 2]);
            Fnthel = [n1 n2]' * hel;
            [I0,d] = KirchhoffRodGeometry.computeSPDMatrixFamily(kn,Fnthel);
            Ibeta = KirchhoffRodGeometry.computeMostCircularCrossSections(I0,d);
            Qbeta = [cos(beta) -sin(beta); sin(beta) cos(beta)];
            I = Qbeta' * Ibeta * Qbeta;
            
            J = 4*det(I)/trace(I);
            dbeta = dot(dg, hel) / (J*muOverE);
        end
        
        function [g,Fbeta, kbeta, I, J] = evaluateRod(s, beta_sol, framed_curve_fcn, c, cbar, muOverE)
            ns = length(s);
            [g,dg,n2,k] = framed_curve_fcn(s);
            beta = deval(beta_sol,s);
            n1 = cross(n2,dg,1);
            hel = cross(repmat(c,1,ns),g,1)+cbar;
            
            kn = k([1 2],:);
            Fnthel = [sum(n1.*hel,1); sum(n2.*hel,1)];
            [I0,d] = KirchhoffRodGeometry.computeSPDMatrixFamily(kn,Fnthel);
            Ibeta = KirchhoffRodGeometry.computeMostCircularCrossSections(I0,d);
            
            cs = cos(beta);
            sn = sin(beta);
            cssqr = permute(cs.*cs,[1 3 2]);
            snsqr = permute(sn.*sn,[1 3 2]);
            cssn = permute(cs.*sn,[1 3 2]);
            offdiag = cssn.*(Ibeta(2,2,:)-Ibeta(1,1,:)) + (cssqr-snsqr).*Ibeta(1,2,:);
            v = 2*cssn.*Ibeta(1,2,:);
            I = [cssqr.*Ibeta(1,1,:)+v+snsqr.*Ibeta(2,2,:), offdiag; ...
                offdiag, snsqr.*Ibeta(1,1,:)-v+cssqr.*Ibeta(2,2,:)];
            
            J = permute(4*(I(1,1,:).*I(2,2,:) - I(1,2,:).*I(1,2,:)) ./ (I(1,1,:)+I(2,2,:)), [1 3 2]);
            tau = sum(dg.*hel,1) ./ (J*muOverE);
            
            k1beta = cs.*k(1,:) + sn.*k(2,:);
            k2beta = -sn.*k(1,:) + cs.*k(2,:);
            kbeta = [k1beta;k2beta;tau];
            
            n1beta = n1.*cs + n2.*sn;
            n2beta = -n1.*sn + n2.*cs;
            Fbeta = [permute(n1beta, [1 3 2]), permute(n2beta, [1 3 2]), permute(dg, [1 3 2])];
        end
    end
end
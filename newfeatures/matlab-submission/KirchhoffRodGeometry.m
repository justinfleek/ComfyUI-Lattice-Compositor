classdef KirchhoffRodGeometry < handle
    methods(Static)
        % a and b are parallel 2d column vectors such that <a,b> > 0. I is
        % such that Ia=b, and such that the radii of the elliptical cross
        % section described by I have a ratio of 'radius_ratio'.
        function I = computeSPDMatrixParallel(a,b,radius_ratio)
            a_sq_len = sum(a.^2,1);
            evalue1 = sum(a.*b,1) ./ a_sq_len;
            evec1 = a ./ sqrt(a_sq_len);
            evec2 = [-evec1(2,:); evec1(1,:)];
            evalue2 = radius_ratio^2 * evalue1;
            
            Ixx = evalue1 .* evec1(1,:).^2 + evalue2 .* evec2(1,:).^2;
            Ixy = evalue1 .* evec1(1,:).*evec1(2,:) + evalue2 .* evec2(1,:).*evec2(2,:);
            Iyy = evalue1 .* evec1(2,:).^2 + evalue2 .* evec2(2,:).^2;
            
            I = reshape([Ixx;Ixy;Ixy;Iyy],2,2,[]);
        end
        
        % Compute Istar according to Section 5.3 of the paper
        function [Istar, radii, frame] = ellipticizeStiffness(I,J,kn)
            kn_dir = kn/norm(kn);
            Q = [kn_dir'; [-kn_dir(2) kn_dir(1)]];
            Itilde = Q*I*Q';
            
            Itildestar = Itilde;
            Itildestar(2,2) = (J*Itilde(1,1) + 4*Itilde(1,2)^2) / (4*Itilde(1,1) - J);
            
            Istar = Q'*Itildestar*Q;
            [radii, frame] = KirchhoffRodGeometry.momentMatrixToEllipse(Istar);
        end
        
        % Compute the Kirchhoff rod geometry for the load-free case
        function [frames,k,Is,Js] = generateGeometryWithoutLoad(g,dg,ddg,c,cbar,E,mu,min_radius_ratio,p_soft_max)
            if nargin < 8
                min_radius_ratio = 1;
            end
            if nargin < 9
                p_soft_max = inf;
            end
            c_sigma = repmat(c,1,size(g,2));
            cbar_sigma = repmat(cbar,1,size(g,2));
            [frames,k,Is,Js] = KirchhoffRodGeometry.generateGeometryWithConstants(g,dg,ddg,c_sigma,cbar_sigma,E,mu,min_radius_ratio,p_soft_max);
        end
        
        % Compute the Kirchhoff rod geometry for the integrated load
        % Q=A, M=-Abar
        function [frames,k,Is,Js] = generateGeometryWithIntegratedLoad(g,dg,ddg,A,Abar,c,cbar,E,mu,min_radius_ratio,p_soft_max)
            if nargin < 10
                min_radius_ratio = 1;
            end
            if nargin < 11
                p_soft_max = inf;
            end
            c_sigma = c + A;
            cbar_sigma = cbar - Abar;
            [frames,k,Is,Js] = KirchhoffRodGeometry.generateGeometryWithConstants(g,dg,ddg,c_sigma,cbar_sigma,E,mu,min_radius_ratio,p_soft_max);
        end
        
        % Compute the Kirchhoff rod geometry for a line load
        function [frames,k,Is,Js] = generateGeometryWithLineLoad(g,dg,ddg,line_load, c,cbar,E,mu,min_radius_ratio,p_soft_max)
            if nargin < 9
                min_radius_ratio = 1;
            end
            if nargin < 10
                p_soft_max = inf;
            end
            to = g(:,2:end) - g(:,1:end-1);
            seg_lengths = sqrt(sum(to.^2,1));
            line_load_mid = 0.5*(line_load(:,1:end-1)+line_load(:,2:end));
            c_sigma = c + [zeros(3,1), cumsum(seg_lengths.*line_load_mid,2)];
            line_load_moment = cross(line_load, g, 1);
            line_load_moment_mid = 0.5*(line_load_moment(:,1:end-1)+line_load_moment(:,2:end));
            cbar_sigma = cbar - [zeros(3,1), cumsum(seg_lengths.*line_load_moment_mid,2)];
            
            [frames,k,Is,Js] = KirchhoffRodGeometry.generateGeometryWithConstants(g,dg,ddg,c_sigma,cbar_sigma,E,mu,min_radius_ratio,p_soft_max);
        end
        
        % Compute the Kirchhoff rod geometry for one point load
        function [frames,k,Is,Js] = generateGeometryWithWeights(g,dg,ddg,i_last_before_mass, g_mass, mg,c,cbar,E,mu,min_radius_ratio,p_soft_max)
            if nargin < 11
                min_radius_ratio = 1;
            end
            if nargin < 12
                p_soft_max = inf;
            end
            cs = [c - 0.5*mg, c + 0.5*mg];
            cbars = [cbar + 0.5*cross(mg,g_mass), cbar - 0.5*cross(mg,g_mass)];
            
            n = size(g,2);
            c_vector = [repmat(cs(:,1),1,i_last_before_mass), repmat(cs(:,2),1,n-i_last_before_mass)];
            cbar_vector = [repmat(cbars(:,1),1,i_last_before_mass), repmat(cbars(:,2),1,n-i_last_before_mass)];
            
            [frames,k,Is,Js] = KirchhoffRodGeometry.generateGeometryWithConstants(g,dg,ddg,c_vector,cbar_vector,E,mu,min_radius_ratio,p_soft_max);
        end
        
        % Compute the Kirchhoff rod geometry with load according to Section
        % 8.3 and 9.2 (Step 2), where c_vector = c+Q, and cbar_vector =
        % cbar+M.
        function [frames,k,Is,Js] = generateGeometryWithConstants(g,dg,ddg,c_vector,cbar_vector,E,mu,min_radius_ratio,p_soft_max)
            if nargin < 8
                min_radius_ratio = 1;
            end
            if nargin < 9
                p_soft_max = inf;
            end
            n = size(g,2);
            to = g(:,2:end) - g(:,1:end-1);
            seg_lengths = sqrt(sum(to.^2,1));
            
            frames = zeros(3,3,n);
            Is = zeros(2,2,n);
            Js = zeros(1,n);
            k = zeros(3,n);
            [n1,n2] = GeometryHelper.generateBasis(dg(:,1));
            frames(:,:,1) = [n1 n2 dg(:,1)];
            for i=1:n
                c = c_vector(:,i);
                cbar = cbar_vector(:,i);
                F_n = frames(:,[1 2],i);
                k_n = F_n' * cross(dg(:,i), ddg(:,i));
                hel = cross(c, g(:,i)) + cbar;
                y = F_n' * hel;
                x = E * k_n;
                Jx = [-x(2); x(1)];
                Istar = (1/dot(x,y)) * (y*y' + (dot(y,y)/dot(x,x))*(Jx*Jx'));
                [~,eigvals] = eig(Istar);
                radius_ratio = sqrt(eigvals(2,2)/eigvals(1,1));
                if isinf(p_soft_max)
                    if radius_ratio < min_radius_ratio
                        % choose other
                        [~,I2] = KirchhoffRodGeometry.computeSPDWithEigenvalueRatio(x,y,min_radius_ratio^2);
                        Is(:,:,i) = I2;
                    else
                        Is(:,:,i) = Istar;
                    end
                else
                    rr_adjusted = (radius_ratio^p_soft_max + min_radius_ratio^p_soft_max)^(1/p_soft_max);
                    [~,I2] = KirchhoffRodGeometry.computeSPDWithEigenvalueRatio(x,y,rr_adjusted^2);
                    Is(:,:,i) = I2;
                end
%                 Is(:,:,i) = (1/dot(x,y)) * (y*y' + (dot(y,y)/dot(x,x))*(Jx*Jx'));
%                 Js(i) = 2*dot(x,y)/dot(x,x);
                Js(i) = 4*det(Is(:,:,i))/trace(Is(:,:,i));
                tau = (1/(mu*Js(i))) * dot(dg(:,i), hel);
                k(:,i) = [k_n;tau];
                
                if i < n
                    B = cross(dg(:,i),dg(:,i+1));
                    B = B/norm(B);
                    alpha = acos(dot(dg(:,i), dg(:,i+1)));
                    R_dihedral = rodrigues_rotation(B,alpha);
                    R_twist = rodrigues_rotation(dg(:,i),tau*seg_lengths(i));
                    frames(:,:,i+1) = R_dihedral * R_twist * frames(:,:,i);
                end
            end
        end
        
        % Computes the set of SPD matrices I satisfying Ia=b. a and b must
        % 2d vectors such that <a,b> > 0. Returns two 2-by-2 matrices I0
        % and d. I satisfies the requirements if
        % I=I0+lambda*d, with lambda>0.
        function [I0,d] = computeSPDMatrixFamily(a,b)
            aa = sum(a.^2,1);
            axay = a(1,:).*a(2,:);
            ax2 = a(1,:).*a(1,:);
            ay2 = a(2,:).*a(2,:);
            Ibar = (1./(aa.*aa-axay.*axay)) .* [...
                a(1,:).*(aa.*b(1,:)-axay.*b(2,:)); ...
                aa.*(a(2,:).*b(1,:)+a(1,:).*b(2,:))-axay.*sum(a.*b,1); ...
                a(2,:).*(aa.*b(2,:)-axay.*b(1,:))];
            
            d = reshape([ay2; -axay;-axay; ax2], 2, 2, []);
            
            lambda_lb = -(Ibar(1,:).*Ibar(3,:)-Ibar(2,:).^2)./(ay2.*Ibar(3,:)+ax2.*Ibar(1,:)+2*axay.*Ibar(2,:));
            I0 = reshape(Ibar([1 2 2 3],:), 2,2,[]) + permute(lambda_lb, [1 3 2]).*d;
        end
        
        % Among all SPD 2x2 matrices satisfying Ix=y, compute the ones with
        % eigenvalue ratio r.
        function [I1,I2] = computeSPDWithEigenvalueRatio(x,y,r)
            if r > 1
                r = 1/r;
            end
            root = sqrt((1+r)^2 * (2*(1+r)^2*x(1)*x(2)*y(1)*y(2)+x(2)^2*(-4*r*y(1)^2+(r-1)^2*y(2)^2)+x(1)^2*((r-1)^2*y(1)^2-4*r*y(2)^2)));
            a = -2*r*(x(2)*y(1)-x(1)*y(2))^2 + dot(x,y)^2*(1+r^2);
            denom = 2*r*dot(x,x)^2*dot(x,y);
            t1 =  (a - dot(x,y)*root)/denom;
            t2 =  (a + dot(x,y)*root)/denom;
            
            Jx = [-x(2);x(1)];
            I1 = (y*y')/dot(x,y) + t1*(Jx*Jx');
            I2 = (y*y')/dot(x,y) + t2*(Jx*Jx');
        end
        
        % The parameters correspond to the outputs of 'computeSPDMatrixFamily'.
        % Returns the matrix in the family with the condition number
        % closest to one, i.e., the one corresponding to the most circular
        % cross section.
        function I = computeMostCircularCrossSections(I0,d)
            t = (I0(1,1,:)+I0(2,2,:)) ./ (d(1,1,:)+d(2,2,:));
            I = I0 + t.*d;
        end
        
        % Compute elliptical areas based on radii
        function a = computeArea(radii)
            a = pi * radii(1,:) .* radii(2,:);
        end
        
        % I is the second area moment matrix of an ellipse; returns the two
        % axes of the ellipse with their radii
        function [radii, frame] = momentMatrixToEllipse(I)
            [V,D] = eig(I);
            if det(V) < 0
                frame = V(:,[2 1]);
                l1 = D(2,2);
                l2 = D(1,1);
            else
                frame = V;
                l1 = D(1,1);
                l2 = D(2,2);
            end
            f = 1.062251932027197e+00; % (pi/4)^(-1/4)
            radii = f*[l1^-0.125 * l2^0.375; l1^0.375 * l2^-0.125];
        end
        
        function [radii, frames] = momentMatricesToEllipse(I)
            traces = I(1,1,:) + I(2,2,:);
            dets = I(1,1,:).*I(2,2,:) - I(1,2,:).^2;
            q = sqrt(max(0,traces.^2 - 4*dets));
            evalues = (traces + [-q;q])*0.5;
            
            B = I;
            B(1,1,:) = B(1,1,:) - evalues(1,1,:);
            B(2,2,:) = B(2,2,:) - evalues(1,1,:);
            
            Bcol1_norm = sum(abs(B(:,1,:)), 1);
            Bcol2_norm = sum(abs(B(:,2,:)), 1);
            evec_unique = (Bcol1_norm + Bcol2_norm) > 1.e-15;
            col1_larger = Bcol1_norm > Bcol2_norm;
            use_col1 = evec_unique & col1_larger;
            use_col2 = evec_unique & ~col1_larger;
            
            evector1 = repmat([1;0],[1,1,size(I,3)]);
            evector1(1,1,use_col1) = sum(B(:,1,use_col1).*B(:,2,use_col1), 1) ./ sum(B(:,1,use_col1).^2);
            evector1(2,1,use_col1) = -1;
            evector1(1,1,use_col2) = -1;
            evector1(2,1,use_col2) = sum(B(:,1,use_col2).*B(:,2,use_col2), 1) ./ sum(B(:,2,use_col2).^2);
            
            evector1 = evector1 ./ sqrt(sum(evector1.^2,1));
            evector2 = [-evector1(2,1,:); evector1(1,1,:)];
            frames = [evector1 evector2];
            
            f = 1.062251932027197e+00; % (pi/4)^(-1/4)
            radii = f*[evalues(1,1,:).^-0.125 .* evalues(2,1,:).^0.375; ...
                evalues(1,1,:).^0.375 .* evalues(2,1,:).^-0.125];
            radii = permute(radii, [1 3 2]);
        end
        
        % Produces n samples along the boundary of the given ellipse, such
        % that the first sample is on the right side, and the samples are
        % ordered ccw.
        function V = sampleEllipse(radii,semi_axes,n)
            angles = linspace(0,2*pi,n+1);
            c = [cos(angles(1:end-1)); sin(angles(1:end-1))];
            V = semi_axes * (radii(:) .* (semi_axes' * c));
        end
        
        function V = sampleEllipses(radii,semi_axes,n)
            radii = permute(radii, [1 3 2]);
            angles = linspace(0,2*pi,n+1);
            c = [cos(angles(1:end-1)); sin(angles(1:end-1))];
            t1 = [sum(semi_axes(:,1,:) .* c, 1); sum(semi_axes(:,2,:) .* c, 1)];
            t2 = radii .* t1;
            t3x = sum(permute(semi_axes(1,:,:), [2 1 3]) .* t2, 1);
            t3y = sum(permute(semi_axes(2,:,:), [2 1 3]) .* t2, 1);
            V = [t3x; t3y];
        end
        
        function [V,F,C] = generateUndeformedGeometry(radii,semi_axes,s,n,add_caps,closed)
            if nargin < 5
                add_caps = true;
            end
            if nargin < 6
                closed = true;
            end
            V = KirchhoffRodGeometry.sampleEllipses(radii,semi_axes,n);
            V = [V; repmat(permute(s,[1 3 2]), [1 n 1])];
            V = reshape(V, 3, []);
            if ~closed
                m = size(radii,2);
                V = [V V(:,[1:n m*n-n+1:m*n])];
            end
            [F,C] = KirchhoffRodGeometry.triangulateCylinder(n,length(s),add_caps,true,closed);
        end
        
        function res = generateMoldCurve(radii, semi_axes, err_tol)
            if nargin < 3
                err_tol = 1.e-10;
            end
            
            n = size(radii, 2);
            
            A11 = radii(1,:).*permute(semi_axes(1,1,:),[1 3 2]).^2 + radii(2,:).*permute(semi_axes(1,2,:),[1 3 2]).^2;
            A12 = radii(1,:).*permute(semi_axes(1,1,:),[1 3 2]).*permute(semi_axes(2,1,:),[1 3 2]) ...
                + radii(2,:).*permute(semi_axes(1,2,:),[1 3 2]).*permute(semi_axes(2,2,:),[1 3 2]);
            A22 = radii(1,:).*permute(semi_axes(2,1,:),[1 3 2]).^2 + radii(2,:).*permute(semi_axes(2,2,:),[1 3 2]).^2;
            
            a = zeros(1,n);
            b = zeros(1,n);
            a(A12>=0) = pi/2;
            b(A12<0) = -pi/2;
            
            fa = -sin(a).*A11 + cos(a).*A12;
            fb = -sin(b).*A11 + cos(b).*A12;
            while any(abs(fa)>err_tol & abs(fb)>err_tol)
                c = (a.*fb - b.*fa)./(fb-fa);
                b(c>=0) = c(c>=0);
                a(c<0) = c(c<0);
                fa = -sin(a).*A11 + cos(a).*A12;
                fb = -sin(b).*A11 + cos(b).*A12;
            end
            
            s = a;
            s(abs(fb) < abs(fa)) = b(abs(fb) < abs(fa));
            cs = cos(s);
            sn = sin(s);
            res = [A11.*cs + A12.*sn; A12.*cs + A22.*sn];
        end
        
        % Exports a FeatureScript that generates the undeformed rod as a
        % CAD model
        function str = generateUndeformedFeatureScript(radii,semi_axes,s,unit_string,feature_name)
            if nargin < 4
                unit_string = "millimeter";
            end
            if nargin < 5
                feature_name = "Undeformed Rod";
            end
            template_file = fopen('fs-templates/undeformed_rod_fs_template.txt');
            str = fscanf(template_file,'%c');
            fclose(template_file);
            
            m = length(s);
            str = replace(str, '%M%', num2str(m));
            str = replace(str, '%UNIT%', unit_string);
            str = replace(str, '%FEATURE_NAME%', feature_name);
            var_name = erase(erase(feature_name, '-'), '_');
            str = replace(str, '%VAR_NAME%', var_name);
            
            s_all = sprintf('%.15g,',s);
            s_def = ['var s = [' s_all(1:end-1) '];'];
            r1_all = sprintf('%.15g,',radii(1,:));
            r1_def = ['var r1 = [' r1_all(1:end-1) '];'];
            r2_all = sprintf('%.15g,',radii(2,:));
            r2_def = ['var r2 = [' r2_all(1:end-1) '];'];
            ax_all = sprintf('vector(%.15g,%.15g),',semi_axes(:,1,:));
            ax_def = ['var ax = [' ax_all(1:end-1) '];'];
            
            str = replace(str, '%S_DEF%', s_def);
            str = replace(str, '%R1_DEF%', r1_def);
            str = replace(str, '%R2_DEF%', r2_def);
            str = replace(str, '%AX_DEF%', ax_def);
            
%             output_file = fopen(output_path,'w');
%             fprintf(output_file, '%s', str);
%             fclose(output_file);
        end
        
        % Exports a FeatureScript that generates the deformed rod as a
        % CAD model, with extrusions at both ends
        % (gamma,F,radii,semi_axes,n,add_caps,closed)
        function str = generateDeformedFeatureScript(gamma,F,radii,semi_axes,unit_string,feature_name)
            if nargin < 5
                unit_string = "millimeter";
            end
            if nargin < 6
                feature_name = "Deformed Rod";
            end
            template_file = fopen('fs-templates/deformed_rod_fs_template.txt');
            str = fscanf(template_file,'%c');
            fclose(template_file);
            
%             gamma = [gamma(:,1)-extrude*F(:,3,1), gamma, gamma(:,end)+extrude*F(:,3,end)];
%             F = F(:,:,[1 1:end end]);
%             radii = radii(:,[1 1:end end]);
%             semi_axes = semi_axes(:,[1 1:end end]);
            
            m = size(gamma,2);
            str = replace(str, '%M%', num2str(m));
            str = replace(str, '%UNIT%', unit_string);
            str = replace(str, '%FEATURE_NAME%', feature_name);
            var_name = erase(erase(feature_name, '-'), '_');
            str = replace(str, '%VAR_NAME%', var_name);
            
            gamma_all = sprintf('vector(%.15g,%.15g,%.15g),',gamma);
            gamma_def = ['var gamma = [' gamma_all(1:end-1) '];'];
            dgamma_all = sprintf('vector(%.15g,%.15g,%.15g),',F(:,3,:));
            dgamma_def = ['var dgamma = [' dgamma_all(1:end-1) '];'];
            n1_all = sprintf('vector(%.15g,%.15g,%.15g),',F(:,1,:));
            n1_def = ['var n1 = [' n1_all(1:end-1) '];'];
            r1_all = sprintf('%.15g,',radii(1,:));
            r1_def = ['var r1 = [' r1_all(1:end-1) '];'];
            r2_all = sprintf('%.15g,',radii(2,:));
            r2_def = ['var r2 = [' r2_all(1:end-1) '];'];
            ax_all = sprintf('vector(%.15g,%.15g),',semi_axes(:,1,:));
            ax_def = ['var ax = [' ax_all(1:end-1) '];'];
            
            str = replace(str, '%GAMMA_DEF%', gamma_def);
            str = replace(str, '%DGAMMA_DEF%', dgamma_def);
            str = replace(str, '%N1_DEF%', n1_def);
            str = replace(str, '%R1_DEF%', r1_def);
            str = replace(str, '%R2_DEF%', r2_def);
            str = replace(str, '%AX_DEF%', ax_def);
            
%             output_file = fopen(output_path,'w');
%             fprintf(output_file, '%s', str);
%             fclose(output_file);
        end
        
        function str = generateLedStripScript(centers,normals,radii,unit_string,feature_name)
            if nargin < 4
                unit_string = "millimeter";
            end
            if nargin < 5
                feature_name = "Led Strip";
            end
            template_file = fopen('fs-templates/led_strip_fs_template.txt');
            str = fscanf(template_file,'%c');
            fclose(template_file);
            
            m = size(centers,2);
            str = replace(str, '%M%', num2str(m));
            str = replace(str, '%UNIT%', unit_string);
            str = replace(str, '%FEATURE_NAME%', feature_name);
            var_name = erase(erase(feature_name, '-'), '_');
            str = replace(str, '%VAR_NAME%', var_name);
            
            centers_all = sprintf('vector(%.15g,%.15g,%.15g),',centers);
            centers_def = ['var center = [' centers_all(1:end-1) '];'];
            normals_all = sprintf('vector(%.15g,%.15g,%.15g),',normals);
            normals_def = ['var normal = [' normals_all(1:end-1) '];'];
            r_all = sprintf('%.15g,',radii);
            r_def = ['var r = [' r_all(1:end-1) '];'];
            
            str = replace(str, '%CENTER_DEF%', centers_def);
            str = replace(str, '%NORMAL_DEF%', normals_def);
            str = replace(str, '%R_DEF%', r_def);
        end
        
        function str = generateMoldingSurfacesFeatureScript(p,s,xmax,unit_string,xtol,feature_name)
            if nargin < 5
                xtol = 0.0;
            end
            if nargin < 6
                feature_name = "Mold Surfaces";
            end
            template_file = fopen('fs-templates/molding_surfaces_fs_template.txt');
            str = fscanf(template_file,'%c');
            fclose(template_file);
            
            s = [s(1)-xmax, s, s(end)+xmax];
            p = p(:,[1 1:end end]);
            
            m = length(s);
            str = replace(str, '%M%', num2str(m));
            str = replace(str, '%UNIT%', unit_string);
            str = replace(str, '%XMAX%', sprintf('%.15g', xmax));
            str = replace(str, '%XTOL%', sprintf('%.15g', xtol));
            str = replace(str, '%FEATURE_NAME%', feature_name);
            var_name = erase(erase(feature_name, '-'), '_');
            str = replace(str, '%VAR_NAME%', var_name);
            
            s_all = sprintf('%.15g,',s);
            s_def = ['var s = [' s_all(1:end-1) '];'];
            p_all = sprintf('vector(%.15g,%.15g),',p);
            p_def = ['var p = [' p_all(1:end-1) '];'];
            
            str = replace(str, '%S_DEF%', s_def);
            str = replace(str, '%P_DEF%', p_def);

%             output_file = fopen(output_path,'w');
%             fprintf(output_file, '%s', str);
%             fclose(output_file);
        end
        
        function exportAllScripts(path,s,g,frames,radii,semi_axes,unit_string,feature_name)
            if nargin < 8
                feature_name = 'Rod';
            end
            script1 = KirchhoffRodGeometry.generateUndeformedFeatureScript(radii,semi_axes,s,unit_string, [feature_name '-undef']);
            
            p = KirchhoffRodGeometry.generateMoldCurve(radii, semi_axes);
            xmax = 5 * max(p(1,:));
            xtol = 0.5 * min(radii(:));
            script2 = KirchhoffRodGeometry.generateMoldingSurfacesFeatureScript(p,s,xmax,unit_string,xtol, [feature_name '-sepsurf']);
            
            script3 = KirchhoffRodGeometry.generateDeformedFeatureScript(g,frames,radii,semi_axes,unit_string, [feature_name '-def']);

            FeatureScriptHelper.export(path, {script1, script2, script3});
        end
        
        function [V,F,C] = generateDeformedGeometry(gamma,frame,radii,semi_axes,n,add_caps,closed)
            if nargin < 6
                add_caps = true;
            end
            if nargin < 7
                closed = true;
            end
            V = KirchhoffRodGeometry.sampleEllipses(radii,semi_axes,n);
            V = [V; zeros(1,n,size(gamma,2))];
            Ft = permute(frame,[2 1 3]);
            V = [sum(Ft(:,1,:) .* V, 1); sum(Ft(:,2,:) .* V, 1); sum(Ft(:,3,:) .* V, 1)];
            V = V + permute(gamma, [1 3 2]);
            V = reshape(V, 3, []);
            if ~closed
                m = size(gamma,2);
                V = [V V(:,[1:n m*n-n+1:m*n])];
            end
            [F,C] = KirchhoffRodGeometry.triangulateCylinder(n,size(gamma,2),add_caps,true,closed);
        end
        
        % Assumes their are n samples on every cross section, and m cross
        % sections along the length of the cylinder.
        function [F,C] = triangulateCylinder(n,m,add_caps,reversed,closed)
            if nargin < 3
                add_caps = true;
            end
            if nargin < 4
                reversed = false;
            end
            if nargin < 5
                closed = true;
            end
            
            A = reshape(1:n*m, n, m);
            A = A([1:end 1],:);
            F1 = A(1:end-1,1:end-1);
            F2 = A(1:end-1,2:end);
            F3 = A(2:end,2:end);
            F4 = A(2:end,1:end-1);
            F = [F1(:) F2(:) F3(:) F1(:) F3(:) F4(:)]';
            F = reshape(F, 3, []);
            if add_caps
                cap1 = [ones(1,n-2);2:n-1;3:n];
                cap2 = [repmat(n*m-n+1,1,n-2);n*m:-1:n*m-n+3;n*m-1:-1:n*m-n+2];
                if ~closed
                    cap1 = cap1 + m*n;
                    cap2 = cap2 + 2*n;
                end
                F = [F cap1 cap2];
            end
            
            if reversed
                F = F([1 3 2],:);
            end
            
            if nargout > 1
                % provide stripe pattern (for visualizing twist)
                pattern = zeros(1,n)';
                pattern(1:round(n*0.25)) = 1;
                pattern(round(n*0.5)+1:round(n*0.75)) = 1;
                C = repmat(kron(pattern,[1;1]),m-1,1);
                if add_caps
                    C = [C;zeros(2*(n-2),1)];
                end
                C = C';
            end
        end
    end
end
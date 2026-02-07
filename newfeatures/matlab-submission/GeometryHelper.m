classdef GeometryHelper < handle
    methods(Static)
        % Returns the centroid and normal of every face. The returned
        % normals are scaled with the average edge length of edge triangle.
        function [P,N] = generateVisualizationNormals(V,F)
            V1 = V(:,F(1,:));
            V2 = V(:,F(2,:));
            V3 = V(:,F(3,:));
            P = (1/3) * (V1+V2+V3);
            N = cross(V2-V1,V3-V1);
            N = N./sqrt(sum(N.^2,1));
            lens = (1/6) * (sqrt(sum((V2-V1).^2,1)) + sqrt(sum((V3-V2).^2,1)) + sqrt(sum((V1-V3).^2,1)));
            N = N .* lens;
        end
        
        % Returns a frame F consisting of three edges, attached to every
        % point in gamma. The edges are scaled by 'l'. Colors R,G,B are
        % returns for the x, y and z directions of every frame.
        function [V,E,C] = generateFramesAlongCurve(gamma,F,l)
            n = size(gamma,2);
            V = [gamma, ...
                gamma+permute(F(:,1,:), [1 3 2])*l, ...
                gamma+permute(F(:,2,:), [1 3 2])*l, ...
                gamma+permute(F(:,3,:), [1 3 2])*l];
            E = [n+1:4*n;[1:n,1:n,1:n]];
            C = kron([[0;0;0],eye(3)],ones(1,n));
        end
        
        function col = convertToKirchhoffColors(C)
            col = zeros(3, length(C));
            col(:,logical(C)) = repmat([15;153;144]/255,1,nnz(C));
            col(:,~logical(C)) = repmat([84;63;173]/255,1,length(C)-nnz(C));
        end
        
        function addKirchhoffLights(ax)
            if nargin < 1
                lightangle(0,90);
                for az=[-120 0 120]
                    lgt = lightangle(az,-45);
                    lgt.Color = [0.7 0.7 0.7];
                end
            else
                lightangle(ax,0,90);
                for az=[-120 0 120]
                    lgt = lightangle(ax,az,-45);
                    lgt.Color = [0.7 0.7 0.7];
                end
            end
        end
        
        % Generates the parameters for a helix
        % gamma: t |-> o+Q*(r cos t, r sin t, h t),
        % with radius r, pitch h, origin o, and rotation matrix Q,
        % such that gamma(0) = x, and gamma'(t) || cross(c,gamma(s))+cbar
        function [r,h,o,Q] = helixParameters(c,cbar,x0)
            o = cross(c,cbar)/dot(c,c);
            lambda = dot(x0-o,c)/dot(c,c);
            o = o + lambda*c;
            e3 = c/norm(c);
            r = norm(x0-o);
            e1 = (x0-o)/r;
            e2 = cross(e3,e1);
            Q = [e1 e2 e3];
%             v = cross(c,x0)+cbar;
%             h = r*dot(v,e3)/dot(v,e2);
            h = dot(c,cbar)/dot(c,c);
            
%             dg = Q*[-r*sin(0);r*cos(0);h];
%             hel = cross(c,x0)+cbar;
%             x0hel = o+Q*[r*cos(0);r*sin(0);0];
        end
        
        function ret = drawKirchhoffGeometry(V,F,C)
            ret = patch('Vertices',V','Faces',F','FaceVertexCData',C','EdgeColor','none','FaceColor','flat',...
                'SpecularStrength', 0.4, 'FaceLighting', 'gouraud');
        end
        
        function F = generateStripFaces(n,reverse)
            if nargin < 2
                reverse = false;
            end
            F = reshape([1:n-1;n+2:2*n;n+1:2*n-1;1:n-1;2:n;n+2:2*n],3,[]);
            if reverse
                F = F([1 3 2],:);
            end
        end
        
        function F = generateMeshGridFaces(nvx,nvy)
            i_mat = reshape(1:nvx*nvy, nvy, nvx);
            i1 = i_mat(1:end-1,1:end-1);
            i2 = i_mat(1:end-1,2:end);
            i3 = i_mat(2:end,2:end);
            i4 = i_mat(2:end,1:end-1);
            F = [i1(:) i2(:) i3(:) i1(:) i3(:) i4(:)];
            F = reshape(F',3,[]);
        end
        
        function [n1,n2,t] = generateBasis(tangent_dir)
            t = tangent_dir / norm(tangent_dir);
            tabs = abs(t);
            if tabs(1) < tabs(2) && tabs(1) < tabs(3)
                n1 = [0;t(3);-t(2)];
            elseif tabs(2) < tabs(3)
                n1 = [-t(3);0;t(1)];
            else
                n1 = [t(2);-t(1);0];
            end
            n1 = n1 / norm(n1);
            n2 = cross(t,n1);
        end
        
        function ret = facesFrontFacing(V,F,view_vector)
            if nargin < 3
                [az,el] = view();
                view_vector = rodrigues_rotation([0;0;1],az/180*pi) * rodrigues_rotation([-1;0;0],el/180*pi) * [0;1;0];
            end
            V1 = V(:,F(1,:));
            V2 = V(:,F(2,:));
            V3 = V(:,F(3,:));
            n = cross(V2-V1,V3-V1,1);
            ret = sum(n.*view_vector(:),1) < 0;
        end
        
        % Returns the intersections of the ellipse with positive x- and y-
        % semiaxes.
        function [x,y] = computeEllipseAxisIntersection(a,b,angle)
            cs = cos(angle);
            sn = sin(angle);
            x = fzero(@(s) (s*cs)^2/a^2 + (s*sn)^2/b^2 - 1, [min(a,b)*0.9, max(a,b)*1.1]);
            y = fzero(@(s) (s*sn)^2/a^2 + (s*cs)^2/b^2 - 1, [min(a,b)*0.9, max(a,b)*1.1]);
        end

        function [V,F] = makeCuboid(lb,ub)
            F = 1+reshape([2, 6, 7, 2, 3, 7,0, 4, 5,0, 1, 5,0, 2, 6,0, 4, 6,1, 3, 7,1, 5, 7,0, 2, 3,0, 1, 3,4, 6, 7,4, 5, 7],3,[]);
            V = reshape([lb(1),lb(2),ub(3),ub(1),lb(2),ub(3),lb(1),ub(2),ub(3),ub(1),ub(2),ub(3),lb(1),lb(2),lb(3),ub(1),lb(2),lb(3),lb(1),ub(2),lb(3),ub(1),ub(2),lb(3)],3,[]);
        end

        function [V,F] = makeCylinder(p1,p2,r,num_samples,add_caps,closed)
            gamma = [p1, p2];
            g_to = p2-p1;
            dir = g_to/norm(g_to);
            [n1,n2,t] = GeometryHelper.generateBasis(dir);
            frame = repmat([n1 n2 t],1,1,2);
            radii = [r r];
            semi_axes = repmat(eye(2),1,1,2);

            [V,F] = KirchhoffRodGeometry.generateDeformedGeometry(gamma,frame,radii,semi_axes,num_samples,add_caps,closed);
        end
    end
end
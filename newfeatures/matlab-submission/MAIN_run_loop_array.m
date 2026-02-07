% Script to reproduce the "Loop Array" example from the paper.

% Enable to run forward simulation on the result of the computational
% design algorithm. If the result changes significantly during that step,
% something went wrong, and the output was not at (a stable) equilibrium.
do_forward_simulation_for_verification = false;

% Parameter to choose curve from curve family
bz_samples = linspace(0., 2.8, 8);
bz_samples = bz_samples([1 2 4 6 7 8]);

% Setting up graphics output
fig_deformed = figure();
title('Deformed rods');
GeometryHelper.addKirchhoffLights();
deformed_max_angle = (3/4)*3.7*3.5/180*pi;
deformed_radius = -1;
min_radius_ratio = 1.5;
num_samples = 401;

fig_undeformed = figure();
title('Undeformed rods');
GeometryHelper.addKirchhoffLights();

hold on;

% Iterate over all curves chosen from family
for bz_i=1:length(bz_samples)
    % Sample i-th input curve with 1st and 2nd derivatives
    bz = bz_samples(bz_i);
    t_range = [-pi pi];
    t_samples = linspace(t_range(1), t_range(2), num_samples);
    [g,dg,ddg] = curve_fcn(t_samples,bz);

    % Rescale curve and rescale 1st and 2nd derivatives as if it was an
    % arc-length parametrization
    A = diag(0.022*ones(1,3));
    g = A*g;
    dg = A*dg;
    ddg = A*ddg;
    g_to = g(:,2:end)-g(:,1:end-1);
    seg_lengths = sqrt(sum(g_to.^2,1));
    s = [0 cumsum(seg_lengths)];
    total_length = s(end);
    [dg,ddg,kappa] = CurveHelper.makeCurveSamplesArcLength(dg,ddg);

    % Solve for the parameters of the linear complex (without load)
    lb = 0.1;
    reg_weight = 1.5;
    [c,cbar] = EquilibriumCurve.solveWithoutLoad(g,dg,ddg,lb,reg_weight);
    
    density = 1.25e3; % in kg/m^3
    gravity = [0;0;9.8]; % Gravitational acceleration, in m/s^2
    E = 2.3e6; % Young's modulus in Pascal; from measurement for SmoothSil 960
    nu = 0.48; % Poisson's ratio
    mu = E/(2*(1+nu)); % Shear modulus

    % Compute geometry of rod for load-free solution
    [frames,k,Is,Js] = KirchhoffRodGeometry.generateGeometryWithoutLoad(g,dg,ddg,c,cbar,E,mu,1.5);
    [radii, semi_axes] = KirchhoffRodGeometry.momentMatricesToEllipse(Is);



    %%%% Post-process for dead load

    % Compute line load due to gravity, based on load-free solution
    areas = KirchhoffRodGeometry.computeArea(radii);
    line_load = (density*gravity)*areas;
    [Q,M] = AsfromLineLoad(line_load, g, seg_lengths);

    % Heuristically compute c and cbar (according to Section 9.2, Step 1)
    c = c - 0.5*(min(Q,[],2) + max(Q,[],2));
    cbar = cbar - 0.5*(min(M,[],2) + max(M,[],2));

    % Fixed-point iteration
    for i=1:50
        % Compute Q and M of current iterate
        areas = KirchhoffRodGeometry.computeArea(radii);
        line_load = (density*gravity)*areas;
        [Q,M] = AsfromLineLoad(line_load, g, seg_lengths);
        Is_old = Is;
        k_old = k;

        % Compute geometry assuming Q and M fixed to define next iterate
        [frames,k,Is,Js] = KirchhoffRodGeometry.generateGeometryWithIntegratedLoad(g,dg,ddg,Q,-M,c,cbar,E,mu,min_radius_ratio);
        [radii, semi_axes] = KirchhoffRodGeometry.momentMatricesToEllipse(Is);

        max_err = max(abs([Is(:)-Is_old(:); k(:)-k_old(:)]));

        if max_err < 1.e-10
            break;
        end
    end
    fprintf('%u iterations\n',i);
    
    if do_forward_simulation_for_verification
        % Forward-simulate with deadload (if you see the curve move around, the
        % solution provided by the inverse design algorithm is not a stable
        % equilibrium!)
        sim = makeSim(seg_lengths, E, mu, Is, Js, g, dg, frames);
        vertex_areas = pi * radii(1,:).*radii(2,:);
        vertex_masses = density * vertex_areas .* sim.vertex_weights;
        sim.setVertexMasses(vertex_masses);
        sim.solve();
    end

    % Generate and draw deformed geometry
    figure(fig_deformed);
    [V,F,C] = KirchhoffRodGeometry.generateDeformedGeometry(g,frames,radii,semi_axes,64,true,false);
    angle = 2*(bz_i-1)/(length(bz_samples)-1)-1;
    angle = -deformed_max_angle * angle;
    rot_mat = rodrigues_rotation([0;0;1], angle);
    V = rot_mat*V;
    origin = deformed_radius*[cos(angle);sin(angle);0]-[deformed_radius;0;0];
    V = V+origin;
    C = GeometryHelper.convertToKirchhoffColors(C);

    GeometryHelper.drawKirchhoffGeometry(V,F,C);
    view(20,20);
    axis tight equal vis3d;

    % Render undeformed geometry
    figure(fig_undeformed);
    Vun = KirchhoffRodGeometry.generateUndeformedGeometry(radii,semi_axes,s,64,true,false);
    Vun = bz_i*[0;0;-0.03] + rodrigues_rotation([0;1;0], pi/2) * Vun;
    GeometryHelper.drawKirchhoffGeometry(Vun,F,C);
    view(20,20);
    axis tight equal vis3d;

    % Generate a file containing FeatureScripts. They can be executed in
    % the CAD browser app OnShape to generate the geometry as CAD geometry.
    KirchhoffRodGeometry.exportAllScripts(sprintf('output/dog/dog-fs-%u.txt',bz_i),s,g,frames,radii,semi_axes,'meter',sprintf('dog-%u',bz_i));
end

% Define family of curves. bz is the parameter that picks a curve from the
% family, and t is the curve parameter (not arc-length)
% bz |-> (t |-> \gamma_bz(t))
function [g,dg,ddg] = curve_fcn(t, bz)
    a = 1;
    bx = 2;
    var = 3;
    w = 2;
    
    z = bz*sin(t) - a*t;
    x = bx*cos(t)+bx;
    y = -2*w/var * t .* exp(-t.^2 / var);
    
    g = [x;y;z];
    dg = [-bx*sin(t); -2*w/var*(1-2*t.^2/var).*exp(-t.^2/var); bz*cos(t)-a];
    ddg = [-bx*cos(t); -2*w/var*(-6*t/var + 4*t.^3/var^2).*exp(-t.^2/var); -bz*sin(t)];
end

% Method for integrating load distribution (consisting of line loads and
% point loads), according to Section 9.1 in the paper
function [Q,M] = AsfromLineLoad(line_load, g, seg_lengths, point_weights, i_point_weights)
    if nargin < 4
        point_weights = zeros(3,0);
        i_point_weights = zeros(1,0);
    end
    w_points = zeros(size(g));
    w_points(:,i_point_weights) = point_weights;
    ll_mid = 0.5*(line_load(:,1:end-1)+line_load(:,2:end));
    Q = [zeros(3,1) cumsum(seg_lengths.*ll_mid,2)] + cumsum(w_points, 2);
    
    m_points = zeros(size(g));
    m_points(:,i_point_weights) = cross(g(:,i_point_weights), point_weights, 1);
    llm = cross(g,line_load,1);
    llm_mid = 0.5*(llm(:,1:end-1)+llm(:,2:end));
    M = [zeros(3,1) cumsum(seg_lengths.*llm_mid,2)] + cumsum(m_points, 2);
end

% Short hand for instantiating forward simulation
function sim = makeSim(seg_lengths, E, mu, Is, Js, g, dg, frames)
    sim = KirchhoffRodSimulation(seg_lengths);

    Ixx = reshape(Is(1,1,:),[],1);
    Ixy = reshape(Is(1,2,:),[],1);
    Iyy = reshape(Is(2,2,:),[],1);
    J = reshape(Js,[],1);
    sim.setStiffness(E, mu, Ixx,Ixy,Iyy,J);

    sim.setBoundaryConditions(g(:,1),dg(:,1),frames(:,1,1),g(:,end),dg(:,end),frames(:,1,end));
    sim.setInitialGuessFromVertexFrames(frames);
end
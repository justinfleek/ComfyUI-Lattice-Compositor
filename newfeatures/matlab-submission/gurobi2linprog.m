% Wrapper function that feeds the input data for the gurobi LP solver to
% the Matlab LP solver, and returns the output in the way that gurobi
% would.
function sln = gurobi2linprog(model, params)
    Aineq = [model.A(model.sense == '<', :); -model.A(model.sense == '>', :)];
    bineq = [model.rhs(model.sense == '<', :); -model.rhs(model.sense == '>', :)];
    Aeq = model.A(model.sense == '=', :);
    beq = model.rhs(model.sense == '=', :);
    f = model.obj;
    lb = zeros(length(f), 1);
    if isfield(model, 'lb')
        lb = model.lb;
    end
    ub = inf(length(f), 1);
    if isfield(model, 'ub')
        ub = model.ub;
    end
    displ = 'final';
    if isfield(params, 'OutputFlag')
        if params.OutputFlag == 0
            displ = 'off';
        end
    end
    options = optimoptions('linprog','Display',displ);
    [x,fval,exitflag] = linprog(f,Aineq,bineq,Aeq,beq,lb,ub,options);

    if exitflag == 1
        status = 'OPTIMAL';
    elseif exitflag == -3
        status = 'UNBOUNDED';
    elseif exitflag == -5
        status = 'INFEASIBLE';
    else
        status = 'NON_OPTIMAL';
    end

    sln = struct('x',x,'objval',fval,'status',status);
end
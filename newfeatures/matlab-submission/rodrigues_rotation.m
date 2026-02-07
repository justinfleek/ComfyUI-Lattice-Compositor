function R = rodrigues_rotation(axis,angle)
    K = cross_product_matrix(axis);
    R = eye(3)+sin(angle)*K+(1-cos(angle))*K*K;
end
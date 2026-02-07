% State structur for Kirchhoff Rod simulation

classdef KirchhoffRodState < matlab.mixin.Copyable
    properties
        tangents
        normals
    end
    
    methods
        function obj = KirchhoffRodState(tangents, normals)
            obj.tangents = tangents;
            obj.normals = normals;
        end
        
        function binormals = computeBinormals(obj)
            binormals = cross(obj.tangents, obj.normals, 1);
        end
    end
end
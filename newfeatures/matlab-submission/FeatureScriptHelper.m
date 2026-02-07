classdef FeatureScriptHelper < handle
    methods(Static)
        function export(output_path, features)
            if ~iscell(features)
                features = {features};
            end
            header_file = fopen('fs-templates/header_fs_template.txt');
            header = fscanf(header_file,'%c');
            fclose(header_file);
            
            output_file = fopen(output_path,'w');
            fprintf(output_file, '%s', header);
            for i=1:length(features)
                fprintf(output_file, '%s', features{i});
            end
            fclose(output_file);
        end
    end
end
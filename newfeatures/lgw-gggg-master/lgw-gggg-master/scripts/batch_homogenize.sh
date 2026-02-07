#!/bin/bash

filename=$1
parentdir="$(dirname ${filename})"
#"../scenes/spheres/spheres_press_shear_ortho.yaml"
iterations=16

for i in $(seq 1 ${iterations}); do
    outfilename="${2}_${i}.log" #"../homogenized_results/spheres/ortho_shear_vel_f00_${i}.log"
	infilename="${parentdir}/temp_fixed.yaml"
	tr "\n" "@" < ${filename}\
		| sed "s/\bseed: [0-9]*\b/seed: $RANDOM/1"\
		| sed "s/\bseed: [0-9]*\b/seed: $RANDOM/2"\
		| tr "@" "\n" \
		> ${infilename}
	echo "Starting homogenization experiment ${i}"
	../build/Release/bin/CLIHomogenization ${infilename} > ${outfilename}
done

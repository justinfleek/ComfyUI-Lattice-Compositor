#!/bin/bash

filename="../scenes/spheres/spheres_press.yaml"
outfilename="../homogenized_results/spheres/spheres_press.log"
minsize=5
maxsize=20

echo "Size search log" > ${outfilename}
for i in $(seq ${minsize} ${maxsize}); do
	infilename="../scenes/spheres/temp_fixed.yaml"
	tr "\n" "@" < ${filename}\
		| sed "s/\bedge_size: [0-9]*\b/edge_size: ${i}/1"\
		| sed "s/\bseed: [0-9]*\b/seed: $RANDOM/1"\
		| sed "s/\bseed: [0-9]*\b/seed: $RANDOM/2"\
		| tr "@" "\n" \
		> ${infilename}
	echo "Starting homogenization experiment ${i}"
	echo "Size: ${i} x ${i} x ${i}" >> ${outfilename}
	../build/Release/bin/CLIHomogenization ${infilename} >> ${outfilename}
done

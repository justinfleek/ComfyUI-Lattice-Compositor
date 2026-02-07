# Degenerate cases 

This directory includes cases of objects and meshes that are designed to exhibit degenerancies in the algorithm.
While some of this setups might not be handled separately in the code, they most likely need more attention and
more clever design.


## Inlcuded files: 

* `triangle_yz_one_cell.obj`: one triangle parallel to the yz plane.  When using the grid size of 10, this triangle will cut through exactly through the middle of the cell. 

* `cube_12faces_diag.obj`: a coarse mesh of cube with YZ-faces consisting of 2 triangles joined by the diagonal edge. Useful to check the edge on edge labeling cases.

* `cube_12faces_horisontal.obj`: a coarse mesh of cube with YZ-faces consisting of 2 triangles joined by the horisontal edge. Same as `_diag` version but rotated 45 degrees in the YZ plane.
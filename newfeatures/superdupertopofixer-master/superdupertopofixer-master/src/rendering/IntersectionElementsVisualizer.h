#include "Visualizer.h"

class IntersectionElementsVisualizer : public Visualizer {
	friend ImGUIWindows;

 public:
	IntersectionElementsVisualizer() = default;
	~IntersectionElementsVisualizer() = default;

	// We have to initialize separately, because the visualizer is used in a static object.
	// TODO: refactor the visualization system to be able to use constructors directly.
	virtual void init(SDTopoFixer* topofixer, std::vector<Vec4d> colors) override;

	// Draws intersection elements based on the current state.
	virtual void display() override;

	// Switch to the next rendering state.
	// 0: draw nothing
	// 1: draw grid edge - mesh face intersections stored on grid.
	// 2: draw grid face - mesh edge intersections stored on grid.
	virtual void nextState() override;

	// Switch to the next rendering direction.
	// 0 - 2 correspond to grid orientation 0 - 2.
	// 3 enables all directions simultaneously.
	void nextDirection();

 private:
	void printDescription() const;

	void renderGridEdgeMeshFaceIntersections(unsigned int direction);
	void renderGridFaceMeshEdgeIntersections(unsigned int direction);

	// Parameters to track current draw state.
	int current_state_;
	int current_direction_;
	const unsigned int kMaxStates = 3;
	// 3 orientations + 1 for all directions together.
	const unsigned int kMaxDirections = 4;

	SDTopoFixer* topofixer_;

	Vec4d intersection_point_color_;
	Vec4d edge_color_;
	Vec4d inner_mesh_edge_color_;
	Vec4d outer_mesh_edge_color_;

	// Intersection elements per orientation.
	std::vector<std::vector<GridEdgeMeshFaceIntersection>> grid_edge_mesh_face_inters_;
	std::vector<std::vector<GridFaceMeshEdgeIntersection>> grid_face_mesh_edge_inters_;
};

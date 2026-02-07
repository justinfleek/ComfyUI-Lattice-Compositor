#include "LinearMesh3DView.h"

namespace sdtf::viewer::logic {
;

LinearMesh3DView::LinearMesh3DView(const Mesh3DInterface* mesh) : mesh_(mesh) { buildLinearView(); }

void LinearMesh3DView::buildLinearView() {
	buildLinearElementView(&v_, &v_map_, mesh_->ListVertices());
	buildLinearElementView(&t_, &t_map_, mesh_->ListTriangles());
	buildLinearElementView(&h_, &h_map_, mesh_->ListHalfCorners());

	v_hc_.resize(numVertices());
	for (int hci=0;hci<numHalfCorners();hci++)
	{
		auto hc = halfCorner(hci);
		v_hc_[vertexIndex(halfCorner(hci)->getVertex())] = hc;
	}
}
}  // namespace sdtf::viewer::logic
#pragma once

#include <Eigen/Core>
#include <Eigen/Dense>
#include <cmath>

namespace sdtf::viewer::geom {
;

template <typename T>
struct Mesh {
	Eigen::Matrix<T, 3, -1> vertices = Eigen::Matrix<T, 3, -1>(3, 0);
	Eigen::Matrix<unsigned int, 3, -1> triangles = Eigen::Matrix<unsigned int, 3, -1>(3, 0);
	Eigen::Matrix<unsigned int, 2, -1> edges = Eigen::Matrix<unsigned int, 2, -1>(2, 0);
	Eigen::Matrix<T, 3, -1> normals = Eigen::Matrix<T, 3, -1>(3, 0);
};

// Returns a matrix in SO(3) whose third column equals z.
template <typename T>
static Eigen::Matrix<T, 3, 3> buildBasis(const Eigen::Vector<T, 3>& z) {
	unsigned int i = (std::abs(z[0]) < std::abs(z[1])) ? 0 : 1;
	Eigen::Vector<T, 3> x = Eigen::Vector<T, 3>::Zero();
	x[i] = 1;
	Eigen::Vector<T, 3> y = z.cross(x).normalized();
	x = y.cross(z);
	Eigen::Matrix<T, 3, 3> ret;
	ret.col(0) = x;
	ret.col(1) = y;
	ret.col(2) = z;
	return ret;
}

// Provides static methods to generate common 3D primitives, such as cubes, cylinders, and cones.
// The data is returned as by filling in the Mesh<T> datastructure above. Methods ending in
// "Indexed" will return a vertex list that can be indexed by triangles or edges. Methods not ending
// in "Indexed" will return vertex lists in which three consecutive vertices will constitute a
// triangle.

template <typename T>
class MeshPrimitives {
 public:
	static Mesh<T> getUnitCubeIndexed(bool verts = false, bool triangles = false,
	                                  bool edges = false) {
		Mesh<T> ret;
		if (verts) {
			getCubeVerticesIndexed(&ret.vertices);
		}
		if (triangles) {
			getCubeTrianglesIndexed(&ret.triangles);
		}
		if (edges) {
			getCubeEdgesIndexed(&ret.edges);
		}
		return ret;
	}

	static Mesh<T> getCubeIndexed(const Eigen::Vector<T, 3>& p0, const Eigen::Vector<T, 3>& p1,
	                              bool verts = false, bool triangles = false, bool edges = false) {
		Mesh<T> ret;
		if (verts) {
			getCubeVerticesIndexed(&ret.vertices, p0, p1);
		}
		if (triangles) {
			getCubeTrianglesIndexed(&ret.triangles);
		}
		if (edges) {
			getCubeEdgesIndexed(&ret.edges);
		}
		return ret;
	}

	static Mesh<T> getUnitCubeTriangles(bool verts = false, bool normals = false) {
		Mesh<T> ret;
		if (verts) {
			getCubeTriangleVertices(&ret.vertices);
		}
		if (normals) {
			getCubeTriangleNormals(&ret.normals);
		}
		return ret;
	}

	static Mesh<T> getCubeTriangles(const Eigen::Vector<T, 3>& p0, const Eigen::Vector<T, 3>& p1,
	                                bool verts = false, bool normals = false) {
		Mesh<T> ret;
		if (verts) {
			getCubeTriangleVertices(&ret.vertices, p0, p1);
		}
		if (normals) {
			getCubeTriangleNormals(&ret.normals);
		}
		return ret;
	}

	static Mesh<T> getUnitCylinderIndexed(unsigned int num_segments, bool cap, bool verts = false,
	                                      bool triangles = false, bool normals = false) {
		Mesh<T> ret;
		if (verts) {
			getCylinderVerticesIndexed(&ret.vertices, Eigen::Vector<T, 3>::Zero(),
			                           Eigen::Vector<T, 3>(0, 0, 1), 1, num_segments, cap);
		}
		if (triangles) {
			getCylinderTrianglesIndexed(&ret.triangles, num_segments, cap);
		}
		if (normals) {
			getCylinderNormalsIndexed(&ret.normals, Eigen::Vector<T, 3>::Zero(),
			                          Eigen::Vector<T, 3>(0, 0, 1), num_segments, cap);
		}
		return ret;
	}

	static Mesh<T> getCylinderIndexed(const Eigen::Vector<T, 3>& p0, const Eigen::Vector<T, 3>& p1,
	                                  T radius, unsigned int num_segments, bool cap,
	                                  bool verts = false, bool triangles = false,
	                                  bool normals = false) {
		Mesh<T> ret;
		if (verts) {
			getCylinderVerticesIndexed(&ret.vertices, p0, p1, radius, num_segments, cap);
		}
		if (triangles) {
			getCylinderTrianglesIndexed(&ret.triangles, num_segments, cap);
		}
		if (normals) {
			getCylinderNormalsIndexed(&ret.normals, p0, p1, num_segments, cap);
		}
		return ret;
	}

	static Mesh<T> getConeIndexed(const Eigen::Vector<T, 3>& p0, const Eigen::Vector<T, 3>& p1,
	                              T radius, unsigned int num_segments, bool verts = false,
	                              bool triangles = false, bool normals = false) {
		Mesh<T> ret;
		if (verts) {
			getConeVerticesIndexed(&ret.vertices, p0, p1, radius, num_segments);
		}
		if (triangles) {
			getConeTrianglesIndexed(&ret.triangles, num_segments);
		}
		if (normals) {
			getConeNormalsIndexed(&ret.normals, p0, p1, radius, num_segments);
		}
		return ret;
	}

 private:
	static void getCubeVerticesIndexed(
	    Eigen::Matrix<T, 3, -1>* data, const Eigen::Vector<T, 3>& p0 = Eigen::Vector<T, 3>::Zero(),
	    const Eigen::Vector<T, 3>& p1 = Eigen::Vector<T, 3>::Constant(1)) {
		data->resize(3, 8);
		data->col(0) << p0;
		data->col(1) << p1(0), p0(1), p0(2);
		data->col(2) << p1(0), p1(1), p0(2);
		data->col(3) << p0(0), p1(1), p0(2);
		data->col(4) << p0(0), p0(1), p1(2);
		data->col(5) << p1(0), p0(1), p1(2);
		data->col(6) << p1;
		data->col(7) << p0(0), p1(1), p1(2);
	}

	static void getCubeEdgesIndexed(Eigen::Matrix<unsigned int, 2, -1>* data) {
		data->resize(2, 12);
		data->col(0) << 0, 1;
		data->col(1) << 1, 2;
		data->col(2) << 2, 3;
		data->col(3) << 3, 0;
		data->col(4) << 4, 5;
		data->col(5) << 5, 6;
		data->col(6) << 6, 7;
		data->col(7) << 7, 4;
		data->col(8) << 0, 4;
		data->col(9) << 1, 5;
		data->col(10) << 2, 6;
		data->col(11) << 3, 7;
	}

	static void getCubeTrianglesIndexed(Eigen::Matrix<unsigned int, 3, -1>* data) {
		data->resize(3, 12);
		data->col(0) << 0, 2, 1;
		data->col(1) << 0, 3, 2;
		data->col(2) << 4, 5, 6;
		data->col(3) << 4, 6, 7;
		data->col(4) << 0, 1, 5;
		data->col(5) << 0, 5, 4;
		data->col(6) << 1, 2, 6;
		data->col(7) << 1, 6, 5;
		data->col(8) << 2, 3, 7;
		data->col(9) << 2, 7, 6;
		data->col(10) << 3, 0, 4;
		data->col(11) << 3, 4, 7;
	}

	static void getCubeTriangleVertices(
	    Eigen::Matrix<T, 3, -1>* data, const Eigen::Vector<T, 3>& p0 = Eigen::Vector<T, 3>::Zero(),
	    const Eigen::Vector<T, 3>& p1 = Eigen::Vector<T, 3>::Constant(1)) {
		data->resize(3, 36);

		Eigen::Matrix<T, 3, -1> v;
		Eigen::Matrix<unsigned, 3, -1> e;
		getCubeVerticesIndexed(&v, p0, p1);
		getCubeTrianglesIndexed(&e);
		for (int i = 0; i < 36; i++)
			data->col(i) = v.col(*(e.data() + i));
	}

	static void getCubeTriangleNormals(Eigen::Matrix<T, 3, -1>* data) {
		Eigen::Matrix<T, 3, 6> n = Eigen::Matrix<T, 3, 6>::Zero();
		n(2, 0) = -1;
		n(2, 1) = 1;
		n(1, 2) = -1;
		n(0, 3) = 1;
		n(1, 4) = 1;
		n(0, 5) = -1;

		data->resize(3, 36);
		for (int i = 0; i < 36; i++)
			data->col(i) = n.col(i / 6);
	}

	static void getCylinderVerticesIndexed(
	    Eigen::Matrix<T, 3, -1>* data, const Eigen::Vector<T, 3>& p0 = Eigen::Vector<T, 3>::Zero(),
	    const Eigen::Vector<T, 3>& p1 = Eigen::Vector<T, 3>(0., 0., 1.), T radius = 1.0,
	    unsigned int num_segments = 36, bool cap = true) {
		Eigen::Vector<T, 3> z = (p1 - p0).normalized();
		auto basis = buildBasis(z);
		Eigen::Array<T, 1, -1> angles = Eigen::Array<T, 1, -1>::LinSpaced(
		    num_segments, 0, 2 * PI_CONSTANT * static_cast<T>(num_segments - 1) / num_segments);
		Eigen::Matrix<T, 2, -1> pos_loc(2, num_segments);
		pos_loc << angles.cos(), angles.sin();
		pos_loc *= radius;

		Eigen::Matrix<T, 3, -1> v0 = basis.template block<3, 2>(0, 0) * pos_loc;
		Eigen::Matrix<T, 3, -1> v1 = v0;
		v0.colwise() += p0;
		v1.colwise() += p1;

		if (cap) {
			data->resize(3, num_segments * 4 + 2);
			*data << v0, v1, p0, v0, p1, v1;
		} else {
			data->resize(3, num_segments * 2);
			*data << v0, v1;
		}
	}

	static void getCylinderTrianglesIndexed(Eigen::Matrix<unsigned int, 3, -1>* data,
	                                        unsigned int num_segments = 36, bool cap = true) {
		Eigen::Matrix<unsigned int, 3, -1> f_barrel(3, 2 * num_segments);
		for (unsigned int i = 0; i < num_segments; i++) {
			unsigned int j = i + num_segments;
			unsigned int ip = (i + 1) % num_segments;
			unsigned int jp = ip + num_segments;
			f_barrel.col(2 * i) << i, jp, j;
			f_barrel.col(2 * i + 1) << jp, i, ip;
		}
		if (cap) {
			Eigen::Matrix<unsigned int, 3, -1> f0(3, num_segments);
			Eigen::Matrix<unsigned int, 3, -1> f1(3, num_segments);
			unsigned int pi0 = 2 * num_segments;
			unsigned int pi = pi0 + 1;
			unsigned int pj0 = 3 * num_segments + 1;
			unsigned int pj = pj0 + 1;
			for (unsigned int i = 0; i < num_segments - 1; i++) {
				f0.col(i) << pi0, pi + 1, pi;
				f1.col(i) << pj0, pj, pj + 1;
				pi++;
				pj++;
			}
			f0.template rightCols<1>() << pi0, pi0 + 1, pi0 + num_segments;
			f1.template rightCols<1>() << pj0, pj0 + num_segments, pj0 + 1;

			data->resize(3, 4 * num_segments);
			*data << f_barrel, f0, f1;
		} else {
			*data = f_barrel;
		}
	}

	static void getCylinderNormalsIndexed(Eigen::Matrix<T, 3, -1>* data,
	                                      const Eigen::Vector<T, 3>& p0 = Eigen::Vector<T, 3>::Zero(),
	                                      const Eigen::Vector<T, 3>& p1 = Eigen::Vector<T, 3>(0., 0.,
	                                                                                          1.),
	                                      unsigned int num_segments = 36, bool cap = true) {
		Eigen::Vector<T, 3> z = (p1 - p0).normalized();
		auto basis = buildBasis(z);
		Eigen::Array<T, 1, -1> angles = Eigen::Array<T, 1, -1>::LinSpaced(
		    num_segments, 0, 2 * PI_CONSTANT * static_cast<T>(num_segments - 1) / num_segments);
		Eigen::Matrix<T, 2, -1> n_loc(2, num_segments);
		n_loc << angles.cos(), angles.sin();
		Eigen::Matrix<T, 3, -1> n = basis.template block<3, 2>(0, 0) * n_loc;

		if (cap) {
			data->resize(3, num_segments * 4 + 2);
			data->block(0, 0, 3, 2 * num_segments) << n, n;
			data->block(0, 2 * num_segments, 3, num_segments + 1).colwise() = -z;
			data->block(0, 3 * num_segments + 1, 3, num_segments + 1).colwise() = z;
		} else {
			data->resize(3, 2 * num_segments);
			*data << n, n;
		}
	}

	static void getConeVerticesIndexed(Eigen::Matrix<T, 3, -1>* data,
	                                   const Eigen::Vector<T, 3>& p0 = Eigen::Vector<T, 3>::Zero(),
	                                   const Eigen::Vector<T, 3>& p1 = Eigen::Vector<T, 3>(0., 0.,
	                                                                                       1.),
	                                   T radius = 1.0, unsigned int num_segments = 36) {
		Eigen::Vector<T, 3> z = (p1 - p0).normalized();
		auto basis = buildBasis(z);
		Eigen::Array<T, 1, -1> angles = Eigen::Array<T, 1, -1>::LinSpaced(
		    num_segments, 0, 2 * PI_CONSTANT * static_cast<T>(num_segments - 1) / num_segments);
		Eigen::Matrix<T, 2, -1> pos_loc(2, num_segments);
		pos_loc << angles.cos(), angles.sin();
		pos_loc *= radius;

		Eigen::Matrix<T, 3, -1> v0 = basis.template block<3, 2>(0, 0) * pos_loc;
		v0.colwise() += p0;

		data->resize(3, 2 * num_segments + 2);
		*data << p1, v0, p0, v0;
	}

	static void getConeTrianglesIndexed(Eigen::Matrix<unsigned int, 3, -1>* data,
	                                    unsigned int num_segments = 36) {
		data->resize(3, 2 * num_segments);
		Eigen::Matrix<unsigned int, 3, -1> f0(3, num_segments);
		Eigen::Matrix<unsigned int, 3, -1> f1(3, num_segments);
		unsigned int pi0 = 0;
		unsigned int pi = pi0 + 1;
		unsigned int pj0 = num_segments + 1;
		unsigned int pj = pj0 + 1;
		for (unsigned int i = 0; i < num_segments - 1; i++) {
			f0.col(i) << pi0, pi, pi + 1;
			f1.col(i) << pj0, pj + 1, pj;
			pi++;
			pj++;
		}
		f0.template rightCols<1>() << pi0, pi0 + num_segments, pi0 + 1;
		f1.template rightCols<1>() << pj0, pj0 + 1, pj0 + num_segments;
		*data << f0, f1;
	}

	static void getConeNormalsIndexed(Eigen::Matrix<T, 3, -1>* data,
	                                  const Eigen::Vector<T, 3>& p0 = Eigen::Vector<T, 3>::Zero(),
	                                  const Eigen::Vector<T, 3>& p1 = Eigen::Vector<T, 3>(0., 0., 1.),
	                                  T radius = 1.0, unsigned int num_segments = 36) {
		data->resize(3, 2 * num_segments + 2);
		Eigen::Vector<T, 3> to = p1 - p0;
		T h = to.norm();
		Eigen::Vector<T, 3> z = to / h;
		T s = sqrt(h * h + radius * radius);

		auto basis = buildBasis(z);
		Eigen::Array<T, 1, -1> angles = Eigen::Array<T, 1, -1>::LinSpaced(
		    num_segments, 0, 2 * PI_CONSTANT * static_cast<T>(num_segments - 1) / num_segments);
		Eigen::Matrix<T, 2, -1> pos_loc(2, num_segments);
		pos_loc << angles.cos(), angles.sin();
		Eigen::Matrix<T, 3, -1> n_loc(3, num_segments);
		n_loc.template topRows<2>() = pos_loc * (h / s);
		n_loc.row(2).fill(radius / s);

		data->col(0) << 0., 0., 1.e-10f;
		data->block(0, 1, 3, num_segments) = basis * n_loc;
		data->block(0, num_segments + 1, 3, num_segments + 1).colwise() = -basis.col(2);
	}

	inline static const T PI_CONSTANT = 3.141592653589793238463;
};

}  // namespace sdtf::viewer::geom
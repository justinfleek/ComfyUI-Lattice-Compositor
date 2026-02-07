/* GridLattice.h
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, Malina Strugaru 2022
 *
 * This header defines the grid lattice class: a data structure used to sparsely store values on the
 * grid, by mapping grid rays to vectors of values. This can be thought as a projection of values
 * stored on the grid onto a 2D point set along a fixed direction, where each point corresponds to a
 * separate ray, with its separate storage bucket. No memory is allocated for rays with no values
 * stored on them. Rays are considered to point in the increasing direction along one of the
 * cartesian axes (x, y, or z), determined by the orientation parameter. A value on the grid is
 * specified by three coordinates: two that specify a grid ray, and one that specifies the position
 * on the ray. Values on each grid ray can be sorted by their ray coordinates, and subsequently
 * traversed along the direction determined by orientation. Values as well as coordinates are
 * templated.
 */

#pragma once

//------------------------------------------------------------
// includes
//------------------------------------------------------------
#include <functional>
#include <unordered_map>

#include "../../abseil-cpp/absl/container/flat_hash_map.h"
#include "../utilities/vec.h"

//------------------------------------------------------------
// classes
//------------------------------------------------------------

// `T` is a value stored on the grid (eg. an intersection), `Coord` is a coordinate that is used to
// specify both a grid ray (using two `Coord` values), and a position on the ray (using one `Coord`
// value). Three `Coord` values can therefore specify any position on the grid. Consequently,
// `Coord` should be a stand-in for a numerical value (i.e. double, int,...).
template <typename T, typename Coord>
class GridLattice {
 private:
	// -------------------- struct
	// An element `T` that is stored on the grid, together with its ray coordinate `Coord`.
	typedef struct Value_ {
		T element;
		Coord coord_on_ray;
	} Value_;

	// -------------------- typedef
	// A container holding all rays for a specific direction, it maps 2 coordinates that define the
	// ray (i.e. the two coordinates that are constant for a ray) to a vector of values saved on that
	// ray.
	typedef absl::flat_hash_map<std::pair<Coord, Coord>, std::vector<Value_>> Container;

 public:
	// -------------------- constructors
	// Default constructor.
	GridLattice() = default;

	// Additional constructor, constructs a lattice from the input data. Namely, it takes a vector of
	// values of type `T`, an `orientation` that specifies ray direction on the grid, and a function
	// pointer `coord_extractor` that assigns to a type `T` value three coordinates of type `Coord`.
	// Each element in `elements` is matched to its coordinates via `coord_extractor`. Two of these
	// coordinates are then used to assign elements into rays along the given grid `orientation` (each
	// ray is uniquely defined by two coorinates that remain constant along itself). The remaining
	// coordinate is used to sort elements along each ray in increasing order, determined by
	// `orientation`.
	GridLattice(const std::vector<T>& elements, const long long orientation,
	            std::function<Vec<3U, Coord>(const T&)> coord_extractor);
	// Default destructor.
	~GridLattice() = default;

	// -------------------- typedefs
	// typedefs to simplify `Container` interface, specifically iterating over lattice rays.
	typedef Value_ Point;
	typedef typename Container::iterator iterator;
	typedef typename Container::const_iterator const_iterator;

	// -------------------- functions
	// Returns a lattice iterator/const iterator pointing to the ray determined by the coordinates on
	// the input `element` (does not check if the element is actually saved in the lattice), or by the
	// input pair of `ray_coords`. Returns `lattice_.end()` when there is no data stored on the ray
	// with the these coordinates, or when the coordinates are out of bounds.
	iterator find_ray(const T& element);
	const_iterator find_ray(const T& element) const;
	iterator find_ray(const std::pair<Coord, Coord>& ray_coords) { return lattice_.find(ray_coords); }
	const_iterator find_ray(const std::pair<Coord, Coord>& ray_coords) const {
		return lattice_.find(ray_coords);
	}

	// Return `lattice_` begin and end pointers, which allows iterating over a GridLattice object as
	// iterating over `Container`, i.e. over the map of grid rays.
	iterator begin() { return lattice_.begin(); }
	const_iterator begin() const { return lattice_.begin(); }
	iterator end() { return lattice_.end(); }
	const_iterator end() const { return lattice_.end(); }

	// Returns number of rays in the lattice.
	int size() const { return lattice_.size(); }

	// Returns a unit vector of `Coord` values corresponding to `orientation_` of rays in the lattice,
	// i.e. unit vector in the increasing direction along lattice rays (one of
	// (1,0,0),(0,1,0),(0,0,1)).
	Vec<3U, Coord> get_ray_direction() const;

	int get_orientation() const { return orientation_; }

 private:
	// -------------------- functions
	// Reshuffles input coordinates in such a way that on output, first two coordinates are constant
	// along `orientation_` and the last coordinate is variable.
	void reorient_coords(Vec<3U, Coord>& coords) const;

	// -------------------- data mambers
	// Determines one of the 3 permissible grid orientations for the grid lattice:
	// -0: rays taken along increasing x-coordinate, fixed coordinates are (y,z)
	// -1: rays taken along increasing y-coordinate, fixed coordinates are (z,x)
	// -2: rays taken along increasing z-coordinate, fixed coordinates are (x,y)
	long long orientation_;
	// Map that assignes to 2 coordinates (which define a ray) a vector of values saved on that ray.
	Container lattice_;
	// Fuction that to a value of type `T` assigns its grid coordinates.
	std::function<Vec<3U, Coord>(const T&)> coord_extractor_;
};

// A constructor that constructs a GridLattice from the input data, and sorts the values on all grid
// rays by their ray coordinates.
template <typename T, typename Coord>
GridLattice<T, Coord>::GridLattice(const std::vector<T>& elements, const long long orientation,
                                   std::function<Vec<3U, Coord>(const T&)> coord_extractor)
    : orientation_(orientation), coord_extractor_(std::move(coord_extractor)) {
	// sort elements into rays
	for (const auto& element : elements) {
		Vec<3U, Coord> coords = coord_extractor_(element);
		reorient_coords(coords);
		// add into `lattice_` at a ray defined by (coords[0],coords[1]) a `Value_` consisting of
		// {element,coords[2]}
		lattice_[std::pair<Coord, Coord>(coords[0], coords[1])].push_back(Value_{element, coords[2]});
	}

	// Sort elements within each ray.
	auto sort_cmp = [orientation](const Value_& first, const Value_& second) {
		return first.coord_on_ray < second.coord_on_ray;
	};
	for (auto& vals : lattice_) {
		std::sort(vals.second.begin(), vals.second.end(), sort_cmp);
	}
}

// Reshuffles input coordinates so that on output, first two coordinates are constant along
// `orientation_` and the last coordinate is variable.
template <typename T, typename Coord>
void GridLattice<T, Coord>::reorient_coords(Vec<3U, Coord>& coords) const {
	double tmp;
	for (int i = 0; i < 2 - orientation_; ++i) {
		tmp = coords[2];
		coords[2] = coords[1];
		coords[1] = coords[0];
		coords[0] = tmp;
	}
}

// Returns a lattice iterator pointing to the ray given by `orientation_` and `element` coordinates.
template <typename T, typename Coord>
typename GridLattice<T, Coord>::iterator GridLattice<T, Coord>::find_ray(const T& element) {
	Vec<3U, Coord> coords = coord_extractor_(element);
	reorient_coords(coords);
	return lattice_.find({coords[0], coords[1]});
}

// Returns a lattice const iterator pointing to the ray given by `orientation_` and `element`
// coordinates.
template <typename T, typename Coord>
typename GridLattice<T, Coord>::const_iterator GridLattice<T, Coord>::find_ray(
    const T& element) const {
	Vec<3U, Coord> coords = coord_extractor_(element);
	reorient_coords(coords);
	return lattice_.find({coords[0], coords[1]});
}

// Returns a unit vector corresponding to `orientation_` of rays in the lattice, i.e. unit vector in
// the increasing direction along lattice rays.
template <typename T, typename Coord>
Vec<3U, Coord> GridLattice<T, Coord>::get_ray_direction() const {
	Vec<3U, Coord> direction(0.0);
	direction[orientation_] = static_cast<Coord>(1.0);
	return direction;
}
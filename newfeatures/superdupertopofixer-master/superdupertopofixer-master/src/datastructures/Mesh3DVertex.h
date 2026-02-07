/* Mesh3DVertex.h
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, Malina Strugaru, 2021
 *
 * This is the header for the mesh vertex class and the vertex properties struct.
 */

#pragma once

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include <iostream>
#include <memory>
#include <fstream>

#include "VertexProperties.h"
#include "../utilities/vec.h"

//------------------------------------------------------------
// declarations
//------------------------------------------------------------

class Mesh3DHalfCorner;

//------------------------------------------------------------
// classes
//------------------------------------------------------------

// this class represents a mesh vertex
class Mesh3DVertex {
 public:
	Mesh3DVertex() = default;
	~Mesh3DVertex() = default;

	// set and get functions
	void setCoords(Vec3d coords) { xyz = coords; };
	void setXCoord(double new_coord) { xyz[0] = new_coord; }
	void setYCoord(double new_coord) { xyz[1] = new_coord; }
	void setZCoord(double new_coord) { xyz[2] = new_coord; }
	Vec3d getCoords() const { return xyz; };
	double getCoord(int index) { return xyz[index]; }
	double getXCoord() { return xyz[0]; }
	double getYCoord() { return xyz[1]; }
	double getZCoord() { return xyz[2]; }

	// functions related to vertex properties
	// Note that some functions in the struct VertexProperties are duplicated here.
	// This is because the function getProperties() returns a copy of the struct as
	// structs are treated like primitives.
	// For instance, in order to modify the velocity of a mesh vertex one should call
	// setVelocity() here, and not getProperties().setVelocity().
	Vec3d getVelocity() { return properties.getVelocity(); }
	double getVelocityComponent(int index) { return getVelocity()[index]; }
	void setVelocity(Vec3d vel) { properties.setVelocity(vel); };
	double getThickness() { return properties.getThickness(); }
	void setThickness(double th_v) { properties.setThickness(th_v); }
	const VertexProperties& getProperties() const { return properties; }
	VertexProperties& getProperties() { return properties; }
	void setProperties(VertexProperties vert_props) { properties = vert_props; }
	void setPropertiesToZero() { properties.setZero(); }
	void addProperties(const VertexProperties& other) { properties.iadd(other); }
	void addProperties(const VertexProperties& other, double scale) { properties.iadd(other, scale); }
	void divProperties(double scale) { properties.idiv(scale); }

 private:
	bool exact;
	Vec3d xyz;  // position of vertex
	VertexProperties properties;  // struct including velocity, thickness, uthickness, and flow
};

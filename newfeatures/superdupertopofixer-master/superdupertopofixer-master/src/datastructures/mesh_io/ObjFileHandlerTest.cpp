#include <filesystem>
#include <sstream>
#define DOCTEST_CONFIG_IMPLEMENT_WITH_MAIN

#include "../../schemes/TopoFixerSettings.h"
#include "../../utilities/doctest/doctest.h"
#include "../Mesh3DCornerTable.h"
#include "ObjFileHandler.h"

TEST_CASE("obj reading and writing works on a small mesh") {
	// Construct a tetrahedron.
	TopoFixerSettings settings;
	Mesh3DCornerTable corner_table(settings);

	Mesh3DVertex* v1 = corner_table.makeNewVertex();
	Mesh3DVertex* v2 = corner_table.makeNewVertex();
	Mesh3DVertex* v3 = corner_table.makeNewVertex();
	Mesh3DVertex* v4 = corner_table.makeNewVertex();

	std::vector<Vec3d> coords = {{1.0, 0.0, 0.0}, {0.0, 1.0, 0.0}, {0.0, 0.0, 1.0}, {1.0, 1.0, 1.0}};

	v1->setCoords(coords[0]);
	v2->setCoords(coords[1]);
	v3->setCoords(coords[2]);
	v4->setCoords(coords[3]);

	corner_table.makeNewTriangle(v1, v2, v3, {0, 1});
	corner_table.makeNewTriangle(v2, v4, v3, {0, 1});
	corner_table.makeNewTriangle(v4, v1, v3, {0, 1});
	corner_table.makeNewTriangle(v2, v1, v4, {0, 1});

	REQUIRE_EQ(corner_table.getNumberVerts(), 4);
	REQUIRE_EQ(corner_table.getNumberTris(), 4);

	SUBCASE("Round trip produces the same mesh.") {
		ObjFileHandler obj_handler;

		std::stringstream stream;

		auto [status, message] = obj_handler.writeToStream(&corner_table, stream);
		CHECK_EQ(status, 0);

		Mesh3DCornerTable new_mesh(settings);
		std::tuple(status, message) = obj_handler.readFromStream(&new_mesh, stream);
		CHECK_EQ(status, 0);

		CHECK_EQ(new_mesh.getNumberVerts(), 4);
		CHECK_EQ(new_mesh.getNumberTris(), 4);

		std::vector<Vec3d> new_coords;
		for (Mesh3DVertex* v : new_mesh.ListVertices()) {
			auto it = std::find(coords.begin(), coords.end(), v->getCoords());
			CHECK_NE(it, coords.end());
		}
	}
}

TEST_CASE("Obj reader handles inputs") {
	std::stringstream obj_textured(R"(
v 1.0 0.0 0.0
v 0.0 1.0 0.0
v 0.0 0.0 1.0
v 1.0 1.0 1.0
f 1/1 2/2 3/3
f 2/2 4/4 3/3
f 4/4 1/1 3/3
f 2/2 1/1 3/3
m 0 1
m 0 1
m 0 1
m 0 1
    )");
	std::vector<Vec3d> coords = {{1.0, 0.0, 0.0}, {0.0, 1.0, 0.0}, {0.0, 0.0, 1.0}, {1.0, 1.0, 1.0}};

	TopoFixerSettings settings;
	Mesh3DCornerTable mesh(settings);
	ObjFileHandler obj_handler;
	obj_handler.readFromStream(&mesh, obj_textured);

	CHECK_EQ(mesh.getNumberVerts(), 4);
	CHECK_EQ(mesh.getNumberTris(), 4);

	std::vector<Vec3d> new_coords;
	for (Mesh3DVertex* v : mesh.ListVertices()) {
		auto it = std::find(coords.begin(), coords.end(), v->getCoords());
		CHECK_NE(it, coords.end());
	}
}

TEST_CASE("Obj reader handles adding vertices to an existing mesh") {
	std::stringstream obj_textured(R"(
v 1.0 0.0 0.0
v 0.0 1.0 0.0
v 0.0 0.0 1.0
v 1.0 1.0 1.0
f 1/1 2/2 3/3
f 2/2 4/4 3/3
f 4/4 1/1 3/3
f 2/2 1/1 3/3
m 0 1
m 0 1
m 0 1
m 0 1
    )");

	std::stringstream obj_textured2(R"(
v 2.0 0.0 0.0
v 0.0 2.0 0.0
v 0.0 0.0 2.0
v 2.0 2.0 2.0
f 1/1 2/2 3/3
f 2/2 4/4 3/3
f 4/4 1/1 3/3
f 2/2 1/1 3/3
m 0 1
m 0 1
m 0 1
m 0 1
    )");
	std::vector<Vec3d> coords = {{1.0, 0.0, 0.0}, {0.0, 1.0, 0.0}, {0.0, 0.0, 1.0}, {1.0, 1.0, 1.0},
	                             {2.0, 0.0, 0.0}, {0.0, 2.0, 0.0}, {0.0, 0.0, 2.0}, {2.0, 2.0, 2.0}};

	TopoFixerSettings settings;
	Mesh3DCornerTable mesh(settings);
	ObjFileHandler obj_handler;
	obj_handler.readFromStream(&mesh, obj_textured);
	obj_handler.readFromStream(&mesh, obj_textured2, true);

	CHECK_EQ(mesh.getNumberVerts(), 8);
	CHECK_EQ(mesh.getNumberTris(), 8);

	std::vector<Vec3d> new_coords;
	for (Mesh3DVertex* v : mesh.ListVertices()) {
		auto it = std::find(coords.begin(), coords.end(), v->getCoords());
		CHECK_NE(it, coords.end());
	}
}
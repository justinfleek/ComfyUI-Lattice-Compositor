#include "Utils.hpp"

#include <numeric>
#include <limits>
#include <algorithm>


using namespace Type;


NumT invBilerpApproxTest(const Vec3& pos,
                         const Vec3& pos00, const Vec3& pos10,
                         const Vec3& pos01, const Vec3& pos11,
                         const Vec2& uv00, const Vec2& uv10,
                         const Vec2& uv01, const Vec2& uv11,
                         const Vec3& normal00, const Vec3& normal10,
                         const Vec3& normal01, const Vec3& normal11,
                         bool &isInside, Vec2 &uv, Vec3& normal,
                         int configuration) {

#warning APPROX_INV_BILERP
    // Does not use real inv bilerp since quad might not be planar
    // https://stackoverflow.com/questions/808441/inverse-bilinear-interpolation
    // Instead approximates using triangles
    
    NumT dist = std::numeric_limits<NumT>::infinity();

    // Diagonal is 0/2
    std::array<Vec3i, 2> vIds;
    const std::array<Vec3, 4> poss    = {   pos00,    pos10,    pos11,    pos01};
    const std::array<Vec2, 4> uvs     = {    uv00,     uv10,     uv11,     uv01}; 
    const std::array<Vec3, 4> normals = {normal00, normal10, normal11, normal01}; 
    if (configuration == 0) {
        // Diagonal is 00/11
        vIds = { Vec3i(2, 0, 1), Vec3i(0, 2, 3) };
    } else {
        // Diagonal is 10/01
        vIds = { Vec3i(1, 3, 0), Vec3i(3, 1, 2) };
    }
    
    Vec3 barCoords[2];
    bool areInside[2];
    NumT dists[2];
    // Naive projection
    for (int i = 0; i < 2; ++i) {
        dists[i] = distancePointTriangle(pos,
                                         poss[vIds[i][0]],
                                         poss[vIds[i][1]],
                                         poss[vIds[i][2]],
                                         nullptr, &(barCoords[i]), &(areInside[i]));
        if ( (!areInside[i])
             && ((barCoords[i][0] <= 0) || (barCoords[i][1] <= 0))
             ) {
            // Out from the wrong side: discard
            isInside = false;
            uv =
                barCoords[i][0] * uvs[vIds[i][0]]
                + barCoords[i][1] * uvs[vIds[i][1]]
                + barCoords[i][2] * uvs[vIds[i][2]];
            return dists[i];
        }
    } // i

    isInside = (areInside[0] || areInside[1]);
    if (true || !isInside) {
        // Pseudo inverse ray-cast backup
        // Compute the smooth normal

        /*
        // OLD WAY - INTERPOLATING FROM TRIANGLES
        const Vec3 normalsLoc[2] =
            {
                Magnum::Math::cross(poss[vIds[0][1]] - poss[vIds[0][0]], 
                                    poss[vIds[0][2]] - poss[vIds[0][0]])//.normalized()
                ,
                Magnum::Math::cross(poss[vIds[1][1]] - poss[vIds[1][0]], 
                                    poss[vIds[1][2]] - poss[vIds[1][0]])//.normalized()
            };
        
        const Vec3 normalLoc =
            -(
                (1 - barCoords[1][2]) * normalsLoc[0]
                + (1 - barCoords[0][2]) * normalsLoc[1]
              ).normalized();
        /*/
        // NEW WAY - USING PROVIDED NORMALS
        const Vec3 normalsLoc[2] =
            {
                (barCoords[0][0] * normals[vIds[0][0]]
                 + barCoords[0][1] * normals[vIds[0][1]]
                 + barCoords[0][2] * normals[vIds[0][2]])
                .normalized()
                ,
                (barCoords[1][0] * normals[vIds[1][0]]
                 + barCoords[1][1] * normals[vIds[1][1]]
                 + barCoords[1][2] * normals[vIds[1][2]])
                .normalized()
            } ;
        const int idClosest =
            ( (isInside && areInside[0] && ((!areInside[1]) || (dists[0] < dists[1])))
              || (!isInside && (dists[0] < dists[1])) )?
            0 : 1;
        const Vec3 normalLoc =
            -normalsLoc[idClosest];
        /* */

        // Line triangle intersection
        for (int i = 0; i < 2; ++i) {
            areInside[i] = intersectionRayTriangle(pos, normalLoc,
                                                   poss[vIds[i][0]],
                                                   poss[vIds[i][1]],
                                                   poss[vIds[i][2]],
                                                   nullptr, &(barCoords[i]), &(dists[i]));
        } // i
    } //inverse ray cast
    
    // Return
    isInside = (areInside[0] || areInside[1]);
    const int idClosest =
        //*
        (areInside[0]
         && ( (!areInside[1]) || (dists[0] < dists[1]) )) ?
        /*/
        ( (isInside && areInside[0] && ((!areInside[1]) || (dists[0] < dists[1])))
          || (!isInside && (dists[0] < dists[1])) )?
          /* */
        0 : 1;
    if (true || isInside) {
        uv =
            barCoords[idClosest][0] * uvs[vIds[idClosest][0]]
            + barCoords[idClosest][1] * uvs[vIds[idClosest][1]]
            + barCoords[idClosest][2] * uvs[vIds[idClosest][2]];
        normal =
            (barCoords[idClosest][0] * normals[vIds[idClosest][0]]
            + barCoords[idClosest][1] * normals[vIds[idClosest][1]]
             + barCoords[idClosest][2] * normals[vIds[idClosest][2]]).normalized();
    }
    dist = dists[idClosest];
    
    return dist;
}


NumT invBilerpApprox(const Vec3& pos,
                     const Vec3& pos00, const Vec3& pos10,
                     const Vec3& pos01, const Vec3& pos11,
                     const Vec2& uv00, const Vec2& uv10,
                     const Vec2& uv01, const Vec2& uv11,
                     const Vec3& normal00, const Vec3& normal10,
                     const Vec3& normal01, const Vec3& normal11,
                     bool &isInside, Vec2 &uv, Vec3 &normal) {

    bool areInside[2];
    Vec2 uvs[2];
    Vec3 normals[2];
    NumT dists[2];
    
    dists[0] = invBilerpApproxTest(pos,
                                   pos00, pos10, pos01, pos11,
                                   uv00, uv10, uv01, uv11,
                                   normal00, normal10, normal01, normal11,
                                   areInside[0], uvs[0], normals[0], 0);
    dists[1] = invBilerpApproxTest(pos,
                                   pos00, pos10, pos01, pos11,
                                   uv00, uv10, uv01, uv11,
                                   normal00, normal10, normal01, normal11,
                                   areInside[1], uvs[1], normals[1], 1);
    isInside = areInside[0] || areInside[1];
    const int idClosest =
        (areInside[0]
         && ( (!areInside[1]) || (dists[0] < dists[1]) )) ?
        0 : 1;
    if (isInside) {
        if (areInside[0] && areInside[1]) {
            // Weight according to distance to respective diagonal
            const NumT k0 = (uvs[0]
                             - 0.5 * (uvs[0][0] + uvs[0][1])
                             * Vec2(1., 1.)).norm() + 0.00;
            const NumT k1 = (uvs[1] - Vec2(0., 1.)
                             - 0.5 * (uvs[0][0] - uvs[0][1] + 1)
                             * Vec2(1., -1.)).norm() + 0.00;
            uv = (k0 * uvs[0] + k1 * uvs[1]) / (k0 + k1);
            normal = ((k0 * normals[0] + k1 * normals[1])).normalized();
        } else {
            uv = uvs[idClosest];
            normal = normals[idClosest];
        }
    } else {
        uv = uvs[idClosest];
        normal = normals[idClosest];
    }
    return dists[idClosest];

}

NumT cross2d(const Vec2& a, const Vec2& b) {
    return a.x() * b.y() - a.y() * b.x();
}

// https://iquilezles.org/articles/ibilinear/
void invBilerp2D(const Vec2& pos,
                 const Vec2& pos00, const Vec2& pos10,
                 const Vec2& pos01, const Vec2& pos11,
                 bool& isInside, Vec2& bar) {

    isInside = true;

    const Vec2 e = pos10 - pos00;
    const Vec2 f = pos11 - pos00;
    const Vec2 g = pos00 - pos10 + pos01 - pos11;
    const Vec2 h = pos - pos00;
        
    const NumT k2 = cross2d(g, f);
    const NumT k1 = cross2d(e, f) + cross2d(h, g);
    const NumT k0 = cross2d(h, e);
    
    // if edges are parallel, this is a linear equation
    const NumT epsParallel = 1.e-3 *abs(k0); //* std::(pos11 - pos00).length();
    if (abs(k2) < epsParallel) {
        bar = Vec2( (h.x() * k1 + f.x() * k0)
                    /(e.x() * k1 - g.x() * k0),
                    -k0 / k1 );
    }
    // otherwise, it's a quadratic
    else {
        NumT w = k1 * k1 - 4.0 * k0 * k2;
        if (w < 0.0) {
            isInside = false;
            return;
        }
        w = sqrt(w);

        const NumT ik2 = 0.5 / k2;
        NumT v = (-k1 - w) * ik2;
        NumT u = (h.x() - f.x() * v) / (e.x() + g.x() * v);
        
        if (u<0.0 || u>1.0 || v<0.0 || v>1.0) {
            v = (-k1 + w) * ik2;
            u = (h.x() - f.x() * v) / (e.x() + g.x() * v);
        }
        bar = Vec2(u, v);
        if (u<0.0 || u>1.0 || v<0.0 || v>1.0) {
            isInside = false;
        }
    }
    
    
}

NumT areaPolygon(const VectorVec2& positions) {
    // Compute centroid
    Vec2 centroid;
    for (const Vec2& pos : positions) {
        centroid += pos;
    }
    centroid /= positions.size();
    // Compute angles wrt centroid to sort
    VectorNumT angles;
    for (const Vec2& pos : positions) {
        Vec2 orientation = pos - centroid;
        angles.push_back(atan2(orientation[1], orientation[0]));
    }
    // Sort
    VectorUi orderedPosIds(positions.size());
    std::iota(orderedPosIds.begin(), orderedPosIds.end(), 0); // Naive order
    std::sort(orderedPosIds.begin(), orderedPosIds.end(),
              [&](unsigned int i, unsigned int j) -> bool {
                  return angles[i] < angles[j];
              });
    // Compute area with sorted positions using shoelace
    NumT a1 = 0, a2 = 0;
    orderedPosIds.push_back(orderedPosIds[0]);
    for (int i = 0; i < orderedPosIds.size() - 1; ++i) {
        a1 += positions[orderedPosIds[i]][0] * positions[orderedPosIds[i + 1]][1];
        a2 += positions[orderedPosIds[i]][1] * positions[orderedPosIds[i + 1]][0];
    }
    return std::fabs(a2 - a1) / 2;
}
    
NumT volumePolyhedra(const VectorVec3& positions) {
#warning TODO_VOLUME
    return 0;
}

Vec2i vecToOctant(const Vec2& dir) {
    Vec2 tmp = dir / dir.norm();
    const Vec2i intDir =
        { sgn(dir[0]) * ( (fabs(tmp[0]) > COS_3PI_8)? 1 : 0 ),
          sgn(dir[1]) * ( (fabs(tmp[1]) > COS_3PI_8)? 1 : 0 ) };
    return intDir;
}



NumT barycenter(NumT lVal, NumT rVal, NumT val) {
    // No clamp check
    return std::min(static_cast<NumT>(1),
                    std::max((val - lVal) / (rVal - lVal),
                             static_cast<NumT>(0)));
}


NumT distancePointEdge(const Vec2& point,
                       const Vec2& eEnd1,
                       const Vec2& eEnd2,
                       Vec2* projection) {
    return distancePointLine(point, eEnd1, eEnd2, projection, true);   
}

NumT distancePointLine(const Vec2& point,
                       const Vec2& eEnd1,
                       const Vec2& eEnd2,
                       Vec2* projection,
                       bool boundToSegment) {
    // Compute projection
    const Vec2 edge = eEnd2 - eEnd1;
    NumT bar = edge.dot(point - eEnd1) / (edge.squaredNorm());
    if (boundToSegment) {
        clamp<NumT>(bar, 0, 1);
    }
    // Distance
    const Vec2 proj = eEnd1 + bar * edge;
    if (projection) {
        *projection = proj;
    }
    return (point - proj).norm();    
}


// From Christer Ericson -- Real-Time Collision Detection
NumT distancePointTriangle(const Vec3& p,
                           const Vec3& a,
                           const Vec3& b,
                           const Vec3& c,
                           Vec3* projPtr,
                           Vec3* barCoordPtr,
                           bool* isInsidePtr) {
    Vec3 proj = p;
    Vec3 barCoord;
    bool isInside = false;
    
    if (true) {
#warning MODIFIED_PT_DISTANCE
        const Vec3 v0 = b - a, v1 = c - a, v2 = p - a;
        const NumT d00 = v0.dot(v0);
        const NumT d01 = v0.dot(v1);
        const NumT d11 = v1.dot(v1);
        const NumT d20 = v2.dot(v0);
        const NumT d21 = v2.dot(v1);
        const NumT invDenom = 1.0 / (d00 * d11 - d01 * d01);
        const NumT v = (d11 * d20 - d01 * d21) * invDenom;
        const NumT w = (d00 * d21 - d01 * d20) * invDenom;
        const NumT u = 1.0f - v - w;

        proj = u * a + v * b + w * c;
        if (projPtr) {
            *projPtr = proj;
        }
        if (barCoordPtr) {
            *barCoordPtr = Vec3(u, v, w); 
        }
        if (isInsidePtr) {
            *isInsidePtr = ( (0 <= u) && (u <= 1)
                             && (0 <= v) && (v <= 1)
                             && (0 <= w) && (w <= 1) );
        }
        return (p - proj).norm();
    }
    
    // Check if P in vertex region outside A
    const Vec3 ab = b - a;
    const Vec3 ac = c - a;
    const Vec3 ap = p - a;
    const double d1 = ab.dot(ap);
    const double d2 = ac.dot(ap);
    const bool isOutA = d1 <= 0.0 && d2 <= 0.0;
    
    if (isOutA) {
            proj = a;
            barCoord = Vec3(1, 0, 0);
    } else {
        // Check if P in vertex region outside B
        const Vec3 bp = p - b;
        const double d3 = ab.dot(bp);
        const double d4 = ac.dot(bp);
        const bool isOutB = d3 >= 0.0 && d4 <= d3;
        if (isOutB) {
            proj = b;
            barCoord = Vec3(0, 1, 0);
        } else {
            // Check if P in edge region of AB, if so return projection of P onto AB
            const double vc = d1*d4 - d3*d2;
            const bool isOutAB = vc <= 0.0 && d1 >= 0.0 && d3 <= 0.0;
            if (isOutAB) {
                const double v = d1 / (d1 - d3);
                proj =  a + v * ab;
                barCoord = Vec3(1-v, v, 0);
            } else {
                // Check if P in vertex region outside C
                const Vec3 cp = p - c;
                const double d5 = ab.dot(cp);
                const double d6 = ac.dot(cp);
                const bool isOutC = d6 >= 0.0 && d5 <= d6;
                if (isOutC) {
                    proj = c;
                    barCoord = Vec3(0, 0, 1);
                } else {
                    // Check if P in edge region of AC, if so return projection of P onto AC
                    const double vb = d5*d2 - d1*d6;
                    const bool isOutAC = vb <= 0.0 && d2 >= 0.0 && d6 <= 0.0;
                    if (isOutAC) {
                        const double w = d2 / (d2 - d6);
                        proj = a + w * ac; 
                        barCoord = Vec3(1 - w, 0, w);
                    } else {
                        // Check if P in edge region of BC, if so return projection of P onto BC
                        const double va = d3*d6 - d5*d4;
                        const bool isOutBC = va <= 0.0 && (d4 - d3) >= 0.0 && (d5 - d6) >= 0.0;
                        if (isOutBC) {
                            const double w = (d4 - d3) / ((d4 - d3) + (d5 - d6));
                            proj = b + w * (c - b); 
                            barCoord = Vec3(0, 1 - w, w);
                        } else {
                            // P inside face region. Compute Q through its barycentric coordinates (u,v,w)
                            const double denom = 1.0 / (va + vb + vc);
                            const double v = vb * denom;
                            const double w = vc * denom;

                            proj = a + ab * v + ac * w;// = u*a + v*b + w*c, u = va * denom = 1.0d - v - w
                            const double u = 1 - v - w;
                            barCoord = Vec3(u, v, w);
                            isInside = true;
                        } // BC
                    } // AC
                } // C
            } // AB
        } // B
    } // A
    
    if (projPtr) {
        *projPtr = proj;
    }
    if (barCoordPtr) {
        *barCoordPtr = barCoord;
    }
    if (isInsidePtr) {
        *isInsidePtr = isInside;
    }
            
    
    return (p - proj).norm(); 
}

bool intersectionRayTriangle(const Vec3& p,
                             const Vec3& dir,
                             const Vec3& p0,
                             const Vec3& p1,
                             const Vec3& p2,
                             Vec3* interPtr,
                             Vec3* barCoordPtr,
                             NumT* distPtr) {
    constexpr NumT eps = 1.e-12;
    const Vec3 edge1 = p1 - p0;
    const Vec3 edge2 = p2 - p0;
    const Vec3 h = dir.cross(edge2);
    const NumT a = edge1.dot(h);
    if ( (-eps < a) && (a < eps)) {
        // This ray is parallel to this triangle.
        return false;
    }
    const NumT f = 1.0/a;
    const Vec3 s = p - p0;
    const NumT u = f * s.dot(h);
    if ((u < 0.0) || (u > 1.0)) {
        return false;
    }
    const Vec3 q = s.cross(edge1);
    const NumT v = f * dir.dot(q);
    if ((v < 0.0) || (u + v > 1.0)) {
        return false;
    }
    // At this stage we can compute t to find out where the intersection point is on the line.
    const NumT t = f * edge2.dot(q);
    //if (t > eps) {
        if (interPtr) {
            *interPtr = p + t * dir;
        }
        if (barCoordPtr) {
            *barCoordPtr = Vec3(1 - u - v, u, v);
        }
        if (distPtr) {
            *distPtr = std::fabs(t);// * dir.length();
        }
        return true;
        //} 
    // This means that there is a line intersection but not a ray intersection.
    //return false;


}

#include "UtilsTriDist.cpp.cimpl"
#include "UtilsPointEllipsoidDist.cpp.cimpl"

NumT distancePointEllipsoid(const Vec3& point,
                            const Vec3& center,
                            NumT eX, NumT eY, NumT eZ) {
    const GTE::Vector<3, NumT> gtePoint(
        {point[0] - center[0],
         point[1] - center[1],
         point[2] - center[2]});
    const GTE::Vector<3, NumT> gteExt({eX, eY, eZ});
    
    GTE::DCPPoint3Ellipsoid3<NumT> distancer;
    return distancer(gtePoint, gteExt).distance;
}


VectorBool::VectorBool(size_t size) :
    m_data(size / 32 + 1) {}
bool VectorBool::get(size_t pos) const {
    // Cannot declare and atomic read
    uint32_t tmp;
#pragma omp atomic read
    tmp = m_data[pos / 32]; 
    return tmp & (1 << (pos % 32));
}
void VectorBool::set(size_t pos, bool val) {
    if (val) {
#pragma omp atomic update
        m_data[pos / 32] |= (1 << (pos % 32));
    } else {
#pragma omp atomic update
        m_data[pos / 32] &= ~(1 << (pos % 32));
    }
}

bool VectorBool::getAndSet(size_t pos, bool val) {
    const uint32_t cmp = 1 << (pos % 32);
    uint32_t res;
    if (val) {
        res = __atomic_fetch_or(&(m_data[pos / 32]), cmp, __ATOMIC_RELAXED);
    } else {
        const uint32_t neg = ~cmp;
        res = __atomic_fetch_and(&(m_data[pos / 32]), neg, __ATOMIC_RELAXED);
    }
    return res & cmp;
}

void VectorBool::resize(size_t newSize) {
    m_data.resize(newSize / 32 + 1);
}
void VectorBool::reset() {
    std::fill(m_data.begin(), m_data.end(), 0);
}


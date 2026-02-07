#include "marchingSquare.hpp"
#include "Common/Utils.hpp"

using namespace Type;

Vec2 evalPosFace2D(unsigned int i, unsigned int j,
                   NumT dx, NumT dy,
                   const std::pair<Face2D, NumT>& bar) {
    Vec2 res;
    switch(bar.first) {
    case Face2D::BOT:
        res = Vec2((i + bar.second) * dx, j * dy);
        break;
    case Face2D::LEFT:
        res = Vec2(i * dx, (j + bar.second) * dy);
        break;
    case Face2D::RIGHT:
        res = Vec2((i + 1) * dx, (j + bar.second) * dy);
    break;
    case Face2D::TOP:
        res = Vec2((i + bar.second) * dx, (j + 1) * dy);
        break;
    default:
        break;
    }
    return res;
}

Face2D findSide(const Vec2& pos,
                unsigned int i, unsigned int j,
                NumT dx, NumT dy) {
    const NumT dLeft  = std::fabs(pos[0] - (i * dx));
    const NumT dRight = std::fabs(((i + 1) * dx) - pos[0]);
    const NumT dBot   = std::fabs(pos[1] - (j * dy));
    const NumT dTop   = std::fabs(((j + 1) * dy) - pos[1]);
    
    const NumT eps = 1.e-10;
    Face2D side = Face2D::None;
    if (dLeft  <= eps * dx) side |= Face2D::LEFT;
    if (dRight <= eps * dx) side |= Face2D::RIGHT;
    if (dBot   <= eps * dy) side |= Face2D::BOT;
    if (dTop   <= eps * dy) side |= Face2D::TOP;
    return side;
}

Face2D getOppositeSide(const Face2D& side) {
    Face2D opp = Face2D::None;
    if (side & Face2D::LEFT)  opp |= Face2D::RIGHT;
    if (side & Face2D::RIGHT) opp |= Face2D::LEFT;
    if (side & Face2D::BOT)   opp |= Face2D::TOP;
    if (side & Face2D::TOP)   opp |= Face2D::BOT;
    return opp;
}


Vec2i goToOppositeSide(const Face2D& side) {
    Vec2i offset;
    if (side & Face2D::LEFT)  offset[0] = -1;
    if (side & Face2D::RIGHT) offset[0] = 1;
    if (side & Face2D::BOT)   offset[1] = -1;
    if (side & Face2D::TOP)   offset[1] = 1;
    return offset;
}


void marchingSquare(NumT blVal, NumT brVal,
                    NumT tlVal, NumT trVal,
                    NumT valThr,
                    std::vector<std::pair<Face2D, NumT>>& res) {

#define ADD_TOP   (res.push_back(std::make_pair(Face2D::TOP,   barycenter(tlVal, trVal, valThr))))
#define ADD_RIGHT (res.push_back(std::make_pair(Face2D::RIGHT, barycenter(brVal, trVal, valThr))))
#define ADD_BOT   (res.push_back(std::make_pair(Face2D::BOT,   barycenter(blVal, brVal, valThr))))
#define ADD_LEFT  (res.push_back(std::make_pair(Face2D::LEFT,  barycenter(blVal, tlVal, valThr))))
    
    if (blVal > valThr) {
        if (brVal > valThr) {
            if (tlVal > valThr) {
                if (trVal > valThr) {
                    // Inside
                } else { // trVal <= valThr
                    // 3 points, bl
                    ADD_TOP;
                    ADD_RIGHT;
                }
            } else { // tlVal <= valThr
                if (trVal > valThr) {
                    // 3 points, brVal
                    ADD_LEFT;
                    ADD_TOP;
                } else { // trVal <= valThr
                    // 2 points, b
                    ADD_LEFT;
                    ADD_RIGHT;
                }
            }
        } else { // brVal <= valThr
            if (tlVal > valThr) {
                if (trVal > valThr) {
                    // 3 points, tlVal
                    ADD_RIGHT;
                    ADD_BOT;
                } else { // trVal <= valThr
                    // 2 points, l
                    ADD_TOP;
                    ADD_BOT;
                }
            } else { // tlVal <= valThr
                if (trVal > valThr) {
                    // double val
                    // blVal
                    ADD_LEFT;
                    ADD_BOT;
                    // trVal
                    ADD_RIGHT;
                    ADD_TOP;
                } else { // trVal <= valThr
                    // 1 point, blVal
                    ADD_LEFT;
                    ADD_BOT;
                }
            }
        }
    } else { // blVal <= valThr
        if (brVal > valThr) {
            if (tlVal > valThr) {
                if (trVal > valThr) {
                    // 3 points, trVal
                    ADD_BOT;
                    ADD_LEFT;
                } else { // trVal <= valThr
                    // double val
                    // brVal
                    ADD_BOT;
                    ADD_RIGHT;
                    // tlVal
                    ADD_TOP;
                    ADD_LEFT;
                }
            } else { // tlVal <= valThr
                if (trVal > valThr) {
                    // 2 points, r
                    ADD_BOT;
                    ADD_TOP;
                } else { // trVal <= valThr
                    // 1 point, brVal
                    ADD_BOT;
                    ADD_RIGHT;
                }
            }
        } else { // brVal <= valThr
            if (tlVal > valThr) {
                if (trVal > valThr) {
                    // 2 points, t
                    ADD_RIGHT;
                    ADD_LEFT;
                } else { // trVal <= valThr
                    // 1 point, tlVal
                    ADD_TOP;
                    ADD_LEFT;
                }
            } else { // tlVal <= valThr
                if (trVal > valThr) {
                    // 1 point, trVal
                    ADD_RIGHT;
                    ADD_TOP;
                } else { // trVal <= valThr
                    // Outside
                }
            }
        }
    }
#undef ADD_TOP
#undef ADD_RIGHT
#undef ADD_BOT
#undef ADD_LEFT
}
                

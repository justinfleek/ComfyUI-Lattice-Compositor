/* ExactnessPredicates.cpp
*
* source for code and comments:
/*****************************************************************************/
/*                                                                           */
/*  Routines for Arbitrary Precision Floating-point Arithmetic               */
/*  and Fast Robust Geometric Predicates                                     */
/*  (predicates.c)                                                           */
/*                                                                           */
/*  May 18, 1996                                                             */
/*                                                                           */
/*  Placed in the public domain by                                           */
/*  Jonathan Richard Shewchuk                                                */
/*  School of Computer Science                                               */
/*  Carnegie Mellon University                                               */
/*  5000 Forbes Avenue                                                       */
/*  Pittsburgh, Pennsylvania  15213-3891                                     */
/*  jrs@cs.cmu.edu                                                           */
/*                                                                           */
/*  This file contains C implementation of algorithms for exact addition     */
/*    and multiplication of floating-point numbers, and predicates for       */
/*    robustly performing the orientation and incircle tests used in         */
/*    computational geometry.  The algorithms and underlying theory are      */
/*    described in Jonathan Richard Shewchuk.  "Adaptive Precision Floating- */
/*    Point Arithmetic and Fast Robust Geometric Predicates."  Technical     */
/*    Report CMU-CS-96-140, School of Computer Science, Carnegie Mellon      */
/*    University, Pittsburgh, Pennsylvania, May 1996.  (Submitted to         */
/*    Discrete & Computational Geometry.)                                    */
/*                                                                           */
/*  This file, the paper listed above, and other information are available   */
/*    from the Web page http://www.cs.cmu.edu/~quake/robust.html .           */
/*                                                                           */
/*****************************************************************************/
/* adjusted by Peter Synak, Chris Wojtan, Huidong Yang, 2021
*
* This is the implementation file for the exactness predicates class, which reliably answers plane orientation and incircle tests using adaptive arithmetic.
*/

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include "ExactnessPredicates.h"

//------------------------------------------------------------
// constructors
//------------------------------------------------------------

// default constructor
ExactnessPredicates::ExactnessPredicates()
{
}

// default destructor
ExactnessPredicates::~ExactnessPredicates()
{
}

//------------------------------------------------------------
// helper functions
//------------------------------------------------------------

/*****************************************************************************/
/*                                                                           */
/*  exactinit()   Initialize the variables used for exact arithmetic.        */
/*                                                                           */
/*  `epsilon' is the largest power of two such that 1.0 + epsilon = 1.0 in   */
/*  floating-point arithmetic.  `epsilon' bounds the relative roundoff       */
/*  error.  It is used for floating-point error analysis.                    */
/*                                                                           */
/*  `splitter' is used to split floating-point numbers into two half-        */
/*  length significands for exact multiplication.                            */
/*                                                                           */
/*  I imagine that a highly optimizing compiler might be too smart for its   */
/*  own good, and somehow cause this routine to fail, if it pretends that    */
/*  floating-point arithmetic is too much like real arithmetic.              */
/*                                                                           */
/*  Don't change this routine unless you fully understand it.                */
/*                                                                           */
/*****************************************************************************/

void ExactnessPredicates::exactinit()
{
    REAL half;
    REAL check, lastcheck;
    int every_other;

    every_other = 1;
    half = 0.5;
    epsilon = 1.0;
    splitter = 1.0;
    check = 1.0;
    /* Repeatedly divide `epsilon' by two until it is too small to add to    */
    /*   one without causing roundoff.  (Also check if the sum is equal to   */
    /*   the previous sum, for machines that round up instead of using exact */
    /*   rounding.  Not that this library will work on such machines anyway. */
    do {
        lastcheck = check;
        epsilon *= half;
        if (every_other) {
            splitter *= 2.0;
        }
        every_other = !every_other;
        check = 1.0 + epsilon;
    } while ((check != 1.0) && (check != lastcheck));
    splitter += 1.0;

    /* Error bounds for orientation and incircle tests. */
    resulterrbound = (3.0 + 8.0 * epsilon) * epsilon;
    ccwerrboundA = (3.0 + 16.0 * epsilon) * epsilon;
    ccwerrboundB = (2.0 + 12.0 * epsilon) * epsilon;
    ccwerrboundC = (9.0 + 64.0 * epsilon) * epsilon * epsilon;
    o3derrboundA = (7.0 + 56.0 * epsilon) * epsilon;
    o3derrboundB = (3.0 + 28.0 * epsilon) * epsilon;
    o3derrboundC = (26.0 + 288.0 * epsilon) * epsilon * epsilon;
    iccerrboundA = (10.0 + 96.0 * epsilon) * epsilon;
    iccerrboundB = (4.0 + 48.0 * epsilon) * epsilon;
    iccerrboundC = (44.0 + 576.0 * epsilon) * epsilon * epsilon;
    isperrboundA = (16.0 + 224.0 * epsilon) * epsilon;
    isperrboundB = (5.0 + 72.0 * epsilon) * epsilon;
    isperrboundC = (71.0 + 1408.0 * epsilon) * epsilon * epsilon;
}

/*****************************************************************************/
/*                                                                           */
/*  fast_expansion_sum_zeroelim()   Sum two expansions, eliminating zero     */
/*                                  components from the output expansion.    */
/*                                                                           */
/*  Sets h = e + f.  See the long version of my paper for details.           */
/*                                                                           */
/*  If round-to-even is used (as with IEEE 754), maintains the strongly      */
/*  nonoverlapping property.  (That is, if e is strongly nonoverlapping, h   */
/*  will be also.)  Does NOT maintain the nonoverlapping or nonadjacent      */
/*  properties.                                                              */
/*                                                                           */
/*****************************************************************************/

int ExactnessPredicates::fast_expansion_sum_zeroelim(int elen, REAL* e, int flen, REAL* f, REAL* h)  /* h cannot be e or f. */
{
    REAL Q;
    INEXACT REAL Qnew;
    INEXACT REAL hh;
    INEXACT REAL bvirt;
    REAL avirt, bround, around;
    int eindex, findex, hindex;
    REAL enow, fnow;

    enow = e[0];
    fnow = f[0];
    eindex = findex = 0;
    if ((fnow > enow) == (fnow > -enow)) {
        Q = enow;
        enow = e[++eindex];
    }
    else {
        Q = fnow;
        fnow = f[++findex];
    }
    hindex = 0;
    if ((eindex < elen) && (findex < flen)) {
        if ((fnow > enow) == (fnow > -enow)) {
            Fast_Two_Sum(enow, Q, Qnew, hh);
            enow = e[++eindex];
        }
        else {
            Fast_Two_Sum(fnow, Q, Qnew, hh);
            fnow = f[++findex];
        }
        Q = Qnew;
        if (hh != 0.0) {
            h[hindex++] = hh;
        }
        while ((eindex < elen) && (findex < flen)) {
            if ((fnow > enow) == (fnow > -enow)) {
                Two_Sum(Q, enow, Qnew, hh);
                enow = e[++eindex];
            }
            else {
                Two_Sum(Q, fnow, Qnew, hh);
                fnow = f[++findex];
            }
            Q = Qnew;
            if (hh != 0.0) {
                h[hindex++] = hh;
            }
        }
    }
    while (eindex < elen) {
        Two_Sum(Q, enow, Qnew, hh);
        enow = e[++eindex];
        Q = Qnew;
        if (hh != 0.0) {
            h[hindex++] = hh;
        }
    }
    while (findex < flen) {
        Two_Sum(Q, fnow, Qnew, hh);
        fnow = f[++findex];
        Q = Qnew;
        if (hh != 0.0) {
            h[hindex++] = hh;
        }
    }
    if ((Q != 0.0) || (hindex == 0)) {
        h[hindex++] = Q;
    }
    return hindex;
}

/*****************************************************************************/
/*                                                                           */
/*  scale_expansion_zeroelim()   Multiply an expansion by a scalar,          */
/*                               eliminating zero components from the        */
/*                               output expansion.                           */
/*                                                                           */
/*  Sets h = be.  See either version of my paper for details.                */
/*                                                                           */
/*  Maintains the nonoverlapping property.  If round-to-even is used (as     */
/*  with IEEE 754), maintains the strongly nonoverlapping and nonadjacent    */
/*  properties as well.  (That is, if e has one of these properties, so      */
/*  will h.)                                                                 */
/*                                                                           */
/*****************************************************************************/

int ExactnessPredicates::scale_expansion_zeroelim(int elen, REAL* e, REAL b, REAL* h)   /* e and h cannot be the same. */
{
    INEXACT REAL Q, sum;
    REAL hh;
    INEXACT REAL product1;
    REAL product0;
    int eindex, hindex;
    REAL enow;
    INEXACT REAL bvirt;
    REAL avirt, bround, around;
    INEXACT REAL c;
    INEXACT REAL abig;
    REAL ahi, alo, bhi, blo;
    REAL err1, err2, err3;

    SplitEx(b, bhi, blo);
    Two_Product_Presplit(e[0], b, bhi, blo, Q, hh);
    hindex = 0;
    if (hh != 0) {
        h[hindex++] = hh;
    }
    for (eindex = 1; eindex < elen; eindex++) {
        enow = e[eindex];
        Two_Product_Presplit(enow, b, bhi, blo, product1, product0);
        Two_Sum(Q, product0, sum, hh);
        if (hh != 0) {
            h[hindex++] = hh;
        }
        Fast_Two_Sum(product1, sum, Q, hh);
        if (hh != 0) {
            h[hindex++] = hh;
        }
    }
    if ((Q != 0.0) || (hindex == 0)) {
        h[hindex++] = Q;
    }
    return hindex;
}

/*****************************************************************************/
/*                                                                           */
/*  estimate()   Produce a one-word estimate of an expansion's value.        */
/*                                                                           */
/*  See either version of my paper for details.                              */
/*                                                                           */
/*****************************************************************************/

REAL ExactnessPredicates::estimate(int elen, REAL* e)
{
    REAL Q;
    int eindex;

    Q = e[0];
    for (eindex = 1; eindex < elen; eindex++) {
        Q += e[eindex];
    }
    return Q;
}

//------------------------------------------------------------
// orientation tests
//------------------------------------------------------------

/*****************************************************************************/
/*                                                                           */
/*  orient3dfast()   Approximate 3D orientation test.  Nonrobust.            */
/*  orient3dexact()   Exact 3D orientation test.  Robust.                    */
/*  orient3dslow()   Another exact 3D orientation test.  Robust.             */
/*  orient3d()   Adaptive exact 3D orientation test.  Robust.                */
/*                                                                           */
/*               Return a positive value if the point pd lies below the      */
/*               plane passing through pa, pb, and pc; "below" is defined so */
/*               that pa, pb, and pc appear in counterclockwise order when   */
/*               viewed from above the plane.  Returns a negative value if   */
/*               pd lies above the plane.  Returns zero if the points are    */
/*               coplanar.  The result is also a rough approximation of six  */
/*               times the signed volume of the tetrahedron defined by the   */
/*               four points.                                                */
/*                                                                           */
/*  Only the first and last routine should be used; the middle two are for   */
/*  timings.                                                                 */
/*                                                                           */
/*  The last three use exact arithmetic to ensure a correct answer.  The     */
/*  result returned is the determinant of a matrix.  In orient3d() only,     */
/*  this determinant is computed adaptively, in the sense that exact         */
/*  arithmetic is used only to the degree it is needed to ensure that the    */
/*  returned value has the correct sign.  Hence, orient3d() is usually quite */
/*  fast, but will run more slowly when the input points are coplanar or     */
/*  nearly so.                                                               */
/*                                                                           */
/*****************************************************************************/

REAL ExactnessPredicates::orient3dfast(REAL* pa, REAL* pb, REAL* pc, REAL* pd)
{
    REAL adx, bdx, cdx;
    REAL ady, bdy, cdy;
    REAL adz, bdz, cdz;

    adx = pa[0] - pd[0];
    bdx = pb[0] - pd[0];
    cdx = pc[0] - pd[0];
    ady = pa[1] - pd[1];
    bdy = pb[1] - pd[1];
    cdy = pc[1] - pd[1];
    adz = pa[2] - pd[2];
    bdz = pb[2] - pd[2];
    cdz = pc[2] - pd[2];

    return adx * (bdy * cdz - bdz * cdy)
        + bdx * (cdy * adz - cdz * ady)
        + cdx * (ady * bdz - adz * bdy);
}

REAL ExactnessPredicates::orient3dexact(REAL* pa, REAL* pb, REAL* pc, REAL* pd)
{
    INEXACT REAL axby1, bxcy1, cxdy1, dxay1, axcy1, bxdy1;
    INEXACT REAL bxay1, cxby1, dxcy1, axdy1, cxay1, dxby1;
    REAL axby0, bxcy0, cxdy0, dxay0, axcy0, bxdy0;
    REAL bxay0, cxby0, dxcy0, axdy0, cxay0, dxby0;
    REAL ab[4], bc[4], cd[4], da[4], ac[4], bd[4];
    REAL temp8[8];
    int templen;
    REAL abc[12], bcd[12], cda[12], dab[12];
    int abclen, bcdlen, cdalen, dablen;
    REAL adet[24], bdet[24], cdet[24], ddet[24];
    int alen, blen, clen, dlen;
    REAL abdet[48], cddet[48];
    int ablen, cdlen;
    REAL deter[96];
    int deterlen;
    int i;

    INEXACT REAL bvirt;
    REAL avirt, bround, around;
    INEXACT REAL c;
    INEXACT REAL abig;
    REAL ahi, alo, bhi, blo;
    REAL err1, err2, err3;
    INEXACT REAL _i, _j;
    REAL _0;

    Two_Product(pa[0], pb[1], axby1, axby0);
    Two_Product(pb[0], pa[1], bxay1, bxay0);
    Two_Two_Diff(axby1, axby0, bxay1, bxay0, ab[3], ab[2], ab[1], ab[0]);

    Two_Product(pb[0], pc[1], bxcy1, bxcy0);
    Two_Product(pc[0], pb[1], cxby1, cxby0);
    Two_Two_Diff(bxcy1, bxcy0, cxby1, cxby0, bc[3], bc[2], bc[1], bc[0]);

    Two_Product(pc[0], pd[1], cxdy1, cxdy0);
    Two_Product(pd[0], pc[1], dxcy1, dxcy0);
    Two_Two_Diff(cxdy1, cxdy0, dxcy1, dxcy0, cd[3], cd[2], cd[1], cd[0]);

    Two_Product(pd[0], pa[1], dxay1, dxay0);
    Two_Product(pa[0], pd[1], axdy1, axdy0);
    Two_Two_Diff(dxay1, dxay0, axdy1, axdy0, da[3], da[2], da[1], da[0]);

    Two_Product(pa[0], pc[1], axcy1, axcy0);
    Two_Product(pc[0], pa[1], cxay1, cxay0);
    Two_Two_Diff(axcy1, axcy0, cxay1, cxay0, ac[3], ac[2], ac[1], ac[0]);

    Two_Product(pb[0], pd[1], bxdy1, bxdy0);
    Two_Product(pd[0], pb[1], dxby1, dxby0);
    Two_Two_Diff(bxdy1, bxdy0, dxby1, dxby0, bd[3], bd[2], bd[1], bd[0]);

    templen = fast_expansion_sum_zeroelim(4, cd, 4, da, temp8);
    cdalen = fast_expansion_sum_zeroelim(templen, temp8, 4, ac, cda);
    templen = fast_expansion_sum_zeroelim(4, da, 4, ab, temp8);
    dablen = fast_expansion_sum_zeroelim(templen, temp8, 4, bd, dab);
    for (i = 0; i < 4; i++) {
        bd[i] = -bd[i];
        ac[i] = -ac[i];
    }
    templen = fast_expansion_sum_zeroelim(4, ab, 4, bc, temp8);
    abclen = fast_expansion_sum_zeroelim(templen, temp8, 4, ac, abc);
    templen = fast_expansion_sum_zeroelim(4, bc, 4, cd, temp8);
    bcdlen = fast_expansion_sum_zeroelim(templen, temp8, 4, bd, bcd);

    alen = scale_expansion_zeroelim(bcdlen, bcd, pa[2], adet);
    blen = scale_expansion_zeroelim(cdalen, cda, -pb[2], bdet);
    clen = scale_expansion_zeroelim(dablen, dab, pc[2], cdet);
    dlen = scale_expansion_zeroelim(abclen, abc, -pd[2], ddet);

    ablen = fast_expansion_sum_zeroelim(alen, adet, blen, bdet, abdet);
    cdlen = fast_expansion_sum_zeroelim(clen, cdet, dlen, ddet, cddet);
    deterlen = fast_expansion_sum_zeroelim(ablen, abdet, cdlen, cddet, deter);

    return deter[deterlen - 1];
}

REAL ExactnessPredicates::orient3dslow(REAL* pa, REAL* pb, REAL* pc, REAL* pd)
{
    INEXACT REAL adx, ady, adz, bdx, bdy, bdz, cdx, cdy, cdz;
    REAL adxtail, adytail, adztail;
    REAL bdxtail, bdytail, bdztail;
    REAL cdxtail, cdytail, cdztail;
    REAL negate, negatetail;
    INEXACT REAL axby7, bxcy7, axcy7, bxay7, cxby7, cxay7;
    REAL axby[8], bxcy[8], axcy[8], bxay[8], cxby[8], cxay[8];
    REAL temp16[16], temp32[32], temp32t[32];
    int temp16len, temp32len, temp32tlen;
    REAL adet[64], bdet[64], cdet[64];
    int alen, blen, clen;
    REAL abdet[128];
    int ablen;
    REAL deter[192];
    int deterlen;

    INEXACT REAL bvirt;
    REAL avirt, bround, around;
    INEXACT REAL c;
    INEXACT REAL abig;
    REAL a0hi, a0lo, a1hi, a1lo, bhi, blo;
    REAL err1, err2, err3;
    INEXACT REAL _i, _j, _k, _l, _m, _n;
    REAL _0, _1, _2;

    Two_Diff(pa[0], pd[0], adx, adxtail);
    Two_Diff(pa[1], pd[1], ady, adytail);
    Two_Diff(pa[2], pd[2], adz, adztail);
    Two_Diff(pb[0], pd[0], bdx, bdxtail);
    Two_Diff(pb[1], pd[1], bdy, bdytail);
    Two_Diff(pb[2], pd[2], bdz, bdztail);
    Two_Diff(pc[0], pd[0], cdx, cdxtail);
    Two_Diff(pc[1], pd[1], cdy, cdytail);
    Two_Diff(pc[2], pd[2], cdz, cdztail);

    Two_Two_Product(adx, adxtail, bdy, bdytail,
        axby7, axby[6], axby[5], axby[4],
        axby[3], axby[2], axby[1], axby[0]);
    axby[7] = axby7;
    negate = -ady;
    negatetail = -adytail;
    Two_Two_Product(bdx, bdxtail, negate, negatetail,
        bxay7, bxay[6], bxay[5], bxay[4],
        bxay[3], bxay[2], bxay[1], bxay[0]);
    bxay[7] = bxay7;
    Two_Two_Product(bdx, bdxtail, cdy, cdytail,
        bxcy7, bxcy[6], bxcy[5], bxcy[4],
        bxcy[3], bxcy[2], bxcy[1], bxcy[0]);
    bxcy[7] = bxcy7;
    negate = -bdy;
    negatetail = -bdytail;
    Two_Two_Product(cdx, cdxtail, negate, negatetail,
        cxby7, cxby[6], cxby[5], cxby[4],
        cxby[3], cxby[2], cxby[1], cxby[0]);
    cxby[7] = cxby7;
    Two_Two_Product(cdx, cdxtail, ady, adytail,
        cxay7, cxay[6], cxay[5], cxay[4],
        cxay[3], cxay[2], cxay[1], cxay[0]);
    cxay[7] = cxay7;
    negate = -cdy;
    negatetail = -cdytail;
    Two_Two_Product(adx, adxtail, negate, negatetail,
        axcy7, axcy[6], axcy[5], axcy[4],
        axcy[3], axcy[2], axcy[1], axcy[0]);
    axcy[7] = axcy7;

    temp16len = fast_expansion_sum_zeroelim(8, bxcy, 8, cxby, temp16);
    temp32len = scale_expansion_zeroelim(temp16len, temp16, adz, temp32);
    temp32tlen = scale_expansion_zeroelim(temp16len, temp16, adztail, temp32t);
    alen = fast_expansion_sum_zeroelim(temp32len, temp32, temp32tlen, temp32t,
        adet);

    temp16len = fast_expansion_sum_zeroelim(8, cxay, 8, axcy, temp16);
    temp32len = scale_expansion_zeroelim(temp16len, temp16, bdz, temp32);
    temp32tlen = scale_expansion_zeroelim(temp16len, temp16, bdztail, temp32t);
    blen = fast_expansion_sum_zeroelim(temp32len, temp32, temp32tlen, temp32t,
        bdet);

    temp16len = fast_expansion_sum_zeroelim(8, axby, 8, bxay, temp16);
    temp32len = scale_expansion_zeroelim(temp16len, temp16, cdz, temp32);
    temp32tlen = scale_expansion_zeroelim(temp16len, temp16, cdztail, temp32t);
    clen = fast_expansion_sum_zeroelim(temp32len, temp32, temp32tlen, temp32t,
        cdet);

    ablen = fast_expansion_sum_zeroelim(alen, adet, blen, bdet, abdet);
    deterlen = fast_expansion_sum_zeroelim(ablen, abdet, clen, cdet, deter);

    return deter[deterlen - 1];
}

REAL ExactnessPredicates::orient3dadapt(REAL* pa, REAL* pb, REAL* pc, REAL* pd, REAL permanent)
{
    INEXACT REAL adx, bdx, cdx, ady, bdy, cdy, adz, bdz, cdz;
    REAL det, errbound;

    INEXACT REAL bdxcdy1, cdxbdy1, cdxady1, adxcdy1, adxbdy1, bdxady1;
    REAL bdxcdy0, cdxbdy0, cdxady0, adxcdy0, adxbdy0, bdxady0;
    REAL bc[4], ca[4], ab[4];
    INEXACT REAL bc3, ca3, ab3;
    REAL adet[8], bdet[8], cdet[8];
    int alen, blen, clen;
    REAL abdet[16];
    int ablen;
    REAL* finnow, * finother, * finswap;
    REAL fin1[192], fin2[192];
    int finlength;

    REAL adxtail, bdxtail, cdxtail;
    REAL adytail, bdytail, cdytail;
    REAL adztail, bdztail, cdztail;
    INEXACT REAL at_blarge, at_clarge;
    INEXACT REAL bt_clarge, bt_alarge;
    INEXACT REAL ct_alarge, ct_blarge;
    REAL at_b[4], at_c[4], bt_c[4], bt_a[4], ct_a[4], ct_b[4];
    int at_blen, at_clen, bt_clen, bt_alen, ct_alen, ct_blen;
    INEXACT REAL bdxt_cdy1, cdxt_bdy1, cdxt_ady1;
    INEXACT REAL adxt_cdy1, adxt_bdy1, bdxt_ady1;
    REAL bdxt_cdy0, cdxt_bdy0, cdxt_ady0;
    REAL adxt_cdy0, adxt_bdy0, bdxt_ady0;
    INEXACT REAL bdyt_cdx1, cdyt_bdx1, cdyt_adx1;
    INEXACT REAL adyt_cdx1, adyt_bdx1, bdyt_adx1;
    REAL bdyt_cdx0, cdyt_bdx0, cdyt_adx0;
    REAL adyt_cdx0, adyt_bdx0, bdyt_adx0;
    REAL bct[8], cat[8], abt[8];
    int bctlen, catlen, abtlen;
    INEXACT REAL bdxt_cdyt1, cdxt_bdyt1, cdxt_adyt1;
    INEXACT REAL adxt_cdyt1, adxt_bdyt1, bdxt_adyt1;
    REAL bdxt_cdyt0, cdxt_bdyt0, cdxt_adyt0;
    REAL adxt_cdyt0, adxt_bdyt0, bdxt_adyt0;
    REAL u[4], v[12], w[16];
    INEXACT REAL u3;
    int vlength, wlength;
    REAL negate;

    INEXACT REAL bvirt;
    REAL avirt, bround, around;
    INEXACT REAL c;
    INEXACT REAL abig;
    REAL ahi, alo, bhi, blo;
    REAL err1, err2, err3;
    INEXACT REAL _i, _j, _k;
    REAL _0;

    adx = (REAL)(pa[0] - pd[0]);
    bdx = (REAL)(pb[0] - pd[0]);
    cdx = (REAL)(pc[0] - pd[0]);
    ady = (REAL)(pa[1] - pd[1]);
    bdy = (REAL)(pb[1] - pd[1]);
    cdy = (REAL)(pc[1] - pd[1]);
    adz = (REAL)(pa[2] - pd[2]);
    bdz = (REAL)(pb[2] - pd[2]);
    cdz = (REAL)(pc[2] - pd[2]);

    Two_Product(bdx, cdy, bdxcdy1, bdxcdy0);
    Two_Product(cdx, bdy, cdxbdy1, cdxbdy0);
    Two_Two_Diff(bdxcdy1, bdxcdy0, cdxbdy1, cdxbdy0, bc3, bc[2], bc[1], bc[0]);
    bc[3] = bc3;
    alen = scale_expansion_zeroelim(4, bc, adz, adet);

    Two_Product(cdx, ady, cdxady1, cdxady0);
    Two_Product(adx, cdy, adxcdy1, adxcdy0);
    Two_Two_Diff(cdxady1, cdxady0, adxcdy1, adxcdy0, ca3, ca[2], ca[1], ca[0]);
    ca[3] = ca3;
    blen = scale_expansion_zeroelim(4, ca, bdz, bdet);

    Two_Product(adx, bdy, adxbdy1, adxbdy0);
    Two_Product(bdx, ady, bdxady1, bdxady0);
    Two_Two_Diff(adxbdy1, adxbdy0, bdxady1, bdxady0, ab3, ab[2], ab[1], ab[0]);
    ab[3] = ab3;
    clen = scale_expansion_zeroelim(4, ab, cdz, cdet);

    ablen = fast_expansion_sum_zeroelim(alen, adet, blen, bdet, abdet);
    finlength = fast_expansion_sum_zeroelim(ablen, abdet, clen, cdet, fin1);

    det = estimate(finlength, fin1);
    errbound = o3derrboundB * permanent;
    if ((det >= errbound) || (-det >= errbound)) {
        return det;
    }

    Two_Diff_Tail(pa[0], pd[0], adx, adxtail);
    Two_Diff_Tail(pb[0], pd[0], bdx, bdxtail);
    Two_Diff_Tail(pc[0], pd[0], cdx, cdxtail);
    Two_Diff_Tail(pa[1], pd[1], ady, adytail);
    Two_Diff_Tail(pb[1], pd[1], bdy, bdytail);
    Two_Diff_Tail(pc[1], pd[1], cdy, cdytail);
    Two_Diff_Tail(pa[2], pd[2], adz, adztail);
    Two_Diff_Tail(pb[2], pd[2], bdz, bdztail);
    Two_Diff_Tail(pc[2], pd[2], cdz, cdztail);

    if ((adxtail == 0.0) && (bdxtail == 0.0) && (cdxtail == 0.0)
        && (adytail == 0.0) && (bdytail == 0.0) && (cdytail == 0.0)
        && (adztail == 0.0) && (bdztail == 0.0) && (cdztail == 0.0)) {
        return det;
    }

    errbound = o3derrboundC * permanent + resulterrbound * Absolute(det);
    det += (adz * ((bdx * cdytail + cdy * bdxtail)
        - (bdy * cdxtail + cdx * bdytail))
        + adztail * (bdx * cdy - bdy * cdx))
        + (bdz * ((cdx * adytail + ady * cdxtail)
            - (cdy * adxtail + adx * cdytail))
            + bdztail * (cdx * ady - cdy * adx))
        + (cdz * ((adx * bdytail + bdy * adxtail)
            - (ady * bdxtail + bdx * adytail))
            + cdztail * (adx * bdy - ady * bdx));
    if ((det >= errbound) || (-det >= errbound)) {
        return det;
    }

    finnow = fin1;
    finother = fin2;

    if (adxtail == 0.0) {
        if (adytail == 0.0) {
            at_b[0] = 0.0;
            at_blen = 1;
            at_c[0] = 0.0;
            at_clen = 1;
        }
        else {
            negate = -adytail;
            Two_Product(negate, bdx, at_blarge, at_b[0]);
            at_b[1] = at_blarge;
            at_blen = 2;
            Two_Product(adytail, cdx, at_clarge, at_c[0]);
            at_c[1] = at_clarge;
            at_clen = 2;
        }
    }
    else {
        if (adytail == 0.0) {
            Two_Product(adxtail, bdy, at_blarge, at_b[0]);
            at_b[1] = at_blarge;
            at_blen = 2;
            negate = -adxtail;
            Two_Product(negate, cdy, at_clarge, at_c[0]);
            at_c[1] = at_clarge;
            at_clen = 2;
        }
        else {
            Two_Product(adxtail, bdy, adxt_bdy1, adxt_bdy0);
            Two_Product(adytail, bdx, adyt_bdx1, adyt_bdx0);
            Two_Two_Diff(adxt_bdy1, adxt_bdy0, adyt_bdx1, adyt_bdx0,
                at_blarge, at_b[2], at_b[1], at_b[0]);
            at_b[3] = at_blarge;
            at_blen = 4;
            Two_Product(adytail, cdx, adyt_cdx1, adyt_cdx0);
            Two_Product(adxtail, cdy, adxt_cdy1, adxt_cdy0);
            Two_Two_Diff(adyt_cdx1, adyt_cdx0, adxt_cdy1, adxt_cdy0,
                at_clarge, at_c[2], at_c[1], at_c[0]);
            at_c[3] = at_clarge;
            at_clen = 4;
        }
    }
    if (bdxtail == 0.0) {
        if (bdytail == 0.0) {
            bt_c[0] = 0.0;
            bt_clen = 1;
            bt_a[0] = 0.0;
            bt_alen = 1;
        }
        else {
            negate = -bdytail;
            Two_Product(negate, cdx, bt_clarge, bt_c[0]);
            bt_c[1] = bt_clarge;
            bt_clen = 2;
            Two_Product(bdytail, adx, bt_alarge, bt_a[0]);
            bt_a[1] = bt_alarge;
            bt_alen = 2;
        }
    }
    else {
        if (bdytail == 0.0) {
            Two_Product(bdxtail, cdy, bt_clarge, bt_c[0]);
            bt_c[1] = bt_clarge;
            bt_clen = 2;
            negate = -bdxtail;
            Two_Product(negate, ady, bt_alarge, bt_a[0]);
            bt_a[1] = bt_alarge;
            bt_alen = 2;
        }
        else {
            Two_Product(bdxtail, cdy, bdxt_cdy1, bdxt_cdy0);
            Two_Product(bdytail, cdx, bdyt_cdx1, bdyt_cdx0);
            Two_Two_Diff(bdxt_cdy1, bdxt_cdy0, bdyt_cdx1, bdyt_cdx0,
                bt_clarge, bt_c[2], bt_c[1], bt_c[0]);
            bt_c[3] = bt_clarge;
            bt_clen = 4;
            Two_Product(bdytail, adx, bdyt_adx1, bdyt_adx0);
            Two_Product(bdxtail, ady, bdxt_ady1, bdxt_ady0);
            Two_Two_Diff(bdyt_adx1, bdyt_adx0, bdxt_ady1, bdxt_ady0,
                bt_alarge, bt_a[2], bt_a[1], bt_a[0]);
            bt_a[3] = bt_alarge;
            bt_alen = 4;
        }
    }
    if (cdxtail == 0.0) {
        if (cdytail == 0.0) {
            ct_a[0] = 0.0;
            ct_alen = 1;
            ct_b[0] = 0.0;
            ct_blen = 1;
        }
        else {
            negate = -cdytail;
            Two_Product(negate, adx, ct_alarge, ct_a[0]);
            ct_a[1] = ct_alarge;
            ct_alen = 2;
            Two_Product(cdytail, bdx, ct_blarge, ct_b[0]);
            ct_b[1] = ct_blarge;
            ct_blen = 2;
        }
    }
    else {
        if (cdytail == 0.0) {
            Two_Product(cdxtail, ady, ct_alarge, ct_a[0]);
            ct_a[1] = ct_alarge;
            ct_alen = 2;
            negate = -cdxtail;
            Two_Product(negate, bdy, ct_blarge, ct_b[0]);
            ct_b[1] = ct_blarge;
            ct_blen = 2;
        }
        else {
            Two_Product(cdxtail, ady, cdxt_ady1, cdxt_ady0);
            Two_Product(cdytail, adx, cdyt_adx1, cdyt_adx0);
            Two_Two_Diff(cdxt_ady1, cdxt_ady0, cdyt_adx1, cdyt_adx0,
                ct_alarge, ct_a[2], ct_a[1], ct_a[0]);
            ct_a[3] = ct_alarge;
            ct_alen = 4;
            Two_Product(cdytail, bdx, cdyt_bdx1, cdyt_bdx0);
            Two_Product(cdxtail, bdy, cdxt_bdy1, cdxt_bdy0);
            Two_Two_Diff(cdyt_bdx1, cdyt_bdx0, cdxt_bdy1, cdxt_bdy0,
                ct_blarge, ct_b[2], ct_b[1], ct_b[0]);
            ct_b[3] = ct_blarge;
            ct_blen = 4;
        }
    }

    bctlen = fast_expansion_sum_zeroelim(bt_clen, bt_c, ct_blen, ct_b, bct);
    wlength = scale_expansion_zeroelim(bctlen, bct, adz, w);
    finlength = fast_expansion_sum_zeroelim(finlength, finnow, wlength, w,
        finother);
    finswap = finnow; finnow = finother; finother = finswap;

    catlen = fast_expansion_sum_zeroelim(ct_alen, ct_a, at_clen, at_c, cat);
    wlength = scale_expansion_zeroelim(catlen, cat, bdz, w);
    finlength = fast_expansion_sum_zeroelim(finlength, finnow, wlength, w,
        finother);
    finswap = finnow; finnow = finother; finother = finswap;

    abtlen = fast_expansion_sum_zeroelim(at_blen, at_b, bt_alen, bt_a, abt);
    wlength = scale_expansion_zeroelim(abtlen, abt, cdz, w);
    finlength = fast_expansion_sum_zeroelim(finlength, finnow, wlength, w,
        finother);
    finswap = finnow; finnow = finother; finother = finswap;

    if (adztail != 0.0) {
        vlength = scale_expansion_zeroelim(4, bc, adztail, v);
        finlength = fast_expansion_sum_zeroelim(finlength, finnow, vlength, v,
            finother);
        finswap = finnow; finnow = finother; finother = finswap;
    }
    if (bdztail != 0.0) {
        vlength = scale_expansion_zeroelim(4, ca, bdztail, v);
        finlength = fast_expansion_sum_zeroelim(finlength, finnow, vlength, v,
            finother);
        finswap = finnow; finnow = finother; finother = finswap;
    }
    if (cdztail != 0.0) {
        vlength = scale_expansion_zeroelim(4, ab, cdztail, v);
        finlength = fast_expansion_sum_zeroelim(finlength, finnow, vlength, v,
            finother);
        finswap = finnow; finnow = finother; finother = finswap;
    }

    if (adxtail != 0.0) {
        if (bdytail != 0.0) {
            Two_Product(adxtail, bdytail, adxt_bdyt1, adxt_bdyt0);
            Two_One_Product(adxt_bdyt1, adxt_bdyt0, cdz, u3, u[2], u[1], u[0]);
            u[3] = u3;
            finlength = fast_expansion_sum_zeroelim(finlength, finnow, 4, u,
                finother);
            finswap = finnow; finnow = finother; finother = finswap;
            if (cdztail != 0.0) {
                Two_One_Product(adxt_bdyt1, adxt_bdyt0, cdztail, u3, u[2], u[1], u[0]);
                u[3] = u3;
                finlength = fast_expansion_sum_zeroelim(finlength, finnow, 4, u,
                    finother);
                finswap = finnow; finnow = finother; finother = finswap;
            }
        }
        if (cdytail != 0.0) {
            negate = -adxtail;
            Two_Product(negate, cdytail, adxt_cdyt1, adxt_cdyt0);
            Two_One_Product(adxt_cdyt1, adxt_cdyt0, bdz, u3, u[2], u[1], u[0]);
            u[3] = u3;
            finlength = fast_expansion_sum_zeroelim(finlength, finnow, 4, u,
                finother);
            finswap = finnow; finnow = finother; finother = finswap;
            if (bdztail != 0.0) {
                Two_One_Product(adxt_cdyt1, adxt_cdyt0, bdztail, u3, u[2], u[1], u[0]);
                u[3] = u3;
                finlength = fast_expansion_sum_zeroelim(finlength, finnow, 4, u,
                    finother);
                finswap = finnow; finnow = finother; finother = finswap;
            }
        }
    }
    if (bdxtail != 0.0) {
        if (cdytail != 0.0) {
            Two_Product(bdxtail, cdytail, bdxt_cdyt1, bdxt_cdyt0);
            Two_One_Product(bdxt_cdyt1, bdxt_cdyt0, adz, u3, u[2], u[1], u[0]);
            u[3] = u3;
            finlength = fast_expansion_sum_zeroelim(finlength, finnow, 4, u,
                finother);
            finswap = finnow; finnow = finother; finother = finswap;
            if (adztail != 0.0) {
                Two_One_Product(bdxt_cdyt1, bdxt_cdyt0, adztail, u3, u[2], u[1], u[0]);
                u[3] = u3;
                finlength = fast_expansion_sum_zeroelim(finlength, finnow, 4, u,
                    finother);
                finswap = finnow; finnow = finother; finother = finswap;
            }
        }
        if (adytail != 0.0) {
            negate = -bdxtail;
            Two_Product(negate, adytail, bdxt_adyt1, bdxt_adyt0);
            Two_One_Product(bdxt_adyt1, bdxt_adyt0, cdz, u3, u[2], u[1], u[0]);
            u[3] = u3;
            finlength = fast_expansion_sum_zeroelim(finlength, finnow, 4, u,
                finother);
            finswap = finnow; finnow = finother; finother = finswap;
            if (cdztail != 0.0) {
                Two_One_Product(bdxt_adyt1, bdxt_adyt0, cdztail, u3, u[2], u[1], u[0]);
                u[3] = u3;
                finlength = fast_expansion_sum_zeroelim(finlength, finnow, 4, u,
                    finother);
                finswap = finnow; finnow = finother; finother = finswap;
            }
        }
    }
    if (cdxtail != 0.0) {
        if (adytail != 0.0) {
            Two_Product(cdxtail, adytail, cdxt_adyt1, cdxt_adyt0);
            Two_One_Product(cdxt_adyt1, cdxt_adyt0, bdz, u3, u[2], u[1], u[0]);
            u[3] = u3;
            finlength = fast_expansion_sum_zeroelim(finlength, finnow, 4, u,
                finother);
            finswap = finnow; finnow = finother; finother = finswap;
            if (bdztail != 0.0) {
                Two_One_Product(cdxt_adyt1, cdxt_adyt0, bdztail, u3, u[2], u[1], u[0]);
                u[3] = u3;
                finlength = fast_expansion_sum_zeroelim(finlength, finnow, 4, u,
                    finother);
                finswap = finnow; finnow = finother; finother = finswap;
            }
        }
        if (bdytail != 0.0) {
            negate = -cdxtail;
            Two_Product(negate, bdytail, cdxt_bdyt1, cdxt_bdyt0);
            Two_One_Product(cdxt_bdyt1, cdxt_bdyt0, adz, u3, u[2], u[1], u[0]);
            u[3] = u3;
            finlength = fast_expansion_sum_zeroelim(finlength, finnow, 4, u,
                finother);
            finswap = finnow; finnow = finother; finother = finswap;
            if (adztail != 0.0) {
                Two_One_Product(cdxt_bdyt1, cdxt_bdyt0, adztail, u3, u[2], u[1], u[0]);
                u[3] = u3;
                finlength = fast_expansion_sum_zeroelim(finlength, finnow, 4, u,
                    finother);
                finswap = finnow; finnow = finother; finother = finswap;
            }
        }
    }

    if (adztail != 0.0) {
        wlength = scale_expansion_zeroelim(bctlen, bct, adztail, w);
        finlength = fast_expansion_sum_zeroelim(finlength, finnow, wlength, w,
            finother);
        finswap = finnow; finnow = finother; finother = finswap;
    }
    if (bdztail != 0.0) {
        wlength = scale_expansion_zeroelim(catlen, cat, bdztail, w);
        finlength = fast_expansion_sum_zeroelim(finlength, finnow, wlength, w,
            finother);
        finswap = finnow; finnow = finother; finother = finswap;
    }
    if (cdztail != 0.0) {
        wlength = scale_expansion_zeroelim(abtlen, abt, cdztail, w);
        finlength = fast_expansion_sum_zeroelim(finlength, finnow, wlength, w,
            finother);
        finswap = finnow; finnow = finother; finother = finswap;
    }

    return finnow[finlength - 1];
}

REAL ExactnessPredicates::orient3d(REAL* pa, REAL* pb, REAL* pc, REAL* pd)
{
    REAL adx, bdx, cdx, ady, bdy, cdy, adz, bdz, cdz;
    REAL bdxcdy, cdxbdy, cdxady, adxcdy, adxbdy, bdxady;
    REAL det;
    REAL permanent, errbound;

    adx = pa[0] - pd[0];
    bdx = pb[0] - pd[0];
    cdx = pc[0] - pd[0];
    ady = pa[1] - pd[1];
    bdy = pb[1] - pd[1];
    cdy = pc[1] - pd[1];
    adz = pa[2] - pd[2];
    bdz = pb[2] - pd[2];
    cdz = pc[2] - pd[2];

    bdxcdy = bdx * cdy;
    cdxbdy = cdx * bdy;

    cdxady = cdx * ady;
    adxcdy = adx * cdy;

    adxbdy = adx * bdy;
    bdxady = bdx * ady;

    det = adz * (bdxcdy - cdxbdy)
        + bdz * (cdxady - adxcdy)
        + cdz * (adxbdy - bdxady);

    permanent = (Absolute(bdxcdy) + Absolute(cdxbdy)) * Absolute(adz)
        + (Absolute(cdxady) + Absolute(adxcdy)) * Absolute(bdz)
        + (Absolute(adxbdy) + Absolute(bdxady)) * Absolute(cdz);
    errbound = o3derrboundA * permanent;
    if ((det > errbound) || (-det > errbound)) {
        return det;
    }

    return orient3dadapt(pa, pb, pc, pd, permanent);
}

REAL ExactnessPredicates::orient2dfast(REAL* pa, REAL* pb, REAL* pc) {
	REAL acx, bcx, acy, bcy;

	acx = pa[0] - pc[0];
	bcx = pb[0] - pc[0];
	acy = pa[1] - pc[1];
	bcy = pb[1] - pc[1];
	return acx * bcy - acy * bcx;
}

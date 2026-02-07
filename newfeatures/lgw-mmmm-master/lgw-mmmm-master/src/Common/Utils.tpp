#ifndef _UTILS_TPP
#define _UTILS_TPP



template <typename T>
int sgn(T val) {
    return (static_cast<T>(0) < val) - (val < static_cast<T>(0));
}

template <typename T>
void clamp(T& val, T valMin, T valMax) {
    if (val < valMin) {
        val = valMin;
    } else if (val > valMax) {
        val = valMax;
    }
}
template <typename T>
T clamp(const T &val, T valMin, T valMax) {
    T res = val;
    clamp(res, valMin, valMax);
    return res;
}

template <typename T>
T lerp(const T& val0, const T& val1, NumT k) {
    return (1 - k) * val0 + k * val1;
}

template <typename T>
T bilerp(const T& val00, const T& val10,
         const T& val01, const T& val11,
         NumT ku, NumT kv) {
    return lerp( lerp(val00, val10, ku),
                 lerp(val01, val11, ku), kv);
}

template <typename T>
T trilerp(const T& val000, const T& val100,
          const T& val010, const T& val110,
          const T& val001, const T& val101,
          const T& val011, const T& val111,
          NumT ku, NumT kv, NumT kw) {
    return lerp(bilerp(val000, val100, val010, val110, ku, kv),
                bilerp(val001, val101, val011, val111, ku, kv),
                kw);
}

template <typename T>
T cerp(const T& valm, const T& val0, const T& val1, const T& val2, NumT k) {
    // Cubic interpolation, f'(0) = (v1 - vm) / 2; f'(1) = (v2 - v0) / 2
    const T a = 0.5 * (val2 - 3. * val1 + 3. * val0 - valm);
    const T b = 0.5 * (-val2 + 4. * val1 - 5. * val0 + 2. * valm);
    const T c = 0.5 * (val1 - valm);
    const T d = val0;
    // Cubic interpolation
    // f'(0) = (v1 - vm) / 2; f'(1) = (v2 - v0) / 2
    //const T fp0 = 0.5 * (val1 - valm);
    //const T fp1 = 0.5 * (val2 - val0);
    //const T a = 2 * (val0 - val1) + fp0 + fp1;
    //const T b = 3 * (-val0 + val1) - 2 * fp0 - fp1;
    //const T c = fp0;
    //const T d = val0;
    return ((((a * k) + b) * k) + c) * k + d;
}


template <typename T>
T bicerp(const T& valmm, const T& val0m, const T& val1m, const T& val2m,
         const T& valm0, const T& val00, const T& val10, const T& val20,
         const T& valm1, const T& val01, const T& val11, const T& val21,
         const T& valm2, const T& val02, const T& val12, const T& val22,
         NumT ku, NumT kv) {
    return cerp( cerp(valmm, val0m, val1m, val2m, ku),
                 cerp(valm0, val00, val10, val20, ku),
                 cerp(valm1, val01, val11, val21, ku),
                 cerp(valm2, val02, val12, val22, ku),
                 kv);
}

template <typename T, int N, template<class, int> typename Array3D>
T tricerp(const Array3D<T, N>& vals,
          int i, int j, int k,
          NumT ku, NumT kv, NumT kw) {

    // No gradient provided, Catmull-Rom style
    return cerp( bicerp(vals(i-1, j-1, k-1), vals(i, j-1, k-1), vals(i+1, j-1, k-1), vals(i+2, j-1, k-1),
                        vals(i-1, j,   k-1), vals(i, j,   k-1), vals(i+1, j,   k-1), vals(i+2, j,   k-1),
                        vals(i-1, j+1, k-1), vals(i, j+1, k-1), vals(i+1, j+1, k-1), vals(i+2, j+1, k-1),
                        vals(i-1, j+2, k-1), vals(i, j+2, k-1), vals(i+1, j+2, k-1), vals(i+2, j+2, k-1),
                        ku, kv),
                 bicerp(vals(i-1, j-1, k  ), vals(i, j-1, k  ), vals(i+1, j-1, k  ), vals(i+2, j-1, k  ),
                        vals(i-1, j,   k  ), vals(i, j,   k  ), vals(i+1, j,   k  ), vals(i+2, j,   k  ),
                        vals(i-1, j+1, k  ), vals(i, j+1, k  ), vals(i+1, j+1, k  ), vals(i+2, j+1, k  ),
                        vals(i-1, j+2, k  ), vals(i, j+2, k  ), vals(i+1, j+2, k  ), vals(i+2, j+2, k  ),
                        ku, kv),
                 bicerp(vals(i-1, j-1, k+1), vals(i, j-1, k+1), vals(i+1, j-1, k+1), vals(i+2, j-1, k+1),
                        vals(i-1, j,   k+1), vals(i, j,   k+1), vals(i+1, j,   k+1), vals(i+2, j,   k+1),
                        vals(i-1, j+1, k+1), vals(i, j+1, k+1), vals(i+1, j+1, k+1), vals(i+2, j+1, k+1),
                        vals(i-1, j+2, k+1), vals(i, j+2, k+1), vals(i+1, j+2, k+1), vals(i+2, j+2, k+1),
                        ku, kv),
                 bicerp(vals(i-1, j-1, k+2), vals(i, j-1, k+2), vals(i+1, j-1, k+2), vals(i+2, j-1, k+2),
                        vals(i-1, j,   k+2), vals(i, j,   k+2), vals(i+1, j,   k+2), vals(i+2, j,   k+2),
                        vals(i-1, j+1, k+2), vals(i, j+1, k+2), vals(i+1, j+1, k+2), vals(i+2, j+1, k+2),
                        vals(i-1, j+2, k+2), vals(i, j+2, k+2), vals(i+1, j+2, k+2), vals(i+2, j+2, k+2),
                        ku, kv),
                 kw);
}


template <typename T>
T qerp(const T& valm, const T& val0, const T& val1, const T& val2, NumT k) {
    /*
    // Quintic f'(0) = (v1 - vm) / 2; f'(1) = (v2 - v0) / 2, f''(0) = 0; f''(1) = 0
    const T a = 0.5 * (-3 * val2 +  9 * val1 -  9 * val0 + 3 * valm1);
    const T b = 0.5 * ( 7 * val2 - 22 * val1 + 23 * val0 - 8 * valm1);
    const T c =        -2 * val2 +  7 * val1 -  8 * val0 + 3 * valm1;
    //const T d = 0.;
    const T e = 0.5 * (                 val1             -     valm1);
    const T f =                                     val0;
    /*/
    // Quintic f'(0) = (v1 - vm) / 2; f'(1) = (v2 - v0) / 2,
    //         f''(0) = 0; f''(1) = 0
    const T fp0 = 0.5 * (val1 - valm);
    const T fp1 = 0.5 * (val2 - val0);
    const T fs0 = val1 - 2 * val0 + valm;
    const T fs1 = val2 - 2 * val1 + val0;
    const T a =  -6 * val0 +  6 * val1 - 3 * fp0 - 3 * fp1 - 0.5 * fs0 + 0.5 * fs1;
    const T b =  15 * val0 - 15 * val1 + 8 * fp0 + 7 * fp1 + 1.5 * fs0 -   1 * fs1;
    const T c = -10 * val0 + 10 * val1 - 6 * fp0 - 4 * fp1 - 1.5 * fs0 + 0.5 * fs1;
    const T d =                                              0.5 * fs0;
    const T e =                              fp0;
    const T f =       val0;
    /* */
    return (((((a * k) + b) * k + c) * k + d) * k + e) * k + f;
}
template <typename T, template<class> typename Array3D>
T triqerp(const Array3D<T>& vals,
          int i, int j, int k,
          NumT ku, NumT kv, NumT kw) {
    return qerp(
        qerp(
            qerp(vals(i-1, j-1, k-1), vals(i  , j-1, k-1), vals(i+1, j-1, k-1), vals(i+2, j-1, k-1), ku),
            qerp(vals(i-1, j  , k-1), vals(i  , j  , k-1), vals(i+1, j  , k-1), vals(i+2, j  , k-1), ku),
            qerp(vals(i-1, j+1, k-1), vals(i  , j+1, k-1), vals(i+1, j+1, k-1), vals(i+2, j+1, k-1), ku),
            qerp(vals(i-1, j+2, k-1), vals(i  , j+2, k-1), vals(i+1, j+2, k-1), vals(i+2, j+2, k-1), ku),
            kv),
        qerp(
            qerp(vals(i-1, j-1, k  ), vals(i  , j-1, k  ), vals(i+1, j-1, k  ), vals(i+2, j-1, k  ), ku),
            qerp(vals(i-1, j  , k  ), vals(i  , j  , k  ), vals(i+1, j  , k  ), vals(i+2, j  , k  ), ku),
            qerp(vals(i-1, j+1, k  ), vals(i  , j+1, k  ), vals(i+1, j+1, k  ), vals(i+2, j+1, k  ), ku),
            qerp(vals(i-1, j+2, k  ), vals(i  , j+2, k  ), vals(i+1, j+2, k  ), vals(i+2, j+2, k  ), ku),
            kv),
        qerp(
            qerp(vals(i-1, j-1, k+1), vals(i  , j-1, k+1), vals(i+1, j-1, k+1), vals(i+2, j-1, k+1), ku),
            qerp(vals(i-1, j  , k+1), vals(i  , j  , k+1), vals(i+1, j  , k+1), vals(i+2, j  , k+1), ku),
            qerp(vals(i-1, j+1, k+1), vals(i  , j+1, k+1), vals(i+1, j+1, k+1), vals(i+2, j+1, k+1), ku),
            qerp(vals(i-1, j+2, k+1), vals(i  , j+2, k+1), vals(i+1, j+2, k+1), vals(i+2, j+2, k+1), ku),
            kv),
        qerp(
            qerp(vals(i-1, j-1, k+2), vals(i  , j-1, k+2), vals(i+1, j-1, k+2), vals(i+2, j-1, k+2), ku),
            qerp(vals(i-1, j  , k+2), vals(i  , j  , k+2), vals(i+1, j  , k+2), vals(i+2, j  , k+2), ku),
            qerp(vals(i-1, j+1, k+2), vals(i  , j+1, k+2), vals(i+1, j+1, k+2), vals(i+2, j+1, k+2), ku),
            qerp(vals(i-1, j+2, k+2), vals(i  , j+2, k+2), vals(i+1, j+2, k+2), vals(i+2, j+2, k+2), ku),
            kv),
        kw);


}

    
template <typename T, typename Vec>
T cerpGrad(const std::pair<T, Vec> &p0,
           const std::pair<T, Vec> &p1,
           const Vec &k, int dir) {
    const Vec &grad0 = p0.second;
    const Vec &grad1 = p1.second;

    auto interp = [&grad0, &grad1, &k, &dir] (const T& lVal, const T& rVal) -> T
                  {
                      const T a = grad1[dir] - rVal + lVal;
                      const T b = 2 * (rVal - lVal) - grad1[dir] - grad0[dir];
                      const T c = grad0[dir];
                      const T d = lVal;
                      return ((((a * k[dir]) + b) * k[dir]) + c) * k[dir] + d;

                  };
    // Value
    const T val = interp(p0.first, p1.first);
    
    return val;
}
template <typename T, typename Vec, template<class> typename Array3D>
T tricerpGrad(const Array3D<T>& vals,
              int i, int j, int k,
              NumT ku, NumT kv, NumT kw,
              NumT dx, const Array3D<Vec>& grads) {

    // First round - data
    const Vec3 coeff(ku, kv, kw);
    const std::pair<T, Vec> p000 = {vals      (i,     j,     k),
                                    dx * grads(i,     j,     k)};
    const std::pair<T, Vec> p100 = {vals      (i + 1, j,     k),
                                    dx * grads(i + 1, j,     k) };
    const std::pair<T, Vec> p010 = {vals      (i,     j + 1, k),
                                    dx * grads(i,     j + 1, k) };
    const std::pair<T, Vec> p110 = {vals      (i + 1, j + 1, k),
                                    dx * grads(i + 1, j + 1, k) };
    const std::pair<T, Vec> p001 = {vals      (i,     j,     k + 1),
                                    dx * grads(i,     j,     k + 1) };
    const std::pair<T, Vec> p101 = {vals      (i + 1, j,     k + 1),
                                    dx * grads(i + 1, j,     k + 1) };
    const std::pair<T, Vec> p011 = {vals      (i,     j + 1, k + 1),
                                    dx * grads(i,     j + 1, k + 1) };
    const std::pair<T, Vec> p111 = {vals      (i + 1, j + 1, k + 1),
                                    dx * grads(i + 1, j + 1, k + 1) };

    // First round - interp
    const T val00 = cerpGrad<T, Vec>(p000, p100, coeff, 0);
    const T val10 = cerpGrad<T, Vec>(p010, p110, coeff, 0);
    const T val01 = cerpGrad<T, Vec>(p001, p101, coeff, 0);
    const T val11 = cerpGrad<T, Vec>(p011, p111, coeff, 0);
    //*
    const Vec grad00 = lerp(p000.second, p100.second, ku);
    const Vec grad10 = lerp(p010.second, p110.second, ku);
    const Vec grad01 = lerp(p001.second, p101.second, ku);
    const Vec grad11 = lerp(p011.second, p111.second, ku);
    /*/
    const Vec grad00 = dx * tricerp<Vec>(grads, i, j, k, ku, 0, 0);
    const Vec grad10 = dx * tricerp<Vec>(grads, i, j, k, ku, 1, 0);
    const Vec grad01 = dx * tricerp<Vec>(grads, i, j, k, ku, 0, 1);
    const Vec grad11 = dx * tricerp<Vec>(grads, i, j, k, ku, 1, 1);
    /* */
    
    // Secound round - data
    const std::pair<T, Vec> p00 = { val00, grad00 };
    const std::pair<T, Vec> p10 = { val10, grad10 };
    const std::pair<T, Vec> p01 = { val01, grad01 };
    const std::pair<T, Vec> p11 = { val11, grad11 };

    // Secound round - interp
    const T val0 = cerpGrad<T, Vec>(p00, p10, coeff, 1);
    const T val1 = cerpGrad<T, Vec>(p01, p11, coeff, 1);
    //*
    const Vec grad0 = lerp(grad00, grad10, kv);
    const Vec grad1 = lerp(grad01, grad11, kv);
    /*/
    const Vec grad0 = dx * tricerp<Vec>(grads, i, j, k, ku, kv, 0);
    const Vec grad1 = dx * tricerp<Vec>(grads, i, j, k, ku, kv, 1);
    /* */
    
    // Third round - data
    const std::pair<T, Vec> p0 = { val0, grad0 };
    const std::pair<T, Vec> p1 = { val1, grad1 };

    const T res = cerpGrad<T, Vec>(p0, p1, coeff, 2);
    
    return res;
    
}


template <typename T>
void atomicMin(T& currMin, T& testVal) {
    T prevMin = currMin;
    while ( (prevMin > testVal)
            && !(__atomic_compare_exchange(&currMin, &prevMin, &testVal,
                                           false, __ATOMIC_RELAXED,
                                           __ATOMIC_RELAXED)))
    {}
}

template <typename T>
void atomicMax(T& currMax, T& testVal) {
    T prevMax = currMax;
    while ( (prevMax < testVal)
            && !(__atomic_compare_exchange(&currMax, &prevMax, &testVal,
                                           false, __ATOMIC_RELAXED,
                                           __ATOMIC_RELAXED)))
    {}
}

template <typename V2, typename V3>
void triangleBarycenter(const V2& p,
                        const V2& a, 
                        const V2& b, 
                        const V2& c,
                        V3& bar,
                        NumT tol) {
    const V2 v0 = b - a, v1 = c - a, v2 = p - a;
    const auto den = v0[0] * v1[1] - v1[0] * v0[1];
    bar[1] = (v2[0] * v1[1] - v1[0] * v2[1]) / den;
    bar[2] = (v0[0] * v2[1] - v2[0] * v0[1]) / den;
    if ( (bar[1] < -tol) || (bar[1] > 1+tol)
         || (bar[2] < -tol) || (bar[2] > 1+tol)) {
        bar[0] = std::nan("");
        bar[1] = std::nan("");
        bar[2] = std::nan("");
        return;
    }
    if (tol > 0) {
        clamp<NumT>(bar[1], 0., 1.);
        clamp<NumT>(bar[2], 0., 1.);
    }
    bar[0] = 1.0 - bar[1] - bar[2];
}

template <typename V2>
NumT triangleInterpolation(const V2& p,
                           const V2& a, NumT aVal,
                           const V2& b, NumT bVal,
                           const V2& c, NumT cVal,
                           NumT tol) {
    NumT bar[3];
    triangleBarycenter(p, a, b, c, bar, tol);
    return bar[0] * aVal + bar[1] * bVal + bar[2] * cVal;
}


#endif // _UTILS_TPP

{ pkgs ? import <nixpkgs> { } }:
let
  deps = with pkgs; [
    glfw
    libzip
    # (
      # (suitesparse.overrideAttrs
      #   (old: rec {
      #     version = "7.7.0";
      #     src = fetchFromGitHub {
      #       owner = "DrTimothyAldenDavis";
      #       repo = "SuiteSparse";
      #       rev = "v${version}";
      #       #sha256 = "sha256-Anen1YtXsSPhk8DpA4JtADIz9m8oXFl9umlkb4iImf8=";
      #       sha256 = "sha256-wE1DKC0Hn3Q9X1FzKH7Kev26ICNWH0LEKQIQP98AGuo=";
      #     };
      #     nativeBuildInputs = [
      #       cmake
      #     ];
      #     buildInputs = assert (blas.isILP64 == lapack.isILP64); [
      #       blas
      #       lapack
      #       metis
      #       gfortran.cc.lib
      #       gmp
      #       mpfr
      #       cudatoolkit
      #     ];
      #     propagatedBuildInputs = [
      #       gmp
      #       mpfr
      #     ];
      #     preConfigure = ''
      #       # Mongoose and GraphBLAS are packaged separately
      #       sed -i "Makefile" -e '/GraphBLAS\|Mongoose/d'
      #     '';
      #     dontUseCmakeConfigure = true;
      #     cmakeFlags = [
      #       "-DBLA_VENDOR=Generic"
      #       "-DCMAKE_INSTALL_BINDIR=${placeholder "out"}/bin"
      #       "-DCMAKE_INSTALL_INCLUDEDIR=${placeholder "dev"}/include"
      #       "-DCMAKE_INSTALL_LIBDIR=${placeholder "out"}/lib"
      #     ] ++ lib.optionals blas.isILP64 [
      #       "-DALLOW_64BIT_BLAS=ON"
      #     ];
      #     CMAKE_OPTIONS = lib.concatStringsSep " " cmakeFlags;
      #     makeFlags = [
      #       "JOBS=$(NIX_BUILD_CORES)"
      #     ] ++ [
      #       "CUDA_PATH=${cudatoolkit}"
      #       "CUDART_LIB=${cudatoolkit.lib}/lib/libcudart.so"
      #       "CUBLAS_LIB=${cudatoolkit}/lib/libcublas.so"
      #     ];
      #     buildFlags = [
      #       # Build individual shared libraries, not demos
      #       "library"
      #       "docs"
      #     ];
      #
      #     postInstall = ''
      #       mkdir -p $doc
      #       for docdir in */Doc; do
      #         local name="$(dirname "$docdir")"
      #         local dest_dir="$doc/share/doc/$name"
      #
      #         if [[ $name = Mongoose || $name = GraphBLAS ]]; then
      #           # Mongoose and GraphBLAS are packaged separately
      #           continue
      #         fi
      #
      #         echo "installing docs from $docdir to $dest_dir"
      #         install -Dt "$dest_dir" "$docdir/"*.{txt,pdf}
      #       done
      #     '';
      #
      #     meta = with lib; {
      #       homepage = "http://faculty.cse.tamu.edu/davis/suitesparse.html";
      #       description = "A suite of sparse matrix algorithms";
      #       license = with licenses; [ bsd2 gpl2Plus lgpl21Plus ];
      #       maintainers = with maintainers; [ ttuegel ];
      #       platforms = with platforms; unix;
      #     };
      #   })).override {
      #   enableCuda = true;
      #   blas = blas;
      # }
    # )
    suitesparse
    xorg.libX11
  ];
  clangDeps = with pkgs; [
    clang-tools
    llvmPackages.openmp
  ];
  clangBuildDeps = with pkgs; [
    llvmPackages.openmp
  ];
  cmakeGuiDeps = with pkgs; [
    stdenv
    cmakeWithGui
  ];
  headerOnlyDeps = with pkgs; [
    eigen
    boost
  ];
  bDeps = with pkgs; [
    cmake
    patchelf
  ];
in
{
  shellDeps = cmakeGuiDeps ++ clangDeps ++ deps ++ headerOnlyDeps;
  buildDeps = deps;
  buildNativeDeps = bDeps ++ clangBuildDeps ++ headerOnlyDeps;
}

# nix/modules/flake/prelude.nix
#
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#                           // the straylight prelude //
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#
#     "The Sprawl was a long strange way home over the Pacific now, and he
#      was no console man, no cyberspace cowboy."
#
#                                                         — Neuromancer
#
# A flake-parts module that exposes the Weyl Prelude from the overlay.
#
# The prelude overlay (nix/overlays/prelude.nix) provides:
#   - straylight.prelude: functional library
#   - straylight.stdenv: build environment matrix
#   - straylight.cross: cross-compilation targets
#   - straylight.platform: platform detection
#   - straylight.gpu: GPU architecture metadata
#   - straylight.turing-registry: non-negotiable build flags
#
# Access via _module.args:
#   perSystem = { prelude, pkgs, ... }: { ... }
#
# Or via config:
#   perSystem = { config, ... }: let p = config.straylight.prelude; in { ... }
#
# See RFC-003: docs/languages/nix/rfc/003-prelude.md
#
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
{ inputs }:
{
  lib,
  flake-parts-lib,
  ...
}:
let
  inherit (flake-parts-lib) mkPerSystemOption;
in
{
  _class = "flake";

  # ────────────────────────────────────────────────────────────────────────────
  # // options //
  # ────────────────────────────────────────────────────────────────────────────

  options = {
    perSystem = mkPerSystemOption (
      { lib, ... }:
      {
        options.straylight = {
          prelude = lib.mkOption {
            type = lib.types.raw;
            description = "The instantiated Weyl Prelude for this system";
          };
        };
      }
    );
  };

  # ────────────────────────────────────────────────────────────────────────────
  # // config //
  # ────────────────────────────────────────────────────────────────────────────

  config = {
    perSystem =
      { pkgs, system, ... }:
      let
        # Get the prelude from the overlay (must have straylight-naught overlay applied)
        straylight =
          pkgs.straylight or (throw ''
            straylight.prelude requires the straylight-naught overlay to be applied.
            Make sure you import straylight-naught.flakeModules.std or apply the overlay manually.
          '');

        # ──────────────────────────────────────────────────────────────────────
        # // wasm infrastructure //
        # ──────────────────────────────────────────────────────────────────────

        wasm-infra = import ../../prelude/wasm-plugin.nix {
          inherit lib;
          inherit (pkgs) stdenv runCommand;
          ghc-wasm-meta = inputs.ghc-wasm-meta or null;
        };

        #                                                               // ghc // wasm
        ghc-wasm =
          if inputs ? ghc-wasm-meta then inputs.ghc-wasm-meta.packages.${system}.all_9_12 else null;

        # ──────────────────────────────────────────────────────────────────────
        # // language toolchains //
        # ──────────────────────────────────────────────────────────────────────

        # Haskell package set - using GHC 9.12 from nixpkgs (stable, well-tested)
        #                                                                  // ghc // 9
        # This replaces the Mercury GHC approach which had package.cache.lock bugs.
        hsPkgs = pkgs.haskell.packages.ghc912;

        python =
          let
            version = straylight.versions.python;
            pkg = pkgs.python312;
            pkgs' = pkgs.python312Packages;
          in
          {
            inherit version pkg pkgs';
            interpreter = pkg;
            build = attrs: pkgs'.buildPythonPackage (straylight.translate-attrs attrs);
            app = attrs: pkgs'.buildPythonApplication (straylight.translate-attrs attrs);
            lib =
              attrs: pkgs'.buildPythonPackage (straylight.translate-attrs attrs // { format = "setuptools"; });
          };

        ghc =
          let
            version = straylight.versions.ghc;
            pkg = hsPkgs.ghc;
            pkgs' = hsPkgs;
            build = attrs: pkgs'.mkDerivation (straylight.translate-attrs attrs);
          in
          {
            inherit
              version
              pkg
              pkgs'
              build
              ;
            compiler = pkg;
            app = build;
            lib = build;

            # Turtle shell scripts - compiled Haskell with bash-like ergonomics
            # Benefits over bash:
            #   - Type-safe path/text manipulation
            #   - Proper error handling with ExceptT/Either
            #   - Identical startup time to bash (~2ms compiled vs ~160ms interpreted)
            #   - No shellcheck needed - types catch more
            #
            # Usage:
            #   ghc.turtle-script {
            #     name = "my-script";
            #     src = ./my-script.hs;
            #     deps = [ pkgs.crane pkgs.bwrap ];  # Runtime deps
            #     hs-deps = p: [ p.aeson p.optparse-applicative ];  # Haskell deps
            #   }
            turtle-script =
              {
                name,
                src,
                deps ? [ ],
                hs-deps ? _: [ ],
              }:
              let
                # Base turtle dependencies (always included)
                baseDeps =
                  p: with p; [
                    turtle # The Haskell package, not ghc.turtle-script
                    text
                    bytestring
                    foldl
                    unix
                  ];

                # Combined Haskell dependencies
                allHsDeps = p: baseDeps p ++ hs-deps p;

                #                                                                       // ghc
                ghcWithDeps = hsPkgs.ghcWithPackages allHsDeps;
              in
              pkgs.stdenv.mkDerivation {
                inherit name src;
                dontUnpack = true;

                nativeBuildInputs = [ ghcWithDeps ] ++ pkgs.lib.optional (deps != [ ]) pkgs.makeWrapper;
                buildInputs = deps;

                buildPhase = ''
                  runHook preBuild
                  ghc -O2 -Wall -o ${name} $src
                  runHook postBuild
                '';

                installPhase = ''
                  runHook preInstall
                  mkdir -p $out/bin
                  cp ${name} $out/bin/
                  runHook postInstall
                '';

                # Wrap with runtime deps
                postFixup = pkgs.lib.optionalString (deps != [ ]) ''
                  wrapProgram $out/bin/${name} \
                    --prefix PATH : ${pkgs.lib.makeBinPath deps}
                '';

                meta = {
                  description = "Compiled Turtle shell script with type-safe path handling";
                };
              };
          };

        lean =
          let
            version = straylight.versions.lean;
            pkg = pkgs.lean4;
            build =
              attrs:
              straylight.stdenv.default (
                attrs
                // {
                  native-deps = (attrs.native-deps or [ ]) ++ [ pkg ];
                }
              );
          in
          {
            inherit version pkg build;
            lib = build;
          };

        rust =
          let
            version = straylight.versions.rust;
            pkg = pkgs.rustc;
            toolchain = pkgs.rustPlatform;
            crates = pkgs.rustPackages;
            build = attrs: pkgs.rustPlatform.buildRustPackage (straylight.translate-attrs attrs);
          in
          {
            inherit
              version
              pkg
              toolchain
              crates
              build
              ;
            bin = build;
            lib = build;
            staticlib = build;
          };

        cpp = {
          bin = straylight.stdenv.default;
          lib = straylight.stdenv.default;
          staticlib = straylight.stdenv.static;
          header-only = straylight.stdenv.default;
          nvidia = {
            build =
              attrs:
              (straylight.stdenv.nvidia or straylight.stdenv.default) (
                builtins.removeAttrs attrs [ "target-gpu" ]
              );
            kernel =
              attrs:
              (straylight.stdenv.nvidia or straylight.stdenv.default) (
                builtins.removeAttrs attrs [ "target-gpu" ]
              );
            host =
              attrs:
              (straylight.stdenv.nvidia or straylight.stdenv.default) (
                builtins.removeAttrs attrs [ "target-gpu" ]
              );
          };
        };

        # ──────────────────────────────────────────────────────────────────────
        # // fetch //
        # ──────────────────────────────────────────────────────────────────────

        fetch = {
          github = pkgs.fetchFromGitHub;
          gitlab = pkgs.fetchFromGitLab;
          git = pkgs.fetchgit;
          url = pkgs.fetchurl;
          tarball = builtins.fetchTarball;
          fod =
            {
              name,
              hash,
              script,
            }:
            pkgs.runCommand name {
              outputHashMode = "recursive";
              outputHashAlgo = "sha256";
              outputHash = hash;
              nativeBuildInputs = [
                pkgs.curl
                pkgs.jq
              ];
              SSL_CERT_FILE = "${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt";
            } script;
        };

        # ──────────────────────────────────────────────────────────────────────
        # // render //
        # ──────────────────────────────────────────────────────────────────────

        render = {
          #                                                                      // json
          json =
            name: value:
            pkgs.writeTextFile {
              inherit name;
              text = builtins.toJSON value;
            };
          #                                                                      // toml
          toml = name: value: (pkgs.formats.toml { }).generate name value;
          yaml = name: value: (pkgs.formats.yaml { }).generate name value;
          ini = name: value: (pkgs.formats.ini { }).generate name value;
          #                                                                       // env
          env =
            name: attrs:
            pkgs.writeTextFile {
              inherit name;
              text = lib.concatStringsSep "\n" (lib.mapAttrsToList (k: v: "${k}=${v}") attrs);
            };
        };

        # ──────────────────────────────────────────────────────────────────────
        # // write //
        # ──────────────────────────────────────────────────────────────────────

        write = {
          # Plain text file
          text = name: content: pkgs.writeText name content;

          # Shell application with dependencies and shellcheck (THE ONLY WAY)
          # Use this for all shell scripts. No exceptions.
          shell-application =
            {
              name,
              deps ? [ ],
              text,
            }:
            pkgs.writeShellApplication {
              inherit name text;
              runtimeInputs = deps;
            };
        };

        # Top-level alias - the blessed way to write shell scripts
        write-shell-application = write.shell-application;

        # ──────────────────────────────────────────────────────────────────────
        # // mk-package //
        # ──────────────────────────────────────────────────────────────────────
        #
        # No inline code allowed. All build phases must be external files.
        # This ensures:
        # - Scripts are shellcheck'd and resholve'd
        # - Build logic is testable outside Nix
        # - Diffs are meaningful (not buried in Nix strings)

        mk-package =
          {
            pname,
            version,
            src,
            # Scripts directory containing phase scripts
            # Expected files: configure.sh, build.sh, install.sh, check.sh
            scripts ? null,
            # Individual phase scripts (override scripts dir)
            configure-script ? null,
            build-script ? null,
            install-script ? null,
            check-script ? null,
            # Dependencies
            deps ? [ ],
            native-deps ? [ ],
            # Disable phases
            dont-configure ? false,
            dont-build ? false,
            dont-install ? false,
            dont-check ? true,
            # Extra attrs passed through
            ...
          }@args:
          let
            # Resolve script paths
            resolve-script =
              name: explicit: dir:
              if explicit != null then
                explicit
              else if dir != null && builtins.pathExists (dir + "/${name}.sh") then
                dir + "/${name}.sh"
              else
                null;

            configure-src = resolve-script "configure" configure-script scripts;
            build-src = resolve-script "build" build-script scripts;
            install-src = resolve-script "install" install-script scripts;
            check-src = resolve-script "check" check-script scripts;

            # Build phase script wrappers
            mk-phase = script-path: if script-path == null then null else builtins.readFile script-path;

            # Filter out our custom attrs
            extra-attrs = builtins.removeAttrs args [
              "pname"
              "version"
              "src"
              "scripts"
              "configure-script"
              "build-script"
              "install-script"
              "check-script"
              "deps"
              "native-deps"
              "dont-configure"
              "dont-build"
              "dont-install"
              "dont-check"
            ];
          in
          straylight.stdenv.default (
            {
              inherit pname version src;
              buildInputs = deps;
              nativeBuildInputs = native-deps;

              dontConfigure = dont-configure || configure-src == null;
              dontBuild = dont-build || build-src == null;
              dontInstall = dont-install || install-src == null;
              doCheck = !dont-check && check-src != null;
            }
            // lib.optionalAttrs (configure-src != null && !dont-configure) {
              configurePhase = mk-phase configure-src;
            }
            // lib.optionalAttrs (build-src != null && !dont-build) {
              buildPhase = mk-phase build-src;
            }
            // lib.optionalAttrs (install-src != null && !dont-install) {
              installPhase = mk-phase install-src;
            }
            // lib.optionalAttrs (check-src != null && !dont-check) {
              checkPhase = mk-phase check-src;
            }
            // extra-attrs
          );

        # ──────────────────────────────────────────────────────────────────────
        # // script //
        # ──────────────────────────────────────────────────────────────────────

        script = {
          bash =
            {
              name,
              deps ? [ ],
              src,
            }:
            pkgs.writeShellApplication {
              inherit name;
              runtimeInputs = deps;
              text = builtins.readFile src;
            };
          python =
            {
              name,
              deps ? [ ],
              src,
            }:
            pkgs.writers.writePython3Bin name { libraries = deps; } (builtins.readFile src);
          c =
            { name, src }:
            pkgs.runCommandCC name { } ''
              mkdir -p $out/bin
              $CC -O2 -o $out/bin/${name} ${src}
            '';
        };

        # ──────────────────────────────────────────────────────────────────────
        # // opt //
        # ──────────────────────────────────────────────────────────────────────

        opt = {
          enable = desc: lib.mkEnableOption desc;
          str =
            {
              default ? null,
              description ? "",
            }:
            lib.mkOption {
              type = lib.types.str;
              inherit default description;
            };
          int =
            {
              default ? null,
              description ? "",
            }:
            lib.mkOption {
              type = lib.types.int;
              inherit default description;
            };
          bool =
            {
              default ? false,
              description ? "",
            }:
            lib.mkOption {
              type = lib.types.bool;
              inherit default description;
            };
          path =
            {
              default ? null,
              description ? "",
            }:
            lib.mkOption {
              type = lib.types.path;
              inherit default description;
            };
          port =
            {
              default ? null,
              description ? "",
            }:
            lib.mkOption {
              type = lib.types.port;
              inherit default description;
            };
          list-of =
            elemType:
            {
              default ? [ ],
              description ? "",
            }:
            lib.mkOption {
              type = lib.types.listOf elemType;
              inherit default description;
            };
          attrs-of =
            elemType:
            {
              default ? { },
              description ? "",
            }:
            lib.mkOption {
              type = lib.types.attrsOf elemType;
              inherit default description;
            };
          one-of =
            values:
            {
              default ? null,
              description ? "",
            }:
            lib.mkOption {
              type = lib.types.enum values;
              inherit default description;
            };
          package =
            {
              default ? null,
              description ? "",
            }:
            lib.mkOption {
              type = lib.types.package;
              inherit default description;
            };
          submodule =
            options:
            {
              default ? { },
              description ? "",
            }:
            lib.mkOption {
              type = lib.types.submodule { inherit options; };
              inherit default description;
            };
        };

        # ──────────────────────────────────────────────────────────────────────
        # // test //
        # ──────────────────────────────────────────────────────────────────────

        test = {
          # Force evaluation of a list of assertions
          # Returns true if all pass, throws on first failure
          # Usage: test.check [ (test.eq 1 1 "one equals one") (test.eq 2 2 "two equals two") ]
          check =
            assertions:
            builtins.deepSeq (map (
              a:
              assert a.pass;
              a
            ) assertions) true;

          # Create an assertion that checks equality
          eq = actual: expected: msg: {
            pass = actual == expected;
            message = msg;
            inherit actual expected;
          };

          # Create an assertion that checks inequality
          neq = actual: unexpected: msg: {
            pass = actual != unexpected;
            message = msg;
            inherit actual;
            expected = "not ${builtins.toString unexpected}";
          };

          # Create an assertion that checks a predicate
          ok = pred: msg: {
            pass = pred;
            message = msg;
            actual = pred;
            expected = true;
          };

          # Create an assertion that a value is not null
          not-null = value: msg: {
            pass = value != null;
            message = msg;
            actual = value;
            expected = "non-null";
          };

          # Create an assertion that a list contains an element
          contains = elem: list: msg: {
            pass = builtins.elem elem list;
            message = msg;
            actual = list;
            expected = "contains ${builtins.toString elem}";
          };

          # Run a test suite (list of named test groups)
          # Returns attrset of results for integration with nix flake check
          suite =
            name: tests:
            let
              results = map (t: {
                inherit (t) name;
                pass = test.check t.assertions;
              }) tests;
              all-pass = builtins.all (r: r.pass) results;
            in
            {
              inherit name results;
              pass = all-pass;
            };
        };

        # ──────────────────────────────────────────────────────────────────────
        # // typed //
        # ──────────────────────────────────────────────────────────────────────
        #
        # Type-check configuration at eval time, fail fast with clear errors.
        # Based on lib.evalModules like NixOS/home-manager configs.

        typed = {
          # Define a typed configuration schema
          # Returns a function that validates config against the schema
          #
          # Usage:
          #   schema = typed.define {
          #     options.name = lib.mkOption { type = lib.types.str; };
          #     options.count = lib.mkOption { type = lib.types.int; default = 0; };
          #   };
          #   config = schema { name = "foo"; count = 42; };
          #
          define =
            module: config:
            let
              evaluated = lib.evalModules {
                modules = [
                  module
                  { inherit config; }
                ];
              };
            in
            evaluated.config;

          # Common type aliases for convenience
          types = {
            inherit (lib.types)
              str
              int
              bool
              float
              path
              package
              ;
            list = lib.types.listOf;
            attrs = lib.types.attrsOf;
            inherit (lib.types) enum;
            null-or = lib.types.nullOr;
            inherit (lib.types) either;
            one-of = lib.types.oneOf;

            #                                                                       // gpu
            cuda-capability = lib.types.enum [
              "7.0"
              "7.5"
              "8.0"
              "8.6"
              "8.7"
              "8.9"
              "9.0"
              "10.0"
              "12.0"
              "12.1"
            ];

            #                                                                       // gpu
            cuda-arch = lib.types.enum [
              "volta"
              "turing"
              "ampere"
              "orin"
              "ada"
              "hopper"
              "thor"
              "blackwell"
            ];
          };

          # Helper to create an option with common patterns
          option = {
            required =
              type: description:
              lib.mkOption {
                inherit type description;
              };

            optional =
              type: default: description:
              lib.mkOption {
                inherit type default description;
              };

            enable =
              description:
              lib.mkOption {
                type = lib.types.bool;
                default = false;
                inherit description;
              };
          };
        };

        # ──────────────────────────────────────────────────────────────────────
        # // derivation helpers //
        # ──────────────────────────────────────────────────────────────────────
        #
        # Re-exported from nixpkgs with lisp-case names.
        # These are critical for building proper derivation wrappers.

        drv = {
          # Extend a mkDerivation-like function (preserves finalAttrs, overrideAttrs)
          # See: https://noogle.dev/f/lib/extendMkDerivation
          extend-mk-derivation = lib.extendMkDerivation;

          # Extend a derivation with additional attributes
          extend-derivation = lib.extendDerivation;

          # Make overridable functions
          make-overridable = lib.makeOverridable;

          # Link farm - create derivation with explicit symlinks (declarative)
          link-farm = pkgs.linkFarm;

          # Symlink join - merge packages into one tree
          symlink-join = pkgs.symlinkJoin;

          # Build environment from packages
          build-env = pkgs.buildEnv;

          # Run a command and capture output
          run-command = pkgs.runCommand;
          run-command-local = pkgs.runCommandLocal;

          # Substitute in place
          inherit (pkgs) substitute;
          substitute-all = pkgs.substituteAll;
        };

        # ──────────────────────────────────────────────────────────────────────
        # // error context //
        # ──────────────────────────────────────────────────────────────────────
        #
        # Better stack traces via builtins.addErrorContext.
        # Wrap library functions with context for debugging.

        error = {
          # Add context to error messages for better stack traces
          # Usage: error.context "parsing config" (parseConfig cfg)
          context = builtins.addErrorContext;

          # Throw with a message
          inherit (builtins) throw;

          # Abort evaluation (harder failure)
          inherit (builtins) abort;

          # Assert with message - evaluates to x if cond is true, throws otherwise
          # Usage: error.assert-msg (x > 0) "x must be positive" x
          assert-msg =
            cond: msg: x:
            if cond then x else throw msg;

          # Trace for debugging (prints to stderr, returns value)
          inherit (builtins) trace;

          # Trace with label
          trace-val = label: x: builtins.trace "${label}: ${builtins.toJSON x}" x;
        };

        # ──────────────────────────────────────────────────────────────────────
        # // module system //
        # ──────────────────────────────────────────────────────────────────────
        #
        # Type-checked configuration via lib.evalModules.
        # Use for complex configs that benefit from NixOS-style type checking.

        modules = {
          # Evaluate modules (NixOS-style configuration)
          eval = lib.evalModules;

          # Create a submodule type
          inherit (lib.types) submodule;

          # Common option helpers
          mk-option = lib.mkOption;
          mk-enable = lib.mkEnableOption;
          mk-if = lib.mkIf;
          mk-default = lib.mkDefault;
          mk-force = lib.mkForce;
          mk-override = lib.mkOverride;
          mk-merge = lib.mkMerge;

          # Types for options
          inherit (lib) types;
        };

        # ──────────────────────────────────────────────────────────────────────
        # // call-package //
        # ──────────────────────────────────────────────────────────────────────
        #
        # Unified package builder. File extension determines backend:
        #   .hs   → Compile to WASM, evaluate via builtins.wasm
        #   .purs → PureScript WASM (infrastructure ready, backend pending)
        #   .nix  → Standard Nix import
        #   .wasm → Pre-compiled WASM, evaluate directly
        #
        # Usage:
        #   nvidia-nccl = call-package ./nvidia-nccl.hs {};
        #   zlib-ng = call-package ./zlib-ng.hs {};
        #

        call-package =
          path: args:
          let
            pathStr = toString path;
            ext = lib.last (lib.splitString "." pathStr);
            straylightModules = ../../../src/tools/scripts;

            # Generated Main.hs that wraps the user's Pkg module
            # User files just need: module Pkg where ... pkg = mkDerivation [...]
            wrapperMain = pkgs.writeText "Main.hs" ''
              {-# LANGUAGE ForeignFunctionInterface #-}
              module Main where

              import Straylight.Nix.Value (Value(..))
              import Straylight.Nix.Derivation (drvToNixAttrs)
              import Straylight.Nix (nixWasmInit)
              import qualified Pkg (pkg)

              main :: IO ()
              main = pure ()

              foreign export ccall "nix_wasm_init_v1" initPlugin :: IO ()
              initPlugin :: IO ()
              initPlugin = nixWasmInit

              foreign export ccall "pkg" pkgExport :: Value -> IO Value
              pkgExport :: Value -> IO Value
              pkgExport _args = drvToNixAttrs Pkg.pkg
            '';

            # Build single-file Haskell to WASM
            buildHsWasm =
              hsPath:
              let
                name = lib.removeSuffix ".hs" (baseNameOf (toString hsPath));
              in
              pkgs.runCommand "${name}.wasm"
                {
                  src = hsPath;
                  nativeBuildInputs = [ ghc-wasm ];
                }
                ''
                  mkdir -p build
                  cd build

                  # Copy Straylight.Nix infrastructure (make writable for .hi files)
                  cp -r ${straylightModules}/Straylight Straylight
                  chmod -R u+w Straylight

                  # Copy user's package as Pkg.hs, wrapper as Main.hs
                  cp $src Pkg.hs
                  cp ${wrapperMain} Main.hs

                  ${ghc-wasm}/bin/wasm32-wasi-ghc \
                    -optl-mexec-model=reactor \
                    '-optl-Wl,--allow-undefined' \
                    '-optl-Wl,--export=hs_init' \
                    '-optl-Wl,--export=nix_wasm_init_v1' \
                    '-optl-Wl,--export=pkg' \
                    -O2 \
                    Main.hs \
                    -o plugin.wasm

                  ${ghc-wasm}/bin/wasm-opt -O3 plugin.wasm -o $out
                '';

            # Build single-file PureScript to WASM
            # Uses pure-sarcasm (Wasm-GC backend) if available, otherwise provides helpful error.
            #                                                                      // note
            buildPursWasm =
              pursPath:
              let
                name = lib.removeSuffix ".purs" (baseNameOf (toString pursPath));
                # Check if pure-sarcasm is available (experimental Wasm-GC backend)
                # This is a community project: https://github.com/ajnsit/pure-sarcasm
                pureSarcasm = pkgs.pure-sarcasm or null;
              in
              if pureSarcasm == null then
                throw ''
                  ════════════════════════════════════════════════════════════════════════════════
                  PureScript WASM Backend Not Available
                  ════════════════════════════════════════════════════════════════════════════════

                  PureScript WASM compilation requires pure-sarcasm (Wasm-GC backend), which is
                  not currently available in your nixpkgs.

                  Current Status:
                    ✅ Infrastructure: Ready (buildPursWasm function exists)
                    ✅ Integration: Ready (call-package supports .purs files)
                    ❌ pure-sarcasm: Not available in nixpkgs

                  Available Options:
                    1. Use Haskell (.hs) files instead (same type system, same API)
                    2. Add pure-sarcasm to nixpkgs overlay (experimental Wasm-GC backend)
                    3. Wait for official PureScript WASM support

                  PureScript WASM Backends:
                    - pure-sarcasm: Experimental Wasm-GC backend (https://github.com/ajnsit/pure-sarcasm)
                    - Official: Not yet available (PureScript currently targets JavaScript)

                  Example (using Haskell instead):
                    # Instead of: call-package ./my-package.purs {}
                    # Use:        call-package ./my-package.hs {}

                  The Haskell and PureScript APIs are identical - just change the file extension.

                  ════════════════════════════════════════════════════════════════════════════════
                ''
            else
              let
                # PureScript wrapper module (equivalent to Main.hs for Haskell)
                # PureScript functions are exported by default when compiled to WASM
                wrapperMain = pkgs.writeText "Main.purs" ''
                  module Main where

                  import Pkg (pkg)
                  import Straylight.Nix.Derivation (drvToNixAttrs)
                  import Straylight.Nix (nixWasmInit)

                  -- Initialize the WASM plugin
                  -- Exported as "nix_wasm_init_v1" by the WASM backend
                  initPlugin :: Effect Unit
                  initPlugin = nixWasmInit

                  -- Export the package specification
                  -- Exported as "pkg" by the WASM backend
                  pkgExport :: Value -> Effect Value
                  pkgExport _args = drvToNixAttrs pkg
                '';

                # Straylight.Nix PureScript modules path
                straylightPursModules = ../../../src/purescript;
              in
              pkgs.runCommand "${name}.wasm"
                {
                  src = pursPath;
                  nativeBuildInputs = [ pureSarcasm pkgs.purescript ];
                }
                ''
                  set -euo pipefail
                  
                  mkdir -p build
                  cd build
                  
                  # Copy Straylight.Nix PureScript modules
                  if [ -d "${straylightPursModules}" ]; then
                    cp -r ${straylightPursModules}/Straylight Straylight
                    chmod -R u+w Straylight
                  fi
                  
                  # Copy user's package as Pkg.purs, wrapper as Main.purs
                  cp $src Pkg.purs
                  cp ${wrapperMain} Main.purs
                  
                  # Compile PureScript to Wasm-GC using pure-sarcasm
                  #                                                                      // note
                  # This implementation attempts compilation and handles errors gracefully
                  
                  # Check if purs-sarcasm is available
                  if ! command -v purs-sarcasm >/dev/null 2>&1; then
                    echo "pure-sarcasm compiler not found in PATH"
                    echo ""
                    echo "To enable PureScript WASM support:"
                    echo "  1. Add pure-sarcasm overlay to your flake"
                    echo "  2. Import straylight.modules.flake.default (includes pure-sarcasm overlay)"
                    echo ""
                    echo "For now, use Haskell (.hs) files instead - same API, fully working."
                    exit 1
                  fi
                  
                  # Compile PureScript to Wasm-GC
                  # pure-sarcasm CLI may vary - try common patterns
                  echo "Compiling PureScript to WASM using pure-sarcasm..."
                  
                  # Try compilation with pure-sarcasm
                  # The exact command depends on pure-sarcasm's actual API
                  # Common patterns: purs-sarcasm compile, purs compile --backend wasm-gc, etc.
                  if purs-sarcasm compile --output-dir output Main.purs Pkg.purs 2>&1; then
                    # Success - find the output WASM file
                    if [ -f "output/Main.wasm" ]; then
                      cp output/Main.wasm $out
                    elif [ -f "output/main.wasm" ]; then
                      cp output/main.wasm $out
                    elif [ -f "output/index.wasm" ]; then
                      cp output/index.wasm $out
                    else
                      echo "pure-sarcasm compilation succeeded but no WASM output found"
                      echo "Searched for: output/Main.wasm, output/main.wasm, output/index.wasm"
                      echo "Output directory contents:"
                      ls -la output/ || true
                      exit 1
                    fi
                  else
                    echo "PureScript WASM compilation failed"
                    echo ""
                    echo "This may be due to:"
                    echo "  1. Missing Straylight.Nix PureScript bindings"
                    echo "  2. PureScript FFI syntax differences"
                    echo "  3. pure-sarcasm CLI changes"
                    echo ""
                    echo "Current status:"
                    echo "  ✅ Infrastructure: Ready"
                    echo "  ✅ pure-sarcasm: Available"
                    echo "  ⚠️  PureScript bindings: Need implementation"
                    echo ""
                    echo "Workaround: Use Haskell (.hs) files instead - same API, fully working."
                    echo "See: https://github.com/ajnsit/pure-sarcasm"
                    exit 1
                  fi
                '';

            # Check if language backend is enabled (if config is available)
            # Default to enabled if config is not available (backward compatibility)
            buildConfig = config.straylight.build.config or null;
            haskellEnabled = buildConfig == null || buildConfig.haskell.enable;
            purescriptEnabled = buildConfig == null || buildConfig.purescript.enable;
            nixEnabled = buildConfig == null || buildConfig.nix.enable;
          in
          if ext == "hs" then
            if !haskellEnabled then
              throw "call-package: Haskell backend (.hs files) is disabled. Enable it with: straylight.build.languages.haskell.enable = true;"
            else if ghc-wasm == null then
              throw ''
                call-package for .hs files requires ghc-wasm-meta input.
                Add ghc-wasm-meta to your flake inputs or pre-compile to .wasm.
              ''
            else if !(builtins ? wasm) then
              throw ''
                call-package for .hs files requires straylight-nix with builtins.wasm.
                Use straylight-nix or pre-compile to .wasm and use a different evaluator.
              ''
            else
              let
                wasmDrv = buildHsWasm path;
                # Call "pkg" export which returns the package spec
                spec = builtins.wasm wasmDrv "pkg" args;
              in
              wasm-infra.buildFromSpec { inherit spec pkgs; }

          else if ext == "purs" then
            if !purescriptEnabled then
              throw "call-package: PureScript backend (.purs files) is disabled. Enable it with: straylight.build.languages.purescript.enable = true;"
            else if !(builtins ? wasm) then
              throw ''
                call-package for .purs files requires straylight-nix with builtins.wasm.
                Use straylight-nix or pre-compile to .wasm and use a different evaluator.
              ''
            else
              let
                # Build PureScript to WASM
                #                                                                      // note
                wasmDrv = buildPursWasm path;
                spec = builtins.wasm wasmDrv "pkg" args;
              in
              wasm-infra.buildFromSpec { inherit spec pkgs; }

          else if ext == "wasm" then
            if !(builtins ? wasm) then
              throw "call-package for .wasm files requires straylight-nix with builtins.wasm"
            else
              let
                # Assume .wasm files export "pkg" like .hs files
                spec = builtins.wasm path "pkg" args;
              in
              wasm-infra.buildFromSpec { inherit spec pkgs; }

          else if ext == "nix" then
            if !nixEnabled then
              throw "call-package: Nix backend (.nix files) is disabled. Enable it with: straylight.build.languages.nix.enable = true;"
            else
              pkgs.callPackage path args

          else
            throw "call-package: unsupported extension .${ext} (expected .hs, .purs, .wasm, or .nix)";

        # ──────────────────────────────────────────────────────────────────────
        # // assembled prelude //
        # ──────────────────────────────────────────────────────────────────────

        prelude = straylight.prelude // {
          # Re-export overlay contents
          inherit (straylight)
            platform
            gpu
            turing-registry
            stdenv
            cross
            versions
            license
            ;

          # pkgs-dependent toolchains
          inherit
            python
            ghc
            lean
            rust
            cpp
            ;

          # pkgs-dependent utilities
          inherit
            fetch
            render
            write
            write-shell-application
            script
            opt
            mk-package
            test
            typed
            call-package
            ;

          # Derivation helpers (lisp-case re-exports)
          inherit drv;

          # Error handling and debugging
          inherit error;

          # Module system helpers
          inherit modules;

          # Raw pkgs access
          inherit pkgs;
        };

      in
      {
        # Expose via config.straylight.prelude
        straylight.prelude = prelude;

        # Expose via _module.args for direct access: { prelude, ... }:
        _module.args.prelude = prelude;
      };
  };
}

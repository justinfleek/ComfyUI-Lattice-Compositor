{
  description = "// weyl // trtllm-serve // TensorRT-LLM inference stack";

  nixConfig = {
    extra-substituters = [
      "https://weyl-ai.cachix.org"
    ];

    extra-trusted-public-keys = [
      "weyl-ai.cachix.org-1:cR0SpSAPw7wejZ21ep4SLojE77gp5F2os260eEWqTTw="
    ];

    extra-experimental-features = [
      "nix-command"
      "flakes"
      "pipe-operators"
    ];
  };

  inputs = {
    flake-parts.url = "github:hercules-ci/flake-parts";

    # NVIDIA SDK provides CUDA, cuDNN, NCCL, TensorRT, Triton
    # Follow nvidia-sdk's nixpkgs to ensure cache hits
    nvidia-sdk.url = "github:weyl-ai/nvidia-sdk";
    nixpkgs.follows = "nvidia-sdk/nixpkgs";
  };

  outputs =
    inputs@{ flake-parts, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [
        "x86_64-linux"
        "aarch64-linux"
      ];

      perSystem =
        {
          config,
          self',
          inputs',
          pkgs,
          system,
          ...
        }:
        let
          # Get nvidia-sdk overlay applied
          pkgs' = import inputs.nixpkgs {
            inherit system;

            config = {
              cudaSupport = true;
              cudaCapabilities = [ "12.0" ];
              allowUnfree = true;
            };

            overlays = [
              inputs.nvidia-sdk.overlays.default
              inputs.nvidia-sdk.overlays.stdenv-overlay
              inputs.self.overlays.default
            ];
          };
        in
        {
          packages = {
            default = pkgs'.openai-proxy-hs;

            # Haskell AI Gateway (OpenAI proxy + tools + metrics)
            inherit (pkgs')
              openai-proxy-hs
              trtllm-validate
              ;

            # Re-export from nvidia-sdk for convenience
            inherit (pkgs')
              tritonserver-trtllm
              cuda
              cudnn
              nccl
              tensorrt
              # TRT-LLM Python wrappers
              trtllm-python
              trtllm-build
              trtllm-env
              qwen3-chat
              ;

            # ════════════════════════════════════════════════════════════════════
            # Example: Qwen3-32B-NVFP4 engine
            # Build with: nix build .#qwen3-32b-engine --option sandbox false
            # ════════════════════════════════════════════════════════════════════
            qwen3-32b-engine = pkgs'.trtllm-engine.mkEngine {
              name = "qwen3-32b-nvfp4";
              hfModel = "nvidia/Qwen3-32B-NVFP4";
              quantization = "NVFP4";
              maxBatchSize = 8;
              maxSeqLen = 16384;
              maxNumTokens = 8192;
              tensorParallelSize = 1;
            };

            # Qwen3-32B Triton server runtime
            tritonserver-qwen3 = pkgs'.trtllm-engine.mkTritonServerRuntime {
              name = "qwen3";
              tokenizerModel = "nvidia/Qwen3-32B-NVFP4";
              httpPort = 8000;
              grpcPort = 8001;
              metricsPort = 8002;
            };
          };

          devShells = {
            default = pkgs'.mkShell {
              packages = [
                pkgs'.tritonserver-trtllm
                pkgs'.openai-proxy-hs
                pkgs'.trtllm-validate
                pkgs'.openmpi
                pkgs'.prrte
                pkgs'.python312
              ];
              shellHook = ''
                echo "trtllm-serve — TensorRT-LLM inference stack"
                echo ""
                echo "Quick start:"
                echo "  nix run .#qwen3         — Chat with Qwen3-32B-NVFP4"
                echo ""
                echo "Tools:"
                echo "  openai-proxy-hs  — Haskell AI Gateway (OpenAI proxy + tools)"
                echo "  trtllm-validate  — TRT-LLM engine validation"
                echo "  tritonserver     — NVIDIA Triton Inference Server"
                echo ""

                # TRT-LLM Python environment
                export PYTHONPATH="${pkgs'.tritonserver-trtllm}/python''${PYTHONPATH:+:$PYTHONPATH}"
                export LD_LIBRARY_PATH="/run/opengl-driver/lib:${pkgs'.tritonserver-trtllm}/lib:${pkgs'.tritonserver-trtllm}/python/tensorrt_llm/libs:${pkgs'.cuda}/lib64:${pkgs'.cudnn}/lib:${pkgs'.nccl}/lib:${pkgs'.tensorrt}/lib:${pkgs'.openmpi}/lib:${pkgs'.python312}/lib''${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
                export CUDA_HOME="${pkgs'.cuda}"
                export TRITON_LIBCUDA_PATH="/run/opengl-driver/lib"
              '';
            };
          };

          apps = {
            # Unified AI Gateway
            default = {
              type = "app";
              program = "${pkgs'.openai-proxy-hs}/bin/openai-proxy-hs";
              meta.description = "Haskell AI Gateway: OpenAI proxy + tools + metrics";
            };

            openai-proxy = {
              type = "app";
              program = "${pkgs'.openai-proxy-hs}/bin/openai-proxy-hs";
              meta.description = "Haskell AI Gateway: OpenAI proxy + tools + metrics";
            };

            trtllm-validate = {
              type = "app";
              program = "${pkgs'.trtllm-validate}/bin/trtllm-validate";
              meta.description = "TRT-LLM engine validation tool";
            };

            tritonserver = {
              type = "app";
              program = "${pkgs'.tritonserver-trtllm}/bin/tritonserver";
              meta.description = "NVIDIA Triton Inference Server with TRT-LLM backend";
            };

            # TRT-LLM Python environment
            trtllm-python = {
              type = "app";
              program = "${pkgs'.trtllm-python}/bin/python";
              meta.description = "Python with TensorRT-LLM environment";
            };

            trtllm-build = {
              type = "app";
              program = "${pkgs'.trtllm-build}/bin/trtllm-build";
              meta.description = "TensorRT-LLM engine build command";
            };

            # Quick start: nix run .#qwen3
            qwen3 = {
              type = "app";
              program = "${pkgs'.qwen3-chat}/bin/qwen3-chat";
              meta.description = "Chat with Qwen3-32B-NVFP4";
            };
          };
        };

        flake = {
        overlays.default =
          final: prev:
          {
            # Haskell packages
            openai-proxy-hs = final.callPackage ./nix/openai-proxy-hs.nix { };
            trtllm-validate = final.haskellPackages.callPackage ./nix/trtllm-validate.nix { };

            # TRT-LLM engine building infrastructure (function set, not a package)
            trtllm-engine = final.callPackage ./nix/trtllm-engine.nix {
              tritonserver-trtllm = final.tritonserver-trtllm;
              cuda = final.cuda;
              cudnn = final.cudnn;
              nccl = final.nccl;
              tensorrt = final.tensorrt;
              trtllm-validate = final.trtllm-validate;
            };

            # ════════════════════════════════════════════════════════════════════
            # TRT-LLM Python environment wrappers
            # ════════════════════════════════════════════════════════════════════

            # Python with TensorRT-LLM environment
            trtllm-python = final.writeShellScriptBin "python" ''
              export PYTHONPATH="${final.tritonserver-trtllm}/python''${PYTHONPATH:+:$PYTHONPATH}"
              export LD_LIBRARY_PATH="/run/opengl-driver/lib:${final.tritonserver-trtllm}/lib:${final.tritonserver-trtllm}/python/tensorrt_llm/libs:${final.cuda}/lib64:${final.cudnn}/lib:${final.nccl}/lib:${final.tensorrt}/lib:${final.openmpi}/lib:${final.python312}/lib''${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
              export CUDA_HOME="${final.cuda}"
              export TRITON_LIBCUDA_PATH="/run/opengl-driver/lib"
              exec ${final.python312}/bin/python "$@"
            '';

            # TRT-LLM build command wrapper
            trtllm-build = final.writeShellScriptBin "trtllm-build" ''
              export PYTHONPATH="${final.tritonserver-trtllm}/python''${PYTHONPATH:+:$PYTHONPATH}"
              export LD_LIBRARY_PATH="/run/opengl-driver/lib:${final.tritonserver-trtllm}/lib:${final.tritonserver-trtllm}/python/tensorrt_llm/libs:${final.cuda}/lib64:${final.cudnn}/lib:${final.nccl}/lib:${final.tensorrt}/lib:${final.openmpi}/lib:${final.python312}/lib''${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
              export CUDA_HOME="${final.cuda}"
              export TRITON_LIBCUDA_PATH="/run/opengl-driver/lib"
              exec ${final.python312}/bin/python -m tensorrt_llm.commands.build "$@"
            '';

            # Full TRT-LLM development environment
            trtllm-env = final.buildEnv {
              name = "trtllm-env";
              paths = [
                final.trtllm-python
                final.trtllm-build
                final.tritonserver-trtllm
                final.openmpi
                final.prrte
              ];
            };

            # Quick start: chat with Qwen3-32B
            qwen3-chat = final.writeShellScriptBin "qwen3-chat" ''
              export PYTHONPATH="${final.tritonserver-trtllm}/python''${PYTHONPATH:+:$PYTHONPATH}"
              export LD_LIBRARY_PATH="/run/opengl-driver/lib:${final.tritonserver-trtllm}/lib:${final.tritonserver-trtllm}/python/tensorrt_llm/libs:${final.cuda}/lib64:${final.cudnn}/lib:${final.nccl}/lib:${final.tensorrt}/lib:${final.openmpi}/lib:${final.python312}/lib''${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
              export CUDA_HOME="${final.cuda}"
              export TRITON_LIBCUDA_PATH="/run/opengl-driver/lib"
              exec ${final.python312}/bin/python -c "
from tensorrt_llm import LLM, SamplingParams
print('Loading Qwen3-32B-NVFP4...')
llm = LLM(model='nvidia/Qwen3-32B-NVFP4', tensor_parallel_size=1)
print('Ready. Type your message (Ctrl+D to exit):')
sampling = SamplingParams(max_tokens=256)
while True:
    try:
        prompt = input('> ')
        if not prompt.strip(): continue
        out = llm.generate([prompt], sampling)[0].outputs[0].text
        print(out)
    except EOFError:
        break
"
            '';

            # TRT-LLM Serve (PyTorch backend with speculative decoding)
            mkTrtllmServe = args: final.callPackage ./nix/trtllm-serve.nix ({
              tritonserver-trtllm = final.tritonserver-trtllm;
              cuda = final.cuda;
            } // args);

            # Convenience aliases
            tool-server = final.openai-proxy-hs;
            tool-server-hs = final.openai-proxy-hs;
          };

        # NixOS module for AI inference services
        nixosModules.default = { config, lib, pkgs, ... }:
          let
            cfg = config.services.trtllm-serve;
          in
          {
            options.services.trtllm-serve = {
              enable = lib.mkEnableOption "TensorRT-LLM inference service";

              openaiProxy = {
                enable = lib.mkEnableOption "OpenAI-compatible proxy";
                port = lib.mkOption {
                  type = lib.types.port;
                  default = 9000;
                  description = "Port for OpenAI proxy";
                };
                tritonHost = lib.mkOption {
                  type = lib.types.str;
                  default = "localhost";
                  description = "Triton server hostname";
                };
                tritonPort = lib.mkOption {
                  type = lib.types.port;
                  default = 8001;
                  description = "Triton gRPC port";
                };
              };
            };

            config = lib.mkIf cfg.enable {
              systemd.services.openai-proxy = lib.mkIf cfg.openaiProxy.enable {
                description = "OpenAI-compatible proxy for TensorRT-LLM";
                wantedBy = [ "multi-user.target" ];
                after = [ "network.target" ];

                environment = {
                  TRITON_HOST = cfg.openaiProxy.tritonHost;
                  TRITON_PORT = toString cfg.openaiProxy.tritonPort;
                  PORT = toString cfg.openaiProxy.port;
                };

                serviceConfig = {
                  ExecStart = "${pkgs.openai-proxy-hs}/bin/openai-proxy-hs";
                  Restart = "always";
                  RestartSec = 5;
                };
              };
            };
          };
      };
    };
}

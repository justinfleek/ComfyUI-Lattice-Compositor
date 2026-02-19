# Checklist: lattice

## lattice
| File | Unit | Property | Regression | TypeScript | Memory | E2E | Integration | Browser | Performance | Security |
|:-----|:----:|:--------:|:----------:|:----------:|:------:|:---:|:-----------:|:-------:|:-----------:|:--------:|
| __init__.py | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | ❌ | N/A | ❌ | ❌ |


## lattice/nodes
| File | Unit | Property | Regression | TypeScript | Memory | E2E | Integration | Browser | Performance | Security |
|:-----|:----:|:--------:|:----------:|:----------:|:------:|:---:|:-----------:|:-------:|:-----------:|:--------:|
| __init__.py | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | ❌ | N/A | ❌ | ❌ |
| compositor_node.py | ✅ | ✅ | ❌ | N/A | ❌ | ❌ | ⚠️ | N/A | ❌ | ⚠️ |
| controlnet_preprocessors.py | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | ❌ | N/A | ❌ | ❌ |
| lattice_api_proxy.py | ⚠️ | ❌ | ❌ | N/A | ❌ | ❌ | ⚠️ | N/A | ❌ | ⚠️ |
| lattice_frame_interpolation.py | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | ❌ | N/A | ❌ | ❌ |
| lattice_layer_decomposition.py | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | ❌ | N/A | ❌ | ❌ |
| lattice_stem_separation.py | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | ❌ | N/A | ❌ | ❌ |
| lattice_vectorize.py | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | ❌ | N/A | ❌ | ❌ |


## lattice/scripts
| File | Unit | Property | Regression | TypeScript | Memory | E2E | Integration | Browser | Performance | Security |
|:-----|:----:|:--------:|:----------:|:----------:|:------:|:---:|:-----------:|:-------:|:-----------:|:--------:|
| decomp_local.py | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | ❌ | N/A | ❌ | ❌ |
| decomp_run.py | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | ❌ | N/A | ❌ | ❌ |
| run_decomp.bat | N/A | N/A | N/A | N/A | N/A | N/A | N/A | N/A | N/A | N/A |
| run_decomp_comfyui.py | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | ❌ | N/A | ❌ | ❌ |
| run_decomp_now.py | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | ❌ | N/A | ❌ | ❌ |
| run_decomposition_gpu.py | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | ❌ | N/A | ❌ | ❌ |
| test_decomp_fp8.py | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | ❌ | N/A | ❌ | ❌ |
| test_decomp_gpu.py | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | ❌ | N/A | ❌ | ❌ |
| test_decomp_minimal.py | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | ❌ | N/A | ❌ | ❌ |
| test_decomposition.sh | N/A | N/A | N/A | N/A | N/A | N/A | N/A | N/A | N/A | N/A |
| test_load.py | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | ❌ | N/A | ❌ | ❌ |
| test_load_all.py | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | ❌ | N/A | ❌ | ❌ |
| test_manual_load.py | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | ❌ | N/A | ❌ | ❌ |
| test_transformer.py | ❌ | ❌ | ❌ | N/A | ❌ | ❌ | ❌ | N/A | ❌ | ❌ |


## lattice/tests
| File | Unit | Property | Regression | TypeScript | Memory | E2E | Integration | Browser | Performance | Security |
|:-----|:----:|:--------:|:----------:|:----------:|:------:|:---:|:-----------:|:-------:|:-----------:|:--------:|
| conftest.py | ⚠️ | ❌ | ❌ | N/A | ❌ | ❌ | ⚠️ | N/A | ❌ | ❌ |
| hypothesis_strategies.py | ⚠️ | ⚠️ | ❌ | N/A | ❌ | ❌ | ⚠️ | N/A | ❌ | ❌ |
| test_compositor_node_hypothesis.py | ✅ | ✅ | ❌ | N/A | ❌ | ❌ | ⚠️ | N/A | ❌ | ❌ |
| test_compositor_node_validation.py | ✅ | ❌ | ❌ | N/A | ❌ | ❌ | ⚠️ | N/A | ❌ | ❌ |
| test_route_registration.py | ✅ | ❌ | ❌ | N/A | ❌ | ❌ | ⚠️ | N/A | ❌ | ❌ |



// s4 // tests/property/test_attention_properties.cpp
// Property-based tests for attention kernel invariants.
// These tests verify mathematical properties without requiring CUDA.

#include <catch2/catch_test_macros.hpp>
#include <catch2/catch_approx.hpp>
#include <rapidcheck.h>

#include <algorithm>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <numeric>
#include <vector>

namespace {

// Constants matching sage_attention_plugin.h
constexpr int kSequenceBlockSize = 128;
constexpr int kScaleFactorGroupSize = 16;
constexpr std::size_t kWorkspaceAlignment = 128;

// ============================================================================
// Reference implementations for property testing
// ============================================================================

// Reference key centering: output[b,h,s,d] = input[b,h,s,d] - mean(input[b,h,:,d])
auto reference_key_centering(
    const std::vector<float>& input,
    std::int32_t batch_size,
    std::int32_t head_count,
    std::int32_t sequence_length,
    std::int32_t head_dimension) -> std::vector<float> {
  
  std::vector<float> output(input.size());
  
  for (std::int32_t b = 0; b < batch_size; ++b) {
    for (std::int32_t h = 0; h < head_count; ++h) {
      for (std::int32_t d = 0; d < head_dimension; ++d) {
        // Compute mean along sequence dimension.
        double sum = 0.0;
        for (std::int32_t s = 0; s < sequence_length; ++s) {
          std::size_t idx = 
              static_cast<std::size_t>(b) * head_count * sequence_length * head_dimension +
              static_cast<std::size_t>(h) * sequence_length * head_dimension +
              static_cast<std::size_t>(s) * head_dimension + d;
          sum += input[idx];
        }
        float mean = static_cast<float>(sum / sequence_length);
        
        // Subtract mean.
        for (std::int32_t s = 0; s < sequence_length; ++s) {
          std::size_t idx = 
              static_cast<std::size_t>(b) * head_count * sequence_length * head_dimension +
              static_cast<std::size_t>(h) * sequence_length * head_dimension +
              static_cast<std::size_t>(s) * head_dimension + d;
          output[idx] = input[idx] - mean;
        }
      }
    }
  }
  
  return output;
}

// Reference query group mean.
struct query_group_mean_result {
  std::vector<float> centered;
  std::vector<float> group_means;
};

auto reference_query_group_mean(
    const std::vector<float>& input,
    std::int32_t batch_size,
    std::int32_t head_count,
    std::int32_t sequence_length,
    std::int32_t head_dimension,
    std::int32_t group_size) -> query_group_mean_result {
  
  std::int32_t const group_count = (sequence_length + group_size - 1) / group_size;
  
  std::vector<float> centered(input.size());
  std::vector<float> group_means(
      static_cast<std::size_t>(batch_size) * head_count * group_count * head_dimension);
  
  for (std::int32_t b = 0; b < batch_size; ++b) {
    for (std::int32_t h = 0; h < head_count; ++h) {
      for (std::int32_t g = 0; g < group_count; ++g) {
        std::int32_t const group_start = g * group_size;
        std::int32_t const group_end = std::min(group_start + group_size, sequence_length);
        std::int32_t const group_length = group_end - group_start;
        
        for (std::int32_t d = 0; d < head_dimension; ++d) {
          // Compute mean for this group and dimension.
          double sum = 0.0;
          for (std::int32_t s = group_start; s < group_end; ++s) {
            std::size_t idx = 
                static_cast<std::size_t>(b) * head_count * sequence_length * head_dimension +
                static_cast<std::size_t>(h) * sequence_length * head_dimension +
                static_cast<std::size_t>(s) * head_dimension + d;
            sum += input[idx];
          }
          float mean = static_cast<float>(sum / group_length);
          
          // Store group mean.
          std::size_t mean_idx = 
              static_cast<std::size_t>(b) * head_count * group_count * head_dimension +
              static_cast<std::size_t>(h) * group_count * head_dimension +
              static_cast<std::size_t>(g) * head_dimension + d;
          group_means[mean_idx] = mean;
          
          // Center the queries in this group.
          for (std::int32_t s = group_start; s < group_end; ++s) {
            std::size_t idx = 
                static_cast<std::size_t>(b) * head_count * sequence_length * head_dimension +
                static_cast<std::size_t>(h) * sequence_length * head_dimension +
                static_cast<std::size_t>(s) * head_dimension + d;
            centered[idx] = input[idx] - mean;
          }
        }
      }
    }
  }
  
  return {centered, group_means};
}

// Compute score correction: delta_S = Q_mean @ K_centered^T
auto reference_score_correction(
    const std::vector<float>& key_centered,
    const std::vector<float>& query_group_mean,
    std::int32_t batch_size,
    std::int32_t head_count,
    std::int32_t group_count,
    std::int32_t key_sequence_length,
    std::int32_t head_dimension) -> std::vector<float> {
  
  std::vector<float> correction(
      static_cast<std::size_t>(batch_size) * head_count * group_count * key_sequence_length);
  
  for (std::int32_t b = 0; b < batch_size; ++b) {
    for (std::int32_t h = 0; h < head_count; ++h) {
      for (std::int32_t g = 0; g < group_count; ++g) {
        for (std::int32_t k = 0; k < key_sequence_length; ++k) {
          // Dot product: Q_mean[b,h,g,:] @ K_centered[b,h,k,:]
          double dot = 0.0;
          for (std::int32_t d = 0; d < head_dimension; ++d) {
            std::size_t q_idx = 
                static_cast<std::size_t>(b) * head_count * group_count * head_dimension +
                static_cast<std::size_t>(h) * group_count * head_dimension +
                static_cast<std::size_t>(g) * head_dimension + d;
            std::size_t k_idx = 
                static_cast<std::size_t>(b) * head_count * key_sequence_length * head_dimension +
                static_cast<std::size_t>(h) * key_sequence_length * head_dimension +
                static_cast<std::size_t>(k) * head_dimension + d;
            dot += query_group_mean[q_idx] * key_centered[k_idx];
          }
          
          std::size_t out_idx = 
              static_cast<std::size_t>(b) * head_count * group_count * key_sequence_length +
              static_cast<std::size_t>(h) * group_count * key_sequence_length +
              static_cast<std::size_t>(g) * key_sequence_length + k;
          correction[out_idx] = static_cast<float>(dot);
        }
      }
    }
  }
  
  return correction;
}

// ============================================================================
// Generators
// ============================================================================

auto gen_small_dimension() -> rc::Gen<std::int32_t> {
  return rc::gen::inRange(1, 17);  // 1 to 16
}

auto gen_sequence_length() -> rc::Gen<std::int32_t> {
  return rc::gen::inRange(1, 65);  // 1 to 64
}

auto gen_float_vector(std::size_t size) -> rc::Gen<std::vector<float>> {
  return rc::gen::container<std::vector<float>>(
      size,
      rc::gen::map(
          rc::gen::inRange(-1000, 1001),
          [](int x) { return static_cast<float>(x) / 100.0f; }));
}

}  // namespace

// ============================================================================
// Property Tests
// ============================================================================

TEST_CASE("key_centering: output has zero mean along sequence dimension", "[attention][property]") {
  rc::prop("centered keys have zero mean per (batch, head, dim)",
    [](std::int32_t batch_size, std::int32_t head_count, 
       std::int32_t sequence_length, std::int32_t head_dimension) {
      
      // Constrain dimensions to reasonable test sizes.
      RC_PRE(batch_size >= 1 && batch_size <= 4);
      RC_PRE(head_count >= 1 && head_count <= 8);
      RC_PRE(sequence_length >= 2 && sequence_length <= 64);
      RC_PRE(head_dimension >= 1 && head_dimension <= 32);
      
      std::size_t const size = 
          static_cast<std::size_t>(batch_size) * head_count * sequence_length * head_dimension;
      
      auto input = *gen_float_vector(size);
      auto output = reference_key_centering(
          input, batch_size, head_count, sequence_length, head_dimension);
      
      // Check that each (b, h, d) slice has zero mean.
      for (std::int32_t b = 0; b < batch_size; ++b) {
        for (std::int32_t h = 0; h < head_count; ++h) {
          for (std::int32_t d = 0; d < head_dimension; ++d) {
            double sum = 0.0;
            for (std::int32_t s = 0; s < sequence_length; ++s) {
              std::size_t idx = 
                  static_cast<std::size_t>(b) * head_count * sequence_length * head_dimension +
                  static_cast<std::size_t>(h) * sequence_length * head_dimension +
                  static_cast<std::size_t>(s) * head_dimension + d;
              sum += output[idx];
            }
            double mean = sum / sequence_length;
            RC_ASSERT(std::abs(mean) < 1e-5);
          }
        }
      }
    });
}

TEST_CASE("key_centering: preserves relative differences", "[attention][property]") {
  rc::prop("differences between sequence positions are preserved",
    [](std::int32_t batch_size, std::int32_t head_count,
       std::int32_t sequence_length, std::int32_t head_dimension) {
      
      RC_PRE(batch_size >= 1 && batch_size <= 2);
      RC_PRE(head_count >= 1 && head_count <= 4);
      RC_PRE(sequence_length >= 2 && sequence_length <= 32);
      RC_PRE(head_dimension >= 1 && head_dimension <= 16);
      
      std::size_t const size = 
          static_cast<std::size_t>(batch_size) * head_count * sequence_length * head_dimension;
      
      auto input = *gen_float_vector(size);
      auto output = reference_key_centering(
          input, batch_size, head_count, sequence_length, head_dimension);
      
      // For any two sequence positions s1, s2 and any (b, h, d):
      // output[s1] - output[s2] == input[s1] - input[s2]
      for (std::int32_t b = 0; b < batch_size; ++b) {
        for (std::int32_t h = 0; h < head_count; ++h) {
          for (std::int32_t d = 0; d < head_dimension; ++d) {
            for (std::int32_t s1 = 0; s1 < sequence_length; ++s1) {
              for (std::int32_t s2 = s1 + 1; s2 < sequence_length; ++s2) {
                auto idx = [&](std::int32_t s) -> std::size_t {
                  return static_cast<std::size_t>(b) * head_count * sequence_length * head_dimension +
                         static_cast<std::size_t>(h) * sequence_length * head_dimension +
                         static_cast<std::size_t>(s) * head_dimension + d;
                };
                
                float input_diff = input[idx(s1)] - input[idx(s2)];
                float output_diff = output[idx(s1)] - output[idx(s2)];
                RC_ASSERT(std::abs(input_diff - output_diff) < 1e-5f);
              }
            }
          }
        }
      }
    });
}

TEST_CASE("query_group_mean: group means are correct", "[attention][property]") {
  rc::prop("group means equal average of group members",
    [](std::int32_t batch_size, std::int32_t head_count,
       std::int32_t sequence_length, std::int32_t head_dimension,
       std::int32_t group_size) {
      
      RC_PRE(batch_size >= 1 && batch_size <= 2);
      RC_PRE(head_count >= 1 && head_count <= 4);
      RC_PRE(sequence_length >= 1 && sequence_length <= 32);
      RC_PRE(head_dimension >= 1 && head_dimension <= 16);
      RC_PRE(group_size >= 1 && group_size <= 16);
      
      std::size_t const size = 
          static_cast<std::size_t>(batch_size) * head_count * sequence_length * head_dimension;
      
      auto input = *gen_float_vector(size);
      auto result = reference_query_group_mean(
          input, batch_size, head_count, sequence_length, head_dimension, group_size);
      
      std::int32_t const group_count = (sequence_length + group_size - 1) / group_size;
      
      // Verify each group mean.
      for (std::int32_t b = 0; b < batch_size; ++b) {
        for (std::int32_t h = 0; h < head_count; ++h) {
          for (std::int32_t g = 0; g < group_count; ++g) {
            std::int32_t const group_start = g * group_size;
            std::int32_t const group_end = std::min(group_start + group_size, sequence_length);
            std::int32_t const group_length = group_end - group_start;
            
            for (std::int32_t d = 0; d < head_dimension; ++d) {
              // Compute expected mean.
              double sum = 0.0;
              for (std::int32_t s = group_start; s < group_end; ++s) {
                std::size_t idx = 
                    static_cast<std::size_t>(b) * head_count * sequence_length * head_dimension +
                    static_cast<std::size_t>(h) * sequence_length * head_dimension +
                    static_cast<std::size_t>(s) * head_dimension + d;
                sum += input[idx];
              }
              float expected_mean = static_cast<float>(sum / group_length);
              
              std::size_t mean_idx = 
                  static_cast<std::size_t>(b) * head_count * group_count * head_dimension +
                  static_cast<std::size_t>(h) * group_count * head_dimension +
                  static_cast<std::size_t>(g) * head_dimension + d;
              
              RC_ASSERT(std::abs(result.group_means[mean_idx] - expected_mean) < 1e-5f);
            }
          }
        }
      }
    });
}

TEST_CASE("query_group_mean: centered queries have zero group mean", "[attention][property]") {
  rc::prop("centered queries sum to zero within each group",
    [](std::int32_t batch_size, std::int32_t head_count,
       std::int32_t sequence_length, std::int32_t head_dimension,
       std::int32_t group_size) {
      
      RC_PRE(batch_size >= 1 && batch_size <= 2);
      RC_PRE(head_count >= 1 && head_count <= 4);
      RC_PRE(sequence_length >= 1 && sequence_length <= 32);
      RC_PRE(head_dimension >= 1 && head_dimension <= 16);
      RC_PRE(group_size >= 1 && group_size <= 16);
      
      std::size_t const size = 
          static_cast<std::size_t>(batch_size) * head_count * sequence_length * head_dimension;
      
      auto input = *gen_float_vector(size);
      auto result = reference_query_group_mean(
          input, batch_size, head_count, sequence_length, head_dimension, group_size);
      
      std::int32_t const group_count = (sequence_length + group_size - 1) / group_size;
      
      for (std::int32_t b = 0; b < batch_size; ++b) {
        for (std::int32_t h = 0; h < head_count; ++h) {
          for (std::int32_t g = 0; g < group_count; ++g) {
            std::int32_t const group_start = g * group_size;
            std::int32_t const group_end = std::min(group_start + group_size, sequence_length);
            std::int32_t const group_length = group_end - group_start;
            
            for (std::int32_t d = 0; d < head_dimension; ++d) {
              double sum = 0.0;
              for (std::int32_t s = group_start; s < group_end; ++s) {
                std::size_t idx = 
                    static_cast<std::size_t>(b) * head_count * sequence_length * head_dimension +
                    static_cast<std::size_t>(h) * sequence_length * head_dimension +
                    static_cast<std::size_t>(s) * head_dimension + d;
                sum += result.centered[idx];
              }
              double mean = sum / group_length;
              RC_ASSERT(std::abs(mean) < 1e-5);
            }
          }
        }
      }
    });
}

TEST_CASE("score_correction: mathematical identity", "[attention][property]") {
  rc::prop("Q @ K^T = Q' @ K'^T + delta_S (expanded over groups)",
    [](std::int32_t batch_size, std::int32_t head_count,
       std::int32_t query_sequence_length, std::int32_t key_sequence_length,
       std::int32_t head_dimension, std::int32_t group_size) {
      
      RC_PRE(batch_size >= 1 && batch_size <= 2);
      RC_PRE(head_count >= 1 && head_count <= 2);
      RC_PRE(query_sequence_length >= 1 && query_sequence_length <= 16);
      RC_PRE(key_sequence_length >= 1 && key_sequence_length <= 16);
      RC_PRE(head_dimension >= 1 && head_dimension <= 8);
      RC_PRE(group_size >= 1 && group_size <= 8);
      
      std::size_t const q_size = 
          static_cast<std::size_t>(batch_size) * head_count * query_sequence_length * head_dimension;
      std::size_t const k_size = 
          static_cast<std::size_t>(batch_size) * head_count * key_sequence_length * head_dimension;
      
      auto query_input = *gen_float_vector(q_size);
      auto key_input = *gen_float_vector(k_size);
      
      // Compute centered versions.
      auto key_centered = reference_key_centering(
          key_input, batch_size, head_count, key_sequence_length, head_dimension);
      auto query_result = reference_query_group_mean(
          query_input, batch_size, head_count, query_sequence_length, head_dimension, group_size);
      
      std::int32_t const group_count = (query_sequence_length + group_size - 1) / group_size;
      
      // Compute score correction.
      auto delta_s = reference_score_correction(
          key_centered, query_result.group_means,
          batch_size, head_count, group_count, key_sequence_length, head_dimension);
      
      // Verify the identity for each (batch, head, query, key) position.
      for (std::int32_t b = 0; b < batch_size; ++b) {
        for (std::int32_t h = 0; h < head_count; ++h) {
          for (std::int32_t q = 0; q < query_sequence_length; ++q) {
            std::int32_t const g = q / group_size;
            
            for (std::int32_t k = 0; k < key_sequence_length; ++k) {
              // Original Q @ K^T.
              double original_score = 0.0;
              for (std::int32_t d = 0; d < head_dimension; ++d) {
                std::size_t q_idx = 
                    static_cast<std::size_t>(b) * head_count * query_sequence_length * head_dimension +
                    static_cast<std::size_t>(h) * query_sequence_length * head_dimension +
                    static_cast<std::size_t>(q) * head_dimension + d;
                std::size_t k_idx = 
                    static_cast<std::size_t>(b) * head_count * key_sequence_length * head_dimension +
                    static_cast<std::size_t>(h) * key_sequence_length * head_dimension +
                    static_cast<std::size_t>(k) * head_dimension + d;
                original_score += query_input[q_idx] * key_input[k_idx];
              }
              
              // Q' @ K'^T.
              double centered_score = 0.0;
              for (std::int32_t d = 0; d < head_dimension; ++d) {
                std::size_t q_idx = 
                    static_cast<std::size_t>(b) * head_count * query_sequence_length * head_dimension +
                    static_cast<std::size_t>(h) * query_sequence_length * head_dimension +
                    static_cast<std::size_t>(q) * head_dimension + d;
                std::size_t k_idx = 
                    static_cast<std::size_t>(b) * head_count * key_sequence_length * head_dimension +
                    static_cast<std::size_t>(h) * key_sequence_length * head_dimension +
                    static_cast<std::size_t>(k) * head_dimension + d;
                centered_score += query_result.centered[q_idx] * key_centered[k_idx];
              }
              
              // Delta S for this query's group.
              std::size_t delta_idx = 
                  static_cast<std::size_t>(b) * head_count * group_count * key_sequence_length +
                  static_cast<std::size_t>(h) * group_count * key_sequence_length +
                  static_cast<std::size_t>(g) * key_sequence_length + k;
              
              // The key insight: Q @ K^T = Q' @ K'^T + Q_mean @ K'^T
              // (Note: Q_mean @ K^T = Q_mean @ K'^T because K' = K - mean(K) and mean(K'^T) = 0)
              double reconstructed = centered_score + delta_s[delta_idx];
              
              // Allow for floating-point tolerance.
              RC_ASSERT(std::abs(original_score - reconstructed) < 1e-4);
            }
          }
        }
      }
    });
}

TEST_CASE("workspace_requirements: monotonic in dimensions", "[attention][property]") {
  // Local implementation of workspace calculation (matches sage_attention_plugin.h)
  auto compute_workspace_size = [](int batch_size, int head_count, 
                                    int query_seq, int key_seq, int head_dim) -> std::size_t {
    auto pad_to_block = [](int len) -> int {
      return ((len + kSequenceBlockSize - 1) / kSequenceBlockSize) * kSequenceBlockSize;
    };
    
    int const q_pad = pad_to_block(query_seq);
    int const k_pad = pad_to_block(key_seq);
    int const groups = (query_seq + kSequenceBlockSize - 1) / kSequenceBlockSize;
    
    std::size_t total = 0;
    auto align_add = [&](std::size_t bytes) {
      total = (total + kWorkspaceAlignment - 1) & ~(kWorkspaceAlignment - 1);
      total += bytes;
    };
    
    std::size_t const bh = static_cast<std::size_t>(batch_size) * head_count;
    
    // BF16 tensors (2 bytes each)
    align_add(bh * k_pad * head_dim * 2);   // key_centered
    align_add(bh * q_pad * head_dim * 2);   // query_centered
    align_add(bh * groups * head_dim * 2);  // query_group_mean
    
    // FP32 score correction (4 bytes)
    align_add(bh * groups * key_seq * 4);
    
    // FP4 packed tensors (1 byte per 2 elements)
    align_add(bh * q_pad * (head_dim / 2));  // query_fp4
    align_add(bh * k_pad * (head_dim / 2));  // key_fp4
    align_add(bh * head_dim * (k_pad / 2));  // value_fp4
    
    // FP8 scale factors (1 byte each)
    int const scales_per_row = head_dim / kScaleFactorGroupSize;
    int const scales_per_col = k_pad / kScaleFactorGroupSize;
    align_add(bh * q_pad * scales_per_row);
    align_add(bh * k_pad * scales_per_row);
    align_add(bh * head_dim * scales_per_col);
    
    // Tile semaphore
    align_add(sizeof(int));
    
    return total;
  };
  
  rc::prop("larger dimensions require more workspace",
    [&compute_workspace_size](std::int32_t batch1, std::int32_t batch2,
       std::int32_t head_count, std::int32_t head_dimension) {
      
      RC_PRE(batch1 >= 1 && batch1 <= 8);
      RC_PRE(batch2 >= 1 && batch2 <= 8);
      RC_PRE(head_count >= 1 && head_count <= 32);
      RC_PRE(head_dimension >= 16 && head_dimension <= 128);
      RC_PRE((head_dimension % 16) == 0);
      
      std::int32_t const seq = 128;
      
      auto ws1 = compute_workspace_size(batch1, head_count, seq, seq, head_dimension);
      auto ws2 = compute_workspace_size(batch2, head_count, seq, seq, head_dimension);
      
      if (batch1 <= batch2) {
        RC_ASSERT(ws1 <= ws2);
      }
      if (batch1 >= batch2) {
        RC_ASSERT(ws1 >= ws2);
      }
    });
}

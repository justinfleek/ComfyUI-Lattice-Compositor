#include "scheduler.hpp"

#include <algorithm>
#include <random>
#include <cmath>

namespace lattice {

// Karras et al. sigma schedule
SigmaSchedule karras_sigmas(int num_steps, float sigma_min, float sigma_max, float rho) {
    SigmaSchedule schedule;
    schedule.sigmas.resize(num_steps + 1);
    schedule.timesteps.resize(num_steps);
    
    const float inv_rho = 1.0f / rho;
    const float sigma_max_pow = std::pow(sigma_max, inv_rho);
    const float sigma_min_pow = std::pow(sigma_min, inv_rho);
    
    for (int i = 0; i <= num_steps; ++i) {
        float t = static_cast<float>(i) / static_cast<float>(num_steps);
        schedule.sigmas[i] = std::pow(sigma_max_pow + t * (sigma_min_pow - sigma_max_pow), rho);
    }
    
    // Timesteps are indices 0 to num_steps-1
    for (int i = 0; i < num_steps; ++i) {
        schedule.timesteps[i] = i;
    }
    
    return schedule;
}

// Exponential sigma schedule
SigmaSchedule exponential_sigmas(int num_steps, float sigma_min, float sigma_max) {
    SigmaSchedule schedule;
    schedule.sigmas.resize(num_steps + 1);
    schedule.timesteps.resize(num_steps);
    
    const float log_ratio = std::log(sigma_max / sigma_min);
    
    for (int i = 0; i <= num_steps; ++i) {
        float t = static_cast<float>(i) / static_cast<float>(num_steps);
        schedule.sigmas[i] = sigma_max * std::exp(-t * log_ratio);
    }
    
    for (int i = 0; i < num_steps; ++i) {
        schedule.timesteps[i] = i;
    }
    
    return schedule;
}

// Flow matching sigma schedule (linear timesteps with shift)
SigmaSchedule flow_match_sigmas(int num_steps, float shift) {
    SigmaSchedule schedule;
    schedule.sigmas.resize(num_steps + 1);
    schedule.timesteps.resize(num_steps);
    
    // Flow matching uses timesteps in [0, 1]
    // With shift for improved sampling at high resolution
    for (int i = 0; i <= num_steps; ++i) {
        float t = static_cast<float>(num_steps - i) / static_cast<float>(num_steps);
        // Apply shift: t_shifted = shift * t / (1 + (shift - 1) * t)
        float t_shifted = shift * t / (1.0f + (shift - 1.0f) * t);
        schedule.sigmas[i] = t_shifted;
    }
    
    for (int i = 0; i < num_steps; ++i) {
        schedule.timesteps[i] = i;
    }
    
    return schedule;
}

// EulerAScheduler implementation
EulerAScheduler::EulerAScheduler(PredictionType pred_type)
    : pred_type_(pred_type) {}

void EulerAScheduler::set_timesteps(int num_inference_steps) {
    auto schedule = karras_sigmas(num_inference_steps);
    sigmas_ = std::move(schedule.sigmas);
    timesteps_ = std::move(schedule.timesteps);
}

void EulerAScheduler::step(std::span<const float> model_output,
                           std::span<float> sample,
                           int step_index) {
    if (step_index >= static_cast<int>(sigmas_.size()) - 1) return;
    
    const float sigma = sigmas_[step_index];
    const float sigma_next = sigmas_[step_index + 1];
    const size_t n = sample.size();
    
    // Euler ancestral step
    // x_next = x + (sigma_next - sigma) * model_output  (for epsilon prediction)
    // With ancestral noise injection
    
    if (pred_type_ == PredictionType::Epsilon) {
        // Compute predicted x0: x0 = x - sigma * noise
        // Then: x_next = x + (sigma_next - sigma) * noise
        const float dt = sigma_next - sigma;
        
        // For ancestral: sigma_up = sqrt(sigma_next^2 - sigma_down^2)
        // where sigma_down^2 = sigma_next^2 * (1 - (sigma/sigma_next)^2)
        const float sigma_ratio = sigma_next > 0.0f ? (sigma / sigma_next) : 0.0f;
        const float sigma_up = sigma_next * std::sqrt(1.0f - sigma_ratio * sigma_ratio);
        const float sigma_down = std::sqrt(sigma_next * sigma_next - sigma_up * sigma_up);
        
        // Deterministic step
        const float scale = sigma_down - sigma;
        for (size_t i = 0; i < n; ++i) {
            sample[i] = sample[i] + scale * model_output[i];
        }
        
        // Add ancestral noise (using simple PRNG for now)
        if (sigma_up > 0.0f && step_index < static_cast<int>(sigmas_.size()) - 2) {
            std::mt19937 rng(static_cast<uint32_t>(step_index * 12345 + 67890));
            std::normal_distribution<float> dist(0.0f, 1.0f);
            for (size_t i = 0; i < n; ++i) {
                sample[i] = sample[i] + sigma_up * dist(rng);
            }
        }
    } else if (pred_type_ == PredictionType::VPrediction) {
        // v-prediction: v = alpha * noise - sigma * x
        // x0 = alpha * x - sigma * v, noise = sigma * x + alpha * v
        // For diffusion, alpha = sqrt(1 - sigma^2) approximately
        const float alpha = std::sqrt(1.0f / (1.0f + sigma * sigma));
        const float dt = sigma_next - sigma;
        
        for (size_t i = 0; i < n; ++i) {
            // Convert v to epsilon
            float eps = sigma * sample[i] + alpha * model_output[i];
            sample[i] = sample[i] + dt * eps;
        }
    } else {
        // Flow prediction: model directly predicts velocity
        const float dt = sigma_next - sigma;
        for (size_t i = 0; i < n; ++i) {
            sample[i] = sample[i] + dt * model_output[i];
        }
    }
}

void EulerAScheduler::add_noise(std::span<const float> original,
                                std::span<const float> noise,
                                std::span<float> output,
                                int timestep_index) {
    if (timestep_index >= static_cast<int>(sigmas_.size())) return;
    
    const float sigma = sigmas_[timestep_index];
    const size_t n = original.size();
    
    // x_noisy = x + sigma * noise
    for (size_t i = 0; i < n; ++i) {
        output[i] = original[i] + sigma * noise[i];
    }
}

// DPMPlusPlus2MScheduler implementation
DPMPlusPlus2MScheduler::DPMPlusPlus2MScheduler(PredictionType pred_type)
    : pred_type_(pred_type) {}

void DPMPlusPlus2MScheduler::set_timesteps(int num_inference_steps) {
    auto schedule = karras_sigmas(num_inference_steps);
    sigmas_ = std::move(schedule.sigmas);
    timesteps_ = std::move(schedule.timesteps);
    old_denoised_.clear();
    t_prev_ = 0.0f;
}

void DPMPlusPlus2MScheduler::step(std::span<const float> model_output,
                                   std::span<float> sample,
                                   int step_index) {
    if (step_index >= static_cast<int>(sigmas_.size()) - 1) return;
    
    const float sigma = sigmas_[step_index];
    const float sigma_next = sigmas_[step_index + 1];
    const size_t n = sample.size();
    
    // DPM++ 2M uses second-order multistep
    // Convert model output to denoised (x0 prediction)
    std::vector<float> denoised(n);
    
    if (pred_type_ == PredictionType::Epsilon) {
        // x0 = x - sigma * noise
        for (size_t i = 0; i < n; ++i) {
            denoised[i] = sample[i] - sigma * model_output[i];
        }
    } else if (pred_type_ == PredictionType::VPrediction) {
        const float alpha = std::sqrt(1.0f / (1.0f + sigma * sigma));
        for (size_t i = 0; i < n; ++i) {
            denoised[i] = alpha * sample[i] - sigma * model_output[i];
        }
    } else {
        // Flow: velocity points from noise to data
        for (size_t i = 0; i < n; ++i) {
            denoised[i] = sample[i] - sigma * model_output[i];
        }
    }
    
    // Compute lambda values for DPM++
    const float lambda = -std::log(sigma);
    const float lambda_next = sigma_next > 1e-7f ? -std::log(sigma_next) : 20.0f;
    const float h = lambda_next - lambda;
    
    if (old_denoised_.empty() || step_index == 0) {
        // First step: use first-order update
        for (size_t i = 0; i < n; ++i) {
            // x_next = (sigma_next/sigma) * x + (1 - sigma_next/sigma) * denoised
            float ratio = sigma_next / sigma;
            sample[i] = ratio * sample[i] + (1.0f - ratio) * denoised[i];
        }
    } else {
        // Second-order update using previous denoised
        const float lambda_prev = t_prev_;
        const float h_prev = lambda - lambda_prev;
        const float r = h_prev / h;
        
        // D = (1 + 1/(2r)) * denoised - (1/(2r)) * old_denoised
        for (size_t i = 0; i < n; ++i) {
            float D = (1.0f + 0.5f / r) * denoised[i] - (0.5f / r) * old_denoised_[i];
            float ratio = sigma_next / sigma;
            sample[i] = ratio * sample[i] + (1.0f - ratio) * D;
        }
    }
    
    // Store for next step
    old_denoised_ = denoised;
    t_prev_ = lambda;
}

void DPMPlusPlus2MScheduler::add_noise(std::span<const float> original,
                                        std::span<const float> noise,
                                        std::span<float> output,
                                        int timestep_index) {
    if (timestep_index >= static_cast<int>(sigmas_.size())) return;
    
    const float sigma = sigmas_[timestep_index];
    const size_t n = original.size();
    
    for (size_t i = 0; i < n; ++i) {
        output[i] = original[i] + sigma * noise[i];
    }
}

// FlowMatchScheduler implementation  
FlowMatchScheduler::FlowMatchScheduler(float shift)
    : shift_(shift) {}

void FlowMatchScheduler::set_timesteps(int num_inference_steps) {
    auto schedule = flow_match_sigmas(num_inference_steps, shift_);
    sigmas_ = std::move(schedule.sigmas);
    timesteps_ = std::move(schedule.timesteps);
}

void FlowMatchScheduler::step(std::span<const float> model_output,
                               std::span<float> sample,
                               int step_index) {
    if (step_index >= static_cast<int>(sigmas_.size()) - 1) return;
    
    const float t = sigmas_[step_index];       // Current timestep
    const float t_next = sigmas_[step_index + 1];  // Next timestep
    const float dt = t_next - t;  // Negative, going from 1 to 0
    const size_t n = sample.size();
    
    // Flow matching: x = (1-t)*x0 + t*noise
    // velocity = dx/dt = noise - x0 = (x - (1-t)*x0) / t - x0
    // Euler step: x_next = x + dt * velocity
    
    for (size_t i = 0; i < n; ++i) {
        sample[i] = sample[i] + dt * model_output[i];
    }
}

void FlowMatchScheduler::add_noise(std::span<const float> original,
                                    std::span<const float> noise,
                                    std::span<float> output,
                                    int timestep_index) {
    if (timestep_index >= static_cast<int>(sigmas_.size())) return;
    
    const float t = sigmas_[timestep_index];
    const size_t n = original.size();
    
    // Flow matching interpolation: x_t = (1-t)*x0 + t*noise
    for (size_t i = 0; i < n; ++i) {
        output[i] = (1.0f - t) * original[i] + t * noise[i];
    }
}

// Factory function
std::unique_ptr<Scheduler> create_scheduler(SchedulerType type, PredictionType pred_type) {
    switch (type) {
        case SchedulerType::Euler:
        case SchedulerType::EulerA:
            return std::make_unique<EulerAScheduler>(pred_type);
            
        case SchedulerType::DPMPlusPlus2M:
        case SchedulerType::DPMPlusPlus2Mv2:
            return std::make_unique<DPMPlusPlus2MScheduler>(pred_type);
            
        case SchedulerType::FlowMatch:
        case SchedulerType::RectifiedFlow:
            return std::make_unique<FlowMatchScheduler>(1.0f);
            
        default:
            return std::make_unique<EulerAScheduler>(pred_type);
    }
}

} // namespace lattice

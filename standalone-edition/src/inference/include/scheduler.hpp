#pragma once

#include <cstdint>
#include <cstddef>
#include <vector>
#include <cmath>
#include <numbers>
#include <span>

namespace lattice {

enum class SchedulerType {
    Euler,
    EulerA,
    Heun,
    DPM2,
    DPMPlusPlus2M,
    DPMPlusPlus2Mv2,
    DPMPlusPlus2Sa,
    LCM,
    FlowMatch,
    RectifiedFlow,
};

enum class PredictionType {
    Epsilon,
    VPrediction,
    Flow,
};

// Sigma schedule computation
struct SigmaSchedule {
    std::vector<float> sigmas;
    std::vector<int> timesteps;
};

[[nodiscard]] SigmaSchedule karras_sigmas(
    int num_steps,
    float sigma_min = 0.0292f,
    float sigma_max = 14.6146f,
    float rho = 7.0f
);

[[nodiscard]] SigmaSchedule exponential_sigmas(
    int num_steps,
    float sigma_min = 0.0292f,
    float sigma_max = 14.6146f
);

[[nodiscard]] SigmaSchedule flow_match_sigmas(
    int num_steps,
    float shift = 1.0f
);

// Base scheduler interface
class Scheduler {
public:
    virtual ~Scheduler() = default;
    
    virtual void set_timesteps(int num_inference_steps) = 0;
    
    [[nodiscard]] virtual const std::vector<float>& sigmas() const = 0;
    [[nodiscard]] virtual const std::vector<int>& timesteps() const = 0;
    
    // Single denoising step
    // model_output: predicted noise or velocity
    // sample: current noisy sample
    // step_index: current step (0 to num_steps-1)
    // Returns: previous sample (less noisy)
    virtual void step(
        std::span<const float> model_output,
        std::span<float> sample,
        int step_index
    ) = 0;
    
    // Add noise at timestep (for img2img)
    virtual void add_noise(
        std::span<const float> original,
        std::span<const float> noise,
        std::span<float> output,
        int timestep_index
    ) = 0;
};

// Euler Ancestral sampler
class EulerAScheduler : public Scheduler {
public:
    explicit EulerAScheduler(PredictionType pred_type = PredictionType::Epsilon);
    
    void set_timesteps(int num_inference_steps) override;
    [[nodiscard]] const std::vector<float>& sigmas() const override { return sigmas_; }
    [[nodiscard]] const std::vector<int>& timesteps() const override { return timesteps_; }
    
    void step(std::span<const float> model_output,
              std::span<float> sample,
              int step_index) override;
    
    void add_noise(std::span<const float> original,
                   std::span<const float> noise,
                   std::span<float> output,
                   int timestep_index) override;

private:
    PredictionType pred_type_;
    std::vector<float> sigmas_;
    std::vector<int> timesteps_;
};

// DPM++ 2M scheduler
class DPMPlusPlus2MScheduler : public Scheduler {
public:
    explicit DPMPlusPlus2MScheduler(PredictionType pred_type = PredictionType::Epsilon);
    
    void set_timesteps(int num_inference_steps) override;
    [[nodiscard]] const std::vector<float>& sigmas() const override { return sigmas_; }
    [[nodiscard]] const std::vector<int>& timesteps() const override { return timesteps_; }
    
    void step(std::span<const float> model_output,
              std::span<float> sample,
              int step_index) override;
    
    void add_noise(std::span<const float> original,
                   std::span<const float> noise,
                   std::span<float> output,
                   int timestep_index) override;

private:
    PredictionType pred_type_;
    std::vector<float> sigmas_;
    std::vector<int> timesteps_;
    std::vector<float> old_denoised_;
    float t_prev_ = 0.0f;
};

// Flow Matching scheduler (for Flux, Wan, etc.)
class FlowMatchScheduler : public Scheduler {
public:
    explicit FlowMatchScheduler(float shift = 1.0f);
    
    void set_timesteps(int num_inference_steps) override;
    [[nodiscard]] const std::vector<float>& sigmas() const override { return sigmas_; }
    [[nodiscard]] const std::vector<int>& timesteps() const override { return timesteps_; }
    
    void step(std::span<const float> model_output,
              std::span<float> sample,
              int step_index) override;
    
    void add_noise(std::span<const float> original,
                   std::span<const float> noise,
                   std::span<float> output,
                   int timestep_index) override;

private:
    float shift_;
    std::vector<float> sigmas_;
    std::vector<int> timesteps_;
};

// Factory function
[[nodiscard]] std::unique_ptr<Scheduler> create_scheduler(
    SchedulerType type,
    PredictionType pred_type = PredictionType::Epsilon
);

} // namespace lattice

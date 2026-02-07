#pragma once
#include <imgui/imgui.h>
#include <type_traits>
#include <utility>

namespace ImGui {
template <typename T, typename T_min, typename T_max>
inline bool SliderFloatType(const char* label,
                            T* v,
                            T_min v_min,
                            T_max v_max,
                            const char* format = "%.3f",
                            ImGuiSliderFlags flags = 0) {
	static_assert(std::is_floating_point<T>::value,
	              "Input type for ImGUI must be a floating point!");
	static_assert(std::is_scalar_v<T_min> && std::is_scalar_v<T_max>,
	              "Input ranges must be scalars!");
	ImGuiDataType_ dataType;
	T v_min_T = T(v_min);
	T v_max_T = T(v_max);
	if constexpr (std::is_same<T, float>::value) {
		dataType = ImGuiDataType_Float;
	} else if constexpr (std::is_same<T, double>::value) {
		dataType = ImGuiDataType_Double;
	}
	return ImGui::SliderScalar(label, dataType, v, &v_min_T, &v_max_T, format,
	                           flags);
}
template <typename T>
inline bool InputFloatType(const char* label, T* v) {
	static_assert(std::is_floating_point<T>::value,
	              "Input type for ImGUI must be a floating point!");
	ImGuiDataType_ dataType;
	if constexpr (std::is_same<T, float>::value) {
		dataType = ImGuiDataType_Float;
	} else if constexpr (std::is_same<T, double>::value) {
		dataType = ImGuiDataType_Double;
	}
	ImGuiInputTextFlags_ flags = ImGuiInputTextFlags_CharsScientific;
	return InputScalar(label, dataType, (void*)v, NULL, NULL, "%.3f", flags);
}
template <typename T, typename U, typename V>
inline bool InputFloatType(const char* label,
                           T* v,
                           U step = 0.0f,
                           V step_fast = 0.0f,
                           const char* format = "%.3f",
                           ImGuiInputTextFlags flags = 0) {
	static_assert(std::is_floating_point<T>::value,
	              "Input type for ImGUI must be a floating point!");
	static_assert(std::is_scalar_v<U> && std::is_scalar_v<V>,
	              "Input steps must be scalars!");
	ImGuiDataType_ dataType;
	T step_T = T(step);
	T step_fast_T = T(step_fast);
	if constexpr (std::is_same<T, float>::value) {
		dataType = ImGuiDataType_Float;
	} else if constexpr (std::is_same<T, double>::value) {
		dataType = ImGuiDataType_Double;
	}
	flags |= ImGuiInputTextFlags_CharsScientific;
	return InputScalar(
		label, dataType, (void*)v, (void*)(step_T > 0.0f ? &step_T : NULL),
		(void*)(step_fast_T > 0.0f ? &step_fast_T : NULL), format, flags);
}
template <int N, typename T, typename U, typename V>
inline bool SliderFloatTypeN(const char* label,
                             T* v,
                             U v_min,
                             V v_max,
                             const char* format = "%.3f",
                             ImGuiSliderFlags flags = 0) {
	static_assert(std::is_floating_point<T>::value,
	              "Input type for ImGUI must be a floating point!");
	static_assert(std::is_scalar_v<U> && std::is_scalar_v<V>,
	              "Input steps must be scalars!");
	ImGuiDataType_ dataType;
	if constexpr (std::is_same<T, float>::value) {
		dataType = ImGuiDataType_Float;
	} else if constexpr (std::is_same<T, double>::value) {
		dataType = ImGuiDataType_Double;
	}
	return ImGui::SliderScalarN(label, dataType, v, N, &v_min, &v_max, format,
	                            flags);
}
template <typename... Args>
auto SliderFloatType3(Args&&... args)
	-> decltype(SliderFloatTypeN<3>(std::forward<Args>(args)...)) {
	return SliderFloatTypeN<3>(std::forward<Args>(args)...);
}
template <int N, typename T>
inline bool InputFloatTypeN(const char* label,
                            T *v,
                            const char* format = "%.3f",
                            ImGuiInputTextFlags flags = 0) {
	static_assert(std::is_floating_point<T>::value,
	              "Input type for ImGUI must be a floating point!");
	ImGuiDataType_ dataType;
	if constexpr (std::is_same<T, float>::value) {
		dataType = ImGuiDataType_Float;
	} else if constexpr (std::is_same<T, double>::value) {
		dataType = ImGuiDataType_Double;
	}
	return InputScalarN(label, dataType, v, N, NULL, NULL, format,
	                    flags);
}
template <typename... Args>
auto InputFloatType3(Args&&... args)
	-> decltype(InputFloatTypeN<3>(std::forward<Args>(args)...)) {
	return InputFloatTypeN<3>(std::forward<Args>(args)...);
}
}  // namespace ImGui

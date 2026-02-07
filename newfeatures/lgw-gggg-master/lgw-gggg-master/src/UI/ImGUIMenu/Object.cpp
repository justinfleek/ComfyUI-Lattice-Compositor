#include "ImGUIUtils.h"
#include "Object.h"
namespace Homogenization {
namespace UI {
namespace ff = FrictionFrenzy;
void showImGUIMenu(ff::CollisionObject::RigidObjectBase& obj) {
	std::stringstream ss;
	ss << "Object " << obj.getID();
	if (ImGui::CollapsingHeader(ss.str().c_str(),
	                            ImGuiTreeNodeFlags_DefaultOpen)) {
		ss.str(std::string());
		ImGui::Text("%s", obj.toString().c_str());
		if (ImGui::SliderFloatType("density", &obj.density(), 0.01, 100)) {
			obj.updateDensity(obj.density());
		}
		ff::Vector3 posVec = obj.getTranslation();
		if (ImGui::InputFloatType3("position", posVec.data(), "%.6g")) {
			obj.setTranslation(posVec);
		}
		Eigen::AngleAxis<ff::Scalar> rot(obj.getRotation());
		bool updateRot =
			ImGui::InputFloatType3("axis", rot.axis().data(), "%.6g");
		updateRot |=
			ImGui::InputFloatType("angle", &rot.angle(), 0, M_PI, "%.6f");
		if (updateRot) {
			obj.setRotation(ff::Quaternion(rot));
		}

		ImGui::InputFloatType3("velocity", obj.velocity().data(), "%.6g");
		ImGui::InputFloatType3("angular velocity", obj.angularVel().data(),
		                       "%.6g");
		ImGui::Checkbox("Is static", &obj.getStatic());
		ImGui::Checkbox("Is sticky", &obj.getSticky());
	}
}
}  // namespace UI
}  // namespace FrictionFrenzy

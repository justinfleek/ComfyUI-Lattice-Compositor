uniform mat4 viewMatrix;
uniform mat4 projectionMatrix;

uniform float particleRadius;
uniform float pointSizeScale;
uniform float gamma;
uniform double valueMin;
uniform double valueMax;
uniform int selection;
uniform bool visualizeValue = false;

uniform vec3 cuttingPlanes = vec3(0, 0, 0);
uniform vec3 planeDir = vec3(1, 1, -1);

layout(location = 0) in dvec3 position;
layout(location = 1) in double value;
layout(location = 2) in int id;

out vec3 viewCenter;
out vec3 color;
flat out int vertexID;
flat out int visible;

const vec3 inferno[] = {
	vec3(0.0, 0.0, 0.016),
	vec3(0.129, 0.047, 0.255),
	vec3(0.341, 0.063, 0.431),
	vec3(0.541, 0.133, 0.416),
	vec3(0.737, 0.216, 0.329),
	vec3(0.894, 0.353, 0.192),
	vec3(0.976, 0.557, 0.035),
	vec3(0.976, 0.796, 0.208),
	vec3(0.988, 1, 0.643)
};

vec3 mapValue(double v) {
	float invGamma = 1.0 / gamma;
	float vMap = pow(float(v), invGamma);
	float vn = float(vMap * 8);
	int first = int(floor(vn));
	int second = int(ceil(vn));
	if (first < 0) {
		return inferno[0];
	} else if (first >= 8) {
		return inferno[8];
	} else {
		float mixParam = vn - first;
		return mix(inferno[first], inferno[second], mixParam);
	}
}

bool showParticle(vec3 pos) {
	return (position[0] * planeDir[0] > cuttingPlanes[0] * planeDir[0]
			&& position[1] * planeDir[1] > cuttingPlanes[1] * planeDir[1]
			&& position[2] * planeDir[2] > cuttingPlanes[2] * planeDir[2]);
}

void main() {
	vec4 posF = vec4(position, 1.0);
    vec4 eyeCoord = viewMatrix*posF;
    vec3 posEye = vec3(eyeCoord);

    /* output */
    viewCenter = posEye;
	if (id == selection) {
		color = vec3(0.0, 1.0, 0.0);
	} else if (visualizeValue) {
		color = mapValue((value - valueMin) / (valueMax - valueMin));
	} else {
		color = vec3(0.04, 0.61, 1);
	}
	// color = vec3(0.216, 0.565, 1.0);
    gl_Position = projectionMatrix*eyeCoord;
	vertexID = id;

	if (showParticle(vec3(position))) {
		gl_PointSize = particleRadius * pointSizeScale / length(posEye);
		visible = 1;
	} else {
		gl_PointSize = 1;
		visible = 0;
	}
	// gl_Position = vec4(0.0, 0.0, 0.5, 1.0);
}

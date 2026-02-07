uniform mat4 projectionMatrix;
// uniform vec3 lightDir = vec3(1, 1, 1);
uniform vec3 specularColor = vec3(1, 1, 1);
uniform float particleRadius;
uniform float shininess = 180;

struct PointLight {
	vec4 dir;
	vec3 color;
};

uniform PointLight lights[N_LIGHTS];

in vec3 viewCenter;
in vec3 color;
flat in int vertexID;
flat in int visible;
layout(location = 0) out vec4 fragmentColor;
layout(location = 1) out int vID;

vec3 shadeLight(vec3 normal, vec3 fragPos, vec3 viewDir, PointLight light) {
	vec3 dir = light.dir.xyz;
	vec3 ambientColor = 0.2 * color;
    vec3 halfDir  = normalize(dir - viewDir);
    vec3 diffuse  = max(dot(normal, dir), 0.0)*color*light.color;
    vec3 specular = pow(max(dot(halfDir, normal), 0.0), shininess)*light.color;

    return ambientColor + diffuse * 0.5 + specular; /* scale diffuse to 0.5 */
}

void main() {
	if (visible == 0) {
		discard;
	}

    vec3 viewDir = normalize(viewCenter);
    vec3 normal;
    vec3 fragPos;

    normal.xy = gl_PointCoord.xy*vec2(2.0, -2.0) + vec2(-1.0, 1.0);
    float mag = dot(normal.xy, normal.xy);
    if(mag > 1.0) discard; /* outside the sphere */

    normal.z = sqrt(1.0 - mag);
    fragPos  = viewCenter + normal*particleRadius; /* correct fragment position */

    mat4 prjMatTransposed = transpose(projectionMatrix);
    float z = dot(vec4(fragPos, 1.0), prjMatTransposed[2]);
    float w = dot(vec4(fragPos, 1.0), prjMatTransposed[3]);
	if (z < 0) discard;
    gl_FragDepth = 0.5*(z/w + 1.0); /* correct fragment depth */

	vec3 res = vec3(0.0, 0.0, 0.0);
	for(int i = 0; i < N_LIGHTS; ++i) {
		res += shadeLight(normal, fragPos, viewDir, lights[i]);
	}
    fragmentColor = vec4(res, 1.0);
	vID = vertexID;
}


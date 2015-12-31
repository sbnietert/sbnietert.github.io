/// <reference path="Vector.ts" />
/// <reference path="Color.ts" />
/// <reference path="Material.ts" />
/// <reference path="GeometricObject.ts" />
/// <reference path="SceneObject.ts" />
/// <reference path="Scene.ts" />
var RT;
(function (RT) {
    var Light = (function () {
        function Light(position, color, intensity) {
            this.position = position;
            this.color = color;
            this.intensity = intensity;
        }
        Light.shadowRayIsObstructed = function (shadowRay, distToLight, sceneGraph) {
            for (var _i = 0; _i < sceneGraph.length; _i++) {
                var node = sceneGraph[_i];
                if (!node.boundingShape || node.boundingShape.obstructsShadowRay(shadowRay, distToLight)) {
                    switch (node.type) {
                        case 0 /* Object */:
                            var obj = node.value;
                            if (obj.getGeometry().obstructsShadowRay(shadowRay, distToLight))
                                return true;
                            break;
                        case 1 /* Collection */:
                            var subGraph = node.value;
                            if (Light.shadowRayIsObstructed(shadowRay, distToLight, subGraph))
                                return true;
                            break;
                    }
                }
            }
            return false;
        };
        Light.prototype.illuminate = function (lighting, intersection, sceneGraph) {
            var illumination = RT.Color.BLACK;
            // create shadow ray
            var L = this.position.minus(intersection.point);
            var distToLight = L.length();
            L.scale(1 / distToLight);
            var shadowRay = new RT.Ray(intersection.point, L);
            shadowRay.origin.add(L.plus(intersection.normal).scaledBy(RT.EPSILON));
            // if shadow ray isn't obstructed, continue with diffuse and specular illumination
            if (!Light.shadowRayIsObstructed(shadowRay, distToLight, sceneGraph)) {
                var attenuationFactor = this.intensity / Math.sqrt(0.002 * distToLight * distToLight + 0.02 * distToLight + 0.2);
                var attenuation = this.color.scaledBy(attenuationFactor);
                //diffuse illumination
                var dot = L.dot(intersection.normal);
                if (dot > 0)
                    illumination.add(lighting.color.times(attenuation).scaledBy(dot));
                //specular illumination
                if (lighting.shininess > 0) {
                    var R = L.getReflection(intersection.normal).normalize();
                    dot = R.dot(intersection.incident);
                    if (dot > 0)
                        illumination.add(RT.Color.WHITE.times(attenuation).scaledBy(Math.pow(dot, lighting.shininess)));
                }
            }
            return illumination;
        };
        return Light;
    })();
    RT.Light = Light;
})(RT || (RT = {}));

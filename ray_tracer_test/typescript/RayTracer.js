/// <reference path="Vector.ts" />
/// <reference path="Color.ts" />
/// <reference path="Sphere.ts" />
/// <reference path="Plane.ts" />
/// <reference path="Material.ts" />
/// <reference path="SceneObject.ts" />
/// <reference path="Light.ts" />
/// <reference path="Utils.ts" />
/// <reference path="Scene.ts" />
var RT;
(function (RT) {
    var RayTracer = (function () {
        function RayTracer() {
        }
        // determine refracted ray direction given incident, normal, and refractive indices
        // refraction code found online at http://www.flipcode.com/archives/reflection_transmission.pdf
        // (TIR means total internal reflection)
        RayTracer.performRefraction = function (intersection, n1, n2) {
            var n = n1 / n2;
            var c1 = -intersection.incident.dot(intersection.normal);
            var c2 = 1 - n * n * (1 - c1 * c1);
            var refractedRayDirection;
            var TIR;
            // total internal reflection occurs
            if (c2 < 0) {
                refractedRayDirection = intersection.incident.getReflection(intersection.normal);
                TIR = true;
            }
            else {
                refractedRayDirection = intersection.incident.scaledBy(n).plus(intersection.normal.scaledBy(n * c1 - Math.sqrt(c2)));
                TIR = false;
            }
            return {
                refractedRayDirection: refractedRayDirection,
                TIR: TIR
            };
        };
        // search recursively through scene graph, using bounding shapes for optimization
        RayTracer.findNearestIntersectionR = function (ray, currentInt, sceneGraph) {
            for (var _i = 0; _i < sceneGraph.length; _i++) {
                var node = sceneGraph[_i];
                var tempInt = new RT.RayIntersection();
                if (!node.boundingShape || node.boundingShape.obstructsShadowRay(ray, Infinity)) {
                    switch (node.type) {
                        case 0 /* Object */:
                            var obj = node.value;
                            if (obj.getGeometry().intersectsRay(ray, tempInt)) {
                                if (currentInt.object == null || tempInt.t < currentInt.t) {
                                    RT.Utils.set(currentInt, tempInt);
                                    currentInt.object = obj;
                                }
                            }
                            break;
                        case 1 /* Collection */:
                            var subGraph = node.value;
                            RayTracer.findNearestIntersectionR(ray, currentInt, subGraph);
                            break;
                    }
                }
            }
        };
        RayTracer.prototype.findNearestIntersection = function (ray) {
            var nearestIntersection = new RT.RayIntersection();
            RayTracer.findNearestIntersectionR(ray, nearestIntersection, this.scene.sceneGraph);
            if (nearestIntersection.object == null)
                return null;
            nearestIntersection.point = ray.origin.plus(ray.direction.scaledBy(nearestIntersection.t));
            nearestIntersection.incident = ray.direction;
            nearestIntersection.normal = nearestIntersection.object.getGeometry().findNormal(nearestIntersection);
            return nearestIntersection;
        };
        RayTracer.prototype.traceRay = function (ray, insideObject, depth) {
            // prevent infinite recursion
            if (depth >= this.scene.renderSettings.recursionDepth)
                return RT.Color.BLACK;
            // find closest intersection
            var nearestIntersection = this.findNearestIntersection(ray);
            // if there was an intersection, return the color at that point
            if (nearestIntersection != null)
                return this.shadeObject(nearestIntersection, insideObject, depth);
            // otherwise, return the background color
            return this.scene.background.getColor(ray.direction);
        };
        RayTracer.prototype.shadeObject = function (intersection, insideObject, depth) {
            var color = RT.Color.BLACK;
            var lighting = intersection.object.getMaterialLighting(intersection.point);
            var reflection = lighting.reflection;
            var refraction = lighting.refraction;
            var remaining = 1 - reflection - refraction;
            if (remaining > RT.EPSILON) {
                // ambient illumination
                color.add(lighting.color.scaledBy(lighting.ambient));
                // diffuse and specular illuminations 
                // (loop through all lights)
                for (var _i = 0, _a = this.scene.lights; _i < _a.length; _i++) {
                    var light = _a[_i];
                    color.add(light.illuminate(lighting, intersection, this.scene.sceneGraph));
                }
                color.scale(remaining);
            }
            // calculate reflection contribution
            if (reflection != 0) {
                var reflectedRay = new RT.Ray(intersection.point, intersection.incident.getReflection(intersection.normal));
                reflectedRay.inchForward();
                var reflectedColor = this.traceRay(reflectedRay, insideObject, depth + 1);
                color.add(reflectedColor.scaledBy(reflection));
            }
            // calculate refraction contribution
            if (refraction != 0) {
                var n1, n2;
                // if ray is entering object
                if (insideObject) {
                    n1 = lighting.refractiveIndex;
                    n2 = 1; // index of air
                }
                else {
                    n1 = 1;
                    n2 = lighting.refractiveIndex;
                }
                var refractionResults = RayTracer.performRefraction(intersection, n1, n2);
                var refractedRay = new RT.Ray(intersection.point, refractionResults.refractedRayDirection);
                if (!refractionResults.TIR)
                    insideObject = !insideObject;
                refractedRay.inchForward();
                var refractedColor = this.traceRay(refractedRay, insideObject, depth + 1);
                color.add(refractedColor.scaledBy(refraction));
            }
            return color;
        };
        RayTracer.prototype.render = function (paint) {
            var width = this.scene.renderSettings.camera.pixelWidth;
            var height = this.scene.renderSettings.camera.pixelHeight;
            var subpixelGridSize = this.scene.renderSettings.subpixelGridSize;
            var numSubpixels = subpixelGridSize * subpixelGridSize;
            var camera = this.scene.renderSettings.camera;
            var rowColors = new Array(width);
            var start = Date.now();
            for (var row = 0; row < height; row++) {
                for (var col = 0; col < width; col++) {
                    var pixelColor = RT.Color.BLACK;
                    for (var sr = 0; sr < subpixelGridSize; sr++) {
                        for (var sc = 0; sc < subpixelGridSize; sc++) {
                            var ray = camera.generateRay(row + sr / subpixelGridSize, col + sc / subpixelGridSize);
                            pixelColor.add(this.traceRay(ray, false, 0)); // assuming eye isn't inside object
                        }
                    }
                    pixelColor.scale(1 / numSubpixels).cap();
                    rowColors[col] = pixelColor.toString();
                }
                paint(rowColors, row);
            }
            console.log(((Date.now() - start) / 1000) + ' seconds');
        };
        return RayTracer;
    })();
    RT.RayTracer = RayTracer;
})(RT || (RT = {}));

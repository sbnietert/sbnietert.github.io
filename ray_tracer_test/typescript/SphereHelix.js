/// <reference path="SceneGraph.ts" />
/// <reference path="Vector.ts" />
/// <reference path="Material.ts" />
/// <reference path="AxisAlignedBox.ts" />
/// <reference path="SceneObject.ts" />
/// <reference path="Color.ts" />
var RT;
(function (RT) {
    var SphereHelix = (function () {
        function SphereHelix() {
        }
        SphereHelix.prototype.generateSceneGraphFromData = function (data, scene) {
            var lighting = new RT.MaterialLighting();
            var point = RT.Scene.loadVector(data.point);
            var direction = RT.Scene.loadVector(data.direction).normalize();
            if (direction.z != 0)
                var up = new RT.Vector(1, 1, -(direction.x + direction.y) / direction.z);
            else if (direction.y != 0)
                var up = new RT.Vector(1, 1, -(direction.x + direction.z) / direction.y);
            else
                var up = new RT.Vector(1, 1, -(direction.z + direction.y) / direction.x);
            up.normalize();
            var right = up.cross(direction).normalize();
            var start = data.start;
            var stop = data.stop;
            var step = data.step;
            var sphereR = data.sphereRadius;
            var helixR = data.helixRadius;
            var spheres = [];
            for (var t = start; t < stop; t += step) {
                var axisPos = point.plus(direction.scaledBy(t));
                var rightC = helixR * Math.cos(2 * Math.PI * t);
                var upC = helixR * Math.sin(2 * Math.PI * t);
                var offset = right.scaledBy(rightC).plus(up.scaledBy(upC));
                var sphereCtr = axisPos.plus(offset);
                var sphereGeo = new RT.Sphere(sphereCtr, sphereR);
                var lighting = new RT.MaterialLighting();
                lighting.color = RT.Color.fromHSL((0.75 + t * 0.8) % 1, 0.8, 0.5);
                var sphereMat = new RT.SimpleMaterial(lighting);
                var sphere = new RT.GenericSceneObject(sphereGeo, sphereMat);
                spheres.push(sphere);
            }
            return RT.SceneGraph.generateFromSceneObjects(spheres);
        };
        return SphereHelix;
    })();
    RT.SphereHelix = SphereHelix;
})(RT || (RT = {}));

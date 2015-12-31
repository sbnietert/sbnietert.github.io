/// <reference path="Camera.ts" />
/// <reference path="Background.ts" />
/// <reference path="PhiGradientBackground.ts" />
/// <reference path="Color.ts" />
/// <reference path="Light.ts" />
/// <reference path="Plane.ts" />
/// <reference path="Sphere.ts" />
/// <reference path="Cylinder.ts" />
/// <reference path="Triangle.ts" />
/// <reference path="AxisAlignedBox.ts" />
/// <reference path="MengerSponge.ts" />
/// <reference path="Mesh.ts" />
/// <reference path="SphereHelix.ts" />
/// <reference path="XZSurface.ts" />
/// <reference path="Material.ts" />
/// <reference path="CheckeredMaterial.ts" />
/// <reference path="GeometricObject.ts" />
/// <reference path="SceneObject.ts" />
/// <reference path="SceneGraph.ts" />
var RT;
(function (RT) {
    var Scene = (function () {
        function Scene(data) {
            this.renderSettings = {};
            this.renderSettings.camera = Scene.loadCamera(data.renderSettings.camera);
            this.renderSettings.subpixelGridSize = data.renderSettings.subpixelGridSize || 3;
            this.renderSettings.recursionDepth = data.renderSettings.recursionDepth || 10;
            this.background = Scene.loadBackground(data.background);
            this.lights = [];
            if (data.lights)
                for (var _i = 0, _a = data.lights; _i < _a.length; _i++) {
                    var lightData = _a[_i];
                    this.lights.push(Scene.loadLight(lightData));
                }
            this.materials = {};
            if (data.materials)
                for (var matName in data.materials)
                    this.materials[matName] = Scene.loadMaterial(data.materials[matName]);
            for (var matName in RT.Material.PRESETS)
                this.materials[matName] = (RT.Material.PRESETS[matName]);
            this.sceneGraph = [];
            for (var _b = 0, _c = data.sceneGraph; _b < _c.length; _b++) {
                var nodeData = _c[_b];
                this.sceneGraph.push(this.loadSceneGraphNode(nodeData));
            }
        }
        Scene.loadVector = function (values) {
            return new RT.Vector(values[0], values[1], values[2]);
        };
        Scene.loadColor = function (values) {
            return new RT.Color(values[0], values[1], values[2]);
        };
        Scene.loadCamera = function (data) {
            var eye = Scene.loadVector(data.eye);
            var direction = Scene.loadVector(data.direction).normalize();
            var pose = new RT.Ray(eye, direction);
            var up = Scene.loadVector(data.up).normalize();
            return new RT.Camera(pose, up, data.focalLength, data.pixelWidth, data.pixelHeight);
        };
        Scene.loadBackground = function (data) {
            switch (data.type) {
                case 'solid-color':
                    var color = Scene.loadColor(data.color);
                    return new RT.SolidColorBackground(color);
                case 'phi-gradient':
                    var color1 = Scene.loadColor(data.color1);
                    var color2 = Scene.loadColor(data.color2);
                    var axis = Scene.loadVector(data.axis);
                    return new RT.PhiGradientBackground(color1, color2, data.n, axis);
            }
        };
        Scene.loadLight = function (data) {
            var position = Scene.loadVector(data.position);
            var color = Scene.loadColor(data.color);
            return new RT.Light(position, color, data.intensity);
        };
        Scene.loadMaterial = function (data) {
            var checkered = (data.type.indexOf('checkered') != -1);
            if (data.type == 'simple' || checkered) {
                var lighting = new RT.MaterialLighting();
                if (checkered)
                    lighting.color = Scene.loadColor(data.color1);
                else if (data.color)
                    lighting.color = Scene.loadColor(data.color);
                for (var _i = 0, _a = Scene.materialProps; _i < _a.length; _i++) {
                    var prop = _a[_i];
                    if (data.hasOwnProperty(prop))
                        lighting[prop] = data[prop];
                }
                if (checkered) {
                    var color2 = Scene.loadColor(data.color2);
                    var pattern = (data.type == 'xz-checkered') ? RT.XZCheckeredMaterial : RT.XZDiamondCheckeredMaterial;
                    return new pattern(lighting, color2);
                }
                return new RT.SimpleMaterial(lighting);
            }
        };
        Scene.loadGeometricObject = function (data) {
            switch (data.type) {
                case 'sphere':
                    var center = Scene.loadVector(data.center);
                    return new RT.Sphere(center, data.radius);
                case 'plane':
                    var normal = Scene.loadVector(data.normal).normalize();
                    return new RT.Plane(normal, data.offset);
                case 'cylinder':
                    var point = Scene.loadVector(data.point);
                    var direction = Scene.loadVector(data.direction).normalize();
                    return new RT.Cylinder(new RT.Ray(point, direction), data.radius);
                case 'triangle':
                    var A = Scene.loadVector(data.A);
                    var B = Scene.loadVector(data.B);
                    var C = Scene.loadVector(data.C);
                    return new RT.Triangle(A, B, C);
                case 'axis-aligned-box':
                    var A = Scene.loadVector(data.A);
                    var B = Scene.loadVector(data.B);
                    return new RT.AxisAlignedBox(A, B);
            }
        };
        Scene.prototype.loadSceneObject = function (data) {
            var geo = Scene.loadGeometricObject(data.geometry);
            var mat = this.materials[data.material];
            return new RT.SceneObject(geo, mat);
        };
        Scene.prototype.loadSceneGraphNode = function (data) {
            var type;
            var value;
            switch (data.type) {
                case 'object':
                    type = 0 /* Object */;
                    value = this.loadSceneObject(data.value);
                    break;
                case 'collection':
                    type = 1 /* Collection */;
                    value = [];
                    for (var _i = 0, _a = data.value; _i < _a.length; _i++) {
                        var nodeData = _a[_i];
                        value.push(this.loadSceneGraphNode(nodeData));
                    }
                    break;
                case 'menger-sponge':
                case 'mesh':
                case 'sphere-helix':
                case 'rippled-surface':
                    type = 1 /* Collection */;
                    var sceneGraphGenerator = new Scene.sceneGraphGeneratorMap[data.type]();
                    value = sceneGraphGenerator.generateSceneGraphFromData(data.value, this);
                    break;
            }
            return new RT.SceneGraph.Node(type, value);
        };
        Scene.loadFromFile = function (path, callback) {
            var request = new XMLHttpRequest();
            request.onload = function () {
                var data = JSON.parse(this.responseText);
                callback(new Scene(data));
            };
            request.open('GET', path, true);
            request.send();
        };
        Scene.materialProps = ['ambient', 'shininess', 'reflection', 'refraction', 'refractiveIndex'];
        Scene.sceneGraphGeneratorMap = {
            'menger-sponge': RT.MengerSponge,
            'mesh': RT.Mesh,
            'sphere-helix': RT.SphereHelix,
            'rippled-surface': RT.RippledSurface
        };
        return Scene;
    })();
    RT.Scene = Scene;
})(RT || (RT = {}));

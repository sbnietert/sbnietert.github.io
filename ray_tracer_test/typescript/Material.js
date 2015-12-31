/// <reference path="Color.ts" />
/// <reference path="GeometricObject.ts" />
/// <reference path="Vector.ts" />
/// <reference path="Utils.ts" />
var RT;
(function (RT) {
    var MaterialLighting = (function () {
        function MaterialLighting() {
            this.color = RT.Color.BLACK;
            this.ambient = 0.1;
            this.shininess = 100;
            this.reflection = 0;
            this.refraction = 0;
            this.refractiveIndex = 1.3;
        }
        return MaterialLighting;
    })();
    RT.MaterialLighting = MaterialLighting;
    var SimpleMaterial = (function () {
        function SimpleMaterial(lighting) {
            this.lighting = lighting;
        }
        SimpleMaterial.prototype.getLighting = function (geo, point) {
            return this.lighting;
        };
        return SimpleMaterial;
    })();
    RT.SimpleMaterial = SimpleMaterial;
    var Material;
    (function (Material) {
        var glassLighting = new MaterialLighting();
        glassLighting.refraction = 1;
        var glass = new SimpleMaterial(glassLighting);
        var mirrorLighting = new MaterialLighting();
        mirrorLighting.reflection = 1;
        var mirror = new SimpleMaterial(mirrorLighting);
        Material.PRESETS = {
            'glass': glass,
            'mirror': mirror
        };
    })(Material = RT.Material || (RT.Material = {}));
})(RT || (RT = {}));

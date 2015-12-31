/// <reference path="Color.ts" />
/// <reference path="GeometricObject.ts" />
/// <reference path="Vector.ts" />
/// <reference path="Material.ts" />
var __extends = (this && this.__extends) || function (d, b) {
    for (var p in b) if (b.hasOwnProperty(p)) d[p] = b[p];
    function __() { this.constructor = d; }
    d.prototype = b === null ? Object.create(b) : (__.prototype = b.prototype, new __());
};
var RT;
(function (RT) {
    var CheckeredMaterial = (function () {
        function CheckeredMaterial(lighting, color2) {
            this.lighting = lighting;
            this.color2 = color2;
            this.color1 = lighting.color;
        }
        CheckeredMaterial.prototype.getLighting = function (geo, point) {
            this.lighting.color = this.testPoint(point) ? this.color1 : this.color2;
            return this.lighting;
        };
        return CheckeredMaterial;
    })();
    RT.CheckeredMaterial = CheckeredMaterial;
    var XZCheckeredMaterial = (function (_super) {
        __extends(XZCheckeredMaterial, _super);
        function XZCheckeredMaterial() {
            _super.apply(this, arguments);
        }
        XZCheckeredMaterial.prototype.testPoint = function (point) {
            var x = Math.floor(point.x);
            var z = Math.floor(point.z);
            return (x + z) % 2 == 0;
        };
        return XZCheckeredMaterial;
    })(CheckeredMaterial);
    RT.XZCheckeredMaterial = XZCheckeredMaterial;
    var XZDiamondCheckeredMaterial = (function (_super) {
        __extends(XZDiamondCheckeredMaterial, _super);
        function XZDiamondCheckeredMaterial() {
            _super.apply(this, arguments);
        }
        XZDiamondCheckeredMaterial.prototype.testPoint = function (point) {
            var u = Math.floor(point.x - point.z);
            var v = Math.floor(point.x + point.z);
            return (u + v) % 2 == 0;
        };
        return XZDiamondCheckeredMaterial;
    })(CheckeredMaterial);
    RT.XZDiamondCheckeredMaterial = XZDiamondCheckeredMaterial;
})(RT || (RT = {}));

/// <reference path="GeometricObject.ts" />
/// <reference path="Material.ts" />
/// <reference path="Vector.ts" />
var __extends = (this && this.__extends) || function (d, b) {
    for (var p in b) if (b.hasOwnProperty(p)) d[p] = b[p];
    function __() { this.constructor = d; }
    d.prototype = b === null ? Object.create(b) : (__.prototype = b.prototype, new __());
};
var RT;
(function (RT) {
    // this is generic so the scene graph maker can know if scene object shapes are boundable
    var GenericSceneObject = (function () {
        function GenericSceneObject(geometry, material) {
            this.geometry = geometry;
            this.material = material;
        }
        GenericSceneObject.prototype.getMaterialLighting = function (point) {
            return this.material.getLighting(this.geometry, point);
        };
        GenericSceneObject.prototype.getGeometry = function () {
            return this.geometry;
        };
        return GenericSceneObject;
    })();
    RT.GenericSceneObject = GenericSceneObject;
    var SceneObject = (function (_super) {
        __extends(SceneObject, _super);
        function SceneObject() {
            _super.apply(this, arguments);
        }
        return SceneObject;
    })(GenericSceneObject);
    RT.SceneObject = SceneObject;
})(RT || (RT = {}));

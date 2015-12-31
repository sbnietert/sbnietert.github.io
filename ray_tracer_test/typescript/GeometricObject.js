/// <reference path="Vector.ts" />
/// <reference path="SceneObject.ts" />
var __extends = (this && this.__extends) || function (d, b) {
    for (var p in b) if (b.hasOwnProperty(p)) d[p] = b[p];
    function __() { this.constructor = d; }
    d.prototype = b === null ? Object.create(b) : (__.prototype = b.prototype, new __());
};
var RT;
(function (RT) {
    RT.EPSILON = 0.000001;
    var Ray = (function () {
        function Ray(origin, direction) {
            this.origin = origin;
            this.direction = direction;
        }
        Ray.prototype.inchForward = function () {
            this.origin.add(this.direction.scaledBy(RT.EPSILON));
        };
        return Ray;
    })();
    RT.Ray = Ray;
    var BasicRayIntersection = (function () {
        function BasicRayIntersection() {
        }
        return BasicRayIntersection;
    })();
    RT.BasicRayIntersection = BasicRayIntersection;
    var RayIntersection = (function (_super) {
        __extends(RayIntersection, _super);
        function RayIntersection() {
            _super.apply(this, arguments);
            this.object = null;
        }
        return RayIntersection;
    })(BasicRayIntersection);
    RT.RayIntersection = RayIntersection;
    var GeometricObject = (function () {
        function GeometricObject() {
        }
        GeometricObject.prototype.findNormal = function (intersection) {
            var normal = this.calculateNormal(intersection);
            // ensure that normal vector is directed towards ray source
            // (this results in double-sided surfaces)
            if (normal.dot(intersection.incident) < 0)
                return normal;
            return normal.scaledBy(-1);
        };
        return GeometricObject;
    })();
    RT.GeometricObject = GeometricObject;
    var SimpleGeometricObject = (function (_super) {
        __extends(SimpleGeometricObject, _super);
        function SimpleGeometricObject() {
            _super.apply(this, arguments);
        }
        SimpleGeometricObject.prototype.obstructsShadowRay = function (shadowRay, distToLight) {
            var intersection = new BasicRayIntersection();
            return this.intersectsRay(shadowRay, intersection) && intersection.t < distToLight;
        };
        return SimpleGeometricObject;
    })(GeometricObject);
    RT.SimpleGeometricObject = SimpleGeometricObject;
})(RT || (RT = {}));

/// <reference path="Vector.ts" />
/// <reference path="GeometricObject.ts" />
var __extends = (this && this.__extends) || function (d, b) {
    for (var p in b) if (b.hasOwnProperty(p)) d[p] = b[p];
    function __() { this.constructor = d; }
    d.prototype = b === null ? Object.create(b) : (__.prototype = b.prototype, new __());
};
var RT;
(function (RT) {
    var Plane = (function (_super) {
        __extends(Plane, _super);
        function Plane(normal, offset) {
            _super.call(this);
            this.normal = normal;
            this.offset = offset;
        }
        Plane.prototype.intersectsRay = function (ray, intersection) {
            var u = this.normal.scaledBy(-this.offset).minus(ray.origin);
            var denominator = ray.direction.dot(this.normal);
            if (denominator == 0)
                return false;
            intersection.t = u.dot(this.normal) / denominator;
            if (intersection.t < 0)
                return false;
            return true;
        };
        Plane.prototype.calculateNormal = function (intersection) {
            return this.normal;
        };
        return Plane;
    })(RT.SimpleGeometricObject);
    RT.Plane = Plane;
})(RT || (RT = {}));

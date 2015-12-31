/// <reference path="Vector.ts" />
/// <reference path="GeometricObject.ts" />
var __extends = (this && this.__extends) || function (d, b) {
    for (var p in b) if (b.hasOwnProperty(p)) d[p] = b[p];
    function __() { this.constructor = d; }
    d.prototype = b === null ? Object.create(b) : (__.prototype = b.prototype, new __());
};
var RT;
(function (RT) {
    var Sphere = (function (_super) {
        __extends(Sphere, _super);
        function Sphere(center, radius) {
            _super.call(this);
            this.center = center;
            this.radius = radius;
        }
        Sphere.prototype.intersectsRay = function (ray, intersection) {
            var temp = ray.origin.minus(this.center);
            var B = ray.direction.dot(temp) * 2;
            var C = temp.dot(temp) - this.radius * this.radius;
            // solve for t using the quadratic formula
            var discriminant = B * B - 4 * C;
            if (discriminant < 0)
                return false;
            // intersects line
            var t0 = (-B + Math.sqrt(discriminant)) / 2;
            var t1 = (-B - Math.sqrt(discriminant)) / 2;
            if (t0 < 0 && t1 < 0)
                return false;
            // intersects ray
            if (t0 < 0)
                intersection.t = t1;
            else if (t1 < 0)
                intersection.t = t0;
            else
                intersection.t = Math.min(t0, t1);
            return true;
        };
        Sphere.prototype.getAxisAlignedBoundaryPoints = function () {
            var points = new Array(6);
            for (var i = 0; i < 6; i++)
                points[i] = this.center.copy();
            points[0].x += this.radius;
            points[1].x -= this.radius;
            points[2].y += this.radius;
            points[3].y -= this.radius;
            points[4].z += this.radius;
            points[5].z -= this.radius;
            return points;
        };
        Sphere.prototype.getReferencePoint = function () {
            return this.center;
        };
        Sphere.prototype.calculateNormal = function (intersection) {
            return intersection.point.minus(this.center).scaledBy(1 / this.radius);
        };
        return Sphere;
    })(RT.SimpleGeometricObject);
    RT.Sphere = Sphere;
})(RT || (RT = {}));

/// <reference path="Vector.ts" />
/// <reference path="GeometricObject.ts" />
var __extends = (this && this.__extends) || function (d, b) {
    for (var p in b) if (b.hasOwnProperty(p)) d[p] = b[p];
    function __() { this.constructor = d; }
    d.prototype = b === null ? Object.create(b) : (__.prototype = b.prototype, new __());
};
var RT;
(function (RT) {
    // infinite right cylinder, let's not get too complicated
    var Cylinder = (function (_super) {
        __extends(Cylinder, _super);
        function Cylinder(axis, radius) {
            _super.call(this);
            this.axis = axis;
            this.radius = radius;
        }
        Cylinder.prototype.intersectsRay = function (ray, intersection) {
            var vr = ray.direction;
            var vc = this.axis.direction;
            var dp = ray.origin.minus(this.axis.origin);
            var temp = vr.minus(vc.scaledBy(vr.dot(vc)));
            var temp2 = dp.minus(vc.scaledBy(dp.dot(vc)));
            var A = temp.dot(temp);
            var B = 2 * temp.dot(temp2);
            var C = temp2.dot(temp2) - this.radius * this.radius;
            var discriminant = B * B - 4 * A * C;
            // solve for t using the quadratic formula
            if (discriminant < 0)
                return false;
            var t0 = (-B + Math.sqrt(discriminant)) / (2 * A);
            var t1 = (-B - Math.sqrt(discriminant)) / (2 * A);
            if (t0 < 0 && t1 < 0)
                return false;
            if (t0 < 0)
                intersection.t = t1;
            else if (t1 < 0)
                intersection.t = t0;
            else
                intersection.t = Math.min(t0, t1);
            return true;
        };
        Cylinder.prototype.calculateNormal = function (intersection) {
            var diff = intersection.point.minus(this.axis.origin);
            return diff.minus(this.axis.direction.scaledBy(diff.dot(this.axis.direction))).normalize();
        };
        return Cylinder;
    })(RT.SimpleGeometricObject);
    RT.Cylinder = Cylinder;
})(RT || (RT = {}));

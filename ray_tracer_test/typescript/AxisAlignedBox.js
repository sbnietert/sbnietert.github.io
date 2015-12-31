/// <reference path="Vector.ts" />
/// <reference path="GeometricObject.ts" />
var __extends = (this && this.__extends) || function (d, b) {
    for (var p in b) if (b.hasOwnProperty(p)) d[p] = b[p];
    function __() { this.constructor = d; }
    d.prototype = b === null ? Object.create(b) : (__.prototype = b.prototype, new __());
};
var RT;
(function (RT) {
    var AxisAlignedBox = (function (_super) {
        __extends(AxisAlignedBox, _super);
        // create box given two opposite corners of an axis-aligned box
        function AxisAlignedBox(ll, ur) {
            _super.call(this);
            this.ll = ll;
            this.ur = ur;
        }
        // help from http://gamedev.stackexchange.com/questions/18436/most-efficient-aabb-vs-ray-collision-algorithms
        // a bit of copy and paste, but speed is essential here, and function calls would slow this down
        AxisAlignedBox.prototype.intersectsRay = function (ray, intersection) {
            var t1 = (this.ll.x - ray.origin.x) / ray.direction.x;
            var t2 = (this.ur.x - ray.origin.x) / ray.direction.x;
            var t3 = (this.ll.y - ray.origin.y) / ray.direction.y;
            var t4 = (this.ur.y - ray.origin.y) / ray.direction.y;
            var t5 = (this.ll.z - ray.origin.z) / ray.direction.z;
            var t6 = (this.ur.z - ray.origin.z) / ray.direction.z;
            var t12min;
            var t12minIndex;
            var t12max;
            var t12maxIndex;
            if (t1 < t2) {
                t12min = t1;
                t12minIndex = 1;
                t12max = t2;
                t12maxIndex = 2;
            }
            else {
                t12min = t2;
                t12minIndex = 2;
                t12max = t1;
                t12maxIndex = 1;
            }
            var t34min;
            var t34minIndex;
            var t34max;
            var t34maxIndex;
            if (t3 < t4) {
                t34min = t3;
                t34minIndex = 3;
                t34max = t4;
                t34maxIndex = 4;
            }
            else {
                t34min = t4;
                t34minIndex = 4;
                t34max = t3;
                t34maxIndex = 3;
            }
            var t56min;
            var t56minIndex;
            var t56max;
            var t56maxIndex;
            if (t5 < t6) {
                t56min = t5;
                t56minIndex = 5;
                t56max = t6;
                t56maxIndex = 6;
            }
            else {
                t56min = t6;
                t56minIndex = 6;
                t56max = t5;
                t56maxIndex = 5;
            }
            var tmin;
            var tminIndex;
            if (t12min > t34min) {
                tmin = t12min;
                tminIndex = t12minIndex;
            }
            else {
                tmin = t34min;
                tminIndex = t34minIndex;
            }
            if (t56min > tmin) {
                tmin = t56min;
                tminIndex = t56minIndex;
            }
            var tmax;
            var tmaxIndex;
            if (t12max < t34max) {
                tmax = t12max;
                tmaxIndex = t12maxIndex;
            }
            else {
                tmax = t34max;
                tmaxIndex = t34maxIndex;
            }
            if (t56max < tmax) {
                tmax = t56max;
                tmaxIndex = t56maxIndex;
            }
            // if tmax < 0, ray (line) is intersecting AABB, but whole AABB is behind us
            // if tmin > tmax, ray doesn't intersect AABB
            if (tmax < 0 || tmin > tmax)
                return false;
            intersection.t = tmin;
            intersection.geometricData = tminIndex;
            return true;
        };
        AxisAlignedBox.prototype.calculateNormal = function (intersection) {
            return AxisAlignedBox.normals[intersection.geometricData - 1];
        };
        AxisAlignedBox.normals = [
            RT.Vector.i,
            RT.Vector.i.scale(-1),
            RT.Vector.j,
            RT.Vector.j.scale(-1),
            RT.Vector.k,
            RT.Vector.k.scale(-1)
        ];
        return AxisAlignedBox;
    })(RT.SimpleGeometricObject);
    RT.AxisAlignedBox = AxisAlignedBox;
})(RT || (RT = {}));

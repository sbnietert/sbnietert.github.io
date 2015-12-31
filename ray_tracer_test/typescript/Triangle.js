/// <reference path="Vector.ts" />
/// <reference path="GeometricObject.ts" />
/// <reference path="SceneGraph.ts" />
var __extends = (this && this.__extends) || function (d, b) {
    for (var p in b) if (b.hasOwnProperty(p)) d[p] = b[p];
    function __() { this.constructor = d; }
    d.prototype = b === null ? Object.create(b) : (__.prototype = b.prototype, new __());
};
var RT;
(function (RT) {
    var Triangle = (function (_super) {
        __extends(Triangle, _super);
        function Triangle(A, B, C) {
            _super.call(this);
            this.A = A;
            this.B = B;
            this.C = C;
            this.normalA = null;
            this.normalB = null;
            this.normalC = null;
            this.AB = B.minus(A);
            this.AC = C.minus(A);
            this.normal = this.AB.cross(this.AC).normalize();
        }
        Triangle.prototype.enableNormalInterpolation = function (nA, nB, nC) {
            this.normalA = nA;
            this.normalB = nB;
            this.normalC = nC;
        };
        Triangle.prototype.intersectsRay = function (ray, intersection) {
            var pvec = ray.direction.cross(this.AC);
            var det = this.AB.dot(pvec);
            if (Math.abs(det) < RT.EPSILON)
                return false;
            var invDet = 1 / det;
            var tvec = ray.origin.minus(this.A);
            var u = tvec.dot(pvec) * invDet;
            if (u < 0 || u > 1)
                return false;
            var qvec = tvec.cross(this.AB);
            var v = ray.direction.dot(qvec) * invDet;
            if (v < 0 || u + v > 1)
                return false;
            intersection.u = u;
            intersection.v = v;
            intersection.t = this.AC.dot(qvec) * invDet;
            return intersection.t >= 0;
        };
        Triangle.prototype.getAxisAlignedBoundaryPoints = function () {
            return [this.A, this.B, this.C];
        };
        Triangle.prototype.getReferencePoint = function () {
            return this.A;
        };
        Triangle.prototype.calculateNormal = function (intersection) {
            if (this.normalA == null)
                return this.normal;
            // normal interpolation enabled
            var weightedA = this.normalA.scaledBy(1 - intersection.u - intersection.v);
            var weightedB = this.normalB.scaledBy(intersection.u);
            var weightedC = this.normalC.scaledBy(intersection.v);
            return weightedA.plus(weightedB.plus(weightedC));
        };
        return Triangle;
    })(RT.SimpleGeometricObject);
    RT.Triangle = Triangle;
})(RT || (RT = {}));

/// <reference path="Color.ts" />
/// <reference path="Vector.ts" />
/// <reference path="Background.ts" />
var RT;
(function (RT) {
    var PhiGradientBackground = (function () {
        function PhiGradientBackground(color1, color2, n, axis) {
            this.color1 = color1;
            this.color2 = color2;
            this.n = n;
            this.axis = axis;
            this.c = Math.pow(2, n - 1);
        }
        PhiGradientBackground.prototype.oddpow = function (t) {
            return Math.pow(Math.abs(t), this.n + 1) / t;
        };
        PhiGradientBackground.prototype.getColor = function (direction) {
            var rho = direction.length();
            var cosPhi = direction.dot(this.axis) / rho;
            var t = (cosPhi + 1) / 2;
            var t2;
            if (t < 0.5)
                t2 = this.c * this.oddpow(t);
            else
                t2 = 1 + this.c * this.oddpow(t - 1);
            return this.color1.plus(this.color2.minus(this.color1).scaledBy(t2));
        };
        return PhiGradientBackground;
    })();
    RT.PhiGradientBackground = PhiGradientBackground;
})(RT || (RT = {}));

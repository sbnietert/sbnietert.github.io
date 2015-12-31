/// <reference path="Color.ts" />
/// <reference path="Vector.ts" />
var RT;
(function (RT) {
    var SolidColorBackground = (function () {
        function SolidColorBackground(color) {
            this.color = color;
        }
        SolidColorBackground.prototype.getColor = function (direction) {
            return this.color;
        };
        return SolidColorBackground;
    })();
    RT.SolidColorBackground = SolidColorBackground;
})(RT || (RT = {}));

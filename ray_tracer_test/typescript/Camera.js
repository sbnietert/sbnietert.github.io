/// <reference path="Vector.ts" />
/// <reference path="GeometricObject.ts" />
var RT;
(function (RT) {
    // camera class with necessary information and methods to generate rays from eye point to image plane
    // (plane is a bit of a misnomer, since it has a width and height)
    var Camera = (function () {
        function Camera(pose, up, focalLength, pixelWidth, pixelHeight) {
            this.eye = pose.origin;
            this.up = up;
            this.pixelWidth = pixelWidth;
            this.pixelHeight = pixelHeight;
            this.imagePlaneCenter = pose.origin.plus(pose.direction.scaledBy(focalLength));
            this.right = up.cross(pose.direction); // orthogonal to up and "out" vectors
            this.resize();
        }
        Object.defineProperty(Camera.prototype, "pixelWidth", {
            get: function () { return this._pixelWidth; },
            set: function (w) {
                this._pixelWidth = w;
                this.resize();
            },
            enumerable: true,
            configurable: true
        });
        ;
        Object.defineProperty(Camera.prototype, "pixelHeight", {
            get: function () { return this._pixelHeight; },
            set: function (h) {
                this._pixelHeight = h;
                this.resize();
            },
            enumerable: true,
            configurable: true
        });
        ;
        ;
        ;
        Camera.prototype.resize = function () {
            // set the smaller of the dimensions equal to one unit in the scene space
            if (this.pixelHeight < this.pixelWidth) {
                this.imagePlaneHeight = 1;
                this.imagePlaneWidth = this.pixelWidth / this.pixelHeight;
            }
            else {
                this.imagePlaneWidth = 1;
                this.imagePlaneHeight = this.pixelHeight / this.pixelWidth;
            }
        };
        // generate ray from eye point to point on image plane corresponding to location in image space
        // (row and col can be fractional to allow for subpixel sampling)
        Camera.prototype.generateRay = function (row, col) {
            var rightCoefficient = (col - this.pixelWidth / 2) / this.pixelWidth * this.imagePlaneWidth;
            var upCoefficient = (this.pixelHeight / 2 - row) / this.pixelHeight * this.imagePlaneHeight;
            var right = this.right.scaledBy(rightCoefficient);
            var up = this.up.scaledBy(upCoefficient);
            var target = this.imagePlaneCenter.plus(right).plus(up);
            var direction = target.minus(this.eye).normalize();
            return new RT.Ray(this.eye, direction);
        };
        return Camera;
    })();
    RT.Camera = Camera;
})(RT || (RT = {}));

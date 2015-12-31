var RT;
(function (RT) {
    // class storing point in color space using red, green, and blue components ranging from 0 to 1
    var Color = (function () {
        function Color(r, g, b) {
            this.r = r;
            this.g = g;
            this.b = b;
        }
        Object.defineProperty(Color, "BLACK", {
            get: function () { return new Color(0, 0, 0); },
            enumerable: true,
            configurable: true
        });
        ;
        Object.defineProperty(Color, "WHITE", {
            get: function () { return new Color(1, 1, 1); },
            enumerable: true,
            configurable: true
        });
        ;
        // create a color by calculating RGB components given hue, saturation, and lightness
        // HSL conversion algorithm found at http://www.geekymonkey.com/Programming/CSharp/RGB2HSL_HSL2RGB.htm
        Color.fromHSL = function (h, sl, l) {
            var r = l; // default to gray
            var g = l;
            var b = l;
            var v = (l <= 0.5) ? (l * (1.0 + sl)) : (l + sl - l * sl);
            if (v > 0) {
                var m = l + l - v;
                var sv = (v - m) / v;
                h *= 6.0;
                var sextant = Math.floor(h);
                var fract = h - sextant;
                var vsf = v * sv * fract;
                var mid1 = m + vsf;
                var mid2 = v - vsf;
                switch (sextant) {
                    case 0:
                        r = v;
                        g = mid1;
                        b = m;
                        break;
                    case 1:
                        r = mid2;
                        g = v;
                        b = m;
                        break;
                    case 2:
                        r = m;
                        g = v;
                        b = mid1;
                        break;
                    case 3:
                        r = m;
                        g = mid2;
                        b = v;
                        break;
                    case 4:
                        r = mid1;
                        g = m;
                        b = v;
                        break;
                    case 5:
                        r = v;
                        g = m;
                        b = mid2;
                        break;
                }
            }
            return new Color(r, g, b);
        };
        Color.prototype.copy = function () {
            return new Color(this.r, this.g, this.b);
        };
        Color.prototype.add = function (c) {
            this.r += c.r;
            this.g += c.g;
            this.b += c.b;
            return this;
        };
        Color.prototype.subtract = function (c) {
            this.r -= c.r;
            this.g -= c.g;
            this.b -= c.b;
            return this;
        };
        Color.prototype.scale = function (c) {
            this.r *= c;
            this.g *= c;
            this.b *= c;
            return this;
        };
        Color.prototype.multiplyBy = function (c) {
            this.r *= c.r;
            this.g *= c.g;
            this.b *= c.b;
            return this;
        };
        // restrict color components to values <= 1
        Color.prototype.cap = function () {
            this.r = Math.min(1, this.r);
            this.g = Math.min(1, this.g);
            this.b = Math.min(1, this.b);
            return this;
        };
        Color.prototype.plus = function (v) {
            return this.copy().add(v);
        };
        Color.prototype.minus = function (v) {
            return this.copy().subtract(v);
        };
        Color.prototype.scaledBy = function (c) {
            return this.copy().scale(c);
        };
        Color.prototype.times = function (c) {
            return this.copy().multiplyBy(c);
        };
        Color.prototype.toString = function () {
            var r = Math.floor(this.r * 255);
            var g = Math.floor(this.g * 255);
            var b = Math.floor(this.b * 255);
            return 'rgb(' + r + ',' + g + ',' + b + ')';
        };
        return Color;
    })();
    RT.Color = Color;
})(RT || (RT = {}));

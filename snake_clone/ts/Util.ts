module Snake {
    export class Util {
        public static randColor(): string {
            var hue = Math.floor(Math.random() * 360);
            return 'hsl(' + hue + ', 90%, 50%)';
        }
    }
}
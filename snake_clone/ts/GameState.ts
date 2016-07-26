module Snake {
    export abstract class GameState {
        protected ctx: GameContext;

        constructor(ctx: GameContext) {
            this.ctx = ctx;
            this.randomizeBorderColors();
        }

        protected fillScreen(color: string): void {
            this.ctx.g2D.fillStyle = color;
            this.ctx.g2D.fillRect(0, 0, this.ctx.width, this.ctx.height);
        }

        protected drawSquare(loc: number[], color: string): void {
            this.ctx.g2D.fillStyle = color;
            this.ctx.g2D.fillRect(loc[1] * this.ctx.tileSize, loc[0] * this.ctx.tileSize, this.ctx.tileSize, this.ctx.tileSize);
        }

        protected drawArt(art: string[], rowOffset: number, colOffset: number, color: string): void {
            for(var i = 0; i < art.length; i++) {
                for(var j = 0; j < art[i].length; j++) {
                    if(art[i][j] != ' ')
                        this.drawSquare([rowOffset + i, colOffset + j], color);
                }
            }
        }

        protected drawCenteredArt(art: string[], color: string) {
             var rowOffset = Math.floor((this.ctx.rows - art.length)/2);
             var colOffset = Math.floor((this.ctx.cols - art[0].length)/2);
             this.drawArt(art, rowOffset, colOffset, color);
        }

        private borderColors: string[] = [];

        protected randomizeBorderColors(): void {
            var c = 0;

            for(var i = 0; i < this.ctx.rows; i++, c += 2) {
                this.borderColors[c] = Util.randColor();
                this.borderColors[c+1] = Util.randColor();
            }
            
            for(var j = 0; j < this.ctx.cols; j++, c += 2) {
                this.borderColors[c] = Util.randColor();
                this.borderColors[c+1] = Util.randColor();
            }
        }

        protected drawBorder(type = 'checker'): void {
            var c = 0;

            for(var i = 0; i < this.ctx.rows; i++, c += 2) {

                var color1: string;
                var color2: string;
                if(type == 'colorful') {
                    color1 = this.borderColors[c];
                    color2 = this.borderColors[c+1];
                } else if (type == 'checker') {
                    color1 = (i % 2) ? 'grey' : 'lightgrey';
                    color2 = ((this.ctx.cols - 1 + i) % 2) ? 'grey' : 'lightgrey';
                } else {
                    color1 = color2 = type;
                }

                this.drawSquare([i, 0], color1);
                this.drawSquare([i, this.ctx.cols - 1], color2);
            }
            
            for(var j = 0; j < this.ctx.cols; j++, c += 2) {

                var color1: string;
                var color2: string;
                if(type == 'colorful') {
                    color1 = this.borderColors[c];
                    color2 = this.borderColors[c+1];
                } else if (type == 'checker') {
                    color1 = (j % 2) ? 'grey' : 'lightgrey';
                    color2 = ((this.ctx.rows - 1 + j) % 2) ? 'grey' : 'lightgrey';
                } else {
                    color1 = color2 = type;
                }

                this.drawSquare([0, j], color1);
                this.drawSquare([this.ctx.rows - 1, j], color2);
            }
        }

        protected drawText(text: string, row: number, col: number, color: string) {
            var g = this.ctx.g2D;
            g.font = '50px VT323';
            g.textBaseline = 'top';
            g.fillStyle = color;
            g.fillText(text, col * this.ctx.tileSize, row * this.ctx.tileSize);
        }
        
        private lastUpdated = Date.now();
        protected minTimePerFrame = 0;
        public update(): void {
            if(Date.now() - this.lastUpdated > this.minTimePerFrame) {
                this.advanceFrame();
                this.draw();
                this.lastUpdated = Date.now();
            }
        }

        public advanceFrame(): void {};
        public abstract draw(): void;

        public start(): void {};
    }
}
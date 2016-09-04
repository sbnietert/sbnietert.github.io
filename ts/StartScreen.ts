module Snake {
    export class StartScreen extends GameState {
        public static Name = 'start';
        private nameArt: string[] = [
            ' oooo o                     ',
            'o     o                     ',
            'o     o oooo oooo oooo      ',
            ' ooo  o o  o    o o  o      ',
            '    o o o  o oooo o  o      ',
            '    o o o  o o  o o  o      ',
            'oooo  o oooo oooo o  o      ',
            '                            ',
            'o   o o       o           o ',
            'oo  o         o           o ',
            'o o o o oooo ooo oooo o  ooo',
            'o o o o o  o  o  o  o ooo o ',
            'o o o o oooo  o  oooo o   o ',
            'o  oo o o     o  o    o   o ',
            'o   o o oooo  o  oooo o   o '
        ];

        private artRows = this.nameArt.length;
        private artCols = this.nameArt[0].length;
        private artRowOffset: number;
        private artColOffset: number;

        constructor(ctx: GameContext) {
            super(ctx);
            this.artRowOffset = Math.floor((ctx.rows - this.artRows)/2);
            this.artColOffset = this.artRowOffset;
            this.minTimePerFrame = 250;
        }

        public advanceFrame(): void {
            var mouseLoc = this.ctx.input.getMouseLoc();
            var mouseRow = Math.floor(mouseLoc[1] / this.ctx.tileSize);
            var mouseCol = Math.floor(mouseLoc[0] / this.ctx.tileSize);
            if(this.ctx.input.isMouseOver())
                this.randomizeBorderColors();
        }

        public draw(): void {
            this.fillScreen('white');
            this.drawBorder('colorful');
            this.drawArt(this.nameArt, this.artRowOffset, this.artColOffset, 'black');
            
        }

        public start(): void {
            this.ctx.input.addCustomListener('click', () => {
                this.ctx.switchState(CountDownScreen.Name);
            });
        }
    }
}
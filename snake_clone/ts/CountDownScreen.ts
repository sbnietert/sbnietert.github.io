/// <reference path="GameState.ts" />

module Snake {
    export class CountDownScreen extends GameState {
        public static Name = 'count down';
        private numberArt: string[][] = [[
            'oooo',
            '   o',
            '   o',
            'oooo',
            '   o',
            '   o',
            'oooo'
        ],[
            'oooo',
            '   o',
            '   o',
            'oooo',
            'o   ',
            'o   ',
            'oooo'
        ],[
            '  o ',
            ' oo ',
            '  o ',
            '  o ',
            '  o ',
            '  o ',
            ' ooo'
        ]];
        private currentArt: number;
        private startTime: number;

        public advanceFrame(): void {
            var elapsedSecs = Math.floor((Date.now() - this.startTime)/1000);
            if(elapsedSecs > 2) {
                this.ctx.switchState(PlayScreen.Name);
            } else this.currentArt = elapsedSecs; 
        }

        public draw(): void {
            this.fillScreen('white');
            this.drawCenteredArt(this.numberArt[this.currentArt], 'black');
        }

        public start(): void {
            this.startTime = Date.now();
        }
    }
}
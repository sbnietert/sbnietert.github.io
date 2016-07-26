/// <reference path="GameState.ts" />

module Snake {
    export class GameOverScreen extends GameState {
        public static Name = 'game over';

        private gameOverArt: string[] = [
            'ooooo                  ooooo                 ',
            'o                      o   o                 ',
            'o     oooo ooooo oooo  o   o o   o oooo oooo',
            'o  oo    o o o o o  o  o   o o   o o  o o    ',
            'o   o oooo o o o oooo  o   o o   o oooo o    ',
            'o   o o  o o o o o     o   o  o o  o    o    ',
            'ooooo oooo o o o oooo  ooooo   o   oooo o    ',
            '                                             ',
            '                                             ',
            '                                             '
        ];
        private snake: number[][];

        public advanceFrame(): void {
            
        }

        public draw(): void {
            this.fillScreen('black');
            this.drawBorder('red');

            for(var i = 0; i < this.snake.length; i++) {
                this.drawSquare(this.snake[i], 'darkred');
            }

            this.drawCenteredArt(this.gameOverArt, 'red');
            this.drawText('Score: ' + this.snake.length, 15, 15, 'red');
        }

        public start(): void {
            this.snake = <number[][]> this.ctx.sharedData;
            setTimeout(() => {
                this.ctx.switchState(StartScreen.Name);
            }, 3000);
        }
    }
}
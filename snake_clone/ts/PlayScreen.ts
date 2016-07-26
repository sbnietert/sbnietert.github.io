/// <reference path="GameState.ts" />

module Snake {
    export class PlayScreen extends GameState {
        public static Name = 'play';

        private snake: number[][];
        private powerup: number[];
        private direction: string;
        private lastMove: string;

        private randi(a, b): number {
            return Math.floor(a + (b-a+1)*Math.random());
        }

        private sameloc(a, b): boolean {
            return a[0] == b[0] && a[1] == b[1];
        }

        private randloc(): number[] {
            var loc = [this.randi(1, this.ctx.rows-2), this.randi(1, this.ctx.cols-2)];
            for(var i = 0; i < this.snake.length; i++) {
                    var snake_segment = this.snake[i];
                if(this.sameloc(loc, snake_segment))
                    return this.randloc();
            }
            return loc;
        }

        private die(): void {
            this.ctx.sharedData = this.snake;
            this.ctx.switchState(GameOverScreen.Name);
        }

        public advanceFrame(): void {

            var head = this.snake[this.snake.length - 1];
            head = head.slice();
            var changeRow = this.direction == 'u' || this.direction == 'd';
            var increment = this.direction == 'r' || this.direction == 'd';
            head[changeRow ? 0 : 1] += increment ? 1 : -1;
            
            if(head[0] == 0 || head[0] == this.ctx.rows - 1 || head[1] == 0 || head[1] == this.ctx.cols - 1) {
                this.die();
                return;
            }

            for(var i = 0; i < this.snake.length-1; i++) {
                if(this.sameloc(this.snake[i], head)) {
                    this.die();
                    return;
                }
            }
            
            this.snake.push(head);
            this.lastMove = this.direction;

            if(this.sameloc(head, this.powerup)) {
                this.powerup = this.randloc();
                if(this.minTimePerFrame > 50)
                    this.minTimePerFrame -= 25;
            } else this.snake.shift();
        }

        public draw(): void {
            this.fillScreen('black');
            this.drawBorder('checker');

            for(var i = 0; i < this.snake.length; i++) {
                this.drawSquare(this.snake[i], 'white');
            }
            this.drawSquare(this.powerup, 'yellow');
        }

        private keyBindings: { [key: string]: string } = {
            37: 'l',
            38: 'u',
            39: 'r',
            40: 'd'
        };
        private forbidden: { [dir: string]: string } = {
            'l': 'r',
            'r': 'l',
            'u': 'd',
            'd': 'u'
        };
        public start(): void {
            this.minTimePerFrame = 200;
            this.snake = [[Math.floor(this.ctx.rows/2), Math.floor(this.ctx.cols/2)]];
            this.direction = 'l';
            this.powerup = this.randloc();

            this.ctx.input.addCustomKeyListener((keyCode: number) => {
                var pressed = this.keyBindings[keyCode];
                if(pressed && this.forbidden[this.lastMove] != pressed)
               	    this.direction = pressed;
            });
        }
    }
}
module Snake {
    export class GameContext {
        rows = 23;
        cols = 70;
        tileSize = 10;
        width = this.cols * this.tileSize;
        height = this.rows * this.tileSize;

        currState: string;
        sharedData: Object;
        
        input: Input;
        g2D: CanvasRenderingContext2D;

        constructor(private stateSwitcher: Function) {}

        public switchState(newState: string): void {
            this.stateSwitcher(newState, this);
        }
    };

    export class GameRunner {
        private states : { [type: string]: GameState } = {};
        private ctx = new GameContext((newState: string, ctx: GameContext) => {
            ctx.input.clearCustomListeners();
            ctx.currState = newState;
            this.states[newState].start();
        });

        constructor(private canvas: HTMLCanvasElement) {
            canvas.width = this.ctx.width;
            canvas.height = this.ctx.height;
            this.ctx.g2D = canvas.getContext('2d');

            this.ctx.input = new Input();
            this.ctx.input.addDefaultListeners(canvas);
            this.states[StartScreen.Name] = new StartScreen(this.ctx);
            this.states[CountDownScreen.Name] = new CountDownScreen(this.ctx);
            this.states[PlayScreen.Name] = new PlayScreen(this.ctx);
            this.states[GameOverScreen.Name] = new GameOverScreen(this.ctx);
            this.ctx.currState = StartScreen.Name;
            this.states[StartScreen.Name].start();
        }

        public run() : void {
            this.states[this.ctx.currState].update();
            requestAnimationFrame(() => { this.run(); });
        }
    };
}
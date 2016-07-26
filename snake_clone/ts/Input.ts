module Snake {
    export class Input {
        public static LEFT = 37;
        public static UP = 38;
        public static RIGHT = 39;
        public static DOWN = 40;

        private keyLog : { [code: number]: boolean } = {};
        private mouseOver: boolean;
        private mouseX: number;
        private mouseY: number;
        private listeners: { event: string, callback: EventListener }[] = [];
        private keyListeners: EventListener[] = [];
        private element: HTMLElement;

        public addDefaultListeners(el: HTMLElement): void {
            this.element = el;

            document.addEventListener('keydown', (e: KeyboardEvent) => {
                this.keyLog[e.keyCode] = true;
            });
            document.addEventListener('keyup', (e: KeyboardEvent) => {
                this.keyLog[e.keyCode] = false;
            });

            el.addEventListener('mouseenter', () => { this.mouseOver = true; });
            el.addEventListener('mouseleave', () => { this.mouseOver = false; });
            el.addEventListener('mousemove', (e: MouseEvent) => {
                this.mouseX = e.clientX - el.offsetLeft;
                this.mouseY = e.clientY - el.offsetTop;
            });
        }

        public addCustomListener(event: string, callback: EventListener) {
            this.element.addEventListener(event, callback);
            this.listeners.push({ event: event, callback: callback });
        }

        public addCustomKeyListener(callback: Function) {
            var listener: EventListener = (e: KeyboardEvent) => { callback(e.keyCode); };
            document.addEventListener('keydown', listener);
            this.keyListeners.push(listener);
        }

        public clearCustomListeners() {
            for(var listener of this.listeners) {
                this.element.removeEventListener(listener.event, listener.callback);
            }
            for(var keyListener of this.keyListeners) {
                this.element.removeEventListener('keydown', keyListener);
            }
        }

        public isPressed(keyCode: number): boolean {
            return this.keyLog[keyCode];
        }

        public isMouseOver(): boolean { return this.mouseOver; }
        public getMouseLoc(): number[] { return [this.mouseX, this.mouseY]; }
    }
}
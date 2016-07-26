var Snake;
(function (Snake) {
    var GameState = (function () {
        function GameState(ctx) {
            this.borderColors = [];
            this.lastUpdated = Date.now();
            this.minTimePerFrame = 0;
            this.ctx = ctx;
            this.randomizeBorderColors();
        }
        GameState.prototype.fillScreen = function (color) {
            this.ctx.g2D.fillStyle = color;
            this.ctx.g2D.fillRect(0, 0, this.ctx.width, this.ctx.height);
        };
        GameState.prototype.drawSquare = function (loc, color) {
            this.ctx.g2D.fillStyle = color;
            this.ctx.g2D.fillRect(loc[1] * this.ctx.tileSize, loc[0] * this.ctx.tileSize, this.ctx.tileSize, this.ctx.tileSize);
        };
        GameState.prototype.drawArt = function (art, rowOffset, colOffset, color) {
            for (var i = 0; i < art.length; i++) {
                for (var j = 0; j < art[i].length; j++) {
                    if (art[i][j] != ' ')
                        this.drawSquare([rowOffset + i, colOffset + j], color);
                }
            }
        };
        GameState.prototype.drawCenteredArt = function (art, color) {
            var rowOffset = Math.floor((this.ctx.rows - art.length) / 2);
            var colOffset = Math.floor((this.ctx.cols - art[0].length) / 2);
            this.drawArt(art, rowOffset, colOffset, color);
        };
        GameState.prototype.randomizeBorderColors = function () {
            var c = 0;
            for (var i = 0; i < this.ctx.rows; i++, c += 2) {
                this.borderColors[c] = Snake.Util.randColor();
                this.borderColors[c + 1] = Snake.Util.randColor();
            }
            for (var j = 0; j < this.ctx.cols; j++, c += 2) {
                this.borderColors[c] = Snake.Util.randColor();
                this.borderColors[c + 1] = Snake.Util.randColor();
            }
        };
        GameState.prototype.drawBorder = function (type) {
            if (type === void 0) { type = 'checker'; }
            var c = 0;
            for (var i = 0; i < this.ctx.rows; i++, c += 2) {
                var color1;
                var color2;
                if (type == 'colorful') {
                    color1 = this.borderColors[c];
                    color2 = this.borderColors[c + 1];
                }
                else if (type == 'checker') {
                    color1 = (i % 2) ? 'grey' : 'lightgrey';
                    color2 = ((this.ctx.cols - 1 + i) % 2) ? 'grey' : 'lightgrey';
                }
                else {
                    color1 = color2 = type;
                }
                this.drawSquare([i, 0], color1);
                this.drawSquare([i, this.ctx.cols - 1], color2);
            }
            for (var j = 0; j < this.ctx.cols; j++, c += 2) {
                var color1;
                var color2;
                if (type == 'colorful') {
                    color1 = this.borderColors[c];
                    color2 = this.borderColors[c + 1];
                }
                else if (type == 'checker') {
                    color1 = (j % 2) ? 'grey' : 'lightgrey';
                    color2 = ((this.ctx.rows - 1 + j) % 2) ? 'grey' : 'lightgrey';
                }
                else {
                    color1 = color2 = type;
                }
                this.drawSquare([0, j], color1);
                this.drawSquare([this.ctx.rows - 1, j], color2);
            }
        };
        GameState.prototype.drawText = function (text, row, col, color) {
            var g = this.ctx.g2D;
            g.font = '50px VT323';
            g.textBaseline = 'top';
            g.fillStyle = color;
            g.fillText(text, col * this.ctx.tileSize, row * this.ctx.tileSize);
        };
        GameState.prototype.update = function () {
            if (Date.now() - this.lastUpdated > this.minTimePerFrame) {
                this.advanceFrame();
                this.draw();
                this.lastUpdated = Date.now();
            }
        };
        GameState.prototype.advanceFrame = function () { };
        ;
        GameState.prototype.start = function () { };
        ;
        return GameState;
    })();
    Snake.GameState = GameState;
})(Snake || (Snake = {}));
/// <reference path="GameState.ts" />
var __extends = (this && this.__extends) || function (d, b) {
    for (var p in b) if (b.hasOwnProperty(p)) d[p] = b[p];
    function __() { this.constructor = d; }
    d.prototype = b === null ? Object.create(b) : (__.prototype = b.prototype, new __());
};
var Snake;
(function (Snake) {
    var CountDownScreen = (function (_super) {
        __extends(CountDownScreen, _super);
        function CountDownScreen() {
            _super.apply(this, arguments);
            this.numberArt = [[
                    'oooo',
                    '   o',
                    '   o',
                    'oooo',
                    '   o',
                    '   o',
                    'oooo'
                ], [
                    'oooo',
                    '   o',
                    '   o',
                    'oooo',
                    'o   ',
                    'o   ',
                    'oooo'
                ], [
                    '  o ',
                    ' oo ',
                    '  o ',
                    '  o ',
                    '  o ',
                    '  o ',
                    ' ooo'
                ]];
        }
        CountDownScreen.prototype.advanceFrame = function () {
            var elapsedSecs = Math.floor((Date.now() - this.startTime) / 1000);
            if (elapsedSecs > 2) {
                this.ctx.switchState(Snake.PlayScreen.Name);
            }
            else
                this.currentArt = elapsedSecs;
        };
        CountDownScreen.prototype.draw = function () {
            this.fillScreen('white');
            this.drawBorder('black');
            this.drawCenteredArt(this.numberArt[this.currentArt], 'black');
        };
        CountDownScreen.prototype.start = function () {
            this.startTime = Date.now();
        };
        CountDownScreen.Name = 'count down';
        return CountDownScreen;
    })(Snake.GameState);
    Snake.CountDownScreen = CountDownScreen;
})(Snake || (Snake = {}));
/// <reference path="GameState.ts" />
var Snake;
(function (Snake) {
    var GameOverScreen = (function (_super) {
        __extends(GameOverScreen, _super);
        function GameOverScreen(ctx) {
            _super.call(this, ctx);
            this.gameOverArt = [
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
            this.drawText(' ', -1, -1, 'black');
        }
        GameOverScreen.prototype.advanceFrame = function () {
        };
        GameOverScreen.prototype.draw = function () {
            this.fillScreen('black');
            this.drawBorder('red');
            for (var i = 0; i < this.snake.length; i++) {
                this.drawSquare(this.snake[i], 'darkred');
            }
            this.drawCenteredArt(this.gameOverArt, 'red');
            this.drawText('Score: ' + this.snake.length, 15, 15, 'red');
        };
        GameOverScreen.prototype.start = function () {
            var _this = this;
            this.snake = this.ctx.sharedData;
            setTimeout(function () {
                _this.ctx.switchState(Snake.StartScreen.Name);
            }, 3000);
        };
        GameOverScreen.Name = 'game over';
        return GameOverScreen;
    })(Snake.GameState);
    Snake.GameOverScreen = GameOverScreen;
})(Snake || (Snake = {}));
var Snake;
(function (Snake) {
    var GameContext = (function () {
        function GameContext(stateSwitcher) {
            this.stateSwitcher = stateSwitcher;
            this.rows = 23;
            this.cols = 70;
            this.tileSize = 10;
            this.width = this.cols * this.tileSize;
            this.height = this.rows * this.tileSize;
        }
        GameContext.prototype.switchState = function (newState) {
            this.stateSwitcher(newState, this);
        };
        return GameContext;
    })();
    Snake.GameContext = GameContext;
    ;
    var GameRunner = (function () {
        function GameRunner(canvas) {
            var _this = this;
            this.canvas = canvas;
            this.states = {};
            this.ctx = new GameContext(function (newState, ctx) {
                ctx.input.clearCustomListeners();
                ctx.currState = newState;
                _this.states[newState].start();
            });
            canvas.width = this.ctx.width;
            canvas.height = this.ctx.height;
            this.ctx.g2D = canvas.getContext('2d');
            this.ctx.input = new Snake.Input();
            this.ctx.input.addDefaultListeners(canvas);
            this.states[Snake.StartScreen.Name] = new Snake.StartScreen(this.ctx);
            this.states[Snake.CountDownScreen.Name] = new Snake.CountDownScreen(this.ctx);
            this.states[Snake.PlayScreen.Name] = new Snake.PlayScreen(this.ctx);
            this.states[Snake.GameOverScreen.Name] = new Snake.GameOverScreen(this.ctx);
            this.ctx.currState = Snake.StartScreen.Name;
            this.states[Snake.StartScreen.Name].start();
        }
        GameRunner.prototype.run = function () {
            var _this = this;
            this.states[this.ctx.currState].update();
            requestAnimationFrame(function () { _this.run(); });
        };
        return GameRunner;
    })();
    Snake.GameRunner = GameRunner;
    ;
})(Snake || (Snake = {}));
var Snake;
(function (Snake) {
    var Input = (function () {
        function Input() {
            this.keyLog = {};
            this.listeners = [];
            this.keyListeners = [];
        }
        Input.prototype.addDefaultListeners = function (el) {
            var _this = this;
            this.element = el;
            document.addEventListener('keydown', function (e) {
                _this.keyLog[e.keyCode] = true;
            });
            document.addEventListener('keyup', function (e) {
                _this.keyLog[e.keyCode] = false;
            });
            el.addEventListener('mouseenter', function () { _this.mouseOver = true; });
            el.addEventListener('mouseleave', function () { _this.mouseOver = false; });
            el.addEventListener('mousemove', function (e) {
                _this.mouseX = e.clientX - el.offsetLeft;
                _this.mouseY = e.clientY - el.offsetTop;
            });
        };
        Input.prototype.addCustomListener = function (event, callback) {
            this.element.addEventListener(event, callback);
            this.listeners.push({ event: event, callback: callback });
        };
        Input.prototype.addCustomKeyListener = function (callback) {
            var listener = function (e) { callback(e.keyCode); };
            document.addEventListener('keydown', listener);
            this.keyListeners.push(listener);
        };
        Input.prototype.clearCustomListeners = function () {
            for (var _i = 0, _a = this.listeners; _i < _a.length; _i++) {
                var listener = _a[_i];
                this.element.removeEventListener(listener.event, listener.callback);
            }
            for (var _b = 0, _c = this.keyListeners; _b < _c.length; _b++) {
                var keyListener = _c[_b];
                this.element.removeEventListener('keydown', keyListener);
            }
        };
        Input.prototype.isPressed = function (keyCode) {
            return this.keyLog[keyCode];
        };
        Input.prototype.isMouseOver = function () { return this.mouseOver; };
        Input.prototype.getMouseLoc = function () { return [this.mouseX, this.mouseY]; };
        Input.LEFT = 37;
        Input.UP = 38;
        Input.RIGHT = 39;
        Input.DOWN = 40;
        return Input;
    })();
    Snake.Input = Input;
})(Snake || (Snake = {}));
/// <reference path="GameState.ts" />
var Snake;
(function (Snake) {
    var PlayScreen = (function (_super) {
        __extends(PlayScreen, _super);
        function PlayScreen() {
            _super.apply(this, arguments);
            this.keyBindings = {
                37: 'l',
                38: 'u',
                39: 'r',
                40: 'd'
            };
            this.forbidden = {
                'l': 'r',
                'r': 'l',
                'u': 'd',
                'd': 'u'
            };
        }
        PlayScreen.prototype.randi = function (a, b) {
            return Math.floor(a + (b - a + 1) * Math.random());
        };
        PlayScreen.prototype.sameloc = function (a, b) {
            return a[0] == b[0] && a[1] == b[1];
        };
        PlayScreen.prototype.randloc = function () {
            var loc = [this.randi(1, this.ctx.rows - 2), this.randi(1, this.ctx.cols - 2)];
            for (var i = 0; i < this.snake.length; i++) {
                var snake_segment = this.snake[i];
                if (this.sameloc(loc, snake_segment))
                    return this.randloc();
            }
            return loc;
        };
        PlayScreen.prototype.die = function () {
            this.ctx.sharedData = this.snake;
            this.ctx.switchState(Snake.GameOverScreen.Name);
        };
        PlayScreen.prototype.advanceFrame = function () {
            var head = this.snake[this.snake.length - 1];
            head = head.slice();
            var changeRow = this.direction == 'u' || this.direction == 'd';
            var increment = this.direction == 'r' || this.direction == 'd';
            head[changeRow ? 0 : 1] += increment ? 1 : -1;
            if (head[0] == 0 || head[0] == this.ctx.rows - 1 || head[1] == 0 || head[1] == this.ctx.cols - 1) {
                this.die();
                return;
            }
            for (var i = 0; i < this.snake.length - 1; i++) {
                if (this.sameloc(this.snake[i], head)) {
                    this.die();
                    return;
                }
            }
            this.snake.push(head);
            this.lastMove = this.direction;
            if (this.sameloc(head, this.powerup)) {
                this.powerup = this.randloc();
                if (this.minTimePerFrame > 50)
                    this.minTimePerFrame -= 25;
            }
            else
                this.snake.shift();
        };
        PlayScreen.prototype.draw = function () {
            this.fillScreen('black');
            this.drawBorder('checker');
            for (var i = 0; i < this.snake.length; i++) {
                this.drawSquare(this.snake[i], 'white');
            }
            this.drawSquare(this.powerup, 'yellow');
        };
        PlayScreen.prototype.start = function () {
            var _this = this;
            this.minTimePerFrame = 200;
            this.snake = [[Math.floor(this.ctx.rows / 2), Math.floor(this.ctx.cols / 2)]];
            this.direction = 'l';
            this.powerup = this.randloc();
            this.ctx.input.addCustomKeyListener(function (keyCode) {
                var pressed = _this.keyBindings[keyCode];
                if (pressed && _this.forbidden[_this.lastMove] != pressed)
                    _this.direction = pressed;
            });
        };
        PlayScreen.Name = 'play';
        return PlayScreen;
    })(Snake.GameState);
    Snake.PlayScreen = PlayScreen;
})(Snake || (Snake = {}));
var Snake;
(function (Snake) {
    var StartScreen = (function (_super) {
        __extends(StartScreen, _super);
        function StartScreen(ctx) {
            _super.call(this, ctx);
            this.nameArt = [
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
            this.artRows = this.nameArt.length;
            this.artCols = this.nameArt[0].length;
            this.artRowOffset = Math.floor((ctx.rows - this.artRows) / 2);
            this.artColOffset = this.artRowOffset;
            this.minTimePerFrame = 250;
        }
        StartScreen.prototype.advanceFrame = function () {
            var mouseLoc = this.ctx.input.getMouseLoc();
            var mouseRow = Math.floor(mouseLoc[1] / this.ctx.tileSize);
            var mouseCol = Math.floor(mouseLoc[0] / this.ctx.tileSize);
            if (this.ctx.input.isMouseOver())
                this.randomizeBorderColors();
        };
        StartScreen.prototype.draw = function () {
            this.fillScreen('white');
            this.drawBorder('colorful');
            this.drawArt(this.nameArt, this.artRowOffset, this.artColOffset, 'black');
        };
        StartScreen.prototype.start = function () {
            var _this = this;
            this.ctx.input.addCustomListener('click', function () {
                _this.ctx.switchState(Snake.CountDownScreen.Name);
            });
        };
        StartScreen.Name = 'start';
        return StartScreen;
    })(Snake.GameState);
    Snake.StartScreen = StartScreen;
})(Snake || (Snake = {}));
var Snake;
(function (Snake) {
    var Util = (function () {
        function Util() {
        }
        Util.randColor = function () {
            var hue = Math.floor(Math.random() * 360);
            return 'hsl(' + hue + ', 90%, 50%)';
        };
        return Util;
    })();
    Snake.Util = Util;
})(Snake || (Snake = {}));
window.onload = function () {
    var canvas = document.createElement('canvas');
    document.body.appendChild(canvas);
    var game = new Snake.GameRunner(canvas);
    game.run();
};
//# sourceMappingURL=app.js.map
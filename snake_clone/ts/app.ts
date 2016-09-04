window.onload = () => {
    var canvas = <HTMLCanvasElement> document.getElementById('canvas');
    var game = new Snake.GameRunner(canvas);
    game.run();
}
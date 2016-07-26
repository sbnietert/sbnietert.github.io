window.onload = () => {
    var canvas = document.createElement('canvas');
    document.body.appendChild(canvas);
    var game = new Snake.GameRunner(canvas);
    game.run();
}
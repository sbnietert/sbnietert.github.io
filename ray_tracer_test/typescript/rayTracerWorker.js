var RT;
(function (RT) {
    var rayTracer = new RT.RayTracer();
    var targetOrigin = 'index.html';
    onmessage = function (e) {
        var message = e.data;
        if (message.command == 'load scene') {
            RT.Scene.loadFromFile(message.data, function (scene) {
                rayTracer.scene = scene;
                postMessage({
                    command: 'update scene data',
                    data: {
                        width: scene.renderSettings.camera.pixelWidth,
                        height: scene.renderSettings.camera.pixelHeight,
                        subpixelGridSize: scene.renderSettings.subpixelGridSize,
                        recursionDepth: scene.renderSettings.recursionDepth
                    }
                }, targetOrigin);
            });
        }
        else if (message.command == 'render') {
            rayTracer.scene.renderSettings.camera.pixelWidth = message.data.width;
            rayTracer.scene.renderSettings.camera.pixelHeight = message.data.height;
            rayTracer.scene.renderSettings.subpixelGridSize = message.data.subpixelGridSize;
            rayTracer.scene.renderSettings.recursionDepth = message.data.recursionDepth;
            rayTracer.render(function (rowColors, row) {
                postMessage({
                    command: 'paint',
                    data: {
                        rowColors: rowColors,
                        rowIndex: row
                    }
                }, targetOrigin);
            });
            postMessage({
                command: 'render complete'
            }, targetOrigin);
        }
    };
})(RT || (RT = {}));

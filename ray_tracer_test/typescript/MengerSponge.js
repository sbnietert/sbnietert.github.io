/// <reference path="SceneGraph.ts" />
/// <reference path="Vector.ts" />
/// <reference path="Material.ts" />
/// <reference path="AxisAlignedBox.ts" />
/// <reference path="SceneObject.ts" />
/// <reference path="Color.ts" />
var RT;
(function (RT) {
    var MengerSponge = (function () {
        function MengerSponge() {
            this.sceneGraph = [];
        }
        // split box into sub-boxes to add, or add box if depth has been reached
        MengerSponge.prototype.addBox = function (ll, ur, sceneGraph, depth) {
            // end of recursion
            if (depth == 0) {
                var geo = new RT.AxisAlignedBox(ll, ur);
                var box = new RT.SceneObject(geo, this.material);
                var nodeType = 0 /* Object */;
                var node = new RT.SceneGraph.Node(nodeType, box);
                sceneGraph.push(node);
                return;
            }
            // split box into 3x3x3 grid
            var step = ur.minus(ll).scaledBy(1 / 3);
            for (var x = 0; x < 3; x++) {
                for (var y = 0; y < 3; y++) {
                    for (var z = 0; z < 3; z++) {
                        // we only want "lines" of boxes cut out, not "planes"
                        var centerCount = (x == 1 ? 1 : 0) + (y == 1 ? 1 : 0) + (z == 1 ? 1 : 0);
                        if (centerCount >= 2)
                            continue;
                        var newLl = ll.copy();
                        newLl.add(step.vectorScaledBy(new RT.Vector(x, y, z)));
                        var newUr = newLl.plus(step.scaledBy(0.96));
                        var nodeType = 1 /* Collection */;
                        var subGraph = [];
                        var boundingBox = new RT.AxisAlignedBox(newLl, newUr);
                        var collectionNode = new RT.SceneGraph.Node(nodeType, subGraph, boundingBox);
                        sceneGraph.push(collectionNode);
                        // add lights in the center of bounding boxes
                        if (depth != 1) {
                            var lightPos = newLl.plus(newUr).scaledBy(1 / 2);
                            var lightIntensity = this.lightIntensity * Math.pow(0.5, this.depth - depth);
                            this.scene.lights.push(new RT.Light(lightPos, this.lightColor, lightIntensity));
                        }
                        this.addBox(newLl, newUr, subGraph, depth - 1);
                    }
                }
            }
        };
        MengerSponge.prototype.generateSceneGraphFromData = function (data, scene) {
            this.scene = scene;
            var ll = RT.Scene.loadVector(data.ll);
            var ur = RT.Scene.loadVector(data.ur);
            this.depth = data.depth;
            this.material = scene.materials[data.material];
            this.lightColor = data.lightColor ? RT.Scene.loadColor(data.lightColor) : RT.Color.WHITE;
            this.lightIntensity = data.lightIntensity || 0;
            this.addBox(ll, ur, this.sceneGraph, this.depth);
            return this.sceneGraph;
        };
        return MengerSponge;
    })();
    RT.MengerSponge = MengerSponge;
})(RT || (RT = {}));

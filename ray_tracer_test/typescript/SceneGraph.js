/// <reference path="SceneObject.ts" />
/// <reference path="GeometricObject.ts" />
var __extends = (this && this.__extends) || function (d, b) {
    for (var p in b) if (b.hasOwnProperty(p)) d[p] = b[p];
    function __() { this.constructor = d; }
    d.prototype = b === null ? Object.create(b) : (__.prototype = b.prototype, new __());
};
var RT;
(function (RT) {
    var SceneGraph;
    (function (SceneGraph) {
        var Node = (function () {
            function Node(type, value, boundingShape) {
                if (boundingShape === void 0) { boundingShape = null; }
                this.type = type;
                this.value = value;
                this.boundingShape = boundingShape;
            }
            return Node;
        })();
        SceneGraph.Node = Node;
        ;
        var BoundableSceneObject = (function (_super) {
            __extends(BoundableSceneObject, _super);
            function BoundableSceneObject() {
                _super.apply(this, arguments);
            }
            return BoundableSceneObject;
        })(RT.GenericSceneObject);
        SceneGraph.BoundableSceneObject = BoundableSceneObject;
        function getAxisAlignedBoundingBox(objects) {
            var min = new RT.Vector(Infinity, Infinity, Infinity);
            var max = new RT.Vector(-Infinity, -Infinity, -Infinity);
            for (var _i = 0; _i < objects.length; _i++) {
                var obj = objects[_i];
                for (var _a = 0, _b = obj.getGeometry().getAxisAlignedBoundaryPoints(); _a < _b.length; _a++) {
                    var point = _b[_a];
                    if (point.x < min.x)
                        min.x = point.x;
                    if (point.x > max.x)
                        max.x = point.x;
                    if (point.y < min.y)
                        min.y = point.y;
                    if (point.y > max.y)
                        max.y = point.y;
                    if (point.z < min.z)
                        min.z = point.z;
                    if (point.z > max.z)
                        max.z = point.z;
                }
            }
            return new RT.AxisAlignedBox(min, max);
        }
        SceneGraph.getAxisAlignedBoundingBox = getAxisAlignedBoundingBox;
        function groupObjects(objects, maxGroupSize, parent) {
            if (objects.length <= maxGroupSize) {
                for (var _i = 0; _i < objects.length; _i++) {
                    var obj = objects[_i];
                    var node = new SceneGraph.Node(0 /* Object */, obj);
                    parent.value.push(node);
                }
            }
            else {
                var ref = objects[0].getGeometry().getReferencePoint();
                objects.sort(function (a, b) {
                    var refA = a.getGeometry().getReferencePoint();
                    var refB = b.getGeometry().getReferencePoint();
                    return refA.minus(ref).length() - refB.minus(ref).length();
                });
                var closest = objects.splice(0, Math.floor(objects.length / 2));
                var closestNode = new SceneGraph.Node(1 /* Collection */, [], SceneGraph.getAxisAlignedBoundingBox(closest));
                parent.value.push(closestNode);
                groupObjects(closest, maxGroupSize, closestNode);
                var furthest = objects; // those that remain after the splice
                var furthestNode = new SceneGraph.Node(1 /* Collection */, [], SceneGraph.getAxisAlignedBoundingBox(furthest));
                parent.value.push(furthestNode);
                groupObjects(furthest, maxGroupSize, furthestNode);
            }
        }
        function generateFromSceneObjects(objects, maxSubgraphSize) {
            if (maxSubgraphSize === void 0) { maxSubgraphSize = 2; }
            var parentNode = new SceneGraph.Node(1 /* Collection */, [], SceneGraph.getAxisAlignedBoundingBox(objects));
            groupObjects(objects, maxSubgraphSize, parentNode);
            return [parentNode];
        }
        SceneGraph.generateFromSceneObjects = generateFromSceneObjects;
        function generateFromShapes(shapes, material) {
            var objects = new Array(shapes.length);
            for (var i = 0; i < shapes.length; i++)
                objects[i] = new BoundableSceneObject(shapes[i], material);
            return generateFromSceneObjects(objects, 2);
        }
        SceneGraph.generateFromShapes = generateFromShapes;
    })(SceneGraph = RT.SceneGraph || (RT.SceneGraph = {}));
})(RT || (RT = {}));

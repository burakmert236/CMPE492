import * as go from "gojs";
const $ = go.GraphObject.make;

export const diagramConfiguration = {
    "initialContentAlignment": go.Spot.Center,
    'undoManager.isEnabled': true,
    "draggingTool.isGridSnapEnabled": true,
    "draggingTool.gridSnapCellSize": new go.Size(10, 10),
    "draggingTool.dragsLink": true,
    "dragSelectingTool.isEnabled": false,
    "linkingTool.isUnconnectedLinkValid": true,
    "linkingTool.portGravity": 20,
    "relinkingTool.isUnconnectedLinkValid": true,
    "relinkingTool.portGravity": 20,
    "relinkingTool.fromHandleArchetype":
        $(go.Shape, "Diamond", { segmentIndex: 0, cursor: "pointer", desiredSize: new go.Size(8, 8), fill: "tomato", stroke: "darkred" }),
    "relinkingTool.toHandleArchetype":
        $(go.Shape, "Diamond", { segmentIndex: -1, cursor: "pointer", desiredSize: new go.Size(8, 8), fill: "darkred", stroke: "tomato" }),
    "linkReshapingTool.handleArchetype":
        $(go.Shape, "Diamond", { desiredSize: new go.Size(7, 7), fill: "lightblue", stroke: "deepskyblue" }),
    "rotatingTool.handleAngle": 270,
    "rotatingTool.handleDistance": 30,
    "rotatingTool.snapAngleMultiple": 15,
    "rotatingTool.snapAngleEpsilon": 15,
};

export const paletteNodeDataArray = [  // specify the contents of the Palette
    { text: "Comment", figure: "RoundedRectangle", fill: "lightyellow" }
];

export const paletteLinkDataArray = [
    // the Palette also has a disconnected Link, which the user can drag-and-drop
    { 
        points: new go.List(/*go.Point*/).addAll([new go.Point(0, 0), new go.Point(20, 0), new go.Point(20, 40), new go.Point(50, 40)]), 
        color: "#50E2AD",
    },
    { 
        points: new go.List(/*go.Point*/).addAll([new go.Point(0, 0), new go.Point(20, 0), new go.Point(20, 40), new go.Point(50, 40)]), 
        color: "#50E2AD",
        toArrow: "BackwardTriangle"
    },
    { 
        points: new go.List(/*go.Point*/).addAll([new go.Point(0, 0), new go.Point(20, 0), new go.Point(20, 40), new go.Point(50, 40)]), 
        color: "#50E2AD",
        dash: [4, 2]
    },
    { 
        points: new go.List(/*go.Point*/).addAll([new go.Point(0, 0), new go.Point(20, 0), new go.Point(20, 40), new go.Point(50, 40)]), 
        color: "#50E2AD",
        dash: [4, 2],
        toArrow: "Circle"
    }
];

export const paletteConfiguration = { 
    maxSelectionCount: 1, 
    allowZoom: false,
    layout: $(
        go.GridLayout,
        {
            alignment: "Location",
            cellSize: new go.Size(100, 100),
            spacing: new go.Size(10, 10),
            wrappingColumn: 2, // adjust as needed to fit the number of items in a row
        }
    )
};

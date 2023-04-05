import * as go from "gojs";
const $ = go.GraphObject.make;

export const diagramConfiguration = {
    allowZoom: true,
    "initialContentAlignment": go.Spot.Center,
    'undoManager.isEnabled': true,
    "draggingTool.isGridSnapEnabled": true,
    "draggingTool.gridSnapCellSize": new go.Size(10, 10),
    "draggingTool.dragsLink": true,
    "dragSelectingTool.isEnabled": true,
    "linkingTool.isUnconnectedLinkValid": true,
    "linkingTool.portGravity": 20,
    "relinkingTool.isUnconnectedLinkValid": true,
    "relinkingTool.portGravity": 20,
    "relinkingTool.fromHandleArchetype":
        $(go.Shape, "Diamond", { segmentIndex: 0, cursor: "pointer", desiredSize: new go.Size(8, 8), fill: "tomato", stroke: "darkred" }),
    "relinkingTool.toHandleArchetype":
        $(go.Shape, "Diamond", { segmentIndex: -1, cursor: "pointer", desiredSize: new go.Size(8, 8), fill: "darkred", stroke: "tomato" }),
    "linkReshapingTool.handleArchetype":
        $(go.Shape, "Diamond", { desiredSize: new go.Size(2, 2), fill: "lightblue", stroke: "deepskyblue" }),
};

export const paletteNodeDataArray = [  // specify the contents of the Palette
    { text: "Goal Node", color: "#ACF3DA" }
];

export const paletteLinkDataArray = [
    // the Palette also has a disconnected Link, which the user can drag-and-drop
    { 
        points: new go.List(/*go.Point*/).addAll([new go.Point(0, 0), new go.Point(60, 22)]), 
        color: "black",
        text: "Refinement",
        type: "Refinement",
        fromArrow: "BackwardTriangle",
        toArrow: "",
        fromShortLength: 8,
        toShortLength: 0,
        segmentOffset: new go.Point(5, 20)
    },
    { 
        points: new go.List(/*go.Point*/).addAll([new go.Point(0, 0), new go.Point(65, 25)]), 
        color: "black",
        fromArrow: "Triangle",
        text: "Precedence",
        type: "Precedence",
        toArrow: "",
    },
    { 
        points: new go.List(/*go.Point*/).addAll([new go.Point(0, 0), new go.Point(65, 25)]), 
        color: "#27ba84",
        dash: [6, 3],
        text: "(+) Cost Contribution",
        type: "(+) Cost Contribution",
        fromArrow: "BackwardTriangle",
        toArrow: "",
    },
    { 
        points: new go.List(/*go.Point*/).addAll([new go.Point(0, 0), new go.Point(65, 25)]), 
        color: "rgb(33, 91, 166)",
        dash: [6, 3],
        fromArrow: "BackwardTriangle",
        text: "(-) Cost Contribution",
        type: "(-) Cost Contribution",
        toArrow: "",
    },
    { 
        points: new go.List(/*go.Point*/).addAll([new go.Point(0, 0), new go.Point(65, 25)]), 
        color: "#27ba84",
        dash: [6, 3],
        fromArrow: "Circle",
        text: "(+) Value Contribution",
        type: "(+) Value Contribution",
        toArrow: "",
    },
    { 
        points: new go.List(/*go.Point*/).addAll([new go.Point(0, 0), new go.Point(65, 25)]), 
        color: "rgb(33, 91, 166)",
        dash: [6, 3],
        fromArrow: "Circle",
        text: "(-) Value Contribution",
        type: "(-) Value Contribution",
        toArrow: "",
    },
    { 
        points: new go.List(/*go.Point*/).addAll([new go.Point(0, 0), new go.Point(65, 25)]), 
        color: "red",
        dash: [6, 3],
        fromArrow: "BackwardTriangle",
        text: "Exclusion",
        type: "Exclusion",
        toArrow: "",
    }
];

export const paletteConfiguration = { 
    maxSelectionCount: 1, 
    allowZoom: false,
    layout: $(go.GridLayout,
        {
            alignment: go.GridLayout.Position,
            cellSize: new go.Size(45, 50),
            spacing: new go.Size(0, 0),
            wrappingColumn: 100
        }
    )
};

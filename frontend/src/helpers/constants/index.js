import * as go from "gojs";
const $ = go.GraphObject.make;

export const REACT_APP_BASE_ENDPOINT = "http://localhost:3001/api/v1";

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
    { text: "Goal Node", shape: "Terminator", color: "#ACF3DA", location: new go.Point(0, 0) },
    { text: "Exclusion", color: "#FF0000", shape: "Circle", width: 25, height: 25, location: new go.Point(0, 0), category: "Exclusion" }
];

export const paletteLinkDataArray = [
    // the Palette also has a disconnected Link, which the user can drag-and-drop
    { 
        points: new go.List(/*go.Point*/).addAll([new go.Point(0, 0), new go.Point(60, 15)]), 
        color: "black",
        text: "Refinement",
        type: "Refinement",
        category: "Refinement",
        fromArrow: "BackwardTriangle",
        toArrow: "",
        fromShortLength: 8,
        toShortLength: 0,
        segmentOffset: new go.Point(5, 22)
    },
    { 
        points: new go.List(/*go.Point*/).addAll([new go.Point(0, 0), new go.Point(60, 15)]), 
        color: "black",
        type: "AND Refinement",
        text: "AND Refinement",
        category: "ANDRefinement",
        fromArrow: "Backward",
        toArrow: "",
        fromShortLength: 8,
        toShortLength: 0,
        segmentOffset: new go.Point(5, 22)
    },
    { 
        points: new go.List(/*go.Point*/).addAll([new go.Point(0, 0), new go.Point(60, 15)]), 
        color: "black",
        fromArrow: "Backward",
        text: "Precedence",
        type: "Precedence",
        category: "Precedence",
        toArrow: "",
        fromShortLength: 8,
        toShortLength: 0,
        segmentOffset: new go.Point(5, 20)
    },
    { 
        points: new go.List(/*go.Point*/).addAll([new go.Point(0, 0), new go.Point(60, 15)]), 
        color: "#27ba84",
        dash: [2, 2],
        text: "Positive Cost Contr.",
        type: "C+",
        category: "C+",
        fromArrow: "BackwardTriangle",
        toArrow: "",
        fromShortLength: 8,
        toShortLength: 0,
        segmentOffset: new go.Point(5, 20)
    },
    { 
        points: new go.List(/*go.Point*/).addAll([new go.Point(0, 0), new go.Point(60, 15)]), 
        color: "rgb(33, 91, 166)",
        dash: [2, 2],
        fromArrow: "BackwardTriangle",
        text: "Negative Cost Contr.",
        type: "C-",
        category: "C-",
        toArrow: "",
        fromShortLength: 8,
        toShortLength: 0,
        segmentOffset: new go.Point(5, 20)
    },
    { 
        points: new go.List(/*go.Point*/).addAll([new go.Point(0, 0), new go.Point(60, 15)]), 
        color: "#27ba84",
        dash: [6, 3],
        fromArrow: "BackwardBoomerang",
        text: "Positive Value Contr.",
        type: "V+",
        category: "V+",
        toArrow: "",
        fromShortLength: 8,
        toShortLength: 0,
        segmentOffset: new go.Point(5, 20)
    },
    { 
        points: new go.List(/*go.Point*/).addAll([new go.Point(0, 0), new go.Point(60, 15)]), 
        color: "rgb(33, 91, 166)",
        dash: [6, 3],
        fromArrow: "BackwardBoomerang",
        text: "Negative Value Contr.",
        type: "V-",
        category: "V-",
        toArrow: "",
        fromShortLength: 8,
        toShortLength: 0,
        segmentOffset: new go.Point(5, 20)
    },

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

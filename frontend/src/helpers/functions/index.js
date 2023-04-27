import * as go from "gojs";
const $ = go.GraphObject.make;

export const createPaletteNodeTemplate = () => {
    return $(go.Node, "Vertical",
        { locationObjectName: "TB", locationSpot: go.Spot.Center },
        $(go.Shape,
            { 
                desiredSize: new go.Size(65, 25),
                strokeDashArray: null,
                fill: $(go.Brush, "Linear", { 0.0: "white", 1.0: "gray" }),
            },
            new go.Binding("figure", "shape"),
            new go.Binding("fill", "color"),
            new go.Binding("width", "width"),
            new go.Binding("height", "height")
        ),
        $(go.TextBlock, 
            { 
                textAlign: "Bottom",
                margin: new go.Margin(4, 0, 0, 0),
                font: "9pt sans-serif",
            },
            new go.Binding("text", "text")
        )
    );
};

export const createDiagramNodeTemplate = (setSelectedNode) => {

    return $(go.Node, "Auto",
        {   
            click:(e,node) => {
                setSelectedNode(node);
            },
            selectable: true, 
            selectionAdornmentTemplate:
                $(go.Adornment, "Auto",
                    $(go.Shape, 
                        { 
                            fill: null, 
                            stroke: "deepskyblue", 
                            strokeWidth: 1, 
                            strokeDashArray: [6, 3]
                        }
                    ),
                    $(go.Placeholder)
                )
        },  
        { locationSpot: go.Spot.Center },
        { resizable: true, resizeObjectName: "PANEL", toLinkable: false, fromLinkable: false },

        new go.Binding("location", "location").makeTwoWay(),
        new go.Binding("text", "key").makeTwoWay(),

        $(go.Shape,
            {
                name: "SHAPE", fill: "#000", strokeWidth: 1,
                stroke: "#000",
                portId: "",  // this Shape is the Node's port, not the whole Node
                fromLinkable: true,
                toLinkable: true,
                cursor: "pointer",
            },
            new go.Binding("width", "width"),
            new go.Binding("height", "height"),
            new go.Binding("minSize", "minSize"),
            new go.Binding("figure", "shape"),
            new go.Binding("fill", "color"),
        ),

        $(go.Panel, "Auto",  
            { defaultAlignment: go.Spot.Center },

            $(go.Shape,
                {
                    fill: "red",  // default color
                    strokeWidth: 1,
                    name: "PANEL",
                    minSize: new go.Size(120, 50),
                },
                new go.Binding("figure", "shape"),
                new go.Binding("fill", "color"),
            ),  // shape.fill = data.color

            $(go.TextBlock,
                { 
                    name: "TEXT",
                    font: "bold 14pt sans-serif",
                    editable: false,
                    isMultiline: true,
                    maxSize: new go.Size(160, NaN),
                    wrap: go.TextBlock.WrapFit,
                    textAlign: "center",
                    margin: 15
                },
                new go.Binding("text", "text"),
            ),
            $("TreeExpanderButton", 
                { 
                    alignment: go.Spot.Left, 
                    alignmentFocus: go.Spot.Left,
                    visible: true,
                    margin: new go.Margin(0, 0, 0, 10)
                },
                new go.Binding("visible", "visible"),
            ),
        ),  // textblock.text = data.key
    );
};

export const createDiagramLinkTemplate = () => {
    return $(go.Link,  // the whole link panel
        { relinkableFrom: true, relinkableTo: true, reshapable: true },
        new go.Binding("relinkableFrom").makeTwoWay(),
        new go.Binding("relinkableTo").makeTwoWay(),
        new go.Binding("reshapable").makeTwoWay(),
        new go.Binding("selectable").makeTwoWay(),
        {
            corner: 10,
            toShortLength: 8,
            curve: go.Link.Bezier,
            adjusting: go.Link.Stretch,
        },

        new go.Binding("points").makeTwoWay(),
        new go.Binding("fromShortLength").makeTwoWay(),
        new go.Binding("toShortLength").makeTwoWay(),

        $(go.Shape,  // the link path shape
            { 
                isPanelMain: true, 
                strokeWidth: 3, 
                strokeDashArray: [0, 0]
            },
            new go.Binding("stroke", "color"),
            new go.Binding("strokeDashArray", "dash"),
            new go.Binding("stroke", "fromNode", (fromNode) => {
                if (fromNode.category === "Exclusion") {
                    return "red";
                }
                return "black";
            }).ofObject(),
        ),

        $(go.Shape,  // the arrowhead at the end of the link
            { toArrow: "Standard", stroke: null, scale: 2 },
            new go.Binding("toArrow", "toArrow"),
            new go.Binding("stroke", "color"),
            new go.Binding("fill", "color"),
            new go.Binding("visible", "toArrow", type => type !== "null"),
            new go.Binding("visible", "fromNode", (fromNode) => {
                if (fromNode.category === "Exclusion") {
                    return false;
                }
                return true;
            }).ofObject(),
        ),

        $(go.Shape,  // the arrowhead at the beginning of the link
            { fromArrow: "Standard", stroke: null, scale: 2 },
            new go.Binding("fromArrow", "fromArrow"),
            new go.Binding("stroke", "color"),
            new go.Binding("fill", "color"),
            new go.Binding("visible", "fromArrow", type => type !== "null"),
            new go.Binding("visible", "fromNode", (fromNode) => {
                if (fromNode.category === "Exclusion") {
                    return false;
                }
                return true;
            }).ofObject(),
        ),

        $(go.Panel, "Auto",
            // new go.Binding("visible", "isSelected").ofObject(),
            $(go.Shape, "RoundedRectangle",  // the link shape
                { fill: "#fff", stroke: null },
                new go.Binding("fill", "color"),
                new go.Binding("visible", "type", type => (type !== "Refinement") && (type !== "AND Refinement")),
            ),

            $(go.TextBlock,
                {
                    textAlign: "center",
                    font: "bold 10pt helvetica, arial, sans-serif",
                    stroke: "white",
                    margin: 2,
                    minSize: new go.Size(1, NaN),
                    editable: true,
                    isMultiline: false,
                },
                new go.Binding("text").makeTwoWay(),
                new go.Binding("editable", "type", type => ["C+", "C-", "V+", "V-"].includes(type?.slice(0, 2))),
                new go.Binding("visible", "type", type => (type !== "Refinement") && (type !== "AND Refinement")),
                new go.Binding("font", "type", type => type === "Refinement" ? "0pt helvetica, arial, sans-serif" : "bold 10pt helvetica, arial, sans-serif"),
                // Add the following binding to hide the text block for links coming from exclusion nodes
                new go.Binding("visible", "fromNode", (fromNode) => {
                    return fromNode.category !== "Exclusion";
                }).ofObject(),
            )
        )
    );
};

export const junctionNodeTemplate = () => {
    return $(go.Node, "Auto",
                {
                    isTreeExpanded: false,
                    deletable: true
                },
                new go.Binding("location").makeTwoWay(),
                $(go.Shape, "Circle", 
                    { width: 10, height: 10, fill: "black", stroke: "black"},
                ),
            )
}

export const exclusionNodeTemplate = () => {
    return $(
      go.Node,
      "Auto",
      {
        locationObjectName: "main",
        locationSpot: go.Spot.Center,
        selectionObjectName: "main",
        movable: true,
        deletable: true,
        fromLinkable: true,
        selectable: true,
        resizable: true,
        rotatable: true,
        toLinkable: true,
        category: "Exclusion",
        fromLinkableDuplicates: false,
        toLinkableDuplicates: false,
      },
      new go.Binding("location", "loc", go.Point.parse).makeTwoWay(
        go.Point.stringify
      ),
      new go.Binding("location").makeTwoWay(),
      new go.Binding("key", "key").makeTwoWay(),
      $(go.Panel, "Auto", { name: "main" },
        $(go.Shape, "Circle", {
          strokeWidth: 1,
          stroke: "black",
          width: 30,
          height: 30,
          fill: "red",
        })
      ),
      new go.Binding("fromSpot", "fromSpot", go.Spot.parse).makeTwoWay(
        go.Spot.stringify
      ),
      new go.Binding("toSpot", "toSpot", go.Spot.parse).makeTwoWay(
        go.Spot.stringify
      )
    );
  };

export const createPaletteLinkTemplate = () => {
    return $(go.Link,
        { // because the GridLayout.alignment is Location and the nodes have locationSpot == Spot.Center,
          // to line up the Link in the same manner we have to pretend the Link has the same location spot
            locationSpot: go.Spot.Center,
        },
        {
            routing: go.Link.AvoidsNodes,
            curve: go.Link.FlipBoth,
            corner: 5,
            toShortLength: 8
        },
        new go.Binding("points"),
        new go.Binding("fromShortLength").makeTwoWay(),
        new go.Binding("toShortLength").makeTwoWay(),

        $(go.Shape,  // the link path shape
            { 
                isPanelMain: true, 
                strokeWidth: 3,
                stroke: "red",
                strokeDashArray: [0, 0],
            },
            new go.Binding("stroke", "color"),
            new go.Binding("strokeDashArray", "dash"),
        ),

        $(go.Shape,  // the arrowhead
            { toArrow: "Standard", stroke: null, scale: 1.5 },
            new go.Binding("toArrow", "toArrow"),
            new go.Binding("stroke", "color"),
            new go.Binding("fill", "color"),
        ),

        $(go.Shape,  // the arrowhead
            { fromArrow: "Standard", stroke: null, scale: 1.5 },
            new go.Binding("fromArrow", "fromArrow"),
            new go.Binding("stroke", "color"),
            new go.Binding("fill", "color"),
        ),


        $(go.TextBlock,
            {
                textAlign: "bottom",
                stroke: "black",
                font: "9pt sans-serif",
                segmentOffset: new go.Point(5, 26),
            },
            new go.Binding("text").makeTwoWay(),
            new go.Binding("segmentOffset").makeTwoWay()
        )
    );
}

export const hasCycle = (node, visited, stack, desiredType) => {
    visited[node?.key] = true;
    stack[node?.key] = true;
  
    const iterator = node?.findNodesOutOf();
    while (iterator?.next()) {
        const connectedNode = iterator.value;
        const link = node?.findLinksTo(connectedNode)?.first();
    
        if (link?.data?.type === desiredType) {
            if (!visited[connectedNode.key]) {
                if(hasCycle(connectedNode, visited, stack, desiredType)) {
                    return true
                }
            } else if (stack[connectedNode.key]) {
                return true;
            }
        }
    }
  
    stack[node?.key] = false;
    return false;
}

export const detectCycleForSpecificLinkType = (diagram, desiredType) => {
    const visited = {};
    const stack = {};
  
    const nodes = diagram.nodes;
    while (nodes.next()) {
        const node = nodes.value;
        if (!visited[node.key]) {
            if (hasCycle(node, visited, stack, desiredType)) {
                return true;
            }
        }
    }
  
    return false;
}

export const capitalize = (text) => {
    return text?.slice(0, 1)?.toUpperCase() + text?.slice(1);
}
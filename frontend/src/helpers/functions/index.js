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
                name: "SHAPE", fill: "#000",
                stroke: "#000",
                strokeWidth: 3,
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
            new go.Binding("stroke", "is_implemented", is_implemented => {
                return is_implemented ? "#077709" : "#000"
            }),
            new go.Binding("strokeWidth", "is_implemented", is_implemented => {
                return is_implemented ? 8 : 3
            }),
        ),

        $(go.Panel, "Auto",  
            { defaultAlignment: go.Spot.Center },

            $(go.Shape,
                {
                    fill: "red",  // default color
                    stroke: "#000",
                    strokeWidth: 2,
                    name: "PANEL",
                    minSize: new go.Size(120, 50),
                },
                new go.Binding("figure", "shape"),
                new go.Binding("fill", "color"),
                new go.Binding("fill", "", data => {
                    if(data.smt_result === "true") {
                        return "#B0f3ac";
                    }
                    if(data.smt_result === "false") {
                        return "#F56668";
                    }
                }),
                new go.Binding("stroke", "is_mandatory", is_mandatory => {
                    return is_mandatory ? "#D41c00" : "#000"
                }),
                new go.Binding("strokeWidth", "is_mandatory", is_mandatory => {
                    return is_mandatory ? 4 : 2
                })
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
        new go.Binding("category", "", (linkData) => linkData.category),
        {
            corner: 10,
            curve: go.Link.Bezier,
            adjusting: go.Link.Stretch,
        },
        //new go.Binding("type").makeTwoWay(),
        new go.Binding("points").makeTwoWay(),
        new go.Binding("fromShortLength").makeTwoWay(),
        new go.Binding("toShortLength").makeTwoWay(),

        $(go.Shape,  // the link path shape
            { 
                isPanelMain: true, 
                strokeWidth: 3, 
                strokeDashArray: [0, 0],
                stroke: "red"
            },
            new go.Binding("stroke", "color"),
            new go.Binding("strokeDashArray", "dash"),
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
                new go.Binding("visible", "", (l) => {
                    return l.category !== "Refinement" && l.category !== "ANDRefinement" && l.category !== undefined;
                })
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
                new go.Binding("visible", "", (l) => {
                    return l.category !== "Refinement" && l.category !== "ANDRefinement" && l.category !== undefined;
                })
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
    
    return $(go.Node, "Spot",
        {
            locationSpot: go.Spot.Center,
            deletable: true,
            selectable: true,
            rotatable: false,
            category: "Exclusion" 
        },
        new go.Binding("location").makeTwoWay(),
        new go.Binding("key", "key").makeTwoWay(),

        $(go.Panel, "Auto", { name: "PANEL" },
            $(go.Shape, "Circle", 
                { 
                    portId: "",
                    cursor: "pointer",
                    width: 30, height: 30, 
                    fill: "#Cf080d",
                    fromLinkable: true,
                    toLinkable: false, // Disable linking to this shape
                },
            ),

            $(go.Shape, "Circle", 
                { 
                    portId: "",
                    width: 20, height: 20, 
                    fill: "red",
                    fromLinkable: false,
                    toLinkable: false, // Disable linking to this shape
                },
            ),
        ),
    )
}


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
            toShortLength: 8,
            selectionAdornmentTemplate: null
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
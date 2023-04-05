import * as go from "gojs";
const $ = go.GraphObject.make;

export const makePort = (name, spot, output, input) => {
    const $ = go.GraphObject.make;
    // the port is basically just a small transparent circle
    return $(go.Shape, "Circle",
        {
            fill: null,  // not seen, by default; set to a translucent gray by showSmallPorts, defined below
            stroke: null,
            desiredSize: new go.Size(7, 7),
            alignment: spot,  // align the port on the main Shape
            alignmentFocus: spot,  // just inside the Shape
            portId: name,  // declare this object to be a "port"
            fromSpot: spot, toSpot: spot,  // declare where links may connect at this port
            fromLinkable: output, toLinkable: input,  // declare whether the user may draw links to/from here
            cursor: "pointer"  // show a different cursor to indicate potential link point
        }
    );
};

export const showSmallPorts = (node, show) => {
    node.ports.each(port => {
        if (port.portId !== "") {  // don't change the default port, which is the big shape
            port.fill = show ? "rgba(0,0,0,.2)" : null;
        }
    });
};

export const createPaletteNodeTemplate = () => {
    return $(go.Node, "Vertical",
        { locationObjectName: "TB", locationSpot: go.Spot.Center },
        $(go.Shape,
            { 
                geometryString: "F M0 0 Q7 -8 25 0 Q50 7 75 0 Q93 -8 100 0 Q122 35 100 70 Q93 77 75 70 Q50 63 25 70 Q7 77 0 70 Q-22 35 0 0z",
                desiredSize: new go.Size(65, 25),
                margin: new go.Margin(0, 0, 0, 0),
                strokeDashArray: null,
                parameter1: 100,
                fill: $(go.Brush, "Linear", { 0.0: "white", 1.0: "gray" }),
            },
            new go.Binding("fill", "color"),
            new go.Binding("width", "width"),
            new go.Binding("height", "height")
        ),
        $(go.TextBlock, 
            { 
                name: "TB",
                margin: new go.Margin(7, 0, 0, 0),
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
                            strokeWidth: 1.5, 
                            strokeDashArray: [6, 3]
                        }
                    ),
                    $(go.Placeholder)
                )
        },  
        { locationSpot: go.Spot.Center },
        { resizable: true, resizeObjectName: "PANEL", toLinkable: false, fromLinkable: false },

        $(go.Panel, "Auto",  
            { defaultAlignment: go.Spot.Center },

            $(go.Shape,
                {
                    geometryString: "F M0 0 Q7 -8 25 0 Q50 7 75 0 Q93 -8 100 0 Q122 35 100 70 Q93 77 75 70 Q50 63 25 70 Q7 77 0 70 Q-22 35 0 0z",
                    name: "SHAPE", fill: "#ffffff", strokeWidth: 0,
                    stroke: null,
                    portId: "",  // this Shape is the Node's port, not the whole Node
                    fromLinkable: true,
                    toLinkable: true,
                    cursor: "pointer",
                    minSize: new go.Size(130, 50)
                }
            ),

            $(go.Shape,
                {
                    geometryString: "F M0 0 Q7 -8 25 0 Q50 7 75 0 Q93 -8 100 0 Q122 35 100 70 Q93 77 75 70 Q50 63 25 70 Q7 77 0 70 Q-22 35 0 0z",
                    fill: "red",  // default color
                    strokeWidth: 2,
                    name: "PANEL",
                    parameter1: 100,
                    minSize: new go.Size(130, 50)
                },
                new go.Binding("fill", "color"),
            ),  // shape.fill = data.color

            $(go.TextBlock,
                { 
                    name: "TEXT",
                    text: "Goal",
                    font: "bold 14pt sans-serif",
                    editable: true,
                    isMultiline: true,
                    maxSize: new go.Size(160, NaN),
                    wrap: go.TextBlock.WrapFit,
                    textAlign: "center",
                },
            ),
            $("TreeExpanderButton", 
                { 
                    alignment: go.Spot.Left, 
                    alignmentFocus: go.Spot.Left,
                    visible: true,
                    margin: new go.Margin(0, 0, 0, 10)
                },
            ),
        ),  // textblock.text = data.key
    );
};

export const createDiagramLinkTemplate = () => {
    return $(go.Link,  // the whole link panel
        { relinkableFrom: true, relinkableTo: true, reshapable: true },
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
                strokeWidth: 6, 
                strokeDashArray: [0, 0]
            },
            new go.Binding("stroke", "color"),
            new go.Binding("strokeDashArray", "dash"),
        ),
    
        $(go.Shape,  // the arrowhead
            { toArrow: "Standard", stroke: null, scale: 2 },
            new go.Binding("toArrow", "toArrow"),
            new go.Binding("stroke", "color"),
            new go.Binding("fill", "color"),
        ),

        $(go.Shape,  // the arrowhead
            { fromArrow: "Standard", stroke: null, scale: 2 },
            new go.Binding("fromArrow", "fromArrow"),
            new go.Binding("stroke", "color"),
            new go.Binding("fill", "color"),
        ),

        $(go.Panel, "Auto",
            // new go.Binding("visible", "isSelected").ofObject(),
            $(go.Shape, "RoundedRectangle",  // the link shape
                { fill: "#fff", stroke: null },
                new go.Binding("fill", "color")
            ),

            $(go.TextBlock,
                {
                    textAlign: "center",
                    font: "bold 13pt helvetica, arial, sans-serif",
                    stroke: "white",
                    margin: 2,
                    minSize: new go.Size(1, NaN),
                    editable: true,
                    isMultiline: false,
                },
                new go.Binding("text").makeTwoWay(),
                new go.Binding("editable", "type", type => type?.slice(0, 3) === "(+)" || type?.slice(0, 3) === "(-)"),
                new go.Binding("visible", "type", type => type !== "Refinement"),
                new go.Binding("font", "type", type => type === "Refinement" ? "0pt helvetica, arial, sans-serif" : "bold 13pt helvetica, arial, sans-serif"),

            )
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
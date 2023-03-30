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
        $(go.Shape, "RoundedRectangle",
            { 
                desiredSize: new go.Size(60, 25),
                fill: "white",
                margin: new go.Margin(0, 0, 0, 0),
                strokeDashArray: null,
                parameter1: 100
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

export const createDiagramNodeTemplate = () => {
    return $(go.Node, "Auto",
        { resizable: true, resizeObjectName: "PANEL", toLinkable: false, fromLinkable: false },
        $(go.Shape, "RoundedRectangle",
            {
                portId: "", // the default port: if no spot on link data, use closest side
                fill: "white",  // default color
                strokeWidth: 2,
                width: 110,
                height: 60,
                name: "PANEL",
                parameter1: 100,
                minSize: new go.Size(60, 30)
            },
            new go.Binding("fill", "color"),
            new go.Binding("width", "width"),
            new go.Binding("height", "height"),
            new go.Binding("figure", "figure")
        ),  // shape.fill = data.color

        $(go.Panel, "Table",  
            { 
                background: "lightgray", 
                width: 70,
                height: 70, 
            },
            new go.Binding("background", "color"),
            { defaultAlignment: go.Spot.Center },
            $(go.TextBlock,
                { 
                    text: "Goal",
                    font: "bold 12pt sans-serif",
                    editable: true,
                    isMultiline: false,
                },
            ),
            $("TreeExpanderButton", 
                { alignment: go.Spot.Left, alignmentFocus: go.Spot.Top },
                { visible: true }
            ),
        ),  // textblock.text = data.key

        // four small named ports, one on each side:
        makePort("T", go.Spot.Top, false, true),
        makePort("L", go.Spot.Left, true, true),
        makePort("R", go.Spot.Right, true, true),
        makePort("B", go.Spot.Bottom, true, false),

        { // handle mouse enter/leave events to show/hide the ports
            mouseEnter: (e, node) => showSmallPorts(node, true),
            mouseLeave: (e, node) => showSmallPorts(node, false)
        }
    );
};

export const createDiagramLinkTemplate = () => {
    return $(go.Link,  // the whole link panel
        { selectable: true},
        { relinkableFrom: true, relinkableTo: true, reshapable: true },
        {
            routing: go.Link.AvoidsNodes,
            curve: go.Link.JumpOver,
            corner: 5,
            toShortLength: 4
        },
    
        new go.Binding("points").makeTwoWay(),
    
        $(go.Shape,  // the link path shape
            { 
                isPanelMain: true, 
                strokeWidth: 4, 
                strokeDashArray: [0, 0]
            },
            new go.Binding("stroke", "color"),
            new go.Binding("strokeDashArray", "dash"),
        ),
    
        $(go.Shape,  // the arrowhead
            { toArrow: "Standard", stroke: null, scale: 2 },
            new go.Binding("toArrow", "toArrow")
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
                    font: "10pt helvetica, arial, sans-serif",
                    stroke: "black",
                    margin: 2,
                    minSize: new go.Size(10, NaN),
                    editable: true,
                    isMultiline: false
                },
                new go.Binding("text").makeTwoWay(),
                new go.Binding("editable", "type", type => type?.slice(0, 3) === "(+)" || type?.slice(0, 3) === "(-)"),
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
            curve: go.Link.JumpOver,
            corner: 5,
            toShortLength: 4,
            margin: 100
        },
        new go.Binding("points"),

        $(go.Shape,  // the link path shape
            { 
                isPanelMain: true, 
                strokeWidth: 2,
                stroke: "red",
                strokeDashArray: [0, 0],
                
            },
            new go.Binding("stroke", "color"),
            new go.Binding("strokeDashArray", "dash"),
        ),

        $(go.Shape,  // the arrowhead
            { toArrow: "Standard", stroke: null, scale: 2 },
            new go.Binding("toArrow", "toArrow"),
        ),

        $(go.TextBlock,
            {
                textAlign: "bottom",
                stroke: "black",
                font: "9pt sans-serif",
                segmentOffset: new go.Point(26, 0),
            },
            new go.Binding("text").makeTwoWay()
        )
    );
}
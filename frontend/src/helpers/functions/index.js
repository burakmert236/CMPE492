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
            port.fill = show ? "rgba(0,0,0,.3)" : null;
        }
    });
};

export const createDiagramNodeTemplate = () => {
    return $(go.Node, "Auto",
        { resizable: true, resizeObjectName: "PANEL" },
        $(go.Shape, "RoundedRectangle",
            {
                portId: "", // the default port: if no spot on link data, use closest side
                fromLinkable: true, toLinkable: true, cursor: "pointer",
                fill: "white",  // default color
                strokeWidth: 2
            },
            new go.Binding("fill", "color")
        ),  // shape.fill = data.color

        $(go.Panel, "Table",  
            { background: "lightgray", },
            { defaultAlignment: go.Spot.Left },
            $(go.TextBlock,
                { 
                    font: "bold 12pt sans-serif",
                    editable: true,
                    isMultiline: false,
                    maxSize: new go.Size(200, NaN),
                },
                new go.Binding("font", "", function(textBlock) {
                    var panel = textBlock.panel;
      
                    if (panel && panel.actualBounds.width > panel.maxSize.width) {
                        var fontSize = (panel.maxSize.width / panel.actualBounds.width) * textBlock.font.size;
                        return textBlock.font.fontStyle + " " + fontSize + "pt " + textBlock.font.family;
                    }
                    return textBlock.font;
                }),
                new go.Binding("text", "key")
            ),
            $("TreeExpanderButton")
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
            { isPanelMain: true, strokeWidth: 2 }
        ),
    
        $(go.Shape,  // the arrowhead
            { toArrow: "Standard", stroke: null }
        ),

        $(go.Panel, "Auto",
            new go.Binding("visible", "isSelected").ofObject(),
            $(go.Shape, "RoundedRectangle",  // the link shape
                { fill: "#F8F8F8", stroke: null },
                new go.Binding("fill", "color")
            ),

            $(go.TextBlock,
                {
                    textAlign: "center",
                    font: "10pt helvetica, arial, sans-serif",
                    stroke: "#919191",
                    margin: 2,
                    minSize: new go.Size(10, NaN),
                    editable: true
                },
                new go.Binding("text").makeTwoWay()
            )
        )
    );
};

export const createPaletteLinkTemplate = () => {
    return $(go.Link,
        { // because the GridLayout.alignment is Location and the nodes have locationSpot == Spot.Center,
          // to line up the Link in the same manner we have to pretend the Link has the same location spot
            locationSpot: go.Spot.Center,
            selectionAdornmentTemplate:
                $(go.Adornment, "Link",
                    { locationSpot: go.Spot.Center },
                    $(go.Shape,
                        { isPanelMain: true, fill: null, stroke: "deepskyblue", strokeWidth: 0 }
                    ),
                    $(go.Shape,  // the arrowhead
                        { toArrow: "Standard", stroke: null }
                    )
                )
        },
        {
            routing: go.Link.AvoidsNodes,
            curve: go.Link.JumpOver,
            corner: 5,
            toShortLength: 4
        },
        new go.Binding("points"),

        $(go.Shape,  // the link path shape
            { isPanelMain: true, strokeWidth: 2 }
        ),

        $(go.Shape,  // the arrowhead
            { toArrow: "Standard", stroke: null }
        )
    );
}
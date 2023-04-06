import * as go from "gojs";
const $ = go.GraphObject.make;

export const createPaletteNodeTemplate = () => {
    return $(go.Node, "Vertical",
        { locationObjectName: "TB", locationSpot: go.Spot.Center },
        $(go.Shape, "Terminator",
            { 
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

        $(go.Shape, "Terminator",
            {
                name: "SHAPE", fill: "#000", strokeWidth: 2,
                stroke: "#000",
                portId: "",  // this Shape is the Node's port, not the whole Node
                fromLinkable: true,
                toLinkable: true,
                cursor: "pointer",
                minSize: new go.Size(120, 50),
            },
            new go.Binding("fill", "color"),
        ),

        $(go.Panel, "Auto",  
            { defaultAlignment: go.Spot.Center },

            $(go.Shape, "Terminator",
                {
                    fill: "red",  // default color
                    strokeWidth: 2,
                    name: "PANEL",
                    minSize: new go.Size(120, 50),
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
                    margin: 15
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
                strokeWidth: 3, 
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
                    font: "bold 10pt helvetica, arial, sans-serif",
                    stroke: "white",
                    margin: 2,
                    minSize: new go.Size(1, NaN),
                    editable: true,
                    isMultiline: false,
                },
                new go.Binding("text").makeTwoWay(),
                new go.Binding("editable", "type", type => ["C+", "C-", "V+", "V-"].includes(type?.slice(0, 2))),
                new go.Binding("visible", "type", type => type !== "Refinement"),
                new go.Binding("font", "type", type => type === "Refinement" ? "0pt helvetica, arial, sans-serif" : "bold 10pt helvetica, arial, sans-serif"),

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

export const hasCycle = (diagram, link, linkType) => {
    // Check if the link is of the specific type you want to check for cycles in
    if (link?.data?.type !== linkType) {
        return false;
    }

    var stack = new go.List(/*go.Node*/);
    var coll = new go.List(/*go.List*/);

    function find(source, end) {
        source?.findNodesOutOf().each(n => {
            if (n === source) return;  // ignore reflexive links
            if (n === end) {  // success
                var path = stack.copy();
                path.add(end);  // finish the path at the end node
                coll.add(path);  // remember the whole path
            } else if (!stack.has(n)) {  // inefficient way to check having visited
                stack.add(n);  // remember that we've been here for this path (but not forever)
                find(n, end);
                stack.removeAt(stack.count - 1);
            }  // else might be a cycle
        });
    };

    stack.add(link?.fromNode);  // start the path at the begin node
    find(link?.fromNode, link?.toNode);

    // Return a string representation of a path for humans to read.
    function pathToString(path) {
        var s = path.length + ": ";
        for (var i = 0; i < path.length; i++) {
          if (i > 0) s += " -- ";
          s += path.get(i).data.key;
        }
        return s;
    }

    coll.each(p => {
        console.log(pathToString(p));
    });

    // Find all paths from the link's "from" node to its "to" node
    // var paths = diagram.findPathsBetween(link.fromNode, link.toNode);

    // console.log(paths)

    // // Filter out paths that do not contain the link
    // paths = paths.filter(function(path) {
    //     return path.contains(link);
    // });

    // // Check if there are any cycles in the remaining paths
    // return paths.any(function(path) {
    //     return path.count > 1;
    // });
}
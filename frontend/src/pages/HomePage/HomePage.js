import React from "react";
import { useRef, useEffect, useState } from "react";
import Navbar from "../../components/Navbar/Navbar";
import Toolbar from "../../components/Toolbar/Toolbar";
import Canvas from "../../components/Canvas/Canvas";
import * as go from "gojs";

import "./HomePage.scss";

const HomePage = () => {
    var $ = go.GraphObject.make;
    const diagramRef = useRef(null);
    const paletteRef = useRef(null);
    const commandHandlerRef = useRef(null);

    const [diagramObject, setDiagramObject] = useState();

    useEffect(() => {
        const diagram = go.GraphObject.make(go.Diagram, diagramRef.current, {initialContentAlignment: go.Spot.Center,
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
            "undoManager.isEnabled": true
        });
            

        diagram.commandHandler = new go.CommandHandler();
        commandHandlerRef.current = diagram.commandHandler;
        
        function makePort(name, spot, output, input) {
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
              });
          }

          function showSmallPorts(node, show) {
            node.ports.each(port => {
              if (port.portId !== "") {  // don't change the default port, which is the big shape
                port.fill = show ? "rgba(0,0,0,.3)" : null;
              }
            });
          }

        diagram.nodeTemplate =
            $(go.Node, "Auto",
                { resizable: true, resizeObjectName: "PANEL" },
                $(go.Shape, "RoundedRectangle",
                {
                    portId: "", // the default port: if no spot on link data, use closest side
                    fromLinkable: true, toLinkable: true, cursor: "pointer",
                    fill: "white",  // default color
                    strokeWidth: 2
                },
                new go.Binding("fill", "color")),  // shape.fill = data.color
                $(go.Panel, "Table",  { background: "lightgray", },
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

        diagram.linkTemplate =
            $(go.Link,  // the whole link panel
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
            { isPanelMain: true, strokeWidth: 2 }),
            $(go.Shape,  // the arrowhead
            { toArrow: "Standard", stroke: null }),
            $(go.Panel, "Auto",
            new go.Binding("visible", "isSelected").ofObject(),
            $(go.Shape, "RoundedRectangle",  // the link shape
                { fill: "#F8F8F8", stroke: null },
                new go.Binding("fill", "color")),
            $(go.TextBlock,
                {
                textAlign: "center",
                font: "10pt helvetica, arial, sans-serif",
                stroke: "#919191",
                margin: 2,
                minSize: new go.Size(10, NaN),
                editable: true
                },
                new go.Binding("text").makeTwoWay())
            )
        );

        var nodeDataArray = [
            { key: "Alpha", color: "lightblue" },
            { key: "Beta", color: "pink" }
        ];
        var linkDataArray = [
            { from: "Alpha", to: "Beta", color: "blue", thick: 2 }
        ];
        diagram.model = new go.GraphLinksModel(nodeDataArray, linkDataArray);

        setDiagramObject(diagram);
        
    }, []);

    useEffect(() => {
        if(!diagramObject) return;

        var $ = go.GraphObject.make;
        const myPalette =
        $(go.Palette, paletteRef.current,  // must name or refer to the DIV HTML element
          {
            maxSelectionCount: 1,
            nodeTemplateMap: diagramObject.nodeTemplateMap,  // share the templates used by myDiagram
            linkTemplate: // simplify the link template, just in this Palette
              $(go.Link,
                { // because the GridLayout.alignment is Location and the nodes have locationSpot == Spot.Center,
                  // to line up the Link in the same manner we have to pretend the Link has the same location spot
                  locationSpot: go.Spot.Center,
                  selectionAdornmentTemplate:
                    $(go.Adornment, "Link",
                      { locationSpot: go.Spot.Center },
                      $(go.Shape,
                        { isPanelMain: true, fill: null, stroke: "deepskyblue", strokeWidth: 0 }),
                      $(go.Shape,  // the arrowhead
                        { toArrow: "Standard", stroke: null })
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
                  { isPanelMain: true, strokeWidth: 2 }),
                $(go.Shape,  // the arrowhead
                  { toArrow: "Standard", stroke: null })
              ),
            model: new go.GraphLinksModel([  // specify the contents of the Palette
              { text: "Start", figure: "Ellipse", "size":"75 75", fill: "#00AD5F" },
              { text: "Step" },
              { text: "DB", figure: "Database", fill: "lightgray" },
              { text: "???", figure: "Diamond", fill: "lightskyblue" },
              { text: "End", figure: "Ellipse", "size":"75 75", fill: "#CE0620" },
              { text: "Comment", figure: "RoundedRectangle", fill: "lightyellow" }
            ], [
                // the Palette also has a disconnected Link, which the user can drag-and-drop
                { points: new go.List(/*go.Point*/).addAll([new go.Point(0, 0), new go.Point(30, 0), new go.Point(30, 40), new go.Point(60, 40)]), color: "red" },
                { points: new go.List(/*go.Point*/).addAll([new go.Point(0, 0), new go.Point(30, 0), new go.Point(30, 40), new go.Point(60, 40)]), color: "blue" }
              ])
          });
    
    }, [diagramObject])


    function handleDrop(targetType) {
  
        const diagram = diagramObject;
        const point = diagram.lastInput.viewPoint;

    
        if (targetType) {
          const link = $(go.Link, {
            routing: go.Link.AvoidsNodes,
            curve: go.Link.JumpOver,
            corner: 10,
            toShortLength: 4,
            relinkableFrom: true,
            relinkableTo: true
          });
    
          link.fromSpot = go.Spot.Bottom;
          link.toSpot = go.Spot.Top;
    
          diagram.add(link);
    
          const linkData = {
            targetType: targetType,
            fromPortId: "dummy1",
            toPortId: "dummy2"
          };
    
          diagram.model.addLinkData(linkData);
      
          diagram.toolManager.linkingTool.startObject = link;
          diagram.toolManager.linkingTool.doActivate();
          diagram.toolManager.linkingTool.doMouseMove(point);
        }
    }

    return (
        <div className="homepage-layout">
            
            <Navbar commandHandlerRef={commandHandlerRef}/>

            <div className="homepage-main">

                <div className="palette" ref={paletteRef} style={{ height: "600px", width: "100px"}}></div>

                <Toolbar />

                <Canvas diagramRef={diagramRef} onDrop={handleDrop}/>

            </div>

        </div>
    );
};

export default HomePage;
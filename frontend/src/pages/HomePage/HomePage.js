import React from "react";
import { useRef, useEffect } from "react";
import Navbar from "../../components/Navbar/Navbar";
import Toolbar from "../../components/Toolbar/Toolbar";
import Canvas from "../../components/Canvas/Canvas";
import * as go from "gojs";

import "./HomePage.scss";

const HomePage = () => {
    const diagramRef = useRef(null);
    const commandHandlerRef = useRef(null);
    useEffect(() => {
        const diagram = go.GraphObject.make(go.Diagram, diagramRef.current, {initialContentAlignment: go.Spot.Center,
            'undoManager.isEnabled': true,});

        diagram.commandHandler = new go.CommandHandler();
        commandHandlerRef.current = diagram.commandHandler;
        var $ = go.GraphObject.make;
        diagram.nodeTemplate =
            $(go.Node, "Auto",
                { resizable: true, resizeObjectName: "PANEL" },
                $(go.Shape, "RoundedRectangle",
                { fill: "white" },
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
                        console.log(panel);
                        if (panel && panel.actualBounds.width > panel.maxSize.width) {
                        var fontSize = (panel.maxSize.width / panel.actualBounds.width) * textBlock.font.size;
                        return textBlock.font.fontStyle + " " + fontSize + "pt " + textBlock.font.family;
                        }
                        return textBlock.font;
                    }),
                    new go.Binding("text", "key")
                    ),
                )  // textblock.text = data.key
            );

        diagram.linkTemplate =
            $(go.Link,
                $(go.Shape,
                new go.Binding("stroke", "color"),  // shape.stroke = data.color
                new go.Binding("strokeWidth", "thick")),  // shape.strokeWidth = data.thick
                $(go.Shape,
                { toArrow: "OpenTriangle", fill: null },
                new go.Binding("stroke", "color"),  // shape.stroke = data.color
                new go.Binding("strokeWidth", "thick"))  // shape.strokeWidth = data.thick
            );

        var nodeDataArray = [
            { key: "Alpha", color: "lightblue" },
            { key: "Beta", color: "pink" }
        ];
        var linkDataArray = [
            { from: "Alpha", to: "Beta", color: "blue", thick: 2 }
        ];
        diagram.model = new go.GraphLinksModel(nodeDataArray, linkDataArray);
        
      }, []);
    return (
        <div className="homepage-layout">
            
            <Navbar  commandHandlerRef={commandHandlerRef}/>

            <div className="homepage-main">

                <Toolbar />

                <Canvas diagramRef={diagramRef}/>

            </div>

        </div>
    );
};

export default HomePage;
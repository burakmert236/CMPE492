import React from "react";
import { useRef, useEffect, useState } from "react";
import * as go from "gojs";

import Navbar from "../../components/Navbar/Navbar";
import Palette from "../../components/Palette/Palette";
import Canvas from "../../components/Canvas/Canvas";

import { diagramConfiguration, paletteNodeDataArray, paletteLinkDataArray, paletteConfiguration } from "../../helpers/constants";
import { createDiagramNodeTemplate, createDiagramLinkTemplate, createPaletteLinkTemplate, createPaletteNodeTemplate } from "../../helpers/functions";

import "./HomePage.scss";
import Dashboard from "../../components/Dashboard/Dashboard";

const HomePage = () => {
    const $ = go.GraphObject.make;

    const diagramRef = useRef(null);
    const paletteRef = useRef(null);
    const commandHandlerRef = useRef(null);
    const [selectedNode, setSelectedNode] = useState(null);
    const [diagramObject, setDiagramObject] = useState();

    useEffect(() => {
		// initialize diagram with some configuration
        const diagram = go.GraphObject.make(go.Diagram, diagramRef.current, diagramConfiguration);
            
		// create a command handler to use redo/undo functions
        diagram.commandHandler = new go.CommandHandler();
        commandHandlerRef.current = diagram.commandHandler;

		// initial diagram node temaplate
        diagram.nodeTemplate = createDiagramNodeTemplate(setSelectedNode);

		// initial diagram link template
        diagram.linkTemplate = createDiagramLinkTemplate(setSelectedNode);
            
        diagram.model = new go.GraphLinksModel();

        setDiagramObject(diagram);
        
    }, []);

    useEffect(() => {
        if(!diagramObject) return;

        const palette = $(go.Palette, paletteRef.current, paletteConfiguration);

		palette.nodeTemplate = createPaletteNodeTemplate();

        palette.linkTemplate = createPaletteLinkTemplate();

		palette.model = new go.GraphLinksModel(paletteNodeDataArray, paletteLinkDataArray)
    
    }, [$, diagramObject]);

    useEffect(() => {
        if(!diagramObject) return;

        diagramObject.addDiagramListener("ExternalObjectsDropped", function(e) {
            const sel = e.diagram.selection;
            if (sel.count === 1) {  // make sure only one object was dropped
                const obj = sel.first();

                if (obj instanceof go.Link) {  // make sure it's a link
                    let newText = null;

                    if(obj?.data?.type === "(+) Cost Contribution" || obj?.data?.type === "(+) Value Contribution")
                        newText = "+1";

                    if(obj?.data?.type === "(-) Cost Contribution" || obj?.data?.type === "(-) Value Contribution")
                        newText = "-1";

                    if(obj?.data?.type === "Precedence") newText = "Precedes";

                    if(obj?.data?.type === "Exclusion") newText = "Excludes";

                    const droppedPositionX = diagramObject?.lastInput?.documentPoint?.x;
                    const droppedPositionY = diagramObject?.lastInput?.documentPoint?.y;

                    diagramObject.model.setDataProperty(obj.data, "text", newText);
                    diagramObject.model.setDataProperty(
                        obj.data, 
                        "points", 
                        new go.List(/*go.Point*/).addAll([
                            new go.Point(droppedPositionX - 70, droppedPositionY - 40), 
                            new go.Point(droppedPositionX + 70, droppedPositionY + 40),
                        ])
                    );
                }
            }
        });

        diagramObject.addDiagramListener("TextEdited", function(e) {
            const label = e.subject;
            const newText = label.text;
            let newValue = parseInt(newText);

            const sel = e.diagram.selection;
            const obj = sel.first();

            if (obj instanceof go.Node) {
                return;
            }
          
            if (obj?.data?.type?.slice(0, 3) === "(+)") {
                newValue = Math.abs(parseInt(newValue));

                if(isNaN(newValue)) {
                    // Revert to the previous text
                    label.text = `+${label.part.data.value}`;
                    diagramObject.commitTransaction();
                    return;
                }

                label.part.data.value = parseInt(newValue);
                label.text = `+${parseInt(newValue)}`;
                diagramObject.commitTransaction();
            } else if(obj?.data?.type?.slice(0, 3) === "(-)") {
                newValue = Math.abs(parseInt(newValue));

                if(isNaN(newValue)) {
                    // Revert to the previous text
                    label.text = `-${label.part.data.value}`;
                    diagramObject.commitTransaction();
                    return;
                }

                label.part.data.value = parseInt(newValue);
                label.text = `-${parseInt(newValue)}`;
                diagramObject.commitTransaction();
            } else {
                // Revert to the previous text
                label.text = label.part.data.value;
                diagramObject.commitTransaction();
            }
          });

    }, [diagramObject])

    return (
        <div className="homepage-layout">
            
            <Navbar commandHandlerRef={commandHandlerRef}/>

            <div className="palette-container">
                <Palette paletteRef={paletteRef}/>
            </div>

            <div className="homepage-main">

                <div className="homepage-dashboard">
                    <Dashboard selectedNode={selectedNode} />
                </div>

                <Canvas diagramRef={diagramRef} />

            </div>

        </div>
    );
};

export default HomePage;
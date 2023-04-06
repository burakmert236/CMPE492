import React from "react";
import { useRef, useEffect, useState } from "react";
import * as go from "gojs";

import Navbar from "../../components/Navbar/Navbar";
import Palette from "../../components/Palette/Palette";
import Canvas from "../../components/Canvas/Canvas";

import { 
    diagramConfiguration, 
    paletteNodeDataArray, 
    paletteLinkDataArray, 
    paletteConfiguration 
} from "../../helpers/constants";

import { 
    createDiagramNodeTemplate, 
    createDiagramLinkTemplate, 
    createPaletteLinkTemplate, 
    createPaletteNodeTemplate,
    detectCycleForSpecificLinkType,
    detectCycleAndMarkNodes
} from "../../helpers/functions";

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
        // create terminator shape
        go.Shape.defineFigureGenerator("Terminator", function(shape, w, h) {
            var geo = new go.Geometry();
            var fig = new go.PathFigure(.25 * w, 0, true);
            geo.add(fig);
          
            fig.add(new go.PathSegment(go.PathSegment.Arc, 270, 180, .75 * w, 0.5 * h, .25 * w, .5 * h));
            fig.add(new go.PathSegment(go.PathSegment.Arc, 90, 180, .25 * w, 0.5 * h, .25 * w, .5 * h));
            return geo;
        });
        
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

        const cycleDetectFunction = (e) => {
            const link = e.subject;
            const cycleTypes = ["Refinement", "Precedence"];

            diagramObject.startTransaction('Check for cycle');

            for(let i = 0; i<cycleTypes?.length; i++) {
                if (detectCycleForSpecificLinkType(diagramObject, cycleTypes[i])) {
                    // if cycle found, remove link and display error message
                    alert(`Cannot create cycle with ${cycleTypes[i]} links!`);
                    diagramObject.remove(link);
                    diagramObject.commitTransaction('Check for cycle');
                    break;
                }
            }
        }

        diagramObject.addDiagramListener("LinkDrawn", cycleDetectFunction);
        diagramObject.addDiagramListener("LinkRelinked", cycleDetectFunction);
    }, [diagramObject]);

    useEffect(() => {
        if(!diagramObject) return;

        diagramObject.addDiagramListener("ExternalObjectsDropped", function(e) {
            const sel = e.diagram.selection;
            if (sel.count === 1) {  // make sure only one object was dropped
                const obj = sel.first();

                if (obj instanceof go.Link) {  // make sure it's a link
                    let newText = null;

                    if(obj?.data?.type === "C+" || obj?.data?.type === "C-" || obj?.data?.type === "V+" || obj?.data?.type === "V-")
                        newText = obj?.data?.type;

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
            let newText = label.text;

            const sel = e.diagram.selection;
            const obj = sel.first();

            if(obj instanceof go.Node) {
                diagramObject.commitTransaction();
                return;
            }
          
            if (obj?.data?.type === "C+" || obj?.data?.type === "V+") {
                if(newText?.slice(0, 1) === "C" || newText?.slice(0, 1) === "V") newText = newText.slice(1);

                let newValue = Math.abs(parseInt(newText));

                if(isNaN(newValue)) {
                    // Revert to the previous text
                    label.text = `${obj?.data?.type}${label.part.data.value}`;
                    diagramObject.commitTransaction();
                    return;
                }

                label.part.data.value = parseInt(newValue);
                label.text = `${obj?.data?.type}${parseInt(newValue)}`;
                diagramObject.commitTransaction();
            } else if (obj?.data?.type === "C-" || obj?.data?.type === "V-") {
                if(newText?.slice(0, 1) === "C" || newText?.slice(0, 1) === "V") newText = newText.slice(1);

                let newValue = Math.abs(parseInt(newText));

                if(isNaN(newValue)) {
                    // Revert to the previous text
                    label.text = `${obj?.data?.type}${label.part.data.value}`;
                    diagramObject.commitTransaction();
                    return;
                }

                label.part.data.value = parseInt(newValue);
                label.text = `${obj?.data?.type}${parseInt(newValue)}`;
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
                    <Dashboard selectedNode={selectedNode} diagram={diagramObject} />
                </div>

                <Canvas diagramRef={diagramRef} />

            </div>

        </div>
    );
};

export default HomePage;
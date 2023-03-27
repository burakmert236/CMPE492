import React from "react";
import { useRef, useEffect, useState } from "react";
import * as go from "gojs";

import Navbar from "../../components/Navbar/Navbar";
import Toolbar from "../../components/Toolbar/Toolbar";
import Canvas from "../../components/Canvas/Canvas";

import { diagramConfiguration, paletteNodeDataArray, paletteLinkDataArray, paletteConfiguration } from "../../helpers/constants";
import { createDiagramNodeTemplate, createDiagramLinkTemplate, createPaletteLinkTemplate } from "../../helpers/functions";

import "./HomePage.scss";

const HomePage = () => {
    const $ = go.GraphObject.make;

    const diagramRef = useRef(null);
    const paletteRef = useRef(null);
    const commandHandlerRef = useRef(null);

    const [diagramObject, setDiagramObject] = useState();

    useEffect(() => {
		// initialize diagram with some configuration
        const diagram = go.GraphObject.make(go.Diagram, diagramRef.current, diagramConfiguration);
            
		// create a command handler to use redo/undo functions
        diagram.commandHandler = new go.CommandHandler();
        commandHandlerRef.current = diagram.commandHandler;

		// initial diagram node temaplate
        diagram.nodeTemplate = createDiagramNodeTemplate();

		// initial diagram link template
        diagram.linkTemplate = createDiagramLinkTemplate();
            
        diagram.model = new go.GraphLinksModel();

        setDiagramObject(diagram);
        
    }, []);

    useEffect(() => {
        if(!diagramObject) return;

        const palette = $(go.Palette, paletteRef.current, paletteConfiguration);

		palette.nodeTemplateMap = diagramObject.nodeTemplateMap;

		palette.linkTemplate = createPaletteLinkTemplate();

		palette.model = new go.GraphLinksModel(paletteNodeDataArray, paletteLinkDataArray)
    
    }, [$, diagramObject]);

    return (
        <div className="homepage-layout">
            
            <Navbar commandHandlerRef={commandHandlerRef}/>

            <div className="homepage-main">

                <Toolbar paletteRef={paletteRef}/>

                <Canvas diagramRef={diagramRef}/>

            </div>

        </div>
    );
};

export default HomePage;
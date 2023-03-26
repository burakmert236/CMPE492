import React from "react";
import { useRef, useEffect } from "react";
import Navbar from "../../components/Navbar/Navbar";
import Toolbar from "../../components/Toolbar/Toolbar";
import Canvas from "../../components/Canvas/Canvas";
import * as go from "gojs";

import "./HomePage.scss";

const HomePage = () => {
    const diagramRef = useRef(null);
    useEffect(() => {
        const diagram = go.GraphObject.make(go.Diagram, diagramRef.current, {initialContentAlignment: go.Spot.Center,
            'undoManager.isEnabled': true,});

        diagram.commandHandler = new go.CommandHandler();
        
        diagram.model = new go.GraphLinksModel(
            [{ key: "Hello" },   // two node data, in an Array
             { key: "World!" }],
            [{ from: "Hello", to: "World!"}]  // one link data, in an Array
          );
      }, []);
    return (
        <div className="homepage-layout">
            
            <Navbar />

            <div className="homepage-main">

                <Toolbar />

                <Canvas diagramRef={diagramRef}/>

            </div>

        </div>
    );
};

export default HomePage;
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
    junctionNodeTemplate,
    exclusionNodeTemplate,
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
        
        diagram.nodeTemplateMap.add("Junction", junctionNodeTemplate());
        diagram.nodeTemplateMap.add("Exclusion", exclusionNodeTemplate());
		// initial diagram link template
        diagram.linkTemplate = createDiagramLinkTemplate(setSelectedNode);
        function linkColorConverter(fromNodeType) {
            if (fromNodeType === "Exclusion") {
              return "red";
            } else {
              return "black";
            }
          }
          diagram.linkTemplate =
            $(go.Link,
                { curve: go.Link.Bezier, adjusting: go.Link.Stretch, reshapable: true, relinkableFrom: true, relinkableTo: true },
                $(go.Shape,
                { strokeWidth: 1.5 },
                new go.Binding("stroke", "fromNode.nodeType", linkColorConverter).ofObject() // Update this line
                ),
                $(go.Shape, { toArrow: "Standard", strokeWidth: 0 },
                new go.Binding("fill", "fromNode.nodeType", linkColorConverter).ofObject(), // Add this line
                new go.Binding("stroke", "fromNode.nodeType", linkColorConverter).ofObject() // Add this line
                )
            );

        diagram.linkTemplateMap.add("ANDRefinement", createDiagramLinkTemplate(setSelectedNode))
            
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

    // cycle detect
    useEffect(() => {
        if(!diagramObject) return;

        const cycleDetectFunction = (e) => {
            const link = e.subject;
            const cycleTypes = ["Refinement", "Precedence", "AND Refinement"];

            for(let i = 0; i<cycleTypes?.length; i++) {
                if (detectCycleForSpecificLinkType(diagramObject, cycleTypes[i])) {
                    // if cycle found, remove link and display error message
                    alert(`Cannot create cycle with ${cycleTypes[i]} links!`);
                    diagramObject.remove(link);
                    break;
                }
            }
        }

        const junctionConstruction = (e) => {
            const link = e.subject;
            if (link.category === "ANDRefinement") {
                const fromNode = link?.fromNode;
                const subjectToNode = link?.toNode;

                if(!subjectToNode || !fromNode) return;

                let existingFromLink = false;
                let existingFromNode = null;
                fromNode.findLinksConnected().each(function(l) {
                    if (l.category === "ANDRefinement" && l !== link && l?.data?.fromArrow === "Backward") {
                        existingFromLink = l;
                        existingFromNode = diagramObject.findNodeForKey(l?.data?.to);
                    }
                });

                // Check if there's an existing AND-refinement link
                const existingLinks = new go.List();
                fromNode.findLinksOutOf().all(function(l) {
                    if (l.category === "ANDRefinement" && l !== link) {
                        existingLinks.add(l);
                    }
                });


                const toNodes = existingLinks?.toArray().map(l => l?.toNode);

                const junctionLinkProps = {
                    category: "ANDRefinement",
                    type: "AND Refinement",
                    toArrow: "null",
                    fromArrow: "null",
                    color: "black",
                    fromShortLength: 8,
                    toShortLength: 0,
                    reshapable: false,
                    relinkableTo: false,
                    relinkableFrom: false
                }

                if (existingLinks.count > 0) {

                    const existingJunctionNode = toNodes?.find(n => n?.category === "Junction");
                    const existingJunctionLink = existingLinks?.toArray()?.find(l => l?.toNode?.key === existingJunctionNode?.key);
                    
                    if(existingJunctionNode && existingJunctionLink?.data?.fromArrow !== "Backward" && !existingFromLink) return;

                    if(existingJunctionNode && (!existingFromLink || existingFromNode?.category === "Junction")) {
                        const junctionNode = existingFromLink && existingFromNode?.category === "Junction" ? existingFromNode : existingJunctionNode;
                        diagramObject.model.addLinkData({ from: subjectToNode.key, to: junctionNode.key, ...junctionLinkProps });
                        diagramObject.remove(link);
                        return;
                    }

                    if(existingFromLink && !toNodes?.find(n => n?.key === existingFromNode?.key)) toNodes.push(existingFromNode);

                    // create a new juction node
                    let centerPoint = { x: 0, y: 0 };
                    [fromNode].concat([subjectToNode]).concat(toNodes)?.filter(n => n?.data?.category !== "Junction")?.forEach(n => {
                        centerPoint.x = centerPoint.x + n?.location?.x;
                        centerPoint.y = centerPoint.y + n?.location?.y;
                    })
                    centerPoint.x = centerPoint.x / (toNodes?.length + 2);
                    centerPoint.y = centerPoint.y / (toNodes?.length + 2);

                    // Create a junction node
                    const junctionNodeData = {
                        category: "Junction",
                        location: new go.Point(centerPoint.x, centerPoint.y - 20)
                    };
                    diagramObject.model.addNodeData(junctionNodeData);
                    const junctionNode = diagramObject.findNodeForData(junctionNodeData);

                    diagramObject.model.addLinkData({ from: fromNode.key, to: junctionNode.key, ...junctionLinkProps, fromArrow: "Backward" });
                    diagramObject.model.addLinkData({ from: subjectToNode.key, to: junctionNode.key, ...junctionLinkProps });

                    toNodes?.map(toNode => {
                        return diagramObject.model.addLinkData({ from: toNode.key, to: junctionNode.key, ...junctionLinkProps });
                    })

                    if(existingFromLink) existingLinks.push(existingFromLink);

                    existingLinks?.toArray()?.concat([link])?.forEach(l => {
                        if(l?.data?.fromArrow === "Backward") diagramObject.remove(l);
                    });
                }
            
            }
        }

        const linkEventListener = (e) => {
            cycleDetectFunction(e);
            junctionConstruction(e);
        }

        diagramObject.addDiagramListener("LinkDrawn", linkEventListener);
        diagramObject.addDiagramListener("LinkRelinked", linkEventListener);
    }, [diagramObject]);

    // text edit events
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

                    if(obj?.data?.type === "AND Refinement") newText = "AND";

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

                if (obj instanceof go.Node) {
                    let nodeCount = 0;
                    // Iterate through all the nodes in the diagram
                    diagramObject.nodes.each(function (node) {
                        if(!(node?.data?.category === "Junction" || node?.data?.category === "Exclusion")) nodeCount = nodeCount + 1;
                    });

                    diagramObject.model.setDataProperty(obj.data, "text", "Goal " + nodeCount);
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

    // move listener 
    useEffect(() => {
        if(!diagramObject) return;

        // Add a SelectionMoved event listener to the diagram
        diagramObject.addDiagramListener("SelectionMoved", function(e) {
            const node = e.diagram.selection.first();
            if (node !== null && node instanceof go.Node) {
                setSelectedNode(node);
            }
        });
    }, [diagramObject])

    return (
        <div className="homepage-layout">
            
            <Navbar commandHandlerRef={commandHandlerRef} diagram={diagramObject}/>

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
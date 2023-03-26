import React, { useRef, useEffect } from "react";
import "./Canvas.scss";


const Canvas = ({diagramRef}) => {

    return(
        <div className="canvas-container">
            Canvas
            <div ref={diagramRef} style={{ height: "100%", width: "100%"}}></div>
        </div>
    );
};

export default Canvas;
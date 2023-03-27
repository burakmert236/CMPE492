import React from "react";
import "./Canvas.scss";


const Canvas = ({ diagramRef }) => {

    return(
        <div className="canvas-container" onDragOver={(e) => e.preventDefault()} >
            <div ref={diagramRef} style={{ height: "100%", width: "100%"}}></div>
        </div>
    );
};

export default Canvas;
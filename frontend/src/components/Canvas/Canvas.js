import React, { useRef, useEffect } from "react";
import "./Canvas.scss";


const Canvas = ({diagramRef, onDrop}) => {
    function handleDrop(event) {
        event.preventDefault();
        const targetType = event.dataTransfer.getData('targetType');
        console.log(targetType)
        onDrop(targetType);
      }

    return(
        <div className="canvas-container" onDragOver={(e) => e.preventDefault()} onDrop={handleDrop}>
            Canvas
            <div ref={diagramRef} style={{ height: "100%", width: "100%"}}></div>
        </div>
    );
};

export default Canvas;
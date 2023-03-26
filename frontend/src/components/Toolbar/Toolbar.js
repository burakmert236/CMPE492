import React from "react";

import "./Toolbar.scss";

const Toolbar = ({onDrop}) => {
    function handleDragStart(event) {
        const targetType = event.currentTarget.getAttribute('data-target-type');
        event.dataTransfer.setData('targetType', targetType);
      }
    
    function handleDragOver(event) {
        event.preventDefault();
      }
    
    
    return(
        <div className="toolbar-container">
            Toolbar
            <div onDragOver={handleDragOver}>
                <button data-target-type="Link1" draggable onDragStart={handleDragStart}>
                    Link Type 1
                </button>
                <button data-target-type="Link2" draggable onDragStart={handleDragStart}>
                    Link Type 2
                </button>
                <button data-target-type="Link3" draggable onDragStart={handleDragStart}>
                    Link Type 3
                </button>
            </div>
        </div>
    );
};

export default Toolbar;
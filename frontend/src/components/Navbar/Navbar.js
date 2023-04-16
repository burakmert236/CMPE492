import React from "react";
import { Dropdown, Space } from 'antd';
import { DownOutlined } from '@ant-design/icons';
import * as go from "gojs";

import OptimizeDropdown from "../OptimizeDropdown/OptimizeDropdown";

import "./Navbar.scss";

const Navbar = ({ commandHandlerRef, diagram }) => {
    const generateExportLines = (type, index, func) => {
        return {
            key: `1-${index}`,
            label: (
                <div onClick={() => handleDownload(type, func)} className="export-type-line">
                    as {type}
                    { func === "Import" && 
                        <input 
                            type="file" 
                            id="importJsonFile" 
                            accept=".json" 
                            style={{ display: "none" }} 
                            onChange={(e) => handleImport(e)}
                        /> 
                    }
                </div>
            )
        }
    };

    const handleUndo = () => {
        commandHandlerRef.current.undo();
    }
    const handleRedo = () => {
        commandHandlerRef.current.redo();
    }

    const handleDownload = (type, func) => {
        if(func === "Export") {
            const link = document.createElement("a");
            let url = "";
            let blob = "";
            let fileName = "";

            if(type === "JSON") {
                // Export the diagram as JSON
                const diagramJson = diagram.model.toJson();

                // Create a Blob with the JSON data and a download link
                blob = new Blob([diagramJson], { type: "application/json;charset=utf-8" });
                url = URL.createObjectURL(blob);
                fileName = "diagram.json";
            }

            if(type === "SVG") {
                // Export the diagram as an SVG element
                const svg = diagram.makeSvg({
                    scale: 1,
                    background: "white"
                });

                // Create a Blob with the SVG data and a download link
                const svgData = new XMLSerializer().serializeToString(svg);
                blob = new Blob([svgData], { type: "image/svg;charset=utf-8" });
                url = URL.createObjectURL(blob);
                fileName = "diagram.svg" + (navigator.msSaveBlob ? ".svg" : "");
            }

            if(type === "PNG") {
                // Get the original diagram bounds
                const originalBounds = diagram.documentBounds.copy();

                // Define padding values
                const padding = 50; // You can adjust this value as needed

                // Add padding to the original bounds
                const paddedBounds = new go.Rect(
                    originalBounds.x - padding,
                    originalBounds.y - padding,
                    originalBounds.width + padding * 2,
                    originalBounds.height + padding * 2
                );

                // Export the diagram as a base64-encoded data URL (PNG)
                const imageData = diagram.makeImageData({
                    scale: 1,
                    background: "white",
                    type: "image/png",
                    position: paddedBounds.position,
                    size: paddedBounds.size
                });

                url = imageData;
                fileName = "diagram.png";
            }

            // Set the download link attributes
            link.href = url;
            link.download = fileName;
            link.style.display = "none";

            // Add the download link to the DOM, click it, and remove it
            document.body.appendChild(link);
            link.click();
            document.body.removeChild(link);
        }

        if(func === "Import") {
            const importJsonFile = document.getElementById("importJsonFile");

            // Reset the file input and open the file input dialog
            importJsonFile.value = "";
            importJsonFile.click();
        }
    }

    const handleImport = (e) => {
        // Check if a file was selected
        if (e.target.files && e.target.files.length > 0) {
            // Read the selected JSON file
            const reader = new FileReader();
            reader.onload = function(e) {
                // Parse the JSON data and load it into the diagram
                const jsonData = JSON.parse(e.target.result);
                diagram.model = go.Model.fromJson(jsonData);
            };
            reader.readAsText(e.target.files[0]);
        }
    }

    return(
        <div className="navbar">
            <div className="navbar-buttons"> 
                <div className="navbar-button logo">LOGO</div>

                <div className="navbar-button">
                    <Dropdown
                        menu={{
                            items: [
                                {
                                    key: 1,
                                    label: "Export",
                                    children: ["JSON", "SVG", "PNG", "SMT"].map((abb, index) => generateExportLines(abb, index, "Export")),
                                },
                                {
                                    key: 2,
                                    label: "Import",
                                    children: ["JSON"].map((abb, index) => generateExportLines(abb, index, "Import")),
                                }
                            ]
                        }}
                    >
                        <Space>
                            File
                            <DownOutlined />
                        </Space>
                    </Dropdown>
                </div>

                <div className="navbar-button">Options</div>

                <div className="navbar-button">Help</div>
            </div>

            <div className="right-navbar">
                <div className="redo-undo">
                    <div className="undo" onClick={() => handleUndo()}>
                        <div className="triangle right"></div>
                        <div className="label">Undo</div>
                    </div>
                    <div className="redo" onClick={() => handleRedo()}>
                        <div className="triangle left"></div>
                        <div className="label">Redo</div>
                    </div>
                </div>

                <OptimizeDropdown diagram={diagram}/>
            </div>

        </div>
    );
};

export default Navbar;
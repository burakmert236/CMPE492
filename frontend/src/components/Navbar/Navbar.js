import React from "react";
import { Dropdown, Space } from 'antd';
import { DownOutlined } from '@ant-design/icons';

import OptimizeDropdown from "../OptimizeDropdown/OptimizeDropdown";

import "./Navbar.scss";


// TODO:
//  - Logo, File, Options, Help sections will be implemented at the left side of the navbar
//  - Redo/Undo buttons will be displayed at the right side
//  - Optimize dropdown will be right most part of the navbar

const Navbar = () => {
    const generateExportLines = (type, index) => {
        return {
            key: `1-${index}`,
            label: (
                <div className="export-type-line">as {type}</div>
            )
        }
    };

    console.log(["jSON", "SVG", "PNG", "STM"].map((abb, index) => generateExportLines(abb, index)))

    return(
        <div className="navbar">
            <div className="navbar-buttons"> 
                <div className="navbar-button logo">LOGO</div>

                <div className="navbar-button">
                    <Dropdown
                        menu={{
                            items: [{
                                key: 1,
                                label: "Export",
                                children: ["jSON", "SVG", "PNG", "STM"].map((abb, index) => generateExportLines(abb, index)),
                            }]
                        }}
                    >
                        <Space>
                            File
                            <DownOutlined />
                        </Space>
                    </Dropdown>
                </div>

                <div className="navbar-button">OPTIONS</div>

                <div className="navbar-button">HELP</div>
            </div>

            <div className="right-navbar">
                <div className="redo-undo">
                    <div className="undo">
                        <div className="triangle right"></div>
                    </div>
                    <div className="redo">
                        <div className="triangle left"></div>
                    </div>
                </div>

                <OptimizeDropdown />
            </div>

        </div>
    );
};

export default Navbar;
import React from "react";

import OptimizeDropdown from "../OptimizeDropdown/OptimizeDropdown";

import "./Navbar.scss";


// TODO:
//  - Logo, File, Options, Help sections will be implemented at the left side of the navbar
//  - Redo/Undo buttons will be displayed at the right side
//  - Optimize dropdown will be right most part of the navbar

const Navbar = () => {
    return(
        <div className="navbar">
            <div> 
                Button section
            </div>

            <div>
                Redo / Undo
            </div>

            <OptimizeDropdown />

        </div>
    );
};

export default Navbar;
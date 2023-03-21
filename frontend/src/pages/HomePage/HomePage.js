import React from "react";

import Navbar from "../../components/Navbar/Navbar";
import Toolbar from "../../components/Toolbar/Toolbar";
import Canvas from "../../components/Canvas/Canvas";

import "./HomePage.scss";

const HomePage = () => {
    return (
        <div className="homepage-layout">
            
            <Navbar />

            <div className="homepage-main">

                <Toolbar />

                <Canvas />

            </div>

        </div>
    );
};

export default HomePage;
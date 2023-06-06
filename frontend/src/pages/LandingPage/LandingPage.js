import React from "react";
import { useNavigate, Link } from "react-router-dom";
import Navbar from "../../components/Navbar/Navbar";

import "./LandingPage.scss";

const LandingPage = () => {
    const navigate = useNavigate();

    return(
        <div className="homepage-layout white-background">
            
            <Navbar navType="landing"/>

            <div className="definition-section">
                <div className="definition">
                    <div className="definition-container">
                        <h1>Goal Modeling Tool</h1>
                        <p>An open-source, web-based goal modeling tool. Extremely easy to run.</p>
                        <button style={{ "backgroundColor": "#00cdb2" }} onClick={() => navigate("/tool")}>Start Now</button>
                    </div>
                </div>
                <div className="main-image">
                    <img alt="definition" src={require("./image_0.png")} />
                </div>
            </div>

            <div className="dependencies">
                <h2>Dependencies</h2>
                <p>We used following open-source libraries and frameworks</p>
                <ul>
                    <li>
                        <Link 
                            className="link" 
                            to="https://react.dev"
                            target="_blank"
                            rel="noopener noreferrer"
                        >
                            React
                        </Link>
                        {" "}- The library for web and native user interfaces
                    </li>
                    <li>
                        <Link 
                            className="link" 
                            to="https://gojs.net/latest/index.html"
                            target="_blank"
                            rel="noopener noreferrer"
                        >
                            GoJS
                        </Link>
                        {" "}- A web framework for building interactive diagrams
                    </li>
                    <li>
                        <Link 
                            className="link" 
                            to="https://ant.design"
                            target="_blank"
                            rel="noopener noreferrer"
                        >
                            Ant Design
                        </Link>
                        {" "}- A popular design system for developing enterprise products
                    </li>
                    <li>
                        <Link 
                            className="link" 
                            to="https://sass-lang.com"
                            target="_blank"
                            rel="noopener noreferrer"
                        >
                            Sass
                        </Link>
                        {" "}- A CSS extension language
                    </li>
                </ul>
            </div>

        </div>
    );
};

export default LandingPage;
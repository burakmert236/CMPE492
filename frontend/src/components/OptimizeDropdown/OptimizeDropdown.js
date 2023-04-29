import React, { useState, useEffect } from "react";
import { useSelector } from "react-redux";
import { Switch, Modal } from 'antd';
import { SettingOutlined, DeleteOutlined } from '@ant-design/icons';
import { capitalize } from "../../helpers/functions";
import { optimize } from "../../redux/optimizeSlice";
import SettingsPopup from "./SettingsPopup";

import "./OptimizeDropdown.scss";

const OptimizeDropdown = ({ diagram }) => {

    const [modalVisible, setModalVisible] = useState(false);

    const [optimizationType, setOptimizationType] = useState("lex");
    const [criteriaAttributes, setCriteriaAttributes] = useState([
        {
            key: "cost",
            min: true,
        },
        {
            key: "value",
            min: false
        }
    ]);

    const handleOptimize = () => {
        optimize(diagram.model, criteriaAttributes, optimizationType)
            .then(res => console.log(res))
            .catch(res => console.log("err", res))
    }

    return(
        <div className="optimize-container">
            <Modal 
                open={modalVisible}
                onCancel={() => setModalVisible(v => !v)}
                footer={[]}
                title="Optimization Settings"
                width="65%"
                bodyStyle={{ maxHeight: "60vh" }}
            >
                <SettingsPopup 
                    optimizationType={optimizationType}
                    setOptimizationType={setOptimizationType}
                    criteriaAttributes={criteriaAttributes}
                    setCriteriaAttributes={setCriteriaAttributes}
                />
            </Modal>

            <span 
                className="optimize-title"
            >
                <span onClick={() => handleOptimize()} className="optimize-button">OPTIMIZE</span>
                <span className="settings-button" onClick={() => setModalVisible(v => !v)}> <SettingOutlined /> </span>
            </span>
        </div>
    );
};

export default OptimizeDropdown;
import React, { useState } from "react";
import { Modal, Button } from 'antd';
import { SettingOutlined } from '@ant-design/icons';
import { optimize } from "../../redux/optimizeSlice";
import SettingsPopup from "./SettingsPopup";

import "./OptimizeDropdown.scss";

const OptimizeDropdown = ({ diagram }) => {

    const [modalVisible, setModalVisible] = useState(false);

    const [optimizationType, setOptimizationType] = useState("lex");
    const [minUnsatReq, setMinUnsatReq] = useState(false);
    const [minSatTask, setMinSatTask] = useState(false);

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
        optimize(diagram.model, criteriaAttributes, optimizationType, minUnsatReq, minSatTask)
            .then(res => console.log(res))
            .catch(res => console.log("err", res))
    }

    return(
        <div className="optimize-container">
            <Modal 
                open={modalVisible}
                onCancel={() => setModalVisible(v => !v)}
                title="Optimization Settings"
                width="65%"
                bodyStyle={{ maxHeight: "60vh" }}
                footer={[(
                    <div style={{ 
                        zIndex: "3000", 
                        marginTop: "30px", 
                        padding: "15px", 
                        borderTop: "0.5px solid grey",
                        margin: "30px 5px 0 20px"
                    }}>
                        <Button type="primary" onClick={() => {
                            setModalVisible(false);
                            handleOptimize();
                        }}>Optimize</Button>
                    </div>
                )]}
            >
                <SettingsPopup 
                    optimizationType={optimizationType}
                    setOptimizationType={setOptimizationType}
                    criteriaAttributes={criteriaAttributes}
                    setCriteriaAttributes={setCriteriaAttributes}
                    minSatTask={minSatTask}
                    setMinSatTask={setMinSatTask}
                    minUnsatReq={minUnsatReq}
                    setMinUnsatReq={setMinUnsatReq}
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
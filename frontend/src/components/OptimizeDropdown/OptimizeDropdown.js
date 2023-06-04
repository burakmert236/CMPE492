import React, { useState } from "react";
import { useSelector, useDispatch } from "react-redux";
import { Modal, Button } from 'antd';
import { SettingOutlined, LoadingOutlined } from '@ant-design/icons';
import { optimize, setLastSolution, setLastEdit, setResults, setResultsVisible } from "../../redux/optimizeSlice";
import SettingsPopup from "./SettingsPopup";
import * as go from "gojs";

import "./OptimizeDropdown.scss";
import OptimizationResults from "./OptimizationResults";

const OptimizeDropdown = ({ diagram }) => {
    const dispatch = useDispatch();

    const { resultsVisible } = useSelector((state) => state.optimize);

    const [modalVisible, setModalVisible] = useState(false);
    const [optimizationType, setOptimizationType] = useState("lex");
    const [minUnsatReq, setMinUnsatReq] = useState(false);
    const [minSatTask, setMinSatTask] = useState(false);
    const [loading, setLoading] = useState(false);

    const [criteriaAttributes, setCriteriaAttributes] = useState([
        {
            key: "cost",
            min: true,
        },
        {
            key: "value",
            min: false
        },
        {
            key: "Positive Cost Contribution",
            min: true,
            contribution: true,
            disabled: true,
            label: "PCC"
        },
        {
            key: "Negative Cost Contribution",
            min: true,
            contribution: true,
            disabled: true,
            label: "NCC"
        },
        {
            key: "Positive Value Contribution",
            min: true,
            contribution: true,
            disabled: true,
            label: "PVC"
        },
        {
            key: "Negative Value Contribution",
            min: true,
            contribution: true,
            disabled: true,
            label: "NVC"
        }
    ]);

    const handleOptimize = () => {
        if(loading) return;

        if(!diagram.model?.nodeDataArray?.length) return;

        setLoading(true);

        optimize(diagram.model, criteriaAttributes, optimizationType, minUnsatReq, minSatTask)
            .then(res => {
                setLoading(false);

                const resultModel = res?.model;
                dispatch(setLastSolution(JSON.parse(JSON.stringify(resultModel))));
                dispatch(setLastEdit(null));
                diagram.model = go.Model.fromJson(JSON.parse(JSON.stringify(resultModel)));

                dispatch(setResults(res?.results));
                dispatch(setResultsVisible(true));
            })
            .catch(res => {
                setLoading(false);
                console.log("err", res)
            })
    }

    console.log(resultsVisible)

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

            <Modal
                open={resultsVisible}
                onCancel={() => dispatch(setResultsVisible(v => !v))}
                title="Optimization Results"
                width="35%"
                bodyStyle={{ maxHeight: "60vh" }}
                footer={[(
                    <div>
                        <Button type="primary" onClick={() => {
                            dispatch(setResultsVisible(false));
                        }}>Close</Button>
                    </div>
                )]}
            >
                <OptimizationResults/>
            </Modal>

            <span 
                className="optimize-title with-loading"
            >
                <span onClick={() => handleOptimize()} className={`optimize-button ${loading && "loading"}`}>
                    { loading ? <LoadingOutlined /> : "OPTIMIZE" }
                </span>
            </span>

            <span className="optimize-title">
                <span className="settings-button" onClick={() => setModalVisible(v => !v)}> <SettingOutlined /> </span>
            </span>
        </div>
    );
};

export default OptimizeDropdown;
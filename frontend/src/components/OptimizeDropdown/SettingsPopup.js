import React, { useState, useEffect } from "react";
import { useSelector, useDispatch } from "react-redux";
import { Radio, Select, Checkbox, Input, Button, Collapse } from 'antd';
import { capitalize } from "../../helpers/functions";
import { setOptimizationType, setCriteriaAttributes, setMinSatTask, setMinUnsatReq } from "../../redux/optimizeSlice";
import { arrayMoveImmutable } from 'array-move';
import SortableList from './OrderDecider';

import "./OptimizeDropdown.scss";

const { Panel } = Collapse;

const SettingsPopup = () => {
    const dispatch = useDispatch();

    const { attributes: stateAttributes } = useSelector((state) => state.attributes);
    const { optimizationType, criteriaAttributes, minSatTask, minUnsatReq } = useSelector((state) => state.optimize);

    const [integerAttributes, setIntegerAttributes] = useState([]);
    const [smtCommand, setSmtCommand] = useState("");
    
    const onSortEnd = ({ oldIndex, newIndex }) => {
        dispatch(setCriteriaAttributes(arrayMoveImmutable(criteriaAttributes, oldIndex, newIndex)));
    };

    useEffect(() => {
        setIntegerAttributes(stateAttributes?.filter(a => {
            return a?.type === "integer" && !criteriaAttributes?.find(ca => ca?.key === a?.key);
        }));
    }, [stateAttributes]);

    const updateField = (attributeKey, field, value) => {
        const index = criteriaAttributes.findIndex(c => c?.key === attributeKey);
        let attr = JSON.parse(JSON.stringify(criteriaAttributes[index]));

        attr[field] = value;

        dispatch(setCriteriaAttributes([
            ...criteriaAttributes.slice(0, index),
            attr,
            ...criteriaAttributes.slice(index + 1),
        ]));
    }

    return(
        <div className="popup-container">
            <div className="optimization-type-row">
                <div className="optimization-type" style={{width: "50%"}}>
                    <span className="label bold">
                        Optimization Type
                    </span>
                    <Radio.Group onChange={(e) => dispatch(setOptimizationType(e.target.value))} value={optimizationType}>
                        <Radio value={"lex"}>lex</Radio>
                        <Radio value={"box"}>box</Radio>
                        <Radio value={"pareto"}>pareto</Radio>
                    </Radio.Group>
                </div>
                <div className="optimization-type" style={{width: "50%"}}>
                    <span className="label bold">
                        Additional Criteria
                    </span>
                    <Select
                        placeholder="Add a new criteria"
                        style={{ width: "100%" }}
                        value={null}
                        onChange={value => {
                            const entry = integerAttributes?.find(ia => ia?.key === value);
                            dispatch(setCriteriaAttributes([
                                ...criteriaAttributes,
                                { ...entry, extra: true, min: true }
                            ]));
                            dispatch(setIntegerAttributes(integerAttributes?.filter(ia => ia?.key !== value)));
                        }}
                        options={integerAttributes?.map(a => {
                            return {
                                value: a?.key,
                                label: capitalize(a?.key)
                            }
                        })}
                    />
                </div>
            </div>

            <div className="optimization-type">
                <span className="label bold">
                    Optimization Criteria 
                    <span style={{ color: "grey", marginLeft: "5px" }}>{optimizationType === "lex" ? "(You can order items by drag-and-drop)": ""}</span>
                </span>
                
                <div className="checkbox-container">
                    <Checkbox checked={minUnsatReq} onChange={() => dispatch(setMinUnsatReq(!minUnsatReq))}>
                        Minimize unsatisfactory requirements
                    </Checkbox>
                    <Checkbox checked={minSatTask} onChange={() => dispatch(setMinSatTask(!minSatTask))}>
                        Minimize satisfactory tasks
                    </Checkbox>
                </div>

                <div className="advanced-options">
                    <Collapse collapsible="header">  
                        <Panel header="Advanced Options" key="1">  
                            <span className="label bold">
                                <span style={{ color: "grey", marginLeft: "5px", fontWeight: "300" }}>You can add SMT command here</span>
                            </span>
                            <div className="input-button">
                                <Input value={smtCommand} onChange={e => setSmtCommand(e.target.value)}/>
                                <Button type="primary" onClick={() => {
                                    if(!smtCommand) return;
                                    dispatch(setCriteriaAttributes([
                                        ...criteriaAttributes,
                                        { command: smtCommand, extra: true, smt: true, key: new Date().getTime() }
                                    ]));
                                    setSmtCommand("");
                                }}>Add</Button>
                            </div>
                        </Panel>  
                    </Collapse>
                </div>

                <SortableList 
                    items={criteriaAttributes} 
                    setItems={(value) => dispatch(setCriteriaAttributes(value))} 
                    updateField={updateField} 
                    setIntegerAttributes={setIntegerAttributes} 
                    onSortEnd={onSortEnd}
                    disableItems={optimizationType !== "lex"}
                />
            </div>
        </div>
    )
};

export default SettingsPopup;
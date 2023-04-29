import React, { useState, useEffect } from "react";
import { useSelector } from "react-redux";
import { Radio, Switch, Space, Select, InputNumber, Button } from 'antd';
import { DeleteOutlined } from '@ant-design/icons';
import { capitalize } from "../../helpers/functions";

import "./OptimizeDropdown.scss";

const SettingsPopup = ({
    optimizationType,
    setOptimizationType,
    criteriaAttributes,
    setCriteriaAttributes
}) => {

    const { attributes: stateAttributes } = useSelector((state) => state.attributes);

    const [integerAttributes, setIntegerAttributes] = useState([]);
    

    useEffect(() => {
        setIntegerAttributes(stateAttributes?.filter(a => {
            return a?.type === "integer" && !criteriaAttributes?.find(ca => ca?.key === a?.key);
        }));
    }, [stateAttributes]);

    const updateField = (attributeKey, field, value) => {
        const index = criteriaAttributes.findIndex(c => c?.key === attributeKey);
        let attr = criteriaAttributes[index];

        attr[field] = value;

        setCriteriaAttributes([
            ...criteriaAttributes.slice(0, index),
            attr,
            ...criteriaAttributes.slice(index + 1),
        ]);
    }

    return(
        <div className="popup-container">
            <div className="optimization-type-row">
                <div className="optimization-type" style={{width: "50%"}}>
                    <span className="label bold">
                        Optimization Type
                    </span>
                    <Radio.Group onChange={(e) => setOptimizationType(e.target.value)} value={optimizationType}>
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
                            setCriteriaAttributes(ca => [
                                ...ca,
                                { ...entry, extra: true, min: true }
                            ]);
                            setIntegerAttributes(i => i?.filter(ia => ia?.key !== value));
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
                </span>
                <div className="attributes">
                    { criteriaAttributes?.map(a => (
                        <div className="attribute">
                            <span className="label">
                                {capitalize(a?.key)}
                            </span>
                            <div className="attribute-switch">
                                <Switch
                                    disabled={a?.disabled}
                                    checkedChildren="max" 
                                    unCheckedChildren="min" 
                                    checked={ !a?.min } 
                                    onChange={() => {
                                        const index = criteriaAttributes?.findIndex(aa => aa?.key === a?.key );
                                        setCriteriaAttributes([
                                            ...criteriaAttributes?.slice(0, index),
                                            { ...a, min: !a?.min },
                                            ...criteriaAttributes?.slice(index + 1),
                                        ])
                                    }}
                                />
                            </div>

                            <Button
                                style={{ width: "200px" }}
                                onClick={() => {
                                    updateField(a?.key, "disabled", !a?.disabled);
                                }}
                            >
                                { a?.disabled ? 
                                    (a?.min ? "Enable Maximization" : "Enable Minimization") : 
                                    (a?.min ? "Disable Maximization" : "Disable Minimization")
                                }
                            </Button>

                            <div className="attribute-range">
                                <Space.Compact>
                                    <InputNumber
                                        placeholder="min-range"
                                        value={a?.min_range}
                                        onChange={e => {
                                            updateField(a?.key, "min_range", e)
                                        }}
                                        max={!isNaN(a?.max_range) ? a?.max_range : Infinity}
                                        style={{
                                            width: '50%',
                                        }}
                                    />
                                    <InputNumber
                                        placeholder="max-range"
                                        value={a?.max_range}
                                        onChange={e => {
                                            updateField(a?.key, "max_range", e)
                                        }}
                                        min={!isNaN(a?.min_range) ? a?.min_range : -Infinity}
                                        style={{
                                            width: '50%',
                                        }}
                                    />
                                </Space.Compact>
                            </div>


                            {
                                a?.extra && 
                                <Button 
                                    className="trash-button"
                                    onClick={() => {
                                        const copy = JSON.parse(JSON.stringify(a));
                                        delete copy.min_range;
                                        delete copy.max_range;

                                        setIntegerAttributes(ia  => [...ia, copy]);
                                        setCriteriaAttributes(c => c?.filter(ca => ca?.key !== a?.key));
                                    }} 
                                >
                                    <DeleteOutlined className="trash"/>
                                </Button>
                            }
                        </div>
                    )) }
                </div>
            </div>
        </div>
    )
};

export default SettingsPopup;
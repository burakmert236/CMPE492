import React, { useState, useEffect } from "react";
import { useSelector } from "react-redux";
import { Dropdown, Space, Switch } from 'antd';
import { DownOutlined, DeleteOutlined } from '@ant-design/icons';
import { capitalize } from "../../helpers/functions";
import { optimize } from "../../redux/optimizeSlice";

import "./OptimizeDropdown.scss";

const OptimizeDropdown = ({ diagram }) => {
    const { attributes: stateAttributes } = useSelector((state) => state.attributes);

    const [items, setItems] = useState([]);
    const [integerAttributes, setIntegerAttributes] = useState([]);

    const [criteriaAttributes, setCriteriaAttributes] = useState([
        {
            key: "cost",
            min: true
        },
        {
            key: "value",
            min: true
        }
    ]);

    useEffect(() => {
        setIntegerAttributes(stateAttributes?.filter(a => a?.type === "integer"));
    }, [stateAttributes]);

    useEffect(() => {
        const newItems = criteriaAttributes?.map((a, index) => {
            return {
                key: index,
                label: (
                    <div 
                        className="optimize-line"
                        onClick={(e) => e.stopPropagation()}
                    >
                        <span>{ capitalize(a?.key) }</span>  
                        <Switch
                            checkedChildren="max" 
                            unCheckedChildren="min" 
                            checked={ a?.min } 
                            onChange={() => {
                                const index = criteriaAttributes?.findIndex(aa => aa?.key === a?.key );
                                setCriteriaAttributes([
                                    ...criteriaAttributes?.slice(0, index),
                                    { ...a, min: !a?.min },
                                    ...criteriaAttributes?.slice(index + 1),
                                ])
                            }}
                        />
                        { (a?.key !== "cost" && a?.key !== "value") && 
                            <span 
                                className="criteria-delete" 
                                onClick={(e) => {
                                    e.stopPropagation();
                                    e.preventDefault();
                                    setCriteriaAttributes([...criteriaAttributes?.filter(aa => aa?.key !== a?.key)])
                                }}
                            >
                                <DeleteOutlined />
                            </span>
                        }
                    </div>
                )
            }
        })

        const nonAddedIntegerAttributes = integerAttributes?.filter(a => !criteriaAttributes?.find(aa => aa?.key === a?.key));

        if(nonAddedIntegerAttributes?.length > 0) {
            newItems.push(
                {
                    key: 2,  
                    label: "Select another attribute",
                    children: nonAddedIntegerAttributes?.map((a, index) => {
                        return {
                            key: `1-${index}`,
                            label: (
                                <div 
                                    onClick={() => {
                                        setCriteriaAttributes([...criteriaAttributes, { ...a, min: false }])
                                    }} 
                                    className="export-type-line"
                                >
                                    { capitalize(a?.key) }
                                </div>
                            )
                        }
                    })
                }
            )
        }

        setItems(newItems);
    }, [integerAttributes, criteriaAttributes]);

    const handleOptimize = () => {
        optimize(diagram.model)
            .then(res => console.log(res))
            .catch(res => console.log("err", res))
    }

    return(
        <div className="optimize-container">
            <span 
                className="optimize-title"
                onClick={() => handleOptimize()}
            >
                OPTIMIZE
            </span>
            <Dropdown
                arrow={false}
                placement="bottom"
                menu={{ items, expandIcon: () => (<></>) }}
            >
                <Space>
                    <div className="triangle down"></div>
                    <DownOutlined />
                </Space>
            </Dropdown>
        </div>
    );
};

export default OptimizeDropdown;
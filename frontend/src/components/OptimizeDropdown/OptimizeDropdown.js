import React, { useState, useEffect } from "react";
import { useSelector } from "react-redux";
import { Dropdown, Space, Switch } from 'antd';
import { DownOutlined } from '@ant-design/icons';

import "./OptimizeDropdown.scss";

const OptimizeDropdown = ({ diagram }) => {
    const { attributes: stateAttributes } = useSelector((state) => state.attributes);

    const [costMin, setCostMin] = useState(true);
    const [valueMin, setValueMin] = useState(true);
    const [integerAttributes, setIntegerAttributes] = useState([]);

    // useEffect(() => {
    //     let tempIntegerAttributes = [];

    //     const nodes = diagram.nodes;
    //     while (nodes.next()) {
    //         const node = nodes.value;
    //         const attributes = node?.data?.attributes;
    //         const intAttributes = attributes?.filter(a => a?.type === "string");
            
    //         tempIntegerAttributes = tempIntegerAttributes.concat(intAttributes);
    //     }

    //     tempIntegerAttributes = tempIntegerAttributes?.filter((value, index, self) => self.map(x => x?.key).indexOf(value?.key) === index);
    //     setIntegerAttributes(tempIntegerAttributes);
    // }, [diagram?.nodes]);

    console.log(stateAttributes)

    return(
        <div className="optimize-container">
            <span className="optimize-title">OPTIMIZE</span>
            <Dropdown
                arrow={false}
                placement="bottom"
                menu={{
                    items: [
                        {
                            key: 1,
                            label: (
                                <div 
                                    className="optimize-line"
                                    onClick={(e) => e.stopPropagation()}
                                >
                                    <span>Cost</span>  
                                    <Switch 
                                        checkedChildren="max" 
                                        unCheckedChildren="min" 
                                        checked={!costMin} 
                                        onChange={() => setCostMin(m => !m)}
                                    />
                                </div>
                            )
                        },
                        {
                            key: 2,
                            label: (
                                <div 
                                    className="optimize-line"
                                    onClick={(e) => e.stopPropagation()}
                                >
                                    <span>Value</span>
                                    <Switch 
                                        checkedChildren="max" 
                                        unCheckedChildren="min" 
                                        checked={!valueMin} 
                                        onChange={() => setValueMin(m => !m)}
                                    />
                                </div>
                            )
                        },
                        {
                            key: 3,
                            label: (
                                <div>Select</div>
                            )
                        }
                    ]
                }}
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
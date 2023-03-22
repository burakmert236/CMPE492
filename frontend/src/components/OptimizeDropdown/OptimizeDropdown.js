import React, { useState } from "react";
import { Dropdown, Space, Switch } from 'antd';
import { DownOutlined } from '@ant-design/icons';

import "./OptimizeDropdown.scss";

const OptimizeDropdown = () => {
    const [costMin, setCostMin] = useState(true);
    const [valueMin, setValueMin] = useState(true);

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
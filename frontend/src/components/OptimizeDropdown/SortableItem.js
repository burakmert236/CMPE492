import React from 'react';
import { SortableElement } from 'react-sortable-hoc';
import { Switch, Space, InputNumber, Button } from 'antd';
import { capitalize } from "../../helpers/functions";
import { DeleteOutlined } from '@ant-design/icons';
import "./OptimizeDropdown.scss";

const SortableItem = (props) => {
  return <li>
    <div className="attribute">
            <span className="label">
                {capitalize(props.a?.key)}
            </span>
            <div className="attribute-switch">
                <Switch
                    disabled={props.a?.disabled}
                    checkedChildren="max"
                    unCheckedChildren="min"
                    checked={!props.a?.min}
                    onChange={() => {
                        const index = props.items?.findIndex(aa => aa?.key === props.a?.key);
                        props.setItems([
                            ...props.items?.slice(0, index),
                            { ...props.a, min: !props.a?.min },
                            ...props.items?.slice(index + 1),
                        ]);
                    } } />
            </div>

            <Button
                style={{ width: "200px" }}
                onClick={() => {
                    props.updateField(props.a?.key, "disabled", !props.a?.disabled);
                } }
            >
                {props.a?.disabled ?
                    (props.a?.min ? "Enable Maximization" : "Enable Minimization") :
                    (props.a?.min ? "Disable Maximization" : "Disable Minimization")}
            </Button>

            <div className="attribute-range">
                <Space.Compact>
                    <InputNumber
                        placeholder="min-range"
                        value={props.a?.min_range}
                        onChange={e => {
                            props.updateField(props.a?.key, "min_range", e);
                        } }
                        max={!isNaN(props.a?.max_range) ? props.a?.max_range : Infinity}
                        style={{
                            width: '50%',
                        }} />
                    <InputNumber
                        placeholder="max-range"
                        value={props.a?.max_range}
                        onChange={e => {
                            props.updateField(props.a?.key, "max_range", e);
                        } }
                        min={!isNaN(props.a?.min_range) ? props.a?.min_range : -Infinity}
                        style={{
                            width: '50%',
                        }} />
                </Space.Compact>
            </div>


            {props.a?.extra &&
                <Button
                    className="trash-button"
                    onClick={() => {
                        const copy = JSON.parse(JSON.stringify(props.a));
                        delete copy.min_range;
                        delete copy.max_range;

                        props.setIntegerAttributes(ia => [...ia, copy]);
                        props.setItems(c => c?.filter(ca => ca?.key !== props.a?.key));
                    } }
                >
                    <DeleteOutlined className="trash" />
                </Button>}
            </div>
    </li>
}

export default SortableElement(SortableItem);
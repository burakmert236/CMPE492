import React, { useEffect, useState } from "react";
import { Button, Select, Input, InputNumber, Space } from "antd";
import {DeleteOutlined } from '@ant-design/icons';
import "./Dashboard.scss";
const { TextArea } = Input;

const Dashboard = ({ selectedNode, diagram }) => {

  const [text, setText] = useState(null); 
  const [value, setValue] = useState(null); 
  const [cost, setCost] = useState(null); 
  const [attributes, setAttributes] = useState([]);
  const [isOpen, setIsOpen] = useState(false);
  const [attrKey, setAttrKey] = useState('');
  const [attrValue, setAttrValue] = useState('');
  const [currentType, setCurrentType] = useState('integer');
 // const [option, setOption] = useState();

  const setType = (e) => {
    setCurrentType(e);
  };

  const options = [
    {
      value: 'integer',
      label: 'int',
    },
    {
      value: 'string',
      label: 'str',
    },
  ];

  const toggleInput = () => {
    setIsOpen(!isOpen);
    setAttrKey("");
    setAttrValue("");
  };

  function deleteAttribute(key) {
    setAttributes(attributes?.filter(i => i.key !== key));
    diagram.model.setDataProperty(
      selectedNode?.data, 
      "attributes", 
      selectedNode?.findObject("TEXT")?.attributes?.filter(i => i.key !== key)
    );
  };

  const changeAttributes = (item, newValue) => {
    setAttributes(attributes?.map(i => {
        if(i?.key !== item?.key) return i;

        return {
          ...i,
          value: newValue
        }
      }),
    )
  };

  const handleAttrKeyChange = (e) => {
    setAttrKey(e.target.value);
  };
  
  const handleAttrValueChange = (e) => {
    setAttrValue(e.target.value);
  };

  const submitAttribute = (key, value, type) => {
    if (!selectedNode?.data?.attributes) {
      diagram.model.setDataProperty(selectedNode?.data, "attributes", []);
    }

    if(attributes?.find(i => i.key === key) || key === "Cost" || key === "Value") {
      alert(`Attributes with a key ${key} already exists.`)
      return;
    }
    if(type === "Number" && isNaN(+value)) {
      alert(`The value of the attribute has to have type ${type}.`)
      return;
    }
    if(key === "") {
      alert(`The name of the attribute cannot be empty.`)
      return;
    }
    diagram.model.setDataProperty(selectedNode?.data, "attributes", [...selectedNode?.data?.attributes, {key: key, value: value, type: type}]);
    setAttributes(a => [...(a || []), {key: key, value: value, type: type}]) 
    toggleInput();
  };


  useEffect(() => {
    setText(selectedNode?.data?.text);
    setCost(selectedNode?.data?.cost);
    setValue(selectedNode?.data?.value);
    setAttributes(selectedNode?.data?.attributes);
  }, [selectedNode]);
    
  return (
    <div className="dashboard-container">
      {selectedNode ? (
        <div className="attributes">
          <h3 className="title">Node Properties</h3>

          <div className="single-line">
            <span>Text</span>
            <TextArea 
              placeholder={text} 
              rows={1} 
              value={text} 
              onChange={(e) => {
                setText(e.target.value);
                diagram.model.setDataProperty(selectedNode?.data, "text", e.target.value);
                diagram.commitTransaction("text-edit");
              }}
            />
          </div>

          <div className="single-line">
            <span>Cost</span>
            <InputNumber 
              placeholder={"Enter a cost"} 
              value={cost} 
              className="number-input"
              onChange={(e) => {
                setCost(e)
                diagram.model.setDataProperty(selectedNode?.data, "cost", e);
                diagram.commitTransaction("text-edit");
              }}
            />
          </div>

          <div className="single-line">
            <span>Value</span>
            <InputNumber 
              placeholder={"Enter a value"} 
              value={value} 
              className="number-input"
              onChange={(e) => {
                setValue(e)
                diagram.model.setDataProperty(selectedNode?.data, "value", e);
                diagram.commitTransaction("text-edit");
              }}
            />
          </div>
          
          <div>
            {attributes?.map((attr) => (
              <div key={attr.key} className="new-single-line">
                <span>{attr.key}</span>
                { attr?.type === "string" ?
                  <Input 
                    value={attr.value} 
                    onChange={(e) => changeAttributes(attr, e.target.value)}
                  /> : 
                  <InputNumber 
                    style={{ width: "100%" }}
                    value={attr.value} 
                    onChange={(e) => changeAttributes(attr, e)}
                  />
                }
                <Button 
                  onClick={() => deleteAttribute(attr.key)} 
                >
                  <DeleteOutlined className="trash"/>
                </Button>
              </div>
            ))}
          </div>

          {isOpen && (
            <>
              <span className="define-title">Define new property</span>
              <Space.Compact>
                <Select value={currentType} defaultValue="int" options={options} onChange={(e) => setType(e)}></Select>
                <div style={{display: "grid", gridTemplateColumns: "1fr 1fr"}}>
                  <Input value={attrKey} placeholder="Name" onChange={handleAttrKeyChange} style={{ borderTopRightRadius: "0", borderBottomRightRadius: "0", borderRight: "none" }}/>
                  {
                    currentType === "string" ? 
                    <Input value={attrValue} placeholder="Value" onChange={handleAttrValueChange} /> :
                    <InputNumber value={attrValue} placeholder="Value" onChange={(e) => setAttrValue(e)} />
                  }
                </div>
              </Space.Compact>
            </>
          )}
          
          { !isOpen ? 
            (
              <Button 
                className="submit-button" 
                onClick={(e) => toggleInput()}
              >
                Add Attribute
              </Button>
            ) : 
            (
              <div className="inline-buttons">
                <Button 
                  className="submit-button" 
                  onClick={() => submitAttribute(attrKey, attrValue, currentType)}
                >
                  Submit
                </Button>
                <Button 
                  className="cancel-button" 
                  onClick={(e) => toggleInput()}
                >
                  Cancel
                </Button>
              </div>
            )
          }

        </div>
      ) : (
        <div>
          <p>Select a node to view its properties</p>
        </div>
      )}
    </div>
  );
};

export default Dashboard;
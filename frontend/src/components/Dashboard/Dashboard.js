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
  const [currentType, setCurrentType] = useState('Number');
 // const [option, setOption] = useState();

  const setType = (e) => {
    setCurrentType(e);
  };

  const options = [
    {
      value: 'int',
      label: 'Number',
    },
    {
      value: 'string',
      label: 'Text',
    },
  ];

  const toggleInput = () => {
    setIsOpen(!isOpen);
    setAttrKey("");
    setAttrValue("");
  };

  function deleteAttribute(key) {
    setAttributes(attributes?.filter(i => i.key !== key));
    selectedNode.findObject("TEXT").attributes = selectedNode?.findObject("TEXT")?.attributes?.filter(i => i.key !== key);
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
    if (!selectedNode.findObject("TEXT").attributes)
      selectedNode.findObject("TEXT").attributes = []
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
    selectedNode?.findObject("TEXT")?.attributes?.push({key: key, value: value, type: type});
    setAttributes(a => [...(a || []), {key: key, value: value, type: type}]) 
    toggleInput();
  };


  useEffect(() => {
    setText(selectedNode?.findObject("TEXT")?.text);
    setCost(selectedNode?.findObject("TEXT")?.cost);
    setValue(selectedNode?.findObject("TEXT")?.value);
    setAttributes(selectedNode?.findObject("TEXT")?.attributes);
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
                selectedNode.findObject("TEXT").text = e.target.value;
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
                selectedNode.findObject("TEXT").cost = e;
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
                selectedNode.findObject("TEXT").value = e ;
                diagram.commitTransaction("text-edit");
              }}
            />
          </div>
          
          <div>
            {attributes?.map((attr) => (
              <div key={attr.key} className="new-single-line">
                <span>{attr.key}</span>
                <Input 
                  value={attr.value} 
                  onChange={(e) => changeAttributes(attr, e.target.value)}
                />
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
              &nbsp;&nbsp;&nbsp;&nbsp; Define new property
              <Space.Compact style={{marginLeft: "20px", marginTop: "2%"}}>
                <Select value={currentType} defaultValue="Number" options={options} onChange={(e) => setType(e)}></Select>
                <Input value={attrKey} placeholder="Name" onChange={handleAttrKeyChange} />
                <Input value={attrValue} placeholder="Value" onChange={handleAttrValueChange} />
                <Button onClick={() => submitAttribute(attrKey, attrValue, currentType)}>Submit</Button>
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
              <Button 
                className="cancel-button" 
                onClick={(e) => toggleInput()}
              >
                Cancel
              </Button>
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
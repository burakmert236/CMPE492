import React, { useEffect, useState } from "react";
import { Button, Select, Input, InputNumber, Space } from "antd";
import {DeleteOutlined } from '@ant-design/icons';
import "./Dashboard.scss";
const { TextArea } = Input;

const Dashboard = ({ selectedNode }) => {
  console.log(selectedNode?.findObject("TEXT")?.attributes);
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
    <div>
      {selectedNode ? (
        <div className="dashboard-container" >
          <h3 style={{marginLeft: "20px"}}> Node Properties </h3>
          <div style={{marginLeft: "20px"}}>
            Text: 
            <TextArea placeholder={text} rows={2} value={text} onChange={(e) => {
              setText(e.target.value)
              selectedNode.findObject("TEXT").text = e.target.value
            }}
            />
          </div>
          <div style={{marginLeft: "20px"}}>
            Cost: &nbsp;&nbsp;&nbsp;
            <InputNumber placeholder={"Enter a cost"} value={cost} onChange={(e) => {
              setCost(e)
              selectedNode.findObject("TEXT").cost = e
            }}
            style={{width: "110px"}}
            />
          </div>
          <div style={{marginLeft: "20px"}}>
            Value: &nbsp;
            <InputNumber placeholder={"Enter a value"} value={value} onChange={(e) => {
              setValue(e)
              selectedNode.findObject("TEXT").value = e 
            }}
            
            />
          </div>
          <div>
          {attributes?.map((attr) => (
            <div  key={attr.key} style={{marginLeft: "20px"}}>
              {attr.key} :  &nbsp;&nbsp;&nbsp;&nbsp; <Input value={attr.value}  onChange={(e) => changeAttributes(attr, e.target.value)} style={{width: "110px"}} />
              <Button onClick={() => deleteAttribute(attr.key)} style={{marginLeft: "3px"}}><DeleteOutlined style={{color: "#f71000"}}/></Button>
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
            <Button className="cancel-button" style={{marginLeft: "75%", marginTop: "2%"}} onClick={(e) => toggleInput()}>
              Cancel
            </Button></>
          )}
          
          { !isOpen && (
          <Button className="submit-button" style={{marginLeft: "65%", marginTop: "20%"}} onClick={(e) => toggleInput()}>
            Add Attribute
          </Button>
          )}

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
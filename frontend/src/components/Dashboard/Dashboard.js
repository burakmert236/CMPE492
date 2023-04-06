import React, { useEffect, useState } from "react";
import { Button, Input, InputNumber, Space } from "antd";
import "./Dashboard.scss";
import { v4 } from 'uuid'
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
 // const [option, setOption] = useState();

  const toggleInput = () => {
    setIsOpen(!isOpen);
    setAttrKey("");
    setAttrValue("");
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
    selectedNode?.findObject("TEXT")?.attributes?.push({key: key, value: value, type: type});
    setAttributes(a => [...(a || []), {key: key, value: value, type: type}]) 
    setAttrKey('');
    setAttrValue('');
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
            <div  key={v4()} style={{marginLeft: "20px"}}>
              {attr.key} :  &nbsp;&nbsp;&nbsp;&nbsp; <Input value={attrValue} placeholder={ attr.value } onChange={handleAttrValueChange} style={{width: "110px"}} />
            </div>
          ))}
          </div>

          {isOpen && (
            <>
            &nbsp;&nbsp;&nbsp;&nbsp; Define new property
            <Space.Compact style={{marginLeft: "20px", marginTop: "2%"}}>
              <Input value={attrKey} placeholder="Name" onChange={handleAttrKeyChange} />
              <Input value={attrValue} placeholder="Value" onChange={handleAttrValueChange} />
              <Button onClick={() => submitAttribute(attrKey, attrValue, "int")}>Submit</Button>
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
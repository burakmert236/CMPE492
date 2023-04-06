import React, { useEffect, useState } from "react";
import { Button, Input, InputNumber, Select, Space } from "antd";
import "./Dashboard.scss";
const { TextArea } = Input;

const Dashboard = ({ selectedNode, diagram }) => {

  const [text, setText] = useState(null); 
  const [value, setValue] = useState(null); 
  const [cost, setCost] = useState(null); 
  const [attributes, setAttributes] = useState([]);
  const [isOpen, setIsOpen] = useState(false);
 // const [option, setOption] = useState();

  const toggleInput = () => {
    setIsOpen(!isOpen);
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
        <div>
          <h3>Node Properties</h3>
          <div>
            Text: 
            <TextArea placeholder={text} rows={2} value={text} onChange={(e) => {
              setText(e.target.value);
              selectedNode.findObject("TEXT").text = e.target.value;
              diagram.commitTransaction("text-edit");
            }}
            />
          </div>
          <div>
            Cost: &nbsp;&nbsp;&nbsp;
            <InputNumber placeholder={"Enter a cost"} value={cost} onChange={(e) => {
              setCost(e)
              selectedNode.findObject("TEXT").cost = e;
              diagram.commitTransaction("text-edit");
            }}
            style={{width: "110px"}}
            />
          </div>
          <div>
            Value: &nbsp;
            <InputNumber placeholder={"Enter a value"} value={value} onChange={(e) => {
              setValue(e)
              selectedNode.findObject("TEXT").value = e ;
              diagram.commitTransaction("text-edit");
            }}
            style={{width: "110px"}}
            />
          </div>
          
          {attributes?.map(attr => (
            <div>
            </div>
          ))}

          {isOpen && (
            <Space.Compact>
             
              <Input />
              <Button>Submit</Button>
            </Space.Compact>
          )}

          <Button onClick={(e) => toggleInput()}>
            Add Attribute
          </Button>


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
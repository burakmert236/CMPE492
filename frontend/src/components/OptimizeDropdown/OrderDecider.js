import React from 'react';
import SortableItem from './SortableItem';
import { SortableContainer } from 'react-sortable-hoc';
import "./OptimizeDropdown.scss";

const SortableList = (props) => {
  return (
    <div className='attributes'>
      {props.items.map((a, index) => (
        <SortableItem key={`item-${index}`} index={index} a={a} items={props.items} setItems={props.setItems} updateField={props.updateField} setIntegerAttributes={props.setIntegerAttributes}>
            
        </SortableItem>
      ))}
    </div>
  );
}
 
export default SortableContainer(SortableList);
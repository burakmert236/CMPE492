import React from 'react';
import SortableItem from './SortableItem';
import { SortableContainer } from 'react-sortable-hoc';
import "./OptimizeDropdown.scss";

const SortableList = (props) => {
  return (
    <ul className='attributes'>
      {props.items.map((a, index) => (
        <SortableItem 
          key={`item-${index}`} 
          index={index} 
          value={a}
          a={a} 
          items={props.items} 
          setItems={props.setItems} 
          updateField={props.updateField} 
          setIntegerAttributes={props.setIntegerAttributes}
          disabled={props.disableItems}
          disabledItem={props.disableItems}
        />
      ))}
    </ul>
  );
}
 
export default SortableContainer(SortableList);
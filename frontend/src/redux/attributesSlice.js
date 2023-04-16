import axios from 'axios';
import { createSlice, createAsyncThunk } from '@reduxjs/toolkit';
const url = process.env.REACT_APP_BASE_ENDPOINT;

const attributesSlice = createSlice({
    name: 'attributes',
    initialState: {
      attributes: [],
      status: {},
      error: null,
    },
    reducers: {
      setAttributes: (state, action) => {

        const { attribute, func } = action.payload;

        const existingAttributeIndex = state.attributes?.findIndex(a => a?.key === attribute?.key && a?.type === attribute?.type);
        const existingAttribute = existingAttributeIndex !== -1 ? state.attributes[existingAttributeIndex] : null;

        if(func === "add") {
            if(existingAttribute) {
                state.attributes = [
                    ...state.attributes?.slice(0, existingAttributeIndex), 
                    { ...existingAttribute, occurrence: (existingAttribute?.occurrence || 0) + 1 },
                    ...state.attributes?.slice(existingAttributeIndex + 1), 
                ]
            } else {
                state.attributes = [
                    ...state.attributes, 
                    { ...attribute, occurrence: 1 }
                ]
            }
        }

        if(func === "delete") {
            if(existingAttribute) {
                const currentOccurrence = existingAttribute?.occurrence;
                if(currentOccurrence <= 1) {
                    state.attributes = state.attributes?.filter(a => a?.key !== existingAttribute?.key);
                } else {
                    state.attributes = [
                        ...state.attributes?.slice(0, existingAttributeIndex), 
                        { ...existingAttribute, occurrence: existingAttribute?.occurrence - 1 },
                        ...state.attributes?.slice(existingAttributeIndex + 1), 
                    ]
                }
            }
        }
      },
    },
    extraReducers: {},
  });
  
  export const { setAttributes } = attributesSlice.actions;
  
  export default attributesSlice.reducer;
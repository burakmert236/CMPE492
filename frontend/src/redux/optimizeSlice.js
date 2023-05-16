import axios from 'axios';
import { createSlice } from '@reduxjs/toolkit';
import { REACT_APP_BASE_ENDPOINT as url } from '../helpers/constants';

export const optimize = async (model, criteriaAttributes, optimizationType, minUnsatReq, minSatTask) => {
    const { data } = await axios.post(`${url}/optimize`, { 
        model, 
        criteria: criteriaAttributes, 
        type: optimizationType,
        minUnsatReq,
        minSatTask
    });
    return data;
};

const optimizeSlice = createSlice({
    name: 'optimze',
    initialState: {
      lastSolution: {},
      status: {},
      error: null,
    },
    reducers: {
        setLastSolution: (state, action) => {
            state.lastSolution = action.payload;
        }
    },
    extraReducers: {},
});

export const { setLastSolution } = optimizeSlice.actions;

export default optimizeSlice.reducer;
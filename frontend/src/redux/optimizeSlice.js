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
      lastEdit: null,
      status: {},
      error: null,
      results: {},
      resultsVisible: false
    },
    reducers: {
        setLastSolution: (state, action) => {
            state.lastSolution = action.payload;
        },
        setLastEdit: (state, action) => {
            state.lastEdit = action.payload;
        },
        setResults: (state, action) => {
            state.results = action.payload;
        },
        setResultsVisible: (state, action) => {
            state.resultsVisible = action.payload;
        }
    },
    extraReducers: {},
});

export const { setLastSolution, setLastEdit, setResults, setResultsVisible } = optimizeSlice.actions;

export default optimizeSlice.reducer;
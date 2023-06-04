import axios from 'axios';
import { createSlice } from '@reduxjs/toolkit';
import { REACT_APP_BASE_ENDPOINT as url } from '../helpers/constants';

export const optimize = async ({ model, criteriaAttributes, optimizationType, minUnsatReq, minSatTask, isSmtExport }) => {
    const { data } = await axios.post(`${url}/optimize`, { 
        model, 
        criteria: criteriaAttributes, 
        type: optimizationType,
        minUnsatReq,
        minSatTask,
        isSmtExport
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
      resultsVisible: false,
      criteriaAttributes: [
        {
            key: "cost",
            min: true,
        },
        {
            key: "value",
            min: false
        },
        {
            key: "Positive Cost Contribution",
            min: true,
            contribution: true,
            disabled: true,
            label: "PCC"
        },
        {
            key: "Negative Cost Contribution",
            min: true,
            contribution: true,
            disabled: true,
            label: "NCC"
        },
        {
            key: "Positive Value Contribution",
            min: true,
            contribution: true,
            disabled: true,
            label: "PVC"
        },
        {
            key: "Negative Value Contribution",
            min: true,
            contribution: true,
            disabled: true,
            label: "NVC"
        }
      ],
      optimizationType: "lex",
      minUnsatReq: false,
      minSatTask: false,
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
        },
        setCriteriaAttributes: (state, action) => {
            state.criteriaAttributes = action.payload;
        },
        setOptimizationType: (state, action) => {
            state.optimizationType = action.payload;
        },
        setMinUnsatReq: (state, action) => {
            state.minUnsatReq = action.payload;
        },
        setMinSatTask: (state, action) => {
            state.minSatTask = action.payload;
        },
    },
    extraReducers: {},
});

export const { 
    setLastSolution, 
    setLastEdit, 
    setResults, 
    setResultsVisible,
    setCriteriaAttributes,
    setOptimizationType,
    setMinUnsatReq,
    setMinSatTask
} = optimizeSlice.actions;

export default optimizeSlice.reducer;
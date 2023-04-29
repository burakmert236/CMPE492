import axios from 'axios';
import { REACT_APP_BASE_ENDPOINT as url } from '../helpers/constants';

export const optimize = async (model, criteriaAttributes, optimizationType) => {
    const { data } = await axios.post(`${url}/optimize`, { model, criteria: criteriaAttributes, type: optimizationType });
    return data;
}
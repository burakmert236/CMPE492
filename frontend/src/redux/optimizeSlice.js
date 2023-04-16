import axios from 'axios';
import { REACT_APP_BASE_ENDPOINT as url } from '../helpers/constants';

export const optimize = async (model) => {
    const { data } = await axios.post(`${url}/optimize`, { model });
    return data;
}
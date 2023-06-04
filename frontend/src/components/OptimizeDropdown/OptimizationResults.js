import React from "react";
import { useSelector } from "react-redux";
import { Table } from "antd";
import { capitalize } from "../../helpers/functions";

const OptimizationResults = () => {

    const { results } = useSelector((state) => state.optimize);

    const dataSource = Object.keys(results)?.map((key, index) => {
        return {
            key: `${index+1}`,
            attr: capitalize(key),
            value: results[key]
        }
    });

    const columns = [
        {
            title: 'Attribute',
            dataIndex: 'attr',
            key: 'attr',
        },
        {
            title: 'Value',
            dataIndex: 'value',
            key: 'value',
        },
    ]

    return(
        <div className="results-container">
            <Table dataSource={dataSource} columns={columns} pagination={{
                position: [],
            }}/>
        </div>
    );
};

export default OptimizationResults;
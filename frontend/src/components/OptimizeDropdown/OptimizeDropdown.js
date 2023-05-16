import React, { useState } from "react";
import { useSelector, useDispatch } from "react-redux";
import { Modal, Button } from 'antd';
import { SettingOutlined, LoadingOutlined } from '@ant-design/icons';
import { optimize, setLastSolution } from "../../redux/optimizeSlice";
import SettingsPopup from "./SettingsPopup";
import * as go from "gojs";

import "./OptimizeDropdown.scss";

const OptimizeDropdown = ({ diagram }) => {
    const dispatch = useDispatch();

    const { lastSolution } = useSelector((state) => state.optimize);

    const [modalVisible, setModalVisible] = useState(false);
    const [optimizationType, setOptimizationType] = useState("lex");
    const [minUnsatReq, setMinUnsatReq] = useState(false);
    const [minSatTask, setMinSatTask] = useState(false);
    const [loading, setLoading] = useState(false);

    const [criteriaAttributes, setCriteriaAttributes] = useState([
        {
            key: "cost",
            min: true,
        },
        {
            key: "value",
            min: false
        }
    ]);

    const result = "{\"class\":\"GraphLinksModel\",\"nodeDataArray\":[{\"smt_result\":true,\"text\":\"Goal1\",\"shape\":\"Terminator\",\"color\":\"#ACF3DA\",\"location\":{\"class\":\"go.Point\",\"x\":-70,\"y\":-130},\"key\":-1},{\"smt_result\":false,\"text\":\"Goal2\",\"shape\":\"Terminator\",\"color\":\"#ACF3DA\",\"location\":{\"class\":\"go.Point\",\"x\":-190,\"y\":0},\"key\":-2},{\"smt_result\":true,\"text\":\"Goal3\",\"shape\":\"Terminator\",\"color\":\"#ACF3DA\",\"location\":{\"class\":\"go.Point\",\"x\":30,\"y\":0},\"key\":-3},{\"smt_result\":true,\"text\":\"Goal4\",\"shape\":\"Terminator\",\"color\":\"#ACF3DA\",\"location\":{\"class\":\"go.Point\",\"x\":-50,\"y\":190},\"key\":-4},{\"smt_result\":true,\"text\":\"Goal5\",\"shape\":\"Terminator\",\"color\":\"#ACF3DA\",\"location\":{\"class\":\"go.Point\",\"x\":180,\"y\":190},\"key\":-5},{\"category\":\"Junction\",\"location\":{\"class\":\"go.Point\",\"x\":50,\"y\":93.33333333333333},\"key\":-6},{\"smt_result\":false,\"text\":\"Goal6\",\"shape\":\"Terminator\",\"color\":\"#ACF3DA\",\"location\":{\"class\":\"go.Point\",\"x\":370,\"y\":-140},\"key\":-7},{\"smt_result\":false,\"text\":\"Goal7\",\"shape\":\"Terminator\",\"color\":\"#ACF3DA\",\"location\":{\"class\":\"go.Point\",\"x\":480,\"y\":20},\"key\":-8},{\"smt_result\":false,\"text\":\"Goal8\",\"shape\":\"Terminator\",\"color\":\"#ACF3DA\",\"location\":{\"class\":\"go.Point\",\"x\":270,\"y\":20},\"key\":-9},{\"category\":\"Junction\",\"location\":{\"class\":\"go.Point\",\"x\":363.3333333333333,\"y\":-46.66666666666667},\"key\":-10},{\"text\":\"Goal8\",\"color\":\"#FF0000\",\"shape\":\"Circle\",\"width\":25,\"height\":25,\"location\":{\"class\":\"go.Point\",\"x\":360,\"y\":140},\"category\":\"Exclusion\",\"key\":-11}],\"linkDataArray\":[{\"points\":[-33.29342727774009,-103.26312476401756,-7.343092733403376,-85.60993542000253,11.020704770198739,-60.54556904584216,20.787013676843607,-27.711041253044403],\"color\":\"black\",\"text\":\"\",\"type\":\"Refinement\",\"category\":\"Refinement\",\"fromArrow\":\"BackwardTriangle\",\"toArrow\":\"\",\"fromShortLength\":8,\"toShortLength\":0,\"segmentOffset\":{\"class\":\"go.Point\",\"x\":5,\"y\":22},\"from\":-1,\"to\":-3},{\"points\":[-82.01728639015676,-102.33656126737539,-96.4647011040248,-68.64705800849777,-118.82635380612241,-43.179375478106316,-148.47310687706607,-25.576259395602197],\"color\":\"black\",\"text\":\"\",\"type\":\"Refinement\",\"category\":\"Refinement\",\"fromArrow\":\"BackwardTriangle\",\"toArrow\":\"\",\"fromShortLength\":8,\"toShortLength\":0,\"segmentOffset\":{\"class\":\"go.Point\",\"x\":5,\"y\":22},\"from\":-1,\"to\":-2},{\"from\":-3,\"to\":-6,\"category\":\"ANDRefinement\",\"type\":\"ANDRefinement\",\"toArrow\":\"\",\"fromArrow\":\"Backward\",\"color\":\"black\",\"fromShortLength\":8,\"toShortLength\":0,\"reshapable\":false,\"relinkableTo\":false,\"relinkableFrom\":false,\"selectable\":false,\"points\":[47.08491928765855,27.5625809101385,58.306103054758886,45.665375560836715,63.962343316913184,67.5879276880099,56.93779239083858,93.5245902579108]},{\"from\":-4,\"to\":-6,\"category\":\"ANDRefinement\",\"type\":\"ANDRefinement\",\"toArrow\":\"\",\"fromArrow\":\"\",\"color\":\"black\",\"fromShortLength\":8,\"toShortLength\":0,\"reshapable\":false,\"relinkableTo\":false,\"relinkableFrom\":false,\"selectable\":false,\"points\":[-29.175614421253826,162.5167943459277,-3.42351497642714,129.55020317435296,18.583891925912226,110.25999715181833,50.228956689144525,100.40371622138508]},{\"from\":-5,\"to\":-6,\"category\":\"ANDRefinement\",\"type\":\"ANDRefinement\",\"toArrow\":\"\",\"fromArrow\":\"\",\"color\":\"black\",\"fromShortLength\":8,\"toShortLength\":0,\"reshapable\":false,\"relinkableTo\":false,\"relinkableFrom\":false,\"selectable\":false,\"points\":[133.07489761709297,166.61102988164834,109.46696772083817,155.35361926698613,80.84519678349204,135.3851218253528,58.674451290582994,103.32475393306744]},{\"from\":-7,\"to\":-10,\"category\":\"ANDRefinement\",\"type\":\"ANDRefinement\",\"toArrow\":\"\",\"fromArrow\":\"Backward\",\"color\":\"black\",\"fromShortLength\":8,\"toShortLength\":0,\"reshapable\":false,\"relinkableTo\":false,\"relinkableFrom\":false,\"selectable\":false,\"points\":[378.57513678806936,-112.2793507538558,385.41295979055224,-90.17487618468472,385.1550490420972,-68.32615135127759,371.66638081634386,-45.880883670476265]},{\"from\":-9,\"to\":-10,\"category\":\"ANDRefinement\",\"type\":\"ANDRefinement\",\"toArrow\":\"\",\"fromArrow\":\"\",\"color\":\"black\",\"fromShortLength\":8,\"toShortLength\":0,\"reshapable\":false,\"relinkableTo\":false,\"relinkableFrom\":false,\"selectable\":false,\"points\":[297.5902670849358,-7.343532053016392,320.55834473929855,-30.1062101236879,338.14739477581475,-40.99184480058746,363.3334225887955,-41.13533294494175]},{\"from\":-8,\"to\":-10,\"category\":\"ANDRefinement\",\"type\":\"ANDRefinement\",\"toArrow\":\"\",\"fromArrow\":\"\",\"color\":\"black\",\"fromShortLength\":8,\"toShortLength\":0,\"reshapable\":false,\"relinkableTo\":false,\"relinkableFrom\":false,\"selectable\":false,\"points\":[425.2019128487374,2.313105872290638,410.3885900939225,-1.3806395675603795,388.51583077238524,-12.922799835341106,372.0609105242111,-36.71326959511274]},{\"points\":[-8.771852682920027,-137.25633893082744,97.08242100210524,-149.80145944798605,202.19049402658936,-152.1902792894522,308.0178653462378,-144.5026026863193],\"color\":\"#27ba84\",\"dash\":[2,2],\"text\":\"C+10\",\"type\":\"C+\",\"category\":\"C+\",\"fromArrow\":\"BackwardTriangle\",\"toArrow\":\"\",\"fromShortLength\":8,\"toShortLength\":0,\"segmentOffset\":{\"class\":\"go.Point\",\"x\":5,\"y\":20},\"from\":-1,\"to\":-7,\"value\":10},{\"from\":-11,\"to\":-8,\"points\":[364.84471896090236,130.6844915227416,384.5199367506028,92.8526462514277,412.92896079773163,64.44362220429889,440.52233122927163,46.15928748414803]},{\"from\":-11,\"to\":-5,\"points\":[351.23166556081657,145.77635794966258,316.4148458948757,168.71280208899623,278.6643280202884,179.19905705415937,241.41681622205587,183.27660217993682]}]}"

    const handleOptimize = () => {
        if(loading) return;

        setLoading(true);

        optimize(diagram.model, criteriaAttributes, optimizationType, minUnsatReq, minSatTask)
            .then(res => {
                setLoading(false);
                dispatch(setLastSolution(JSON.parse(result)));
                diagram.model = go.Model.fromJson(JSON.parse(result));
            })
            .catch(res => {
                setLoading(false);
                console.log("err", res)
            })
    }

    return(
        <div className="optimize-container">
            <Modal 
                open={modalVisible}
                onCancel={() => setModalVisible(v => !v)}
                title="Optimization Settings"
                width="65%"
                bodyStyle={{ maxHeight: "60vh" }}
                footer={[(
                    <div style={{ 
                        zIndex: "3000", 
                        marginTop: "30px", 
                        padding: "15px", 
                        borderTop: "0.5px solid grey",
                        margin: "30px 5px 0 20px"
                    }}>
                        <Button type="primary" onClick={() => {
                            setModalVisible(false);
                            handleOptimize();
                        }}>Optimize</Button>
                    </div>
                )]}
            >
                <SettingsPopup 
                    optimizationType={optimizationType}
                    setOptimizationType={setOptimizationType}
                    criteriaAttributes={criteriaAttributes}
                    setCriteriaAttributes={setCriteriaAttributes}
                    minSatTask={minSatTask}
                    setMinSatTask={setMinSatTask}
                    minUnsatReq={minUnsatReq}
                    setMinUnsatReq={setMinUnsatReq}
                />
            </Modal>

            <span 
                className="optimize-title"
            >
                <span onClick={() => handleOptimize()} className={`optimize-button ${loading && "loading"}`}>
                    { loading ? <LoadingOutlined /> : "OPTIMIZE" }
                </span>
                <span className="settings-button" onClick={() => setModalVisible(v => !v)}> <SettingOutlined /> </span>
            </span>
        </div>
    );
};

export default OptimizeDropdown;
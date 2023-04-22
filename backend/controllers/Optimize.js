const httpStatus = require('http-status');
const { 
    initFile,
    declareGoalsAndRefinements,
    closeWorld,
    refinementGoalRelationships,
    mandatoryNodes,
    precedenceRelationships,
    optimizeCriteria,
    runOptiMathSat
} = require('../helpers');

const optimize = async (req, res) => {
    try {
        let { model } = req.body;
        model = JSON.parse(model);

        const inputFile = "./model.smt2";
        const outputFile = "./solution.txt";
        
        initFile(inputFile);
        declareGoalsAndRefinements(inputFile, model);
        closeWorld(inputFile, model);
        refinementGoalRelationships(inputFile, model);
        mandatoryNodes(inputFile, model);
        // do implemented nodes
        precedenceRelationships(inputFile, model);
        optimizeCriteria(inputFile);

        runOptiMathSat(inputFile, outputFile);

        return res.status(httpStatus.OK).send();
    } catch (err) {
        console.log(err)
        return res
            .status(httpStatus.INTERNAL_SERVER_ERROR)
            .send({ message: "Something went wrong" })
    } 
};

module.exports = {
    optimize
}
const httpStatus = require('http-status');
const { 
    initFile,
    declareGoalsAndRefinements,
    closeWorld,
    refinementGoalRelationships,
    mandatoryNodes,
    implementedNodes,
    contributions,
    goalAttributes,
    exclusionFinder,
    leafAndRootNodes,
    precedenceRelationships,
    optimizeCriteria,
    runOptiMathSat
} = require('../helpers');

const optimize = async (req, res) => {
    try {
        let { model, criteria, type, minUnsatReq, minSatTask } = req.body;
        model = JSON.parse(model);

        if(!model?.nodeDataArray?.length) {
            return res.status(httpStatus.NOT_FOUND).send();
        }

        const inputFile = "./model.smt2";
        const outputFile = "./solution.txt";
        
        initFile(inputFile, type);
        declareGoalsAndRefinements(inputFile, model);
        closeWorld(inputFile, model);
        refinementGoalRelationships(inputFile, model);
        mandatoryNodes(inputFile, model);
        implementedNodes(inputFile, model);
        precedenceRelationships(inputFile, model);
        contributions(inputFile, model);
        goalAttributes(inputFile, model);
        exclusionFinder(inputFile, model);
        leafAndRootNodes(inputFile, model);
        optimizeCriteria(inputFile, criteria, minUnsatReq, minSatTask);

        runOptiMathSat(inputFile, outputFile, res, model);

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
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
        let { model, criteria, type, minUnsatReq, minSatTask, isSmtExport } = req.body;
        model = JSON.parse(model);

        if(!model?.nodeDataArray?.length) {
            return res.status(httpStatus.NOT_FOUND).send();
        }

        const inputFile = "./model.smt2";
        const outputFile = "./solution.txt";

        let fileText = "";
        
        fileText += initFile(inputFile, type);
        fileText += declareGoalsAndRefinements(inputFile, model);
        fileText += closeWorld(inputFile, model);
        fileText += refinementGoalRelationships(inputFile, model);
        fileText += mandatoryNodes(inputFile, model);
        fileText += implementedNodes(inputFile, model);
        fileText += precedenceRelationships(inputFile, model);
        fileText += contributions(inputFile, model);
        fileText += goalAttributes(inputFile, model);
        fileText += exclusionFinder(inputFile, model);
        fileText += leafAndRootNodes(inputFile, model);
        fileText += optimizeCriteria(inputFile, criteria, minUnsatReq, minSatTask);

        if(isSmtExport) {
            return res.status(httpStatus.OK).send(fileText);
        }

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
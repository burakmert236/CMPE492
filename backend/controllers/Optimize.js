const httpStatus = require('http-status');
const { 
    initFile,
    declareGoalsAndRefinements,
    closeWorld,
    refinementGoalRelationships
} = require('../helpers');

const optimize = async (req, res) => {
    try {
        let { model } = req.body;
        model = JSON.parse(model);

        const fileName = "./model.smt2";
        
        initFile(fileName);
        declareGoalsAndRefinements(fileName, model);
        closeWorld(fileName, model);
        refinementGoalRelationships(fileName, model);

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
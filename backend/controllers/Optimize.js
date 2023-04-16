const httpStatus = require('http-status');

const optimize = async (req, res) => {
    try {
        const { model } = req.body;
        console.log(model);

        return res.status(httpStatus.OK).send();
    } catch (err) {
        return res
            .status(httpStatus.INTERNAL_SERVER_ERROR)
            .send({ message: "Something went wrong" })
    } 
};

module.exports = {
    optimize
}
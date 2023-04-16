const express = require('express');
const helmet = require('helmet'); // for security
const cors = require('cors');

const { APP_PORT } = require('./constants');

const {
    OptimizeRoutes,
} = require('./api-routes');

const app = express();

app.use(express.json({limit: '50mb'}));
app.use(express.urlencoded({ extended: true }));
app.use(helmet());

app.use(cors());
app.options('*', cors());

app.listen(APP_PORT, () => {
    console.log(`Server is running on port ${APP_PORT}`);
    app.use('/api/v1/optimize', OptimizeRoutes);
})
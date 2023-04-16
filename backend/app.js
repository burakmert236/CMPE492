const express = require('express');
const helmet = require('helmet'); // for security
const cors = require('cors');

const config = require('./config');

const {
    OptimizeRoutes,
} = require('./api-routes');

config();

const app = express();

app.use(express.json({limit: '50mb'}));
app.use(express.urlencoded({ extended: true }));
app.use(helmet());

app.use(cors());
app.options('*', cors());

app.listen(process.env.APP_PORT, () => {
    console.log(`Server is running on port ${process.env.APP_PORT}`);
    app.use('/api/v1/optimize', OptimizeRoutes);
})
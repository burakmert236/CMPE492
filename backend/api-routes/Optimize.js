const express = require('express');
const router = express.Router();

const { optimize } = require('../controllers/Optimize');

router.post('/', optimize);

module.exports = router;
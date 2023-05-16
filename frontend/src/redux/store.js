import { configureStore } from "@reduxjs/toolkit";

import attributesSlice from "./attributesSlice";
import optimizeSlice from "./optimizeSlice";

export const store = configureStore({
    reducer: {
        attributes: attributesSlice,
        optimize: optimizeSlice,
    },
    middleware: (getDefaultMiddleware) => getDefaultMiddleware({
        immutableCheck: false,
        serializableCheck: false,
    })
});
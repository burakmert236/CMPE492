import { configureStore } from "@reduxjs/toolkit";

import attributesSlice from "./attributesSlice";

export const store = configureStore({
    reducer: {
        attributes: attributesSlice,
    },
    middleware: (getDefaultMiddleware) => getDefaultMiddleware({
        immutableCheck: false,
        serializableCheck: false,
    })
});
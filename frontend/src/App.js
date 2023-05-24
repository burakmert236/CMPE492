import { Routes, Route } from 'react-router-dom';

import HomePage from './pages/HomePage/HomePage';
import LandingPage from './pages/LandingPage/LandingPage';

import './App.scss';

function App() {
  return (
    <Routes>
      <Route path="/" element={<LandingPage />} />
      <Route path="/tool" element={<HomePage />} />
    </Routes>
  );
}

export default App;

# Compile-time baseline (2026-10-25; wall-clock, machine sometimes under load)

Cold `make profile-tree`, after the LowerInverse and spelling fixes (slowest 15). SFiniteStrong sits at the 120 s limit; SFiniteCommute and SFiniteIncl were skipped as its dependents (the first run: SFiniteCommute > 120 s, SFiniteMonad 112 s).

| module | depth | status | s |
|---|---|---|---|
| QBS.Continuous.SFiniteStrong | 12 | SLOW | 120.1 |
| QBS.Continuous.SFiniteMonad | 11 | ok | 119.2 |
| QBS.Analysis.JParam | 9 | ok | 84.9 |
| QBS.Continuous.ProbInstance | 9 | ok | 63.6 |
| QBS.Analysis.Tonelli | 8 | ok | 55.6 |
| QBS.Analysis.JSum | 10 | ok | 55.1 |
| QBS.Analysis.Lebesgue | 7 | ok | 54.7 |
| QBS.Model.StatInstance | 6 | ok | 35.6 |
| QBS.Model.ProbInstance | 5 | ok | 31.0 |
| QBS.Analysis.Density | 10 | ok | 20.8 |
| QBS.Continuous.UniformCDF | 16 | ok | 8.5 |
| QBS.Continuous.SFiniteSum | 12 | ok | 8.5 |
| QBS.Analysis.CoinGrid | 10 | ok | 8.1 |
| QBS.Continuous.SubModel | 15 | ok | 8.0 |
| QBS.Continuous.SFinite | 10 | ok | 6.9 |

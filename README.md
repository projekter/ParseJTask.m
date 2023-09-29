# ParseJTask
Mathematica parser for Mosek's JTASK format

In order to inspect Mosek tasks, it is useful to export them to files which can then be studied. Before Mosek 10, the PTF format was the most suitable for this, as it is quite human-readable. Still, this is not optimal.
However, writing a parser for PTF is not easy. While I did this, there is no formal specification of the format, and indeed subtle undocumented syntax changes made it hard to keep the up-to-date. In the end, if you detect an error in the problem, it should be because the problem was erroneous and not because the parser was unable to identify some syntax glitch.
The new JTASK format comes to the rescue: it is JSON-like and therefore much easier to parse. However, parsing now is a necessity, as it is no longer human-readable.

This Mathematica package provides two functions:
- `parseJTask[file, conic, defaultVarName, defaultBarVarName]` opens the JTASK file `file` and outputs an inactivated `Maximize` or `Minimize` expression. Cones are rewritten into their plain definitions, unless you set `conic` to `True`; in this case, whenever possible, the appropriate `VectorGreaterEqual` will be used. This makes it easier to check the result by activating the expression. Variable names are taken from the task itself if assigned; if not, they will be indexed expressions of the default names.
- `parseJTaskSolution[file, defaultVarName, defaultBarVarName, defaultDualVarName, defaultSlackBarVarName, solutionType]` opens an optimized JTASK file and extracts the solution data.

_Disclaimer:_ I wrote this package because I needed it. However, I only use Mosek's interior point optimizer. I have no idea how faithfully the parser reproduces mixed-integer problems/solutions or simplex solutions. You are very welcome to submit a pull request that complements the missing parts.

_Note:_ The export to the JTASK format contained some bugs prior to version 10.1.11. These will probably not materialize unless you modify your task after an optimization (no guarantees!). But if you do so, the export will already be wrong. However, PTF had other bugs, so this wouldn't be a solution either. The only solution - which is also necessary for getting correct results in the optimization after problem modification - is to upgrade to the newest version.
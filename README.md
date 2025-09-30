# PhD meta-repository
This repostiory contains all the contributions to my PhD thesis. Any required libraries that I have not been a part of developing can be found under the contrib directory.

In addition, as part of the thesis I have only contributed the material regarding and extending scenes, in collaboration with Simon Foster. My contrubtions to the Optics library can be found under the following files:
- Optics/Scenes.thy
- Optics/Scene_Spaces.thy
- Optics/Frames.thy

To inspect and run the various Isabelle theories, download [Isabelle2025](isabelle.in.tum.de), and launch Isabelle/jEdit from this directory with command
```
isabelle jedit -d . -l <Base Theory>
```
replacing <Base Session> with the corresponding base session for the desired development, as listed below:
- CAS-Integration: Hybrid-Library
- IsaVODEs_Uncertainty: Hybrid-Verification
- Optics: HOL-Library
- Kolmogorov_Chentsov: HOL-Probability
- Stochastic_Kernels: Standard_Borel_Spaces
- SdL: Shallow_Expressions_Prob

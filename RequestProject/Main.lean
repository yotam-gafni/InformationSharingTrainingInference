import RequestProject.GeneralSignaling
import RequestProject.CorrelationModel
import RequestProject.BayesianGame
import RequestProject.CongestionGame
import RequestProject.KnownCorrelation
import RequestProject.KnownCorrelationAsymmetric
import RequestProject.UnknownCorrelation
import RequestProject.Theorem36
import RequestProject.Consumer
import RequestProject.OpportunitySeeking
import RequestProject.NumericalResults
import RequestProject.Theorem43
import RequestProject.Theorem43Selected
import RequestProject.Theorem46
import RequestProject.Theorem46Selected
import RequestProject.Theorem46UpperBound
import RequestProject.Theorem46Part1Classification
import RequestProject.Theorem46Part1Transfer
import RequestProject.Theorem46Parts
import RequestProject.Theorem46Part1NonInverted
import RequestProject.Theorem46Part1AllActing
import RequestProject.Example47
import RequestProject.TwoHypotheses
import RequestProject.Theorem52
import RequestProject.ModelConnections

/-!
# Information-sharing in training and inference

The project provides:
* extensible interfaces for the general binary signaling model and contracts;
* the Section 3 correlation-model parameterization, its joint signal law, and the
  equilibrium classifications of Lemmas 3.1 and 3.2;
* the congestion-game reduction and the IRPO classifications of Section 3;
* the Section 4 consumer results, including Theorems 4.1, 4.3, 4.4 and 4.6 and the
  inverted-equilibrium Example 4.7;
* the Section 5 extensions, and verified embeddings of the correlation and
  two-hypotheses models into the general model.

`MANUSCRIPT_TO_LEAN.md` maps each numbered result of the manuscript to its formalization.
-/

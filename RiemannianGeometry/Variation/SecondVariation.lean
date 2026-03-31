import Variation.IndexForm
import Variation.FirstVariationEnergy

namespace Variation.Curve

variable {n : ℕ}

/-- The scalar value predicted by the second variation of energy. -/
noncomputable def secondVariationOfEnergyValue
    (a b : ℝ)
    (nablaV : AlongFieldDerivative (n := n))
    (RVTT : ℝ → Vector n)
    (V : ℝ → Vector n) : ℝ :=
  indexForm (n := n) a b nablaV nablaV RVTT V

/-- The scalar value predicted by the second variation of length. -/
noncomputable def secondVariationOfLengthValue
    (a b : ℝ)
    (nablaV : AlongFieldDerivative (n := n))
    (RVTT : ℝ → Vector n)
    (V : ℝ → Vector n) : ℝ :=
  indexForm (n := n) a b nablaV nablaV RVTT V

theorem secondVariationOfEnergy_eq_indexForm
    (a b : ℝ)
    (nablaV : AlongFieldDerivative (n := n))
    (RVTT : ℝ → Vector n) (V : ℝ → Vector n) :
    secondVariationOfEnergyValue (n := n) a b nablaV RVTT V =
      indexForm (n := n) a b nablaV nablaV RVTT V :=
  rfl

theorem secondVariationOfLength_eq_indexForm
    (a b : ℝ)
    (nablaV : AlongFieldDerivative (n := n))
    (RVTT : ℝ → Vector n) (V : ℝ → Vector n) :
    secondVariationOfLengthValue (n := n) a b nablaV RVTT V =
      indexForm (n := n) a b nablaV nablaV RVTT V :=
  rfl

theorem indexForm_eq_secondVariationOfEnergy
    (a b : ℝ)
    (nablaV : AlongFieldDerivative (n := n))
    (RVTT : ℝ → Vector n) (V : ℝ → Vector n) :
    indexForm (n := n) a b nablaV nablaV RVTT V =
      secondVariationOfEnergyValue (n := n) a b nablaV RVTT V :=
  rfl

theorem indexForm_eq_secondVariationOfLength
    (a b : ℝ)
    (nablaV : AlongFieldDerivative (n := n))
    (RVTT : ℝ → Vector n) (V : ℝ → Vector n) :
    indexForm (n := n) a b nablaV nablaV RVTT V =
      secondVariationOfLengthValue (n := n) a b nablaV RVTT V :=
  rfl

end Variation.Curve

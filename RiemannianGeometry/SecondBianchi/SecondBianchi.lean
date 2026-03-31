import SecondBianchi.Basic

namespace SecondBianchi

theorem second_bianchi_identity
    (A : LocalConnectionAlgebra) (conn : ConnectionForm A) :
    covariantExterior A conn (curvature A conn) = 0 := by
  simp only [covariantExterior, curvature]
  rw [A.d2_add, A.d2_d1_eq_zero, A.d2_wedge11]
  rw [A.wedge12_add_right, A.wedge21_add_left, A.wedge_assoc]
  abel

end SecondBianchi




import ConnesRigidity.PropertyTExactCertificateOrbitData









namespace ConnesRigidity.AffineSymplecticOrbitCertificate

set_option maxRecDepth 1000000
set_option maxHeartbeats 0



theorem orbitGramBoundarySymmetryCheck :
    (List.range 425).all
      (fun index => decide (gramEntry 0 index = gramEntry index 0)) = true := by
  decide +kernel


theorem gramEntry_zero_swap (index : Fin 425) :
    gramEntry 0 index.val = gramEntry index.val 0 := by
  have hentry := List.all_eq_true.mp orbitGramBoundarySymmetryCheck
    index.val (List.mem_range.mpr index.isLt)
  exact of_decide_eq_true hentry

end ConnesRigidity.AffineSymplecticOrbitCertificate

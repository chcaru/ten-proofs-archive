


import ConnesRigidity.PropertyTExactCertificateOrbitRadixDenseValidation









namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section

set_option maxRecDepth 1000000



theorem orbitRadixPackedNormalizedGramValue_eq_gramOrbitCoefficient
    (orbit second : Nat) (horbit : orbit < 26) (hsecond : second < 425) :
    orbitRadixPackedSignedValue
        ((radixPackedNormalizedGramRowData.getD orbit []).getD 1 0)
        second =
      gramOrbitCoefficient
        (dataEntry pairOrbitIndexData orbit second).toNat := by
  have hcheck := orbitRadixNormalizedGramRows_valid ⟨orbit, horbit⟩
  cases hnormalized : radixNormalizedGramRowData[orbit]? with
  | none => simp [orbitRadixNormalizedGramRowCheck, hnormalized] at hcheck
  | some normalized =>
      cases normalized with
      | nil => simp [orbitRadixNormalizedGramRowCheck, hnormalized] at hcheck
      | cons stored entries =>
          cases hpacked : radixPackedNormalizedGramRowData[orbit]? with
          | none =>
              simp [orbitRadixNormalizedGramRowCheck, hnormalized, hpacked]
                at hcheck
          | some packedRow =>
              cases packedRow with
              | nil =>
                  simp [orbitRadixNormalizedGramRowCheck, hnormalized, hpacked]
                    at hcheck
              | cons storedPacked remaining =>
                  cases remaining with
                  | nil =>
                      simp [orbitRadixNormalizedGramRowCheck,
                        hnormalized, hpacked] at hcheck
                  | cons packed extra =>
                      cases extra with
                      | cons _ _ =>
                          simp [orbitRadixNormalizedGramRowCheck,
                            hnormalized, hpacked] at hcheck
                      | nil =>
                          cases hpair : pairOrbitIndexData[orbit]? with
                          | none =>
                              simp [orbitRadixNormalizedGramRowCheck,
                                hnormalized, hpacked, hpair] at hcheck
                          | some orbits =>
                              simp only [orbitRadixNormalizedGramRowCheck,
                                hnormalized, hpacked, hpair,
                                Bool.and_eq_true, decide_eq_true_eq] at hcheck
                              obtain ⟨⟨⟨⟨_hstored, _hpackedStored⟩,
                                hlength⟩, hsize⟩, hentries⟩ := hcheck
                              have hentry : second < entries.length := by
                                simpa [hlength] using hsecond
                              obtain ⟨horbitIndex, hnonnegative, hbound,
                                hgram, hvalue⟩ :=
                                orbitRadixNormalizedGramEntriesCheck_get
                                  packed entries orbits.toList 0 second
                                  hentry hentries
                              have hsecondArray : second < orbits.size := by
                                simpa [hsize] using hsecond
                              have hcoefficient :
                                  (orbits.toList)[second] =
                                    dataEntry pairOrbitIndexData orbit second := by
                                simp [dataEntry, Array.getD_eq_getD_getElem?,
                                  hpair, hsecondArray]
                              have hpackedValue :
                                  (radixPackedNormalizedGramRowData.getD
                                    orbit []).getD 1 0 = packed := by
                                change
                                  ((radixPackedNormalizedGramRowData[orbit]?).getD
                                    []).getD 1 0 = packed
                                rw [hpacked]
                                rfl
                              rw [hpackedValue]
                              have hactualIndex :
                                  (orbits.toList)[second].toNat < 2256 :=
                                (Int.toNat_lt hnonnegative).mpr hbound
                              have hactual :=
                                orbitRadixPackedGramOrbitValue_eq_gramOrbitCoefficient
                                  (orbits.toList)[second].toNat hactualIndex
                              simpa [hcoefficient] using
                                hvalue.symm.trans (hgram.trans hactual)

end

end ConnesRigidity.AffineSymplecticOrbitCertificate

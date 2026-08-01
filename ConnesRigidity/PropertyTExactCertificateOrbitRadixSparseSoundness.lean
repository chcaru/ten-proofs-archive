
import ConnesRigidity.PropertyTExactCertificateOrbitRadixCheckers
import ConnesRigidity.PropertyTExactCertificateOrbitRadixSoundness

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

open scoped BigOperators

set_option maxRecDepth 1000000

theorem orbitRadixSparsePairsSorted_head_lt
    (key value : Int) (remaining : List Int)
    (hcheck : orbitRadixSparsePairsSorted (key :: value :: remaining) = true)
    (pair : Int × Int)
    (hpair : pair ∈ scaledInverseDecodePairs remaining) :
    key < pair.1 := by
  induction remaining using scaledInverseDecodePairs.induct generalizing key value with
  | case1 next nextValue rest ih =>
      simp only [orbitRadixSparsePairsSorted, Bool.and_eq_true,
        decide_eq_true_eq] at hcheck
      rcases hcheck with ⟨⟨⟨⟨_, _⟩, _⟩, hnext⟩, hrest⟩
      simp only [scaledInverseDecodePairs, List.mem_cons] at hpair
      rcases hpair with rfl | hpair
      · exact hnext
      · exact lt_trans hnext (ih next nextValue hrest hpair)
  | case2 remaining hshort =>
      cases remaining with
      | nil => simp [scaledInverseDecodePairs] at hpair
      | cons first tail =>
          cases tail with
          | nil => simp [scaledInverseDecodePairs] at hpair
          | cons second rest =>
              exact False.elim (hshort first second rest rfl)

theorem orbitRadixSparsePairsSorted_head
    (key value : Int) (remaining : List Int)
    (hcheck : orbitRadixSparsePairsSorted (key :: value :: remaining) = true) :
    0 ≤ key ∧ key < 424 ∧ orbitRadixSparsePairsSorted remaining = true := by
  cases remaining with
  | nil =>
      simp only [orbitRadixSparsePairsSorted, Bool.and_eq_true,
        decide_eq_true_eq] at hcheck
      exact ⟨hcheck.1.1, hcheck.1.2, rfl⟩
  | cons next tail =>
      cases tail with
      | nil => simp [orbitRadixSparsePairsSorted] at hcheck
      | cons nextValue rest =>
          simp only [orbitRadixSparsePairsSorted, Bool.and_eq_true,
            decide_eq_true_eq] at hcheck ⊢
          exact ⟨hcheck.1.1.1.1, hcheck.1.1.1.2, hcheck.2⟩

theorem orbitRadixSparsePairsSorted_nodup
    (entries : List Int)
    (hcheck : orbitRadixSparsePairsSorted entries = true) :
    ((scaledInverseDecodePairs entries).map Prod.fst).Nodup := by
  induction entries using scaledInverseDecodePairs.induct with
  | case1 key value remaining ih =>
      simp only [scaledInverseDecodePairs, List.map_cons, List.nodup_cons]
      constructor
      · intro hmem
        obtain ⟨pair, hpair, hkey⟩ := List.mem_map.mp hmem
        have hlt := orbitRadixSparsePairsSorted_head_lt key value remaining
          hcheck pair hpair
        change pair.1 = key at hkey
        omega
      · exact ih
          (orbitRadixSparsePairsSorted_head key value remaining hcheck).2.2
  | case2 entries hshort =>
      cases entries with
      | nil => exact List.nodup_nil
      | cons first tail =>
          cases tail with
          | nil => exact List.nodup_nil
          | cons second rest =>
              exact False.elim (hshort first second rest rfl)

theorem scaledInversePairLookup_eq_zero_of_not_mem
    (key : Int) (entries : List Int)
    (hmem : key ∉ (scaledInverseDecodePairs entries).map Prod.fst) :
    scaledInversePairLookup key entries = 0 := by
  induction entries using scaledInversePairLookup.induct key with
  | case1 value remaining =>
      simp [scaledInverseDecodePairs] at hmem
  | case2 present value remaining hne ih =>
      simp only [scaledInverseDecodePairs, List.map_cons, List.mem_cons,
        not_or] at hmem
      simp [scaledInversePairLookup, hne, ih hmem.2]
  | case3 entries hshort =>
      cases entries with
      | nil => rfl
      | cons first tail =>
          cases tail with
          | nil => rfl
          | cons second rest =>
              exact False.elim (hshort first second rest rfl)

theorem orbitRadixSparsePairs_weighted_sum_eq_fin
    (entries : List Int)
    (hcheck : orbitRadixSparsePairsSorted entries = true)
    (weight : Nat → Int) :
    ((scaledInverseDecodePairs entries).map
      (fun pair => pair.2 * weight pair.1.toNat)).sum =
      ∑ index : Fin 424,
        scaledInversePairLookup (index.val : Int) entries * weight index.val := by
  classical
  induction entries using scaledInverseDecodePairs.induct with
  | case1 key value remaining ih =>
      obtain ⟨hzero, hbound, hremaining⟩ :=
        orbitRadixSparsePairsSorted_head key value remaining hcheck
      let selected : Fin 424 := ⟨key.toNat, by omega⟩
      have hselected : (selected.val : Int) = key := by
        dsimp [selected]
        omega
      have hnodup := orbitRadixSparsePairsSorted_nodup
        (key :: value :: remaining) hcheck
      have hnotmem : key ∉
          (scaledInverseDecodePairs remaining).map Prod.fst := by
        change (key :: (scaledInverseDecodePairs remaining).map Prod.fst).Nodup
          at hnodup
        exact (List.nodup_cons.mp hnodup).1
      have hzeroTail : scaledInversePairLookup key remaining = 0 :=
        scaledInversePairLookup_eq_zero_of_not_mem key remaining hnotmem
      have hlookup (index : Fin 424) :
          scaledInversePairLookup (index.val : Int)
              (key :: value :: remaining) =
            if index = selected then value
              else scaledInversePairLookup (index.val : Int) remaining := by
        by_cases hindex : index = selected
        · subst index
          simp [scaledInversePairLookup, hselected]
        · have hne : key ≠ (index.val : Int) := by
            intro heq
            apply hindex
            apply Fin.ext
            omega
          simp [scaledInversePairLookup, hne, hindex]
      simp only [scaledInverseDecodePairs, List.map_cons, List.sum_cons]
      rw [ih hremaining]
      simp_rw [hlookup]
      calc
        value * weight key.toNat +
            ∑ index : Fin 424,
              scaledInversePairLookup (index.val : Int) remaining *
                weight index.val =
          ∑ index : Fin 424,
            ((if index = selected then value * weight selected.val else 0) +
              scaledInversePairLookup (index.val : Int) remaining *
                weight index.val) := by
                  simp [Finset.sum_add_distrib, selected]
        _ = ∑ index : Fin 424,
              (if index = selected then value
                else scaledInversePairLookup (index.val : Int) remaining) *
                  weight index.val := by
              apply Finset.sum_congr rfl
              intro index _
              by_cases hindex : index = selected
              · subst index
                simp [hselected, hzeroTail]
              · simp [hindex]
  | case2 entries hshort =>
      cases entries with
      | nil => simp [scaledInverseDecodePairs, scaledInversePairLookup]
      | cons first tail =>
          cases tail with
          | nil => simp [orbitRadixSparsePairsSorted] at hcheck
          | cons second rest =>
              exact False.elim (hshort first second rest rfl)

theorem orbitRadixEncode_append (left right : List Int) :
    orbitRadixEncode (left ++ right) =
      orbitRadixEncode left + orbitRadixBase ^ left.length *
        orbitRadixEncode right := by
  induction left with
  | nil => simp
  | cons digit remaining ih =>
      simp only [List.cons_append, orbitRadixEncode_cons, List.length_cons,
        ih, pow_succ]
      ring

theorem orbitRadixEncode_range_eq_sum
    (count : Nat) (entry : Nat → Int) :
    orbitRadixEncode ((List.range count).map entry) =
      ∑ index ∈ Finset.range count, entry index * orbitRadixBase ^ index := by
  induction count with
  | zero => simp
  | succ count ih =>
      rw [List.range_succ, List.map_append, orbitRadixEncode_append]
      simp only [List.map_cons, List.map_nil, List.length_map,
        List.length_range, orbitRadixEncode_cons, orbitRadixEncode_nil,
        mul_zero, add_zero]
      rw [Finset.sum_range_succ, ih]
      ring

theorem orbitRadixEncodeSparsePairs_eq_sum
    (entries : List Int) :
    orbitRadixEncodeSparsePairs entries =
      ((scaledInverseDecodePairs entries).map
        (fun pair => pair.2 * radixBase ^ pair.1.toNat)).sum := by
  induction entries using scaledInverseDecodePairs.induct with
  | case1 key value remaining ih =>
      simp [orbitRadixEncodeSparsePairs, scaledInverseDecodePairs, ih]
  | case2 entries hshort =>
      cases entries with
      | nil => rfl
      | cons first tail =>
          cases tail with
          | nil => rfl
          | cons second rest =>
              exact False.elim (hshort first second rest rfl)

theorem orbitRadixEncodeSparsePairs_eq_dense
    (entries : List Int)
    (hcheck : orbitRadixSparsePairsSorted entries = true) :
    orbitRadixEncodeSparsePairs entries =
      orbitRadixEncode ((List.range 424).map fun column =>
        scaledInversePairLookup (column : Int) entries) := by
  calc
    orbitRadixEncodeSparsePairs entries =
        ((scaledInverseDecodePairs entries).map
          (fun pair => pair.2 * radixBase ^ pair.1.toNat)).sum :=
      orbitRadixEncodeSparsePairs_eq_sum entries
    _ = ∑ index : Fin 424,
          scaledInversePairLookup (index.val : Int) entries *
            radixBase ^ index.val :=
      orbitRadixSparsePairs_weighted_sum_eq_fin entries hcheck
        (fun index => radixBase ^ index)
    _ = orbitRadixEncode ((List.range 424).map fun column : Nat =>
          scaledInversePairLookup (column : Int) entries) := by
      rw [orbitRadixEncode_range_eq_sum]
      rw [Fin.sum_univ_eq_sum_range (fun index : Nat =>
        scaledInversePairLookup (index : Int) entries * radixBase ^ index)]
      rfl

end ConnesRigidity.AffineSymplecticOrbitCertificate

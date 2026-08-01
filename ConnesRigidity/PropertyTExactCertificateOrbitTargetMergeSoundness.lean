


import ConnesRigidity.PropertyTExactCertificateOrbitTargetRadix












namespace ConnesRigidity.AffineSymplecticOrbitCertificate

universe u


def targetConsumeCode {α : Type u} (key : α → Int) (code : Int) :
    Nat → List α → Option (List α)
  | 0, products => some products
  | _ + 1, [] => none
  | count + 1, product :: products =>
      if key product = code then
        targetConsumeCode key code count products
      else
        none


def targetGroupCheck {α : Type u} (key : α → Int) :
    Int → Nat → List (List Int) → List α → Bool
  | _, _, [], products => products.isEmpty
  | previous, position, group :: groups, products =>
      let code := group.getD 0 0
      let start := group.getD 1 0
      let count := group.getD 2 0
      if group.length = 3 ∧ previous < code ∧
          start = (position : Int) ∧ 0 < count then
        match targetConsumeCode key code count.toNat products with
        | none => false
        | some remaining =>
            targetGroupCheck key code (position + count.toNat)
              groups remaining
      else
        false


def targetSeekGroup (code : Int) :
    List (List Int) → (Int × List (List Int))
  | [] => (0, [])
  | group :: groups =>
      let groupCode := group.getD 0 0
      if groupCode < code then
        targetSeekGroup code groups
      else if groupCode = code then
        (group.getD 2 0, groups)
      else
        (0, group :: groups)


def targetGroupMultiplicity (code : Int) : List (List Int) → Nat
  | [] => 0
  | group :: groups =>
      (if group.getD 0 0 = code then (group.getD 2 0).toNat else 0) +
        targetGroupMultiplicity code groups


def targetGroupCodesStrict (previous : Int) : List (List Int) → Prop
  | [] => True
  | group :: groups =>
      previous < group.getD 0 0 ∧
        targetGroupCodesStrict (group.getD 0 0) groups



theorem targetConsumeCode_sound {α : Type u} (key : α → Int) (code : Int)
    {count : Nat} {products remaining : List α}
    (hconsume : targetConsumeCode key code count products = some remaining) :
    ∃ segment : List α, products = segment ++ remaining ∧
      segment.length = count ∧ ∀ product ∈ segment, key product = code := by
  induction count generalizing products with
  | zero =>
      simp only [targetConsumeCode, Option.some.injEq] at hconsume
      subst products
      exact ⟨[], by simp⟩
  | succ count ih =>
      cases products with
      | nil => simp [targetConsumeCode] at hconsume
      | cons product products =>
          by_cases hcode : key product = code
          · simp only [targetConsumeCode, hcode, ↓reduceIte] at hconsume
            obtain ⟨segment, hproducts, hlength, hkeys⟩ := ih hconsume
            refine ⟨product :: segment, ?_, ?_, ?_⟩
            · simp [hproducts]
            · simp [hlength]
            · intro value hvalue
              simp only [List.mem_cons] at hvalue
              rcases hvalue with rfl | hvalue
              · exact hcode
              · exact hkeys value hvalue
          · simp [targetConsumeCode, hcode] at hconsume



theorem targetConstantPrefix_countP {α : Type u}
    (key : α → Int) (segment : List α) (storedCode queriedCode : Int)
    (hkeys : ∀ product ∈ segment, key product = storedCode) :
    segment.countP (fun product => decide (key product = queriedCode)) =
      if storedCode = queriedCode then segment.length else 0 := by
  induction segment with
  | nil => simp
  | cons product products ih =>
      have hproduct : key product = storedCode :=
        hkeys product (by simp)
      have hrest : ∀ value ∈ products, key value = storedCode := by
        intro value hvalue
        exact hkeys value (by simp [hvalue])
      by_cases hcode : storedCode = queriedCode
      · simp [hproduct, ih hrest, hcode]
      · simp [hproduct, ih hrest, hcode]



theorem targetGroupCheck_countP {α : Type u} (key : α → Int)
    {previous : Int} {position : Nat} {groups : List (List Int)}
    {products : List α}
    (hcheck : targetGroupCheck key previous position groups products = true)
    (code : Int) :
    products.countP (fun product => decide (key product = code)) =
      targetGroupMultiplicity code groups := by
  induction groups generalizing previous position products with
  | nil =>
      cases products with
      | nil => simp [targetGroupMultiplicity]
      | cons product products => simp [targetGroupCheck] at hcheck
  | cons group groups ih =>
      simp only [targetGroupCheck] at hcheck
      split at hcheck
      next hshape =>
        split at hcheck
        next hnone => contradiction
        next remaining hconsume =>
          obtain ⟨segment, hproducts, hlength, hkeys⟩ :=
            targetConsumeCode_sound key (group.getD 0 0) hconsume
          rw [hproducts, List.countP_append]
          rw [targetConstantPrefix_countP key segment (group.getD 0 0) code hkeys]
          rw [ih hcheck, hlength]
          simp [targetGroupMultiplicity]
      next hshape => contradiction



theorem targetGroupCheck_codesStrict {α : Type u} (key : α → Int)
    {previous : Int} {position : Nat} {groups : List (List Int)}
    {products : List α}
    (hcheck : targetGroupCheck key previous position groups products = true) :
    targetGroupCodesStrict previous groups := by
  induction groups generalizing previous position products with
  | nil => trivial
  | cons group groups ih =>
      simp only [targetGroupCheck] at hcheck
      split at hcheck
      next hshape =>
        split at hcheck
        next hnone => contradiction
        next remaining hconsume =>
          exact ⟨hshape.2.1, ih hcheck⟩
      next hshape => contradiction



theorem targetGroupMultiplicity_eq_zero_of_le
    {previous code : Int} {groups : List (List Int)}
    (hgroups : targetGroupCodesStrict previous groups)
    (hle : code ≤ previous) :
    targetGroupMultiplicity code groups = 0 := by
  induction groups generalizing previous with
  | nil => rfl
  | cons group groups ih =>
      obtain ⟨hhead, htail⟩ := hgroups
      have hne : group.getD 0 0 ≠ code := by omega
      change
        (if group.getD 0 0 = code then (group.getD 2 0).toNat else 0) +
          targetGroupMultiplicity code groups = 0
      simp only [if_neg hne, Nat.zero_add]
      exact ih htail (show code ≤ group.getD 0 0 by omega)



theorem targetSeekGroup_sound
    {previous code : Int} {groups : List (List Int)}
    (hgroups : targetGroupCodesStrict previous groups) :
    (targetSeekGroup code groups).1.toNat =
      targetGroupMultiplicity code groups := by
  induction groups generalizing previous with
  | nil => rfl
  | cons group groups ih =>
      obtain ⟨hhead, htail⟩ := hgroups
      simp only [targetSeekGroup, targetGroupMultiplicity]
      by_cases hlt : group.getD 0 0 < code
      · simp only [hlt, ↓reduceIte]
        have hne : group.getD 0 0 ≠ code := by omega
        simp only [if_neg hne, Nat.zero_add]
        exact ih htail
      · simp only [hlt, ↓reduceIte]
        by_cases heq : group.getD 0 0 = code
        · simp only [heq, ↓reduceIte]
          rw [targetGroupMultiplicity_eq_zero_of_le htail (by omega)]
          simp
        · have hgt : code ≤ group.getD 0 0 := by omega
          simp only [heq, ↓reduceIte]
          simp [targetGroupMultiplicity_eq_zero_of_le htail hgt]



theorem targetGroupCheck_seek_countP {α : Type u} (key : α → Int)
    {previous : Int} {position : Nat} {groups : List (List Int)}
    {products : List α}
    (hcheck : targetGroupCheck key previous position groups products = true)
    (code : Int) :
    products.countP (fun product => decide (key product = code)) =
      (targetSeekGroup code groups).1.toNat := by
  rw [targetGroupCheck_countP key hcheck code]
  exact (targetSeekGroup_sound (targetGroupCheck_codesStrict key hcheck)).symm

end ConnesRigidity.AffineSymplecticOrbitCertificate

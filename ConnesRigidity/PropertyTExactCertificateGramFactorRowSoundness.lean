
import ConnesRigidity.PropertyTExactCertificateGramData
import Lean.Elab.Tactic.Omega

namespace ConnesRigidity

namespace AffineSymplecticCertificate

open GramCheckData

private theorem getD_flatten_uniform_prefix
    (chunks : List (List α)) (last : List α) (n : Nat) (fallback : α)
    (chunkLengths : ∀ chunk ∈ chunks, chunk.length = 25)
    (lastLength : last.length ≤ 25)
    (indexBound : n < chunks.flatten.length + last.length) :
    (chunks.flatten ++ last).getD n fallback =
      ((chunks ++ [last]).getD (n / 25) []).getD (n % 25) fallback := by
  induction chunks generalizing n with
  | nil =>
      have hn : n < 25 := by simpa using indexBound
      simp [Nat.div_eq_of_lt hn, Nat.mod_eq_of_lt hn]
  | cons chunk chunks ih =>
      have hlength : chunk.length = 25 := chunkLengths chunk (by simp)
      have htail : ∀ entry ∈ chunks, entry.length = 25 := by
        intro entry hentry
        exact chunkLengths entry (by simp [hentry])
      by_cases hn : n < 25
      · have hindex : n < chunk.length := hlength ▸ hn
        simp only [List.flatten_cons, List.cons_append]
        rw [List.getD_append chunk (chunks.flatten ++ last) fallback n hindex]
        simp [Nat.div_eq_of_lt hn, Nat.mod_eq_of_lt hn]
      · have hn' : 25 ≤ n := by omega
        have hindex : chunk.length ≤ n := hlength ▸ hn'
        have htailIndex : n - 25 < chunks.flatten.length + last.length := by
          simpa [List.flatten_cons, hlength, Nat.add_assoc] using indexBound
        have hdiv : n / 25 = (n - 25) / 25 + 1 := by omega
        have hmod : n % 25 = (n - 25) % 25 := by omega
        simp only [List.flatten_cons, List.cons_append]
        rw [List.getD_append_right chunk (chunks.flatten ++ last)
          fallback n hindex]
        rw [hlength]
        rw [hdiv, hmod]
        simpa using ih (n - 25) htail htailIndex

theorem factorRow_eq_factorData_getD (r : Fin 424) :
    factorRow r = factorData.getD r [] := by
  have h000 : factorRowChunk000.length = 25 := by unfold factorRowChunk000; rfl
  have h001 : factorRowChunk001.length = 25 := by unfold factorRowChunk001; rfl
  have h002 : factorRowChunk002.length = 25 := by unfold factorRowChunk002; rfl
  have h003 : factorRowChunk003.length = 25 := by unfold factorRowChunk003; rfl
  have h004 : factorRowChunk004.length = 25 := by unfold factorRowChunk004; rfl
  have h005 : factorRowChunk005.length = 25 := by unfold factorRowChunk005; rfl
  have h006 : factorRowChunk006.length = 25 := by unfold factorRowChunk006; rfl
  have h007 : factorRowChunk007.length = 25 := by unfold factorRowChunk007; rfl
  have h008 : factorRowChunk008.length = 25 := by unfold factorRowChunk008; rfl
  have h009 : factorRowChunk009.length = 25 := by unfold factorRowChunk009; rfl
  have h010 : factorRowChunk010.length = 25 := by unfold factorRowChunk010; rfl
  have h011 : factorRowChunk011.length = 25 := by unfold factorRowChunk011; rfl
  have h012 : factorRowChunk012.length = 25 := by unfold factorRowChunk012; rfl
  have h013 : factorRowChunk013.length = 25 := by unfold factorRowChunk013; rfl
  have h014 : factorRowChunk014.length = 25 := by unfold factorRowChunk014; rfl
  have h015 : factorRowChunk015.length = 25 := by unfold factorRowChunk015; rfl
  have h016 : factorRowChunk016.length = 24 := by unfold factorRowChunk016; rfl
  let chunks : List (List (List Int)) :=
    [factorRowChunk000, factorRowChunk001, factorRowChunk002,
      factorRowChunk003, factorRowChunk004, factorRowChunk005,
      factorRowChunk006, factorRowChunk007, factorRowChunk008,
      factorRowChunk009, factorRowChunk010, factorRowChunk011,
      factorRowChunk012, factorRowChunk013, factorRowChunk014,
      factorRowChunk015]
  have hchunks : ∀ chunk ∈ chunks, chunk.length = 25 := by
    simp [chunks, h000, h001, h002, h003, h004, h005, h006, h007,
      h008, h009, h010, h011, h012, h013, h014, h015]
  have hbound : (r : Nat) < chunks.flatten.length + factorRowChunk016.length := by
    simpa [chunks, h000, h001, h002, h003, h004, h005, h006, h007,
      h008, h009, h010, h011, h012, h013, h014, h015, h016]
      using r.isLt
  have hrow := getD_flatten_uniform_prefix chunks factorRowChunk016
    r ([] : List Int) hchunks (by omega) hbound
  unfold factorRow factorData
  change (factorRowChunk ((r : Nat) / 25)).getD ((r : Nat) % 25) [] =
    (chunks.flatten ++ factorRowChunk016).getD r []
  rw [hrow]
  congr 1
  change factorRowChunk ((r : Nat) / 25) =
    (chunks ++ [factorRowChunk016]).getD ((r : Nat) / 25) []
  have hquot : (r : Nat) / 25 < 17 := by omega
  interval_cases h : (r : Nat) / 25 <;>
    simp [factorRowChunk, chunks, h]

end AffineSymplecticCertificate

end ConnesRigidity

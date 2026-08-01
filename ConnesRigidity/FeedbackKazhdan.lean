
import ConnesRigidity.PropertyT

namespace ConnesRigidity

universe u

namespace KazhdanPair

variable {G : CountableDiscreteGroup.{u}}
  {K L : Finset G} {ε ε' : ℝ}

theorem mono_finset
    (hK : ConnesRigidity.IsKazhdanPair G K ε)
    (hKL : K ⊆ L) :
    ConnesRigidity.IsKazhdanPair G L ε := by
  refine ⟨hK.1, ?_⟩
  intro H _ _ _ π ξ hξ hclose
  exact hK.2 H inferInstance inferInstance inferInstance π ξ hξ
    (fun g hg ↦ hclose g (hKL hg))

theorem mono_tolerance
    (hK : ConnesRigidity.IsKazhdanPair G K ε)
    (hε' : 0 < ε')
    (hε : ε' ≤ ε) :
    ConnesRigidity.IsKazhdanPair G K ε' := by
  refine ⟨hε', ?_⟩
  intro H _ _ _ π ξ hξ hclose
  exact hK.2 H inferInstance inferInstance inferInstance π ξ hξ
    (fun g hg ↦ lt_of_lt_of_le (hclose g hg) hε)

theorem mono
    (hK : ConnesRigidity.IsKazhdanPair G K ε)
    (hKL : K ⊆ L)
    (hε' : 0 < ε')
    (hε : ε' ≤ ε) :
    ConnesRigidity.IsKazhdanPair G L ε' :=
  mono_tolerance (mono_finset hK hKL) hε' hε

end KazhdanPair

end ConnesRigidity

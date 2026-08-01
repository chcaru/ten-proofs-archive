
import Lean
import Init.Data.Int.Bitwise
import ConnesRigidity.CertificateLiterals.Benchmarks.PositiveEdgeDirectBase.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

structure BenchmarkIntegerTableTerm where
  key : Fin 73033
  numerator : Int
deriving DecidableEq

def benchmarkCoefficientTerm
    (key : Nat) (numerator : Int) : BenchmarkIntegerTableTerm where
  key := Fin.ofNat 73033 key
  numerator := numerator

@[irreducible] noncomputable def benchmarkPositiveEdgePackets32 :
    Array (Array Int) :=
  ConnesRigidity.CertificateLiterals.Benchmarks.PositiveEdgeDirectBase.Entry000.data

def benchmarkPositivePacketTerms
    (packet : Array Int) : List BenchmarkIntegerTableTerm :=
  let weight := 4 * packet.getD 2 0
  let term (keyOffset : Nat) (coefficient : Int) :=
    benchmarkCoefficientTerm (packet.getD keyOffset 0).toNat
      (weight * coefficient)
  [term 3 4, term 4 (-2), term 5 (-2),
    term 6 (-2), term 7 1, term 8 1,
    term 9 (-2), term 10 1, term 11 1]

noncomputable def benchmarkDirectPositiveTerms32 :
    List BenchmarkIntegerTableTerm :=
  benchmarkPositiveEdgePackets32.toList.flatMap
    benchmarkPositivePacketTerms

def benchmarkPositiveLaneCheckData
    (terms : List BenchmarkIntegerTableTerm) :
    List (List Int) × Nat :=
  terms.foldl
    (fun state term =>
      let block := term.key.val / 1000
      let withinBlock := term.key.val % 1000
      let lane := withinBlock / 16
      let digit := withinBlock % 16
      (state.1.modify block fun row =>
          row.modify lane fun encoded =>
            encoded +
              Int.shiftLeft term.numerator (64 * digit),
        state.2 + term.numerator.natAbs))
    (List.replicate 74 (List.replicate 63 0), 0)

end AffineSymplecticCertificate

end ConnesRigidity

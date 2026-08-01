
import ConnesRigidity.TotalGramPrototype.Base
import ConnesRigidity.CertificateLiterals.TotalGramPrototype.SlackFacts.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

namespace TotalGramPrototype

set_option maxRecDepth 1000000

@[irreducible] noncomputable def allResidualSlacks : List Int :=
  (ConnesRigidity.CertificateLiterals.TotalGramPrototype.SlackFacts.Entry000.data).map fun row => row.headD 0

theorem allResidualSlacks_positive :
    allResidualSlacks.length = 424 ∧
      allResidualSlacks.all (fun slack => decide (0 < slack)) = true := by
  unfold allResidualSlacks
  decide +kernel

end TotalGramPrototype

end AffineSymplecticCertificate

end ConnesRigidity

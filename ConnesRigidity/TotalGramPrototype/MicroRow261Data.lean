
import ConnesRigidity.TotalGramPrototype.Base
import ConnesRigidity.CertificateLiterals.TotalGramPrototype.MicroRow261Data.Entry000
import ConnesRigidity.CertificateLiterals.TotalGramPrototype.MicroRow261Data.Entry001
import ConnesRigidity.CertificateLiterals.TotalGramPrototype.MicroRow261Data.Entry002

namespace ConnesRigidity

namespace AffineSymplecticCertificate

namespace TotalGramPrototype

@[irreducible] noncomputable def productRow261Micro16 : Array Int :=
  (ConnesRigidity.CertificateLiterals.TotalGramPrototype.MicroRow261Data.Entry000.data).getD 0 #[]

@[irreducible] noncomputable def totalRow261Micro16 : Array Int :=
  (ConnesRigidity.CertificateLiterals.TotalGramPrototype.MicroRow261Data.Entry001.data).getD 0 #[]

@[irreducible] noncomputable def lane16Row261Micro16Expected :
    List (List Int) :=
  ConnesRigidity.CertificateLiterals.TotalGramPrototype.MicroRow261Data.Entry002.data

end TotalGramPrototype

end AffineSymplecticCertificate

end ConnesRigidity

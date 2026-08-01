
import ConnesRigidity.TotalGramPrototype.Base
import ConnesRigidity.CertificateLiterals.TotalGramPrototype.Row001Data.Entry000
import ConnesRigidity.CertificateLiterals.TotalGramPrototype.Row001Data.Entry001
import ConnesRigidity.CertificateLiterals.TotalGramPrototype.Row001Data.Entry002
import ConnesRigidity.CertificateLiterals.TotalGramPrototype.Row001Data.Entry003
import ConnesRigidity.CertificateLiterals.TotalGramPrototype.Row001Data.Entry004
import ConnesRigidity.CertificateLiterals.TotalGramPrototype.Row001Data.Entry005
import ConnesRigidity.CertificateLiterals.TotalGramPrototype.Row001Data.Entry006
import ConnesRigidity.CertificateLiterals.TotalGramPrototype.Row001Data.Entry007

namespace ConnesRigidity

namespace AffineSymplecticCertificate

namespace TotalGramPrototype

@[irreducible] noncomputable def productRow001 : Array Int :=
  (ConnesRigidity.CertificateLiterals.TotalGramPrototype.Row001Data.Entry000.data
  ).getD 0 #[]

@[irreducible] noncomputable def fullRow001 : Array Int :=
  (ConnesRigidity.CertificateLiterals.TotalGramPrototype.Row001Data.Entry001.data).getD 0 #[]

@[irreducible] noncomputable def totalRow001 : Array Int :=
  (ConnesRigidity.CertificateLiterals.TotalGramPrototype.Row001Data.Entry002.data).getD 0 #[]

@[irreducible] noncomputable def residualRow000Expected : List Int :=
  (ConnesRigidity.CertificateLiterals.TotalGramPrototype.Row001Data.Entry003.data).headD []

@[irreducible] noncomputable def sparseRow001Expected : List (List Int) :=
  ConnesRigidity.CertificateLiterals.TotalGramPrototype.Row001Data.Entry004.data

@[irreducible] noncomputable def lane16Row001Expected : List (List Int) :=
  ConnesRigidity.CertificateLiterals.TotalGramPrototype.Row001Data.Entry005.data

@[irreducible] noncomputable def lane16Row001Part0Expected :
    List (List Int) :=
  ConnesRigidity.CertificateLiterals.TotalGramPrototype.Row001Data.Entry006.data

@[irreducible] noncomputable def residualRow000Part0Expected : List Int :=
  (ConnesRigidity.CertificateLiterals.TotalGramPrototype.Row001Data.Entry007.data).headD []

end TotalGramPrototype

end AffineSymplecticCertificate

end ConnesRigidity

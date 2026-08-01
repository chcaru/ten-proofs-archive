


import ConnesRigidity.TotalGramPrototype.Base
import ConnesRigidity.CertificateLiterals.TotalGramPrototype.ChunkRow001Part0Data.Entry000
import ConnesRigidity.CertificateLiterals.TotalGramPrototype.ChunkRow001Part0Data.Entry001
import ConnesRigidity.CertificateLiterals.TotalGramPrototype.ChunkRow001Part0Data.Entry002
import ConnesRigidity.CertificateLiterals.TotalGramPrototype.ChunkRow001Part0Data.Entry003
import ConnesRigidity.CertificateLiterals.TotalGramPrototype.ChunkRow001Part0Data.Entry004
import ConnesRigidity.CertificateLiterals.TotalGramPrototype.ChunkRow001Part0Data.Entry005

namespace ConnesRigidity

namespace AffineSymplecticCertificate

namespace TotalGramPrototype

@[irreducible] noncomputable def productRow001Part0 : Array Int :=
  (ConnesRigidity.CertificateLiterals.TotalGramPrototype.ChunkRow001Part0Data.Entry000.data).getD 0 #[]

@[irreducible] noncomputable def totalRow001Part0 : Array Int :=
  (ConnesRigidity.CertificateLiterals.TotalGramPrototype.ChunkRow001Part0Data.Entry001.data).getD 0 #[]

@[irreducible] noncomputable def fullReducedRow000Part0 : Array Int :=
  (ConnesRigidity.CertificateLiterals.TotalGramPrototype.ChunkRow001Part0Data.Entry002.data).getD 0 #[]

@[irreducible] noncomputable def totalReducedRow000Part0 : Array Int :=
  (ConnesRigidity.CertificateLiterals.TotalGramPrototype.ChunkRow001Part0Data.Entry003.data).getD 0 #[]

@[irreducible] noncomputable def lane16Row001Part0Expected :
    List (List Int) :=
  ConnesRigidity.CertificateLiterals.TotalGramPrototype.ChunkRow001Part0Data.Entry004.data

@[irreducible] noncomputable def residualRow000Part0Expected : List Int :=
  (ConnesRigidity.CertificateLiterals.TotalGramPrototype.ChunkRow001Part0Data.Entry005.data).headD []

end TotalGramPrototype

end AffineSymplecticCertificate

end ConnesRigidity

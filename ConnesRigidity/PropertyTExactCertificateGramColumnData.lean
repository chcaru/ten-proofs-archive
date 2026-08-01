
import Lean
import Mathlib.Data.List.GetD
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateGramColumnData.Entry000
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateGramColumnData.Entry001
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateGramColumnData.Entry002
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateGramColumnData.Entry003
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateGramColumnData.Entry004
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateGramColumnData.Entry005
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateGramColumnData.Entry006
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateGramColumnData.Entry007
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateGramColumnData.Entry008
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateGramColumnData.Entry009
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateGramColumnData.Entry010
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateGramColumnData.Entry011
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateGramColumnData.Entry012
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateGramColumnData.Entry013

namespace ConnesRigidity

namespace AffineSymplecticCertificate

namespace GramCheckData

set_option maxRecDepth 1000000

@[irreducible] noncomputable def factorColumnChunk000 : List (List Int) :=
  ConnesRigidity.CertificateLiterals.PropertyTExactCertificateGramColumnData.Entry000.data

@[irreducible] noncomputable def factorColumnChunk001 : List (List Int) :=
  ConnesRigidity.CertificateLiterals.PropertyTExactCertificateGramColumnData.Entry001.data

@[irreducible] noncomputable def factorColumnChunk002 : List (List Int) :=
  ConnesRigidity.CertificateLiterals.PropertyTExactCertificateGramColumnData.Entry002.data

@[irreducible] noncomputable def factorColumnChunk003 : List (List Int) :=
  ConnesRigidity.CertificateLiterals.PropertyTExactCertificateGramColumnData.Entry003.data

@[irreducible] noncomputable def factorColumnChunk004 : List (List Int) :=
  ConnesRigidity.CertificateLiterals.PropertyTExactCertificateGramColumnData.Entry004.data

@[irreducible] noncomputable def factorColumnChunk005 : List (List Int) :=
  ConnesRigidity.CertificateLiterals.PropertyTExactCertificateGramColumnData.Entry005.data

@[irreducible] noncomputable def factorColumnChunk006 : List (List Int) :=
  ConnesRigidity.CertificateLiterals.PropertyTExactCertificateGramColumnData.Entry006.data

@[irreducible] noncomputable def factorColumnChunk007 : List (List Int) :=
  ConnesRigidity.CertificateLiterals.PropertyTExactCertificateGramColumnData.Entry007.data

@[irreducible] noncomputable def factorColumnChunk008 : List (List Int) :=
  ConnesRigidity.CertificateLiterals.PropertyTExactCertificateGramColumnData.Entry008.data

@[irreducible] noncomputable def factorColumnChunk009 : List (List Int) :=
  ConnesRigidity.CertificateLiterals.PropertyTExactCertificateGramColumnData.Entry009.data

@[irreducible] noncomputable def factorColumnChunk010 : List (List Int) :=
  ConnesRigidity.CertificateLiterals.PropertyTExactCertificateGramColumnData.Entry010.data

@[irreducible] noncomputable def factorColumnChunk011 : List (List Int) :=
  ConnesRigidity.CertificateLiterals.PropertyTExactCertificateGramColumnData.Entry011.data

@[irreducible] noncomputable def factorColumnChunk012 : List (List Int) :=
  ConnesRigidity.CertificateLiterals.PropertyTExactCertificateGramColumnData.Entry012.data

@[irreducible] noncomputable def factorColumnChunk013 : List (List Int) :=
  ConnesRigidity.CertificateLiterals.PropertyTExactCertificateGramColumnData.Entry013.data

noncomputable def factorColumnChunk : Nat → List (List Int)
  | 0 => factorColumnChunk000
  | 1 => factorColumnChunk001
  | 2 => factorColumnChunk002
  | 3 => factorColumnChunk003
  | 4 => factorColumnChunk004
  | 5 => factorColumnChunk005
  | 6 => factorColumnChunk006
  | 7 => factorColumnChunk007
  | 8 => factorColumnChunk008
  | 9 => factorColumnChunk009
  | 10 => factorColumnChunk010
  | 11 => factorColumnChunk011
  | 12 => factorColumnChunk012
  | 13 => factorColumnChunk013
  | _ => []

noncomputable def factorColumn (i : Nat) : List Int :=
  (factorColumnChunk (i / 32)).getD (i % 32) []

end GramCheckData

end AffineSymplecticCertificate

end ConnesRigidity

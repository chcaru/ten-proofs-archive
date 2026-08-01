


import ConnesRigidity.PropertyTExactCertificateOrbitData
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateOrbitTargetData.Entry000
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateOrbitTargetData.Entry001
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateOrbitTargetData.Entry002
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateOrbitTargetData.Entry003
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateOrbitTargetData.Entry004



namespace ConnesRigidity.AffineSymplecticOrbitCertificate

def targetCoordinateRadix : Int := 16
def targetCoordinateOffset : Int := 8

@[irreducible] noncomputable def targetGeneratorProductRowData : List (List Int) :=
  ConnesRigidity.CertificateLiterals.PropertyTExactCertificateOrbitTargetData.Entry000.data

@[irreducible] noncomputable def targetGeneratorProductGroupData : List (List Int) :=
  ConnesRigidity.CertificateLiterals.PropertyTExactCertificateOrbitTargetData.Entry001.data

@[irreducible] noncomputable def targetRepresentativeCodeSortedData : List (List Int) :=
  ConnesRigidity.CertificateLiterals.PropertyTExactCertificateOrbitTargetData.Entry002.data

@[irreducible] noncomputable def targetGeneratorProductRowIndexData : List (List Int) :=
  ConnesRigidity.CertificateLiterals.PropertyTExactCertificateOrbitTargetData.Entry003.data

@[irreducible] noncomputable def targetRepresentativeCodeIndexData : List (List Int) :=
  ConnesRigidity.CertificateLiterals.PropertyTExactCertificateOrbitTargetData.Entry004.data

end ConnesRigidity.AffineSymplecticOrbitCertificate

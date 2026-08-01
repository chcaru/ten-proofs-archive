
import ConnesRigidity.TotalGramPrototype.ChunkRow001Part0Data

namespace ConnesRigidity

namespace AffineSymplecticCertificate

namespace TotalGramPrototype

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem residualRow000Part0_check :
    let row := residualChunkRows
      fullReducedRow000Part0 totalReducedRow000Part0
    (row, residualSliceAbsoluteTotal 0 0 row) =
      (residualRow000Part0Expected, 66539960) := by
  unfold residualChunkRows residualSliceAbsoluteTotal
    offDiagonalAbsoluteTotal fullReducedRow000Part0
    totalReducedRow000Part0 residualRow000Part0Expected
  decide +kernel

end TotalGramPrototype

end AffineSymplecticCertificate

end ConnesRigidity

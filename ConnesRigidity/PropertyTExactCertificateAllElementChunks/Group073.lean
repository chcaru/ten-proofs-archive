
namespace ConnesRigidity

namespace AffineSymplecticCertificate

@[irreducible] noncomputable def allElementDataChunk073_000 : Array (Array Int) :=
  #[#[1,0,0,0,-1,1,0,-1,0,0,1,1,0,0,0,1,0,0,0,2],
    #[1,0,0,-1,-1,1,-1,1,0,0,1,1,0,0,0,1,0,0,0,2],
    #[1,0,0,0,-1,1,0,0,0,0,1,1,0,0,0,1,-1,1,0,2],
    #[1,0,0,0,-1,1,0,0,0,0,1,1,0,0,0,1,1,-1,0,2],
    #[1,0,0,0,-1,1,0,0,0,0,1,1,0,0,0,1,0,0,1,3]]

@[irreducible] noncomputable def allElementDataChunk073_001 : Array (Array Int) :=
  #[#[1,1,0,0,0,1,1,-1,0,0,1,0,0,0,-1,1,0,0,0,2],
    #[1,0,0,0,-1,1,0,-1,0,1,1,0,1,0,0,1,0,0,0,2],
    #[1,-1,0,0,0,1,-1,-1,0,0,1,0,0,0,1,1,0,0,0,2],
    #[1,0,0,0,0,2,0,-1,0,0,1,0,0,-1,0,1,0,0,0,2],
    #[1,0,0,0,1,1,0,-1,0,-1,1,0,-1,0,0,1,0,0,0,2]]

@[irreducible] noncomputable def allElementDataChunk073_002 : Array (Array Int) :=
  #[#[1,0,0,0,0,1,0,-2,0,0,1,0,0,0,0,1,0,0,0,2],
    #[1,0,0,-1,0,1,-1,-1,0,0,1,0,0,0,0,1,0,0,0,2],
    #[1,0,0,0,0,1,0,-1,0,0,1,0,0,0,0,1,0,-1,0,3],
    #[1,1,1,-1,0,1,-1,0,0,0,1,0,0,0,-1,1,0,0,0,2],
    #[1,0,0,-1,1,1,-1,1,0,0,1,-1,0,0,0,1,0,0,0,2]]

@[irreducible] noncomputable def allElementDataChunk073_003 : Array (Array Int) :=
  #[#[1,0,0,-1,-1,1,-1,0,1,0,1,0,0,0,0,1,0,0,0,2],
    #[1,-1,0,-1,0,1,-1,0,0,0,1,0,0,1,0,1,0,0,0,2],
    #[1,-1,-1,-1,0,1,-1,0,0,0,1,0,0,0,1,1,0,0,0,2],
    #[1,0,0,-1,-1,1,-1,-1,0,0,1,1,0,0,0,1,0,0,0,2],
    #[1,0,0,-1,1,1,-1,0,-1,0,1,0,0,0,0,1,0,0,0,2]]

@[irreducible] noncomputable def allElementDataChunk073_004 : Array (Array Int) :=
  #[#[1,1,0,-1,0,1,-1,0,0,0,1,0,0,-1,0,1,0,0,0,2],
    #[2,0,0,-1,0,2,-1,0,0,-1,1,0,-1,0,0,1,0,0,0,2],
    #[1,0,0,-2,0,1,-2,0,0,0,1,0,0,0,0,1,0,0,0,2],
    #[1,0,0,-1,0,1,-1,0,0,0,1,0,0,0,0,1,0,1,-1,2],
    #[1,0,0,-1,0,1,-1,0,0,0,1,0,0,0,0,1,0,-1,1,2]]

@[irreducible] noncomputable def allElementDataChunk073_005 : Array (Array Int) :=
  #[#[1,0,0,-1,0,1,-1,0,0,0,1,0,0,0,0,1,-1,0,0,3],
    #[1,0,0,0,1,1,0,0,0,0,1,-1,0,0,0,1,0,0,0,3],
    #[1,0,0,0,0,1,0,1,0,0,1,0,0,0,0,1,0,0,0,3],
    #[1,0,0,1,0,1,1,0,0,0,1,0,0,0,0,1,0,0,0,3],
    #[1,0,0,0,-1,1,0,0,0,0,1,1,0,0,0,1,0,0,0,3]]

@[irreducible] noncomputable def allElementDataChunk073_006 : Array (Array Int) :=
  #[#[1,0,0,0,0,1,0,-1,0,0,1,0,0,0,0,1,0,0,0,3],
    #[1,0,0,-1,0,1,-1,0,0,0,1,0,0,0,0,1,0,0,0,3],
    #[1,0,0,0,0,1,0,0,0,0,1,0,0,0,0,1,0,0,0,4]]

noncomputable def allElementDataGroup073 (i : Nat) : Array Int :=
  let chunk := i / 5
  let row := i % 5
  if chunk < 7 then
    if chunk < 3 then
      if chunk < 1 then
        allElementDataChunk073_000.getD row #[]
      else
        if chunk < 2 then
          allElementDataChunk073_001.getD row #[]
        else
          allElementDataChunk073_002.getD row #[]
    else
      if chunk < 5 then
        if chunk < 4 then
          allElementDataChunk073_003.getD row #[]
        else
          allElementDataChunk073_004.getD row #[]
      else
        if chunk < 6 then
          allElementDataChunk073_005.getD row #[]
        else
          allElementDataChunk073_006.getD row #[]
  else
    #[]

end AffineSymplecticCertificate

end ConnesRigidity

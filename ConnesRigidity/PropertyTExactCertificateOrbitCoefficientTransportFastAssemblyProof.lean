import ConnesRigidity.PropertyTExactCertificateOrbitCoefficientTransportFastAssembly

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section

set_option linter.style.setOption false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem orbitCoefficientTransportPacketsCheck_of_batches
    (h0 : orbitCoefficientTransportPacketsCheck 0
      ((gramOrbitData.toList.drop 0).take 188)
      ((orbitCoefficientTransportPacketData.drop 0).take 188) = true)
    (h1 : orbitCoefficientTransportPacketsCheck 188
      ((gramOrbitData.toList.drop 188).take 188)
      ((orbitCoefficientTransportPacketData.drop 188).take 188) = true)
    (h2 : orbitCoefficientTransportPacketsCheck 376
      ((gramOrbitData.toList.drop 376).take 188)
      ((orbitCoefficientTransportPacketData.drop 376).take 188) = true)
    (h3 : orbitCoefficientTransportPacketsCheck 564
      ((gramOrbitData.toList.drop 564).take 188)
      ((orbitCoefficientTransportPacketData.drop 564).take 188) = true)
    (h4 : orbitCoefficientTransportPacketsCheck 752
      ((gramOrbitData.toList.drop 752).take 188)
      ((orbitCoefficientTransportPacketData.drop 752).take 188) = true)
    (h5 : orbitCoefficientTransportPacketsCheck 940
      ((gramOrbitData.toList.drop 940).take 188)
      ((orbitCoefficientTransportPacketData.drop 940).take 188) = true)
    (h6 : orbitCoefficientTransportPacketsCheck 1128
      ((gramOrbitData.toList.drop 1128).take 188)
      ((orbitCoefficientTransportPacketData.drop 1128).take 188) = true)
    (h7 : orbitCoefficientTransportPacketsCheck 1316
      ((gramOrbitData.toList.drop 1316).take 188)
      ((orbitCoefficientTransportPacketData.drop 1316).take 188) = true)
    (h8 : orbitCoefficientTransportPacketsCheck 1504
      ((gramOrbitData.toList.drop 1504).take 188)
      ((orbitCoefficientTransportPacketData.drop 1504).take 188) = true)
    (h9 : orbitCoefficientTransportPacketsCheck 1692
      ((gramOrbitData.toList.drop 1692).take 188)
      ((orbitCoefficientTransportPacketData.drop 1692).take 188) = true)
    (h10 : orbitCoefficientTransportPacketsCheck 1880
      ((gramOrbitData.toList.drop 1880).take 188)
      ((orbitCoefficientTransportPacketData.drop 1880).take 188) = true)
    (h11 : orbitCoefficientTransportPacketsCheck 2068
      ((gramOrbitData.toList.drop 2068).take 188)
      ((orbitCoefficientTransportPacketData.drop 2068).take 188) = true)
    : orbitCoefficientTransportPacketsCheck 0
      gramOrbitData.toList orbitCoefficientTransportPacketData = true := by
  have hgramLength : gramOrbitData.toList.length = 2256 := by
    simp [gramOrbitData_size]
  have hpacketLength : orbitCoefficientTransportPacketData.length = 2256 := by
    decide +kernel
  apply orbitCoefficientTransportPacketsCheck_step 0 _ _
    (by simp [hgramLength]) (by simp [hpacketLength]) h0
  simp only [List.drop_drop, Nat.zero_add]
  apply orbitCoefficientTransportPacketsCheck_step 188 _ _ (by simp [hgramLength])
    (by simp [hpacketLength]) h1
  simp only [List.drop_drop]
  norm_num
  apply orbitCoefficientTransportPacketsCheck_step 376 _ _ (by simp [hgramLength])
    (by simp [hpacketLength]) h2
  simp only [List.drop_drop]
  norm_num
  apply orbitCoefficientTransportPacketsCheck_step 564 _ _ (by simp [hgramLength])
    (by simp [hpacketLength]) h3
  simp only [List.drop_drop]
  norm_num
  apply orbitCoefficientTransportPacketsCheck_step 752 _ _ (by simp [hgramLength])
    (by simp [hpacketLength]) h4
  simp only [List.drop_drop]
  norm_num
  apply orbitCoefficientTransportPacketsCheck_step 940 _ _ (by simp [hgramLength])
    (by simp [hpacketLength]) h5
  simp only [List.drop_drop]
  norm_num
  apply orbitCoefficientTransportPacketsCheck_step 1128 _ _ (by simp [hgramLength])
    (by simp [hpacketLength]) h6
  simp only [List.drop_drop]
  norm_num
  apply orbitCoefficientTransportPacketsCheck_step 1316 _ _ (by simp [hgramLength])
    (by simp [hpacketLength]) h7
  simp only [List.drop_drop]
  norm_num
  apply orbitCoefficientTransportPacketsCheck_step 1504 _ _ (by simp [hgramLength])
    (by simp [hpacketLength]) h8
  simp only [List.drop_drop]
  norm_num
  apply orbitCoefficientTransportPacketsCheck_step 1692 _ _ (by simp [hgramLength])
    (by simp [hpacketLength]) h9
  simp only [List.drop_drop]
  norm_num
  apply orbitCoefficientTransportPacketsCheck_step 1880 _ _ (by simp [hgramLength])
    (by simp [hpacketLength]) h10
  simp only [List.drop_drop]
  norm_num
  have hlastGrams : (gramOrbitData.toList.drop 2068).length = 188 := by
    simp [hgramLength]
  have hlastPackets :
      (orbitCoefficientTransportPacketData.drop 2068).length = 188 := by
    simp [hpacketLength]
  simpa [List.drop_drop,
    List.take_of_length_le (by omega :
      (gramOrbitData.toList.drop 2068).length ≤ 188),
    List.take_of_length_le (by omega :
      (orbitCoefficientTransportPacketData.drop 2068).length ≤ 188)] using h11

end

end ConnesRigidity.AffineSymplecticOrbitCertificate

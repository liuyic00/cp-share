import Proofs.ReferenceStoreSize
import Proofs.ReferenceLoadSize
namespace NutShellProofs
open nNutCore
theorem load_checker_size_mask_0 (s : State) (i : Inputs)
    (mask : v30865 s i = 0) : v31183 s i = 0 := by
  simp [v31183, v31182, v31181, v31180, v31179, v31164, v24, v31163, v31156, v31155, v31152, v31151, v31154, v31153, v31162, v31161, v31158, v31157, v31160, v31159, v31178, v31177, v31170, v31169, v31166, v31165, v31168, v31167, v31176, v31175, v31172, v31171, v31174, v31173, v2687, mask]
#print axioms load_checker_size_mask_0
theorem load_checker_size_mask_1 (s : State) (i : Inputs)
    (mask : v30865 s i = 1) : v31183 s i = 8 := by
  simp [v31183, v31182, v31181, v31180, v31179, v31164, v24, v31163, v31156, v31155, v31152, v31151, v31154, v31153, v31162, v31161, v31158, v31157, v31160, v31159, v31178, v31177, v31170, v31169, v31166, v31165, v31168, v31167, v31176, v31175, v31172, v31171, v31174, v31173, v2687, mask]
#print axioms load_checker_size_mask_1
theorem load_checker_size_mask_2 (s : State) (i : Inputs)
    (mask : v30865 s i = 2) : v31183 s i = 8 := by
  simp [v31183, v31182, v31181, v31180, v31179, v31164, v24, v31163, v31156, v31155, v31152, v31151, v31154, v31153, v31162, v31161, v31158, v31157, v31160, v31159, v31178, v31177, v31170, v31169, v31166, v31165, v31168, v31167, v31176, v31175, v31172, v31171, v31174, v31173, v2687, mask]
#print axioms load_checker_size_mask_2
theorem load_checker_size_mask_3 (s : State) (i : Inputs)
    (mask : v30865 s i = 3) : v31183 s i = 16 := by
  simp [v31183, v31182, v31181, v31180, v31179, v31164, v24, v31163, v31156, v31155, v31152, v31151, v31154, v31153, v31162, v31161, v31158, v31157, v31160, v31159, v31178, v31177, v31170, v31169, v31166, v31165, v31168, v31167, v31176, v31175, v31172, v31171, v31174, v31173, v2687, mask]
#print axioms load_checker_size_mask_3
theorem load_checker_size_mask_4 (s : State) (i : Inputs)
    (mask : v30865 s i = 4) : v31183 s i = 8 := by
  simp [v31183, v31182, v31181, v31180, v31179, v31164, v24, v31163, v31156, v31155, v31152, v31151, v31154, v31153, v31162, v31161, v31158, v31157, v31160, v31159, v31178, v31177, v31170, v31169, v31166, v31165, v31168, v31167, v31176, v31175, v31172, v31171, v31174, v31173, v2687, mask]
#print axioms load_checker_size_mask_4
theorem load_checker_size_mask_8 (s : State) (i : Inputs)
    (mask : v30865 s i = 8) : v31183 s i = 8 := by
  simp [v31183, v31182, v31181, v31180, v31179, v31164, v24, v31163, v31156, v31155, v31152, v31151, v31154, v31153, v31162, v31161, v31158, v31157, v31160, v31159, v31178, v31177, v31170, v31169, v31166, v31165, v31168, v31167, v31176, v31175, v31172, v31171, v31174, v31173, v2687, mask]
#print axioms load_checker_size_mask_8
theorem load_checker_size_mask_12 (s : State) (i : Inputs)
    (mask : v30865 s i = 12) : v31183 s i = 16 := by
  simp [v31183, v31182, v31181, v31180, v31179, v31164, v24, v31163, v31156, v31155, v31152, v31151, v31154, v31153, v31162, v31161, v31158, v31157, v31160, v31159, v31178, v31177, v31170, v31169, v31166, v31165, v31168, v31167, v31176, v31175, v31172, v31171, v31174, v31173, v2687, mask]
#print axioms load_checker_size_mask_12
theorem load_checker_size_mask_15 (s : State) (i : Inputs)
    (mask : v30865 s i = 15) : v31183 s i = 32 := by
  simp [v31183, v31182, v31181, v31180, v31179, v31164, v24, v31163, v31156, v31155, v31152, v31151, v31154, v31153, v31162, v31161, v31158, v31157, v31160, v31159, v31178, v31177, v31170, v31169, v31166, v31165, v31168, v31167, v31176, v31175, v31172, v31171, v31174, v31173, v2687, mask]
#print axioms load_checker_size_mask_15
theorem load_checker_size_mask_16 (s : State) (i : Inputs)
    (mask : v30865 s i = 16) : v31183 s i = 8 := by
  simp [v31183, v31182, v31181, v31180, v31179, v31164, v24, v31163, v31156, v31155, v31152, v31151, v31154, v31153, v31162, v31161, v31158, v31157, v31160, v31159, v31178, v31177, v31170, v31169, v31166, v31165, v31168, v31167, v31176, v31175, v31172, v31171, v31174, v31173, v2687, mask]
#print axioms load_checker_size_mask_16
theorem load_checker_size_mask_32 (s : State) (i : Inputs)
    (mask : v30865 s i = 32) : v31183 s i = 8 := by
  simp [v31183, v31182, v31181, v31180, v31179, v31164, v24, v31163, v31156, v31155, v31152, v31151, v31154, v31153, v31162, v31161, v31158, v31157, v31160, v31159, v31178, v31177, v31170, v31169, v31166, v31165, v31168, v31167, v31176, v31175, v31172, v31171, v31174, v31173, v2687, mask]
#print axioms load_checker_size_mask_32
theorem load_checker_size_mask_48 (s : State) (i : Inputs)
    (mask : v30865 s i = 48) : v31183 s i = 16 := by
  simp [v31183, v31182, v31181, v31180, v31179, v31164, v24, v31163, v31156, v31155, v31152, v31151, v31154, v31153, v31162, v31161, v31158, v31157, v31160, v31159, v31178, v31177, v31170, v31169, v31166, v31165, v31168, v31167, v31176, v31175, v31172, v31171, v31174, v31173, v2687, mask]
#print axioms load_checker_size_mask_48
theorem load_checker_size_mask_64 (s : State) (i : Inputs)
    (mask : v30865 s i = 64) : v31183 s i = 8 := by
  simp [v31183, v31182, v31181, v31180, v31179, v31164, v24, v31163, v31156, v31155, v31152, v31151, v31154, v31153, v31162, v31161, v31158, v31157, v31160, v31159, v31178, v31177, v31170, v31169, v31166, v31165, v31168, v31167, v31176, v31175, v31172, v31171, v31174, v31173, v2687, mask]
#print axioms load_checker_size_mask_64
theorem load_checker_size_mask_128 (s : State) (i : Inputs)
    (mask : v30865 s i = 128) : v31183 s i = 8 := by
  simp [v31183, v31182, v31181, v31180, v31179, v31164, v24, v31163, v31156, v31155, v31152, v31151, v31154, v31153, v31162, v31161, v31158, v31157, v31160, v31159, v31178, v31177, v31170, v31169, v31166, v31165, v31168, v31167, v31176, v31175, v31172, v31171, v31174, v31173, v2687, mask]
#print axioms load_checker_size_mask_128
theorem load_checker_size_mask_192 (s : State) (i : Inputs)
    (mask : v30865 s i = 192) : v31183 s i = 16 := by
  simp [v31183, v31182, v31181, v31180, v31179, v31164, v24, v31163, v31156, v31155, v31152, v31151, v31154, v31153, v31162, v31161, v31158, v31157, v31160, v31159, v31178, v31177, v31170, v31169, v31166, v31165, v31168, v31167, v31176, v31175, v31172, v31171, v31174, v31173, v2687, mask]
#print axioms load_checker_size_mask_192
theorem load_checker_size_mask_240 (s : State) (i : Inputs)
    (mask : v30865 s i = 240) : v31183 s i = 32 := by
  simp [v31183, v31182, v31181, v31180, v31179, v31164, v24, v31163, v31156, v31155, v31152, v31151, v31154, v31153, v31162, v31161, v31158, v31157, v31160, v31159, v31178, v31177, v31170, v31169, v31166, v31165, v31168, v31167, v31176, v31175, v31172, v31171, v31174, v31173, v2687, mask]
#print axioms load_checker_size_mask_240
theorem load_checker_size_mask_255 (s : State) (i : Inputs)
    (mask : v30865 s i = 255) : v31183 s i = 64 := by
  simp [v31183, v31182, v31181, v31180, v31179, v31164, v24, v31163, v31156, v31155, v31152, v31151, v31154, v31153, v31162, v31161, v31158, v31157, v31160, v31159, v31178, v31177, v31170, v31169, v31166, v31165, v31168, v31167, v31176, v31175, v31172, v31171, v31174, v31173, v2687, mask]
#print axioms load_checker_size_mask_255
theorem store_checker_size_mask_0 (s : State) (i : Inputs)
    (mask : v30869 s i = 0) : v31337 s i = 0 := by
  simp [v31337, v31336, v31335, v31334, v31333, v31318, v24, v31317, v31310, v31309, v31306, v31305, v31308, v31307, v31316, v31315, v31312, v31311, v31314, v31313, v31332, v31331, v31324, v31323, v31320, v31319, v31322, v31321, v31330, v31329, v31326, v31325, v31328, v31327, v2687, mask]
#print axioms store_checker_size_mask_0
theorem store_checker_size_mask_1 (s : State) (i : Inputs)
    (mask : v30869 s i = 1) : v31337 s i = 8 := by
  simp [v31337, v31336, v31335, v31334, v31333, v31318, v24, v31317, v31310, v31309, v31306, v31305, v31308, v31307, v31316, v31315, v31312, v31311, v31314, v31313, v31332, v31331, v31324, v31323, v31320, v31319, v31322, v31321, v31330, v31329, v31326, v31325, v31328, v31327, v2687, mask]
#print axioms store_checker_size_mask_1
theorem store_checker_size_mask_2 (s : State) (i : Inputs)
    (mask : v30869 s i = 2) : v31337 s i = 8 := by
  simp [v31337, v31336, v31335, v31334, v31333, v31318, v24, v31317, v31310, v31309, v31306, v31305, v31308, v31307, v31316, v31315, v31312, v31311, v31314, v31313, v31332, v31331, v31324, v31323, v31320, v31319, v31322, v31321, v31330, v31329, v31326, v31325, v31328, v31327, v2687, mask]
#print axioms store_checker_size_mask_2
theorem store_checker_size_mask_3 (s : State) (i : Inputs)
    (mask : v30869 s i = 3) : v31337 s i = 16 := by
  simp [v31337, v31336, v31335, v31334, v31333, v31318, v24, v31317, v31310, v31309, v31306, v31305, v31308, v31307, v31316, v31315, v31312, v31311, v31314, v31313, v31332, v31331, v31324, v31323, v31320, v31319, v31322, v31321, v31330, v31329, v31326, v31325, v31328, v31327, v2687, mask]
#print axioms store_checker_size_mask_3
theorem store_checker_size_mask_4 (s : State) (i : Inputs)
    (mask : v30869 s i = 4) : v31337 s i = 8 := by
  simp [v31337, v31336, v31335, v31334, v31333, v31318, v24, v31317, v31310, v31309, v31306, v31305, v31308, v31307, v31316, v31315, v31312, v31311, v31314, v31313, v31332, v31331, v31324, v31323, v31320, v31319, v31322, v31321, v31330, v31329, v31326, v31325, v31328, v31327, v2687, mask]
#print axioms store_checker_size_mask_4
theorem store_checker_size_mask_8 (s : State) (i : Inputs)
    (mask : v30869 s i = 8) : v31337 s i = 8 := by
  simp [v31337, v31336, v31335, v31334, v31333, v31318, v24, v31317, v31310, v31309, v31306, v31305, v31308, v31307, v31316, v31315, v31312, v31311, v31314, v31313, v31332, v31331, v31324, v31323, v31320, v31319, v31322, v31321, v31330, v31329, v31326, v31325, v31328, v31327, v2687, mask]
#print axioms store_checker_size_mask_8
theorem store_checker_size_mask_12 (s : State) (i : Inputs)
    (mask : v30869 s i = 12) : v31337 s i = 16 := by
  simp [v31337, v31336, v31335, v31334, v31333, v31318, v24, v31317, v31310, v31309, v31306, v31305, v31308, v31307, v31316, v31315, v31312, v31311, v31314, v31313, v31332, v31331, v31324, v31323, v31320, v31319, v31322, v31321, v31330, v31329, v31326, v31325, v31328, v31327, v2687, mask]
#print axioms store_checker_size_mask_12
theorem store_checker_size_mask_15 (s : State) (i : Inputs)
    (mask : v30869 s i = 15) : v31337 s i = 32 := by
  simp [v31337, v31336, v31335, v31334, v31333, v31318, v24, v31317, v31310, v31309, v31306, v31305, v31308, v31307, v31316, v31315, v31312, v31311, v31314, v31313, v31332, v31331, v31324, v31323, v31320, v31319, v31322, v31321, v31330, v31329, v31326, v31325, v31328, v31327, v2687, mask]
#print axioms store_checker_size_mask_15
theorem store_checker_size_mask_16 (s : State) (i : Inputs)
    (mask : v30869 s i = 16) : v31337 s i = 8 := by
  simp [v31337, v31336, v31335, v31334, v31333, v31318, v24, v31317, v31310, v31309, v31306, v31305, v31308, v31307, v31316, v31315, v31312, v31311, v31314, v31313, v31332, v31331, v31324, v31323, v31320, v31319, v31322, v31321, v31330, v31329, v31326, v31325, v31328, v31327, v2687, mask]
#print axioms store_checker_size_mask_16
theorem store_checker_size_mask_32 (s : State) (i : Inputs)
    (mask : v30869 s i = 32) : v31337 s i = 8 := by
  simp [v31337, v31336, v31335, v31334, v31333, v31318, v24, v31317, v31310, v31309, v31306, v31305, v31308, v31307, v31316, v31315, v31312, v31311, v31314, v31313, v31332, v31331, v31324, v31323, v31320, v31319, v31322, v31321, v31330, v31329, v31326, v31325, v31328, v31327, v2687, mask]
#print axioms store_checker_size_mask_32
theorem store_checker_size_mask_48 (s : State) (i : Inputs)
    (mask : v30869 s i = 48) : v31337 s i = 16 := by
  simp [v31337, v31336, v31335, v31334, v31333, v31318, v24, v31317, v31310, v31309, v31306, v31305, v31308, v31307, v31316, v31315, v31312, v31311, v31314, v31313, v31332, v31331, v31324, v31323, v31320, v31319, v31322, v31321, v31330, v31329, v31326, v31325, v31328, v31327, v2687, mask]
#print axioms store_checker_size_mask_48
theorem store_checker_size_mask_64 (s : State) (i : Inputs)
    (mask : v30869 s i = 64) : v31337 s i = 8 := by
  simp [v31337, v31336, v31335, v31334, v31333, v31318, v24, v31317, v31310, v31309, v31306, v31305, v31308, v31307, v31316, v31315, v31312, v31311, v31314, v31313, v31332, v31331, v31324, v31323, v31320, v31319, v31322, v31321, v31330, v31329, v31326, v31325, v31328, v31327, v2687, mask]
#print axioms store_checker_size_mask_64
theorem store_checker_size_mask_128 (s : State) (i : Inputs)
    (mask : v30869 s i = 128) : v31337 s i = 8 := by
  simp [v31337, v31336, v31335, v31334, v31333, v31318, v24, v31317, v31310, v31309, v31306, v31305, v31308, v31307, v31316, v31315, v31312, v31311, v31314, v31313, v31332, v31331, v31324, v31323, v31320, v31319, v31322, v31321, v31330, v31329, v31326, v31325, v31328, v31327, v2687, mask]
#print axioms store_checker_size_mask_128
theorem store_checker_size_mask_192 (s : State) (i : Inputs)
    (mask : v30869 s i = 192) : v31337 s i = 16 := by
  simp [v31337, v31336, v31335, v31334, v31333, v31318, v24, v31317, v31310, v31309, v31306, v31305, v31308, v31307, v31316, v31315, v31312, v31311, v31314, v31313, v31332, v31331, v31324, v31323, v31320, v31319, v31322, v31321, v31330, v31329, v31326, v31325, v31328, v31327, v2687, mask]
#print axioms store_checker_size_mask_192
theorem store_checker_size_mask_240 (s : State) (i : Inputs)
    (mask : v30869 s i = 240) : v31337 s i = 32 := by
  simp [v31337, v31336, v31335, v31334, v31333, v31318, v24, v31317, v31310, v31309, v31306, v31305, v31308, v31307, v31316, v31315, v31312, v31311, v31314, v31313, v31332, v31331, v31324, v31323, v31320, v31319, v31322, v31321, v31330, v31329, v31326, v31325, v31328, v31327, v2687, mask]
#print axioms store_checker_size_mask_240
theorem store_checker_size_mask_255 (s : State) (i : Inputs)
    (mask : v30869 s i = 255) : v31337 s i = 64 := by
  simp [v31337, v31336, v31335, v31334, v31333, v31318, v24, v31317, v31310, v31309, v31306, v31305, v31308, v31307, v31316, v31315, v31312, v31311, v31314, v31313, v31332, v31331, v31324, v31323, v31320, v31319, v31322, v31321, v31330, v31329, v31326, v31325, v31328, v31327, v2687, mask]
#print axioms store_checker_size_mask_255
end NutShellProofs

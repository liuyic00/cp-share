import Proofs.ShiftDecode
namespace NutShellProofs
open nNutCore
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
theorem idu_shift_0_sll_legal (s : State) (i : Inputs)
    (normal : v26384 s i = 0) (matched : IsShiftImmediate .sll (v26210 s i)) :
    v26905 s i = 0 := by
  change v26210 s i &&& BitVec.ofNat 64 4227887231 = BitVec.ofNat 64 4115 at matched
  have unitOverride : v28077 s i = 0 := normal
  have opOverride : v28454 s i = 0 := normal
  have hv26389 : v26389 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 4115) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26386, v26388, v26387] using (show v26389 s i = 0 by unfold v26389; exact if_neg miss)
  have hv26394 : v26394 s i = 1 := by
    simp [v26394, v26391, v26393, v26392, matched]
  have format : v26897 s i = 4 := by
    simp [v26897, v26385, v26896, v26895, v26395, normal, unitOverride, opOverride, hv26389, hv26394]
  have illegal : v26905 s i = 0 := by
    simp [v26905, v26904, v26903, v26902, v26901, v26899, v26898, v26900, v26380, v26379, v10036, v10035, v10034, v10033, v10032, v10031, v9859, v9834, v9858, v9846, v9840, v9838, v9836, v9835, v9837, v9839, v9845, v9843, v9841, v9842, v9844, v9857, v9851, v9849, v9847, v9848, v9850, v9856, v9854, v9852, v9853, v9855, v10030, v9952, v9913, v9900, v9887, v9874, v9873, v9872, v9860, v9871, v9865, v9862, v9861, v9864, v9863, v9870, v9867, v9866, v9869, v9868, v9881, v9878, v9876, v9875, v9877, v9880, v9879, v9886, v9884, v9882, v2750, v9883, v9885, v9899, v9888, v9894, v9891, v9890, v9889, v9893, v9892, v9898, v9896, v9895, v9897, v9912, v9901, v9907, v9904, v9903, v9902, v9906, v9905, v9911, v9909, v9908, v9910, v9951, v9938, v9925, v9914, v9920, v9917, v9916, v9915, v9919, v9918, v9924, v9922, v9921, v9923, v9937, v9926, v9932, v9929, v9928, v9927, v9931, v9930, v9936, v9934, v9933, v9935, v9950, v9939, v9945, v9942, v9941, v9940, v9944, v9943, v9949, v9947, v9946, v9948, v10029, v9990, v9977, v9964, v9953, v9959, v9956, v9955, v9954, v9958, v9957, v9963, v9961, v9960, v9962, v9976, v9965, v9971, v9968, v9967, v9966, v9970, v9969, v9975, v9973, v9972, v9974, v9989, v9978, v9984, v9981, v9980, v9979, v9983, v9982, v9988, v9986, v9985, v9987, v10028, v10015, v10002, v9991, v9997, v9994, v9993, v9992, v9996, v9995, v10001, v9999, v9998, v10000, v10014, v10003, v10009, v10006, v10005, v10004, v10008, v10007, v10013, v10011, v10010, v10012, v10027, v10016, v10022, v10019, v10018, v10017, v10021, v10020, v10026, v10024, v10023, v10025, v10038, v24, v26190, normal, unitOverride, opOverride, hv26389, hv26394, format]
  exact illegal
#print axioms idu_shift_0_sll_legal

theorem idu_shift_0_srl_legal (s : State) (i : Inputs)
    (normal : v26384 s i = 0) (matched : IsShiftImmediate .srl (v26210 s i)) :
    v26905 s i = 0 := by
  change v26210 s i &&& BitVec.ofNat 64 4227887231 = BitVec.ofNat 64 20499 at matched
  have unitOverride : v28077 s i = 0 := normal
  have opOverride : v28454 s i = 0 := normal
  have hv26389 : v26389 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 20499) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26386, v26388, v26387] using (show v26389 s i = 0 by unfold v26389; exact if_neg miss)
  have hv26394 : v26394 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 20499) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26391, v26393, v26392] using (show v26394 s i = 0 by unfold v26394; exact if_neg miss)
  have hv26399 : v26399 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 20499) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26396, v26398, v26397] using (show v26399 s i = 0 by unfold v26399; exact if_neg miss)
  have hv26404 : v26404 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 20499) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26401, v26403, v26402] using (show v26404 s i = 0 by unfold v26404; exact if_neg miss)
  have hv26409 : v26409 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 20499) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26406, v26408, v26407] using (show v26409 s i = 0 by unfold v26409; exact if_neg miss)
  have hv26414 : v26414 s i = 1 := by
    simp [v26414, v26411, v26413, v26412, matched]
  have format : v26897 s i = 4 := by
    simp [v26897, v26385, v26896, v26895, v26894, v26893, v26892, v26891, v26415, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414]
  have illegal : v26905 s i = 0 := by
    simp [v26905, v26904, v26903, v26902, v26901, v26899, v26898, v26900, v26380, v26379, v10036, v10035, v10034, v10033, v10032, v10031, v9859, v9834, v9858, v9846, v9840, v9838, v9836, v9835, v9837, v9839, v9845, v9843, v9841, v9842, v9844, v9857, v9851, v9849, v9847, v9848, v9850, v9856, v9854, v9852, v9853, v9855, v10030, v9952, v9913, v9900, v9887, v9874, v9873, v9872, v9860, v9871, v9865, v9862, v9861, v9864, v9863, v9870, v9867, v9866, v9869, v9868, v9881, v9878, v9876, v9875, v9877, v9880, v9879, v9886, v9884, v9882, v2750, v9883, v9885, v9899, v9888, v9894, v9891, v9890, v9889, v9893, v9892, v9898, v9896, v9895, v9897, v9912, v9901, v9907, v9904, v9903, v9902, v9906, v9905, v9911, v9909, v9908, v9910, v9951, v9938, v9925, v9914, v9920, v9917, v9916, v9915, v9919, v9918, v9924, v9922, v9921, v9923, v9937, v9926, v9932, v9929, v9928, v9927, v9931, v9930, v9936, v9934, v9933, v9935, v9950, v9939, v9945, v9942, v9941, v9940, v9944, v9943, v9949, v9947, v9946, v9948, v10029, v9990, v9977, v9964, v9953, v9959, v9956, v9955, v9954, v9958, v9957, v9963, v9961, v9960, v9962, v9976, v9965, v9971, v9968, v9967, v9966, v9970, v9969, v9975, v9973, v9972, v9974, v9989, v9978, v9984, v9981, v9980, v9979, v9983, v9982, v9988, v9986, v9985, v9987, v10028, v10015, v10002, v9991, v9997, v9994, v9993, v9992, v9996, v9995, v10001, v9999, v9998, v10000, v10014, v10003, v10009, v10006, v10005, v10004, v10008, v10007, v10013, v10011, v10010, v10012, v10027, v10016, v10022, v10019, v10018, v10017, v10021, v10020, v10026, v10024, v10023, v10025, v10038, v24, v26190, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, format]
  exact illegal
#print axioms idu_shift_0_srl_legal

theorem idu_shift_0_sra_legal (s : State) (i : Inputs)
    (normal : v26384 s i = 0) (matched : IsShiftImmediate .sra (v26210 s i)) :
    v26905 s i = 0 := by
  change v26210 s i &&& BitVec.ofNat 64 4227887231 = BitVec.ofNat 64 1073762323 at matched
  have unitOverride : v28077 s i = 0 := normal
  have opOverride : v28454 s i = 0 := normal
  have hv26389 : v26389 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 1073762323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26386, v26388, v26387] using (show v26389 s i = 0 by unfold v26389; exact if_neg miss)
  have hv26394 : v26394 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 1073762323) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26391, v26393, v26392] using (show v26394 s i = 0 by unfold v26394; exact if_neg miss)
  have hv26399 : v26399 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 1073762323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26396, v26398, v26397] using (show v26399 s i = 0 by unfold v26399; exact if_neg miss)
  have hv26404 : v26404 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 1073762323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26401, v26403, v26402] using (show v26404 s i = 0 by unfold v26404; exact if_neg miss)
  have hv26409 : v26409 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 1073762323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26406, v26408, v26407] using (show v26409 s i = 0 by unfold v26409; exact if_neg miss)
  have hv26414 : v26414 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 1073762323) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26411, v26413, v26412] using (show v26414 s i = 0 by unfold v26414; exact if_neg miss)
  have hv26419 : v26419 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 1073762323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26416, v26418, v26417] using (show v26419 s i = 0 by unfold v26419; exact if_neg miss)
  have hv26424 : v26424 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 1073762323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26421, v26423, v26422] using (show v26424 s i = 0 by unfold v26424; exact if_neg miss)
  have hv26429 : v26429 s i = 1 := by
    simp [v26429, v26426, v26428, v26427, matched]
  have format : v26897 s i = 4 := by
    simp [v26897, v26385, v26896, v26895, v26894, v26893, v26892, v26891, v26890, v26889, v26888, v26430, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429]
  have illegal : v26905 s i = 0 := by
    simp [v26905, v26904, v26903, v26902, v26901, v26899, v26898, v26900, v26380, v26379, v10036, v10035, v10034, v10033, v10032, v10031, v9859, v9834, v9858, v9846, v9840, v9838, v9836, v9835, v9837, v9839, v9845, v9843, v9841, v9842, v9844, v9857, v9851, v9849, v9847, v9848, v9850, v9856, v9854, v9852, v9853, v9855, v10030, v9952, v9913, v9900, v9887, v9874, v9873, v9872, v9860, v9871, v9865, v9862, v9861, v9864, v9863, v9870, v9867, v9866, v9869, v9868, v9881, v9878, v9876, v9875, v9877, v9880, v9879, v9886, v9884, v9882, v2750, v9883, v9885, v9899, v9888, v9894, v9891, v9890, v9889, v9893, v9892, v9898, v9896, v9895, v9897, v9912, v9901, v9907, v9904, v9903, v9902, v9906, v9905, v9911, v9909, v9908, v9910, v9951, v9938, v9925, v9914, v9920, v9917, v9916, v9915, v9919, v9918, v9924, v9922, v9921, v9923, v9937, v9926, v9932, v9929, v9928, v9927, v9931, v9930, v9936, v9934, v9933, v9935, v9950, v9939, v9945, v9942, v9941, v9940, v9944, v9943, v9949, v9947, v9946, v9948, v10029, v9990, v9977, v9964, v9953, v9959, v9956, v9955, v9954, v9958, v9957, v9963, v9961, v9960, v9962, v9976, v9965, v9971, v9968, v9967, v9966, v9970, v9969, v9975, v9973, v9972, v9974, v9989, v9978, v9984, v9981, v9980, v9979, v9983, v9982, v9988, v9986, v9985, v9987, v10028, v10015, v10002, v9991, v9997, v9994, v9993, v9992, v9996, v9995, v10001, v9999, v9998, v10000, v10014, v10003, v10009, v10006, v10005, v10004, v10008, v10007, v10013, v10011, v10010, v10012, v10027, v10016, v10022, v10019, v10018, v10017, v10021, v10020, v10026, v10024, v10023, v10025, v10038, v24, v26190, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, format]
  exact illegal
#print axioms idu_shift_0_sra_legal

theorem idu_shift_1_sll_legal (s : State) (i : Inputs)
    (normal : v26911 s i = 0) (matched : IsShiftImmediate .sll (v26223 s i)) :
    v27432 s i = 0 := by
  change v26223 s i &&& BitVec.ofNat 64 4227887231 = BitVec.ofNat 64 4115 at matched
  have unitOverride : v28261 s i = 0 := normal
  have opOverride : v28649 s i = 0 := normal
  have hv26916 : v26916 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 4115) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26913, v26915, v26914] using (show v26916 s i = 0 by unfold v26916; exact if_neg miss)
  have hv26921 : v26921 s i = 1 := by
    simp [v26921, v26918, v26920, v26919, matched]
  have format : v27424 s i = 4 := by
    simp [v27424, v26912, v27423, v27422, v26922, normal, unitOverride, opOverride, hv26916, hv26921]
  have illegal : v27432 s i = 0 := by
    simp [v27432, v27431, v27430, v27429, v27428, v27426, v27425, v27427, v10039, v10037, v10036, v10035, v10034, v10033, v10032, v10031, v9859, v9834, v9858, v9846, v9840, v9838, v9836, v9835, v9837, v9839, v9845, v9843, v9841, v9842, v9844, v9857, v9851, v9849, v9847, v9848, v9850, v9856, v9854, v9852, v9853, v9855, v10030, v9952, v9913, v9900, v9887, v9874, v9873, v9872, v9860, v9871, v9865, v9862, v9861, v9864, v9863, v9870, v9867, v9866, v9869, v9868, v9881, v9878, v9876, v9875, v9877, v9880, v9879, v9886, v9884, v9882, v2750, v9883, v9885, v9899, v9888, v9894, v9891, v9890, v9889, v9893, v9892, v9898, v9896, v9895, v9897, v9912, v9901, v9907, v9904, v9903, v9902, v9906, v9905, v9911, v9909, v9908, v9910, v9951, v9938, v9925, v9914, v9920, v9917, v9916, v9915, v9919, v9918, v9924, v9922, v9921, v9923, v9937, v9926, v9932, v9929, v9928, v9927, v9931, v9930, v9936, v9934, v9933, v9935, v9950, v9939, v9945, v9942, v9941, v9940, v9944, v9943, v9949, v9947, v9946, v9948, v10029, v9990, v9977, v9964, v9953, v9959, v9956, v9955, v9954, v9958, v9957, v9963, v9961, v9960, v9962, v9976, v9965, v9971, v9968, v9967, v9966, v9970, v9969, v9975, v9973, v9972, v9974, v9989, v9978, v9984, v9981, v9980, v9979, v9983, v9982, v9988, v9986, v9985, v9987, v10028, v10015, v10002, v9991, v9997, v9994, v9993, v9992, v9996, v9995, v10001, v9999, v9998, v10000, v10014, v10003, v10009, v10006, v10005, v10004, v10008, v10007, v10013, v10011, v10010, v10012, v10027, v10016, v10022, v10019, v10018, v10017, v10021, v10020, v10026, v10024, v10023, v10025, v10038, v24, v9812, v9811, normal, unitOverride, opOverride, hv26916, hv26921, format]
  exact illegal
#print axioms idu_shift_1_sll_legal

theorem idu_shift_1_srl_legal (s : State) (i : Inputs)
    (normal : v26911 s i = 0) (matched : IsShiftImmediate .srl (v26223 s i)) :
    v27432 s i = 0 := by
  change v26223 s i &&& BitVec.ofNat 64 4227887231 = BitVec.ofNat 64 20499 at matched
  have unitOverride : v28261 s i = 0 := normal
  have opOverride : v28649 s i = 0 := normal
  have hv26916 : v26916 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 20499) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26913, v26915, v26914] using (show v26916 s i = 0 by unfold v26916; exact if_neg miss)
  have hv26921 : v26921 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 20499) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26918, v26920, v26919] using (show v26921 s i = 0 by unfold v26921; exact if_neg miss)
  have hv26926 : v26926 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 20499) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26923, v26925, v26924] using (show v26926 s i = 0 by unfold v26926; exact if_neg miss)
  have hv26931 : v26931 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 20499) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26928, v26930, v26929] using (show v26931 s i = 0 by unfold v26931; exact if_neg miss)
  have hv26936 : v26936 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 20499) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26933, v26935, v26934] using (show v26936 s i = 0 by unfold v26936; exact if_neg miss)
  have hv26941 : v26941 s i = 1 := by
    simp [v26941, v26938, v26940, v26939, matched]
  have format : v27424 s i = 4 := by
    simp [v27424, v26912, v27423, v27422, v27421, v27420, v27419, v27418, v26942, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941]
  have illegal : v27432 s i = 0 := by
    simp [v27432, v27431, v27430, v27429, v27428, v27426, v27425, v27427, v10039, v10037, v10036, v10035, v10034, v10033, v10032, v10031, v9859, v9834, v9858, v9846, v9840, v9838, v9836, v9835, v9837, v9839, v9845, v9843, v9841, v9842, v9844, v9857, v9851, v9849, v9847, v9848, v9850, v9856, v9854, v9852, v9853, v9855, v10030, v9952, v9913, v9900, v9887, v9874, v9873, v9872, v9860, v9871, v9865, v9862, v9861, v9864, v9863, v9870, v9867, v9866, v9869, v9868, v9881, v9878, v9876, v9875, v9877, v9880, v9879, v9886, v9884, v9882, v2750, v9883, v9885, v9899, v9888, v9894, v9891, v9890, v9889, v9893, v9892, v9898, v9896, v9895, v9897, v9912, v9901, v9907, v9904, v9903, v9902, v9906, v9905, v9911, v9909, v9908, v9910, v9951, v9938, v9925, v9914, v9920, v9917, v9916, v9915, v9919, v9918, v9924, v9922, v9921, v9923, v9937, v9926, v9932, v9929, v9928, v9927, v9931, v9930, v9936, v9934, v9933, v9935, v9950, v9939, v9945, v9942, v9941, v9940, v9944, v9943, v9949, v9947, v9946, v9948, v10029, v9990, v9977, v9964, v9953, v9959, v9956, v9955, v9954, v9958, v9957, v9963, v9961, v9960, v9962, v9976, v9965, v9971, v9968, v9967, v9966, v9970, v9969, v9975, v9973, v9972, v9974, v9989, v9978, v9984, v9981, v9980, v9979, v9983, v9982, v9988, v9986, v9985, v9987, v10028, v10015, v10002, v9991, v9997, v9994, v9993, v9992, v9996, v9995, v10001, v9999, v9998, v10000, v10014, v10003, v10009, v10006, v10005, v10004, v10008, v10007, v10013, v10011, v10010, v10012, v10027, v10016, v10022, v10019, v10018, v10017, v10021, v10020, v10026, v10024, v10023, v10025, v10038, v24, v9812, v9811, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, format]
  exact illegal
#print axioms idu_shift_1_srl_legal

theorem idu_shift_1_sra_legal (s : State) (i : Inputs)
    (normal : v26911 s i = 0) (matched : IsShiftImmediate .sra (v26223 s i)) :
    v27432 s i = 0 := by
  change v26223 s i &&& BitVec.ofNat 64 4227887231 = BitVec.ofNat 64 1073762323 at matched
  have unitOverride : v28261 s i = 0 := normal
  have opOverride : v28649 s i = 0 := normal
  have hv26916 : v26916 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 1073762323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26913, v26915, v26914] using (show v26916 s i = 0 by unfold v26916; exact if_neg miss)
  have hv26921 : v26921 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 1073762323) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26918, v26920, v26919] using (show v26921 s i = 0 by unfold v26921; exact if_neg miss)
  have hv26926 : v26926 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 1073762323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26923, v26925, v26924] using (show v26926 s i = 0 by unfold v26926; exact if_neg miss)
  have hv26931 : v26931 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 1073762323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26928, v26930, v26929] using (show v26931 s i = 0 by unfold v26931; exact if_neg miss)
  have hv26936 : v26936 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 1073762323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26933, v26935, v26934] using (show v26936 s i = 0 by unfold v26936; exact if_neg miss)
  have hv26941 : v26941 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 1073762323) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26938, v26940, v26939] using (show v26941 s i = 0 by unfold v26941; exact if_neg miss)
  have hv26946 : v26946 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 1073762323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26943, v26945, v26944] using (show v26946 s i = 0 by unfold v26946; exact if_neg miss)
  have hv26951 : v26951 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4227887231)
      (BitVec.ofNat 64 1073762323) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26948, v26950, v26949] using (show v26951 s i = 0 by unfold v26951; exact if_neg miss)
  have hv26956 : v26956 s i = 1 := by
    simp [v26956, v26953, v26955, v26954, matched]
  have format : v27424 s i = 4 := by
    simp [v27424, v26912, v27423, v27422, v27421, v27420, v27419, v27418, v27417, v27416, v27415, v26957, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956]
  have illegal : v27432 s i = 0 := by
    simp [v27432, v27431, v27430, v27429, v27428, v27426, v27425, v27427, v10039, v10037, v10036, v10035, v10034, v10033, v10032, v10031, v9859, v9834, v9858, v9846, v9840, v9838, v9836, v9835, v9837, v9839, v9845, v9843, v9841, v9842, v9844, v9857, v9851, v9849, v9847, v9848, v9850, v9856, v9854, v9852, v9853, v9855, v10030, v9952, v9913, v9900, v9887, v9874, v9873, v9872, v9860, v9871, v9865, v9862, v9861, v9864, v9863, v9870, v9867, v9866, v9869, v9868, v9881, v9878, v9876, v9875, v9877, v9880, v9879, v9886, v9884, v9882, v2750, v9883, v9885, v9899, v9888, v9894, v9891, v9890, v9889, v9893, v9892, v9898, v9896, v9895, v9897, v9912, v9901, v9907, v9904, v9903, v9902, v9906, v9905, v9911, v9909, v9908, v9910, v9951, v9938, v9925, v9914, v9920, v9917, v9916, v9915, v9919, v9918, v9924, v9922, v9921, v9923, v9937, v9926, v9932, v9929, v9928, v9927, v9931, v9930, v9936, v9934, v9933, v9935, v9950, v9939, v9945, v9942, v9941, v9940, v9944, v9943, v9949, v9947, v9946, v9948, v10029, v9990, v9977, v9964, v9953, v9959, v9956, v9955, v9954, v9958, v9957, v9963, v9961, v9960, v9962, v9976, v9965, v9971, v9968, v9967, v9966, v9970, v9969, v9975, v9973, v9972, v9974, v9989, v9978, v9984, v9981, v9980, v9979, v9983, v9982, v9988, v9986, v9985, v9987, v10028, v10015, v10002, v9991, v9997, v9994, v9993, v9992, v9996, v9995, v10001, v9999, v9998, v10000, v10014, v10003, v10009, v10006, v10005, v10004, v10008, v10007, v10013, v10011, v10010, v10012, v10027, v10016, v10022, v10019, v10018, v10017, v10021, v10020, v10026, v10024, v10023, v10025, v10038, v24, v9812, v9811, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, format]
  exact illegal
#print axioms idu_shift_1_sra_legal

end NutShellProofs

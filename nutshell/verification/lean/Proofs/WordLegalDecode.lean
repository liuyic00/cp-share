import Proofs.WordDecode
namespace NutShellProofs
open nNutCore
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
theorem idu_word_0_add_legal (s : State) (i : Inputs)
    (normal : v26384 s i = 0) (matched : IsWordImmediate .add (v26210 s i)) :
    v26905 s i = 0 := by
  change v26210 s i &&& BitVec.ofNat 64 28799 = BitVec.ofNat 64 27 at matched
  have unitOverride : v28077 s i = 0 := normal
  have opOverride : v28454 s i = 0 := normal
  have hv26389 : v26389 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26386, v26388, v26387] using (show v26389 s i = 0 by unfold v26389; exact if_neg miss)
  have hv26394 : v26394 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26391, v26393, v26392] using (show v26394 s i = 0 by unfold v26394; exact if_neg miss)
  have hv26399 : v26399 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26396, v26398, v26397] using (show v26399 s i = 0 by unfold v26399; exact if_neg miss)
  have hv26404 : v26404 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26401, v26403, v26402] using (show v26404 s i = 0 by unfold v26404; exact if_neg miss)
  have hv26409 : v26409 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26406, v26408, v26407] using (show v26409 s i = 0 by unfold v26409; exact if_neg miss)
  have hv26414 : v26414 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26411, v26413, v26412] using (show v26414 s i = 0 by unfold v26414; exact if_neg miss)
  have hv26419 : v26419 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26416, v26418, v26417] using (show v26419 s i = 0 by unfold v26419; exact if_neg miss)
  have hv26424 : v26424 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26421, v26423, v26422] using (show v26424 s i = 0 by unfold v26424; exact if_neg miss)
  have hv26429 : v26429 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 1073762323) (by decide) matched
    simpa only [v26426, v26428, v26427] using (show v26429 s i = 0 by unfold v26429; exact if_neg miss)
  have hv26434 : v26434 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 51) (by decide) matched
    simpa only [v26431, v26433, v26432] using (show v26434 s i = 0 by unfold v26434; exact if_neg miss)
  have hv26439 : v26439 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4147) (by decide) matched
    simpa only [v26436, v26438, v26437] using (show v26439 s i = 0 by unfold v26439; exact if_neg miss)
  have hv26444 : v26444 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 8243) (by decide) matched
    simpa only [v26441, v26443, v26442] using (show v26444 s i = 0 by unfold v26444; exact if_neg miss)
  have hv26449 : v26449 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 12339) (by decide) matched
    simpa only [v26446, v26448, v26447] using (show v26449 s i = 0 by unfold v26449; exact if_neg miss)
  have hv26454 : v26454 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 16435) (by decide) matched
    simpa only [v26451, v26453, v26452] using (show v26454 s i = 0 by unfold v26454; exact if_neg miss)
  have hv26459 : v26459 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 20531) (by decide) matched
    simpa only [v26456, v26458, v26457] using (show v26459 s i = 0 by unfold v26459; exact if_neg miss)
  have hv26464 : v26464 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 24627) (by decide) matched
    simpa only [v26461, v26463, v26462] using (show v26464 s i = 0 by unfold v26464; exact if_neg miss)
  have hv26469 : v26469 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 28723) (by decide) matched
    simpa only [v26466, v26468, v26467] using (show v26469 s i = 0 by unfold v26469; exact if_neg miss)
  have hv26474 : v26474 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073741875) (by decide) matched
    simpa only [v26471, v26473, v26472] using (show v26474 s i = 0 by unfold v26474; exact if_neg miss)
  have hv26479 : v26479 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073762355) (by decide) matched
    simpa only [v26476, v26478, v26477] using (show v26479 s i = 0 by unfold v26479; exact if_neg miss)
  have hv26484 : v26484 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 127) (BitVec.ofNat 64 23) (by decide) matched
    simpa only [v26481, v26483, v26482] using (show v26484 s i = 0 by unfold v26484; exact if_neg miss)
  have hv26489 : v26489 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 127) (BitVec.ofNat 64 55) (by decide) matched
    simpa only [v26486, v26488, v26487] using (show v26489 s i = 0 by unfold v26489; exact if_neg miss)
  have hv26494 : v26494 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 127) (BitVec.ofNat 64 111) (by decide) matched
    simpa only [v26491, v26493, v26492] using (show v26494 s i = 0 by unfold v26494; exact if_neg miss)
  have hv26499 : v26499 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 103) (by decide) matched
    simpa only [v26496, v26498, v26497] using (show v26499 s i = 0 by unfold v26499; exact if_neg miss)
  have hv26504 : v26504 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 99) (by decide) matched
    simpa only [v26501, v26503, v26502] using (show v26504 s i = 0 by unfold v26504; exact if_neg miss)
  have hv26509 : v26509 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4195) (by decide) matched
    simpa only [v26506, v26508, v26507] using (show v26509 s i = 0 by unfold v26509; exact if_neg miss)
  have hv26514 : v26514 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16483) (by decide) matched
    simpa only [v26511, v26513, v26512] using (show v26514 s i = 0 by unfold v26514; exact if_neg miss)
  have hv26519 : v26519 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 20579) (by decide) matched
    simpa only [v26516, v26518, v26517] using (show v26519 s i = 0 by unfold v26519; exact if_neg miss)
  have hv26524 : v26524 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24675) (by decide) matched
    simpa only [v26521, v26523, v26522] using (show v26524 s i = 0 by unfold v26524; exact if_neg miss)
  have hv26529 : v26529 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28771) (by decide) matched
    simpa only [v26526, v26528, v26527] using (show v26529 s i = 0 by unfold v26529; exact if_neg miss)
  have hv26534 : v26534 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 3) (by decide) matched
    simpa only [v26531, v26533, v26532] using (show v26534 s i = 0 by unfold v26534; exact if_neg miss)
  have hv26539 : v26539 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4099) (by decide) matched
    simpa only [v26536, v26538, v26537] using (show v26539 s i = 0 by unfold v26539; exact if_neg miss)
  have hv26544 : v26544 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8195) (by decide) matched
    simpa only [v26541, v26543, v26542] using (show v26544 s i = 0 by unfold v26544; exact if_neg miss)
  have hv26549 : v26549 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16387) (by decide) matched
    simpa only [v26546, v26548, v26547] using (show v26549 s i = 0 by unfold v26549; exact if_neg miss)
  have hv26554 : v26554 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 20483) (by decide) matched
    simpa only [v26551, v26553, v26552] using (show v26554 s i = 0 by unfold v26554; exact if_neg miss)
  have hv26559 : v26559 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 35) (by decide) matched
    simpa only [v26556, v26558, v26557] using (show v26559 s i = 0 by unfold v26559; exact if_neg miss)
  have hv26564 : v26564 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4131) (by decide) matched
    simpa only [v26561, v26563, v26562] using (show v26564 s i = 0 by unfold v26564; exact if_neg miss)
  have hv26569 : v26569 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8227) (by decide) matched
    simpa only [v26566, v26568, v26567] using (show v26569 s i = 0 by unfold v26569; exact if_neg miss)
  have hv26574 : v26574 s i = 1 := by
    simp [v26574, v26571, v26573, v26572, matched]
  have format : v26897 s i = 4 := by
    simp [v26897, v26385, v26896, v26895, v26894, v26893, v26892, v26891, v26890, v26889, v26888, v26887, v26886, v26885, v26884, v26883, v26882, v26881, v26880, v26879, v26878, v26877, v26876, v26875, v26874, v26873, v26872, v26871, v26870, v26869, v26868, v26867, v26866, v26865, v26864, v26863, v26862, v26861, v26860, v26859, v26575, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, hv26554, hv26559, hv26564, hv26569, hv26574]
  have illegal : v26905 s i = 0 := by
    simp [v26905, v26904, v26903, v26902, v26901, v26899, v26898, v26900, v26380, v26379, v10036, v10035, v10034, v10033, v10032, v10031, v9859, v9834, v9858, v9846, v9840, v9838, v9836, v9835, v9837, v9839, v9845, v9843, v9841, v9842, v9844, v9857, v9851, v9849, v9847, v9848, v9850, v9856, v9854, v9852, v9853, v9855, v10030, v9952, v9913, v9900, v9887, v9874, v9873, v9872, v9860, v9871, v9865, v9862, v9861, v9864, v9863, v9870, v9867, v9866, v9869, v9868, v9881, v9878, v9876, v9875, v9877, v9880, v9879, v9886, v9884, v9882, v2750, v9883, v9885, v9899, v9888, v9894, v9891, v9890, v9889, v9893, v9892, v9898, v9896, v9895, v9897, v9912, v9901, v9907, v9904, v9903, v9902, v9906, v9905, v9911, v9909, v9908, v9910, v9951, v9938, v9925, v9914, v9920, v9917, v9916, v9915, v9919, v9918, v9924, v9922, v9921, v9923, v9937, v9926, v9932, v9929, v9928, v9927, v9931, v9930, v9936, v9934, v9933, v9935, v9950, v9939, v9945, v9942, v9941, v9940, v9944, v9943, v9949, v9947, v9946, v9948, v10029, v9990, v9977, v9964, v9953, v9959, v9956, v9955, v9954, v9958, v9957, v9963, v9961, v9960, v9962, v9976, v9965, v9971, v9968, v9967, v9966, v9970, v9969, v9975, v9973, v9972, v9974, v9989, v9978, v9984, v9981, v9980, v9979, v9983, v9982, v9988, v9986, v9985, v9987, v10028, v10015, v10002, v9991, v9997, v9994, v9993, v9992, v9996, v9995, v10001, v9999, v9998, v10000, v10014, v10003, v10009, v10006, v10005, v10004, v10008, v10007, v10013, v10011, v10010, v10012, v10027, v10016, v10022, v10019, v10018, v10017, v10021, v10020, v10026, v10024, v10023, v10025, v10038, v24, v26190, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, hv26554, hv26559, hv26564, hv26569, hv26574, format]
  exact illegal
#print axioms idu_word_0_add_legal

theorem idu_word_0_sll_legal (s : State) (i : Inputs)
    (normal : v26384 s i = 0) (matched : IsWordImmediate .sll (v26210 s i)) :
    v26905 s i = 0 := by
  change v26210 s i &&& BitVec.ofNat 64 4261441663 = BitVec.ofNat 64 4123 at matched
  have unitOverride : v28077 s i = 0 := normal
  have opOverride : v28454 s i = 0 := normal
  have hv26389 : v26389 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26386, v26388, v26387] using (show v26389 s i = 0 by unfold v26389; exact if_neg miss)
  have hv26394 : v26394 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26391, v26393, v26392] using (show v26394 s i = 0 by unfold v26394; exact if_neg miss)
  have hv26399 : v26399 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26396, v26398, v26397] using (show v26399 s i = 0 by unfold v26399; exact if_neg miss)
  have hv26404 : v26404 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26401, v26403, v26402] using (show v26404 s i = 0 by unfold v26404; exact if_neg miss)
  have hv26409 : v26409 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26406, v26408, v26407] using (show v26409 s i = 0 by unfold v26409; exact if_neg miss)
  have hv26414 : v26414 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26411, v26413, v26412] using (show v26414 s i = 0 by unfold v26414; exact if_neg miss)
  have hv26419 : v26419 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26416, v26418, v26417] using (show v26419 s i = 0 by unfold v26419; exact if_neg miss)
  have hv26424 : v26424 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26421, v26423, v26422] using (show v26424 s i = 0 by unfold v26424; exact if_neg miss)
  have hv26429 : v26429 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 1073762323) (by decide) matched
    simpa only [v26426, v26428, v26427] using (show v26429 s i = 0 by unfold v26429; exact if_neg miss)
  have hv26434 : v26434 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 51) (by decide) matched
    simpa only [v26431, v26433, v26432] using (show v26434 s i = 0 by unfold v26434; exact if_neg miss)
  have hv26439 : v26439 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4147) (by decide) matched
    simpa only [v26436, v26438, v26437] using (show v26439 s i = 0 by unfold v26439; exact if_neg miss)
  have hv26444 : v26444 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 8243) (by decide) matched
    simpa only [v26441, v26443, v26442] using (show v26444 s i = 0 by unfold v26444; exact if_neg miss)
  have hv26449 : v26449 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 12339) (by decide) matched
    simpa only [v26446, v26448, v26447] using (show v26449 s i = 0 by unfold v26449; exact if_neg miss)
  have hv26454 : v26454 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 16435) (by decide) matched
    simpa only [v26451, v26453, v26452] using (show v26454 s i = 0 by unfold v26454; exact if_neg miss)
  have hv26459 : v26459 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 20531) (by decide) matched
    simpa only [v26456, v26458, v26457] using (show v26459 s i = 0 by unfold v26459; exact if_neg miss)
  have hv26464 : v26464 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 24627) (by decide) matched
    simpa only [v26461, v26463, v26462] using (show v26464 s i = 0 by unfold v26464; exact if_neg miss)
  have hv26469 : v26469 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 28723) (by decide) matched
    simpa only [v26466, v26468, v26467] using (show v26469 s i = 0 by unfold v26469; exact if_neg miss)
  have hv26474 : v26474 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073741875) (by decide) matched
    simpa only [v26471, v26473, v26472] using (show v26474 s i = 0 by unfold v26474; exact if_neg miss)
  have hv26479 : v26479 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073762355) (by decide) matched
    simpa only [v26476, v26478, v26477] using (show v26479 s i = 0 by unfold v26479; exact if_neg miss)
  have hv26484 : v26484 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 127) (BitVec.ofNat 64 23) (by decide) matched
    simpa only [v26481, v26483, v26482] using (show v26484 s i = 0 by unfold v26484; exact if_neg miss)
  have hv26489 : v26489 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 127) (BitVec.ofNat 64 55) (by decide) matched
    simpa only [v26486, v26488, v26487] using (show v26489 s i = 0 by unfold v26489; exact if_neg miss)
  have hv26494 : v26494 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 127) (BitVec.ofNat 64 111) (by decide) matched
    simpa only [v26491, v26493, v26492] using (show v26494 s i = 0 by unfold v26494; exact if_neg miss)
  have hv26499 : v26499 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 103) (by decide) matched
    simpa only [v26496, v26498, v26497] using (show v26499 s i = 0 by unfold v26499; exact if_neg miss)
  have hv26504 : v26504 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 99) (by decide) matched
    simpa only [v26501, v26503, v26502] using (show v26504 s i = 0 by unfold v26504; exact if_neg miss)
  have hv26509 : v26509 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4195) (by decide) matched
    simpa only [v26506, v26508, v26507] using (show v26509 s i = 0 by unfold v26509; exact if_neg miss)
  have hv26514 : v26514 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16483) (by decide) matched
    simpa only [v26511, v26513, v26512] using (show v26514 s i = 0 by unfold v26514; exact if_neg miss)
  have hv26519 : v26519 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 20579) (by decide) matched
    simpa only [v26516, v26518, v26517] using (show v26519 s i = 0 by unfold v26519; exact if_neg miss)
  have hv26524 : v26524 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24675) (by decide) matched
    simpa only [v26521, v26523, v26522] using (show v26524 s i = 0 by unfold v26524; exact if_neg miss)
  have hv26529 : v26529 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28771) (by decide) matched
    simpa only [v26526, v26528, v26527] using (show v26529 s i = 0 by unfold v26529; exact if_neg miss)
  have hv26534 : v26534 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 3) (by decide) matched
    simpa only [v26531, v26533, v26532] using (show v26534 s i = 0 by unfold v26534; exact if_neg miss)
  have hv26539 : v26539 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4099) (by decide) matched
    simpa only [v26536, v26538, v26537] using (show v26539 s i = 0 by unfold v26539; exact if_neg miss)
  have hv26544 : v26544 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8195) (by decide) matched
    simpa only [v26541, v26543, v26542] using (show v26544 s i = 0 by unfold v26544; exact if_neg miss)
  have hv26549 : v26549 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16387) (by decide) matched
    simpa only [v26546, v26548, v26547] using (show v26549 s i = 0 by unfold v26549; exact if_neg miss)
  have hv26554 : v26554 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 20483) (by decide) matched
    simpa only [v26551, v26553, v26552] using (show v26554 s i = 0 by unfold v26554; exact if_neg miss)
  have hv26559 : v26559 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 35) (by decide) matched
    simpa only [v26556, v26558, v26557] using (show v26559 s i = 0 by unfold v26559; exact if_neg miss)
  have hv26564 : v26564 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4131) (by decide) matched
    simpa only [v26561, v26563, v26562] using (show v26564 s i = 0 by unfold v26564; exact if_neg miss)
  have hv26569 : v26569 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8227) (by decide) matched
    simpa only [v26566, v26568, v26567] using (show v26569 s i = 0 by unfold v26569; exact if_neg miss)
  have hv26574 : v26574 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 27) (by decide) matched
    simpa only [v26571, v26573, v26572] using (show v26574 s i = 0 by unfold v26574; exact if_neg miss)
  have hv26579 : v26579 s i = 1 := by
    simp [v26579, v26576, v26578, v26577, matched]
  have format : v26897 s i = 4 := by
    simp [v26897, v26385, v26896, v26895, v26894, v26893, v26892, v26891, v26890, v26889, v26888, v26887, v26886, v26885, v26884, v26883, v26882, v26881, v26880, v26879, v26878, v26877, v26876, v26875, v26874, v26873, v26872, v26871, v26870, v26869, v26868, v26867, v26866, v26865, v26864, v26863, v26862, v26861, v26860, v26859, v26858, v26580, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, hv26554, hv26559, hv26564, hv26569, hv26574, hv26579]
  have illegal : v26905 s i = 0 := by
    simp [v26905, v26904, v26903, v26902, v26901, v26899, v26898, v26900, v26380, v26379, v10036, v10035, v10034, v10033, v10032, v10031, v9859, v9834, v9858, v9846, v9840, v9838, v9836, v9835, v9837, v9839, v9845, v9843, v9841, v9842, v9844, v9857, v9851, v9849, v9847, v9848, v9850, v9856, v9854, v9852, v9853, v9855, v10030, v9952, v9913, v9900, v9887, v9874, v9873, v9872, v9860, v9871, v9865, v9862, v9861, v9864, v9863, v9870, v9867, v9866, v9869, v9868, v9881, v9878, v9876, v9875, v9877, v9880, v9879, v9886, v9884, v9882, v2750, v9883, v9885, v9899, v9888, v9894, v9891, v9890, v9889, v9893, v9892, v9898, v9896, v9895, v9897, v9912, v9901, v9907, v9904, v9903, v9902, v9906, v9905, v9911, v9909, v9908, v9910, v9951, v9938, v9925, v9914, v9920, v9917, v9916, v9915, v9919, v9918, v9924, v9922, v9921, v9923, v9937, v9926, v9932, v9929, v9928, v9927, v9931, v9930, v9936, v9934, v9933, v9935, v9950, v9939, v9945, v9942, v9941, v9940, v9944, v9943, v9949, v9947, v9946, v9948, v10029, v9990, v9977, v9964, v9953, v9959, v9956, v9955, v9954, v9958, v9957, v9963, v9961, v9960, v9962, v9976, v9965, v9971, v9968, v9967, v9966, v9970, v9969, v9975, v9973, v9972, v9974, v9989, v9978, v9984, v9981, v9980, v9979, v9983, v9982, v9988, v9986, v9985, v9987, v10028, v10015, v10002, v9991, v9997, v9994, v9993, v9992, v9996, v9995, v10001, v9999, v9998, v10000, v10014, v10003, v10009, v10006, v10005, v10004, v10008, v10007, v10013, v10011, v10010, v10012, v10027, v10016, v10022, v10019, v10018, v10017, v10021, v10020, v10026, v10024, v10023, v10025, v10038, v24, v26190, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, hv26554, hv26559, hv26564, hv26569, hv26574, hv26579, format]
  exact illegal
#print axioms idu_word_0_sll_legal

theorem idu_word_0_srl_legal (s : State) (i : Inputs)
    (normal : v26384 s i = 0) (matched : IsWordImmediate .srl (v26210 s i)) :
    v26905 s i = 0 := by
  change v26210 s i &&& BitVec.ofNat 64 4261441663 = BitVec.ofNat 64 20507 at matched
  have unitOverride : v28077 s i = 0 := normal
  have opOverride : v28454 s i = 0 := normal
  have hv26389 : v26389 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26386, v26388, v26387] using (show v26389 s i = 0 by unfold v26389; exact if_neg miss)
  have hv26394 : v26394 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26391, v26393, v26392] using (show v26394 s i = 0 by unfold v26394; exact if_neg miss)
  have hv26399 : v26399 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26396, v26398, v26397] using (show v26399 s i = 0 by unfold v26399; exact if_neg miss)
  have hv26404 : v26404 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26401, v26403, v26402] using (show v26404 s i = 0 by unfold v26404; exact if_neg miss)
  have hv26409 : v26409 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26406, v26408, v26407] using (show v26409 s i = 0 by unfold v26409; exact if_neg miss)
  have hv26414 : v26414 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26411, v26413, v26412] using (show v26414 s i = 0 by unfold v26414; exact if_neg miss)
  have hv26419 : v26419 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26416, v26418, v26417] using (show v26419 s i = 0 by unfold v26419; exact if_neg miss)
  have hv26424 : v26424 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26421, v26423, v26422] using (show v26424 s i = 0 by unfold v26424; exact if_neg miss)
  have hv26429 : v26429 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 1073762323) (by decide) matched
    simpa only [v26426, v26428, v26427] using (show v26429 s i = 0 by unfold v26429; exact if_neg miss)
  have hv26434 : v26434 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 51) (by decide) matched
    simpa only [v26431, v26433, v26432] using (show v26434 s i = 0 by unfold v26434; exact if_neg miss)
  have hv26439 : v26439 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4147) (by decide) matched
    simpa only [v26436, v26438, v26437] using (show v26439 s i = 0 by unfold v26439; exact if_neg miss)
  have hv26444 : v26444 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 8243) (by decide) matched
    simpa only [v26441, v26443, v26442] using (show v26444 s i = 0 by unfold v26444; exact if_neg miss)
  have hv26449 : v26449 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 12339) (by decide) matched
    simpa only [v26446, v26448, v26447] using (show v26449 s i = 0 by unfold v26449; exact if_neg miss)
  have hv26454 : v26454 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 16435) (by decide) matched
    simpa only [v26451, v26453, v26452] using (show v26454 s i = 0 by unfold v26454; exact if_neg miss)
  have hv26459 : v26459 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 20531) (by decide) matched
    simpa only [v26456, v26458, v26457] using (show v26459 s i = 0 by unfold v26459; exact if_neg miss)
  have hv26464 : v26464 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 24627) (by decide) matched
    simpa only [v26461, v26463, v26462] using (show v26464 s i = 0 by unfold v26464; exact if_neg miss)
  have hv26469 : v26469 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 28723) (by decide) matched
    simpa only [v26466, v26468, v26467] using (show v26469 s i = 0 by unfold v26469; exact if_neg miss)
  have hv26474 : v26474 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073741875) (by decide) matched
    simpa only [v26471, v26473, v26472] using (show v26474 s i = 0 by unfold v26474; exact if_neg miss)
  have hv26479 : v26479 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073762355) (by decide) matched
    simpa only [v26476, v26478, v26477] using (show v26479 s i = 0 by unfold v26479; exact if_neg miss)
  have hv26484 : v26484 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 127) (BitVec.ofNat 64 23) (by decide) matched
    simpa only [v26481, v26483, v26482] using (show v26484 s i = 0 by unfold v26484; exact if_neg miss)
  have hv26489 : v26489 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 127) (BitVec.ofNat 64 55) (by decide) matched
    simpa only [v26486, v26488, v26487] using (show v26489 s i = 0 by unfold v26489; exact if_neg miss)
  have hv26494 : v26494 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 127) (BitVec.ofNat 64 111) (by decide) matched
    simpa only [v26491, v26493, v26492] using (show v26494 s i = 0 by unfold v26494; exact if_neg miss)
  have hv26499 : v26499 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 103) (by decide) matched
    simpa only [v26496, v26498, v26497] using (show v26499 s i = 0 by unfold v26499; exact if_neg miss)
  have hv26504 : v26504 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 99) (by decide) matched
    simpa only [v26501, v26503, v26502] using (show v26504 s i = 0 by unfold v26504; exact if_neg miss)
  have hv26509 : v26509 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4195) (by decide) matched
    simpa only [v26506, v26508, v26507] using (show v26509 s i = 0 by unfold v26509; exact if_neg miss)
  have hv26514 : v26514 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16483) (by decide) matched
    simpa only [v26511, v26513, v26512] using (show v26514 s i = 0 by unfold v26514; exact if_neg miss)
  have hv26519 : v26519 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 20579) (by decide) matched
    simpa only [v26516, v26518, v26517] using (show v26519 s i = 0 by unfold v26519; exact if_neg miss)
  have hv26524 : v26524 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24675) (by decide) matched
    simpa only [v26521, v26523, v26522] using (show v26524 s i = 0 by unfold v26524; exact if_neg miss)
  have hv26529 : v26529 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28771) (by decide) matched
    simpa only [v26526, v26528, v26527] using (show v26529 s i = 0 by unfold v26529; exact if_neg miss)
  have hv26534 : v26534 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 3) (by decide) matched
    simpa only [v26531, v26533, v26532] using (show v26534 s i = 0 by unfold v26534; exact if_neg miss)
  have hv26539 : v26539 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4099) (by decide) matched
    simpa only [v26536, v26538, v26537] using (show v26539 s i = 0 by unfold v26539; exact if_neg miss)
  have hv26544 : v26544 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8195) (by decide) matched
    simpa only [v26541, v26543, v26542] using (show v26544 s i = 0 by unfold v26544; exact if_neg miss)
  have hv26549 : v26549 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16387) (by decide) matched
    simpa only [v26546, v26548, v26547] using (show v26549 s i = 0 by unfold v26549; exact if_neg miss)
  have hv26554 : v26554 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 20483) (by decide) matched
    simpa only [v26551, v26553, v26552] using (show v26554 s i = 0 by unfold v26554; exact if_neg miss)
  have hv26559 : v26559 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 35) (by decide) matched
    simpa only [v26556, v26558, v26557] using (show v26559 s i = 0 by unfold v26559; exact if_neg miss)
  have hv26564 : v26564 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4131) (by decide) matched
    simpa only [v26561, v26563, v26562] using (show v26564 s i = 0 by unfold v26564; exact if_neg miss)
  have hv26569 : v26569 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8227) (by decide) matched
    simpa only [v26566, v26568, v26567] using (show v26569 s i = 0 by unfold v26569; exact if_neg miss)
  have hv26574 : v26574 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 27) (by decide) matched
    simpa only [v26571, v26573, v26572] using (show v26574 s i = 0 by unfold v26574; exact if_neg miss)
  have hv26579 : v26579 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4123) (by decide) matched
    simpa only [v26576, v26578, v26577] using (show v26579 s i = 0 by unfold v26579; exact if_neg miss)
  have hv26584 : v26584 s i = 1 := by
    simp [v26584, v26581, v26583, v26582, matched]
  have format : v26897 s i = 4 := by
    simp [v26897, v26385, v26896, v26895, v26894, v26893, v26892, v26891, v26890, v26889, v26888, v26887, v26886, v26885, v26884, v26883, v26882, v26881, v26880, v26879, v26878, v26877, v26876, v26875, v26874, v26873, v26872, v26871, v26870, v26869, v26868, v26867, v26866, v26865, v26864, v26863, v26862, v26861, v26860, v26859, v26858, v26857, v26585, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, hv26554, hv26559, hv26564, hv26569, hv26574, hv26579, hv26584]
  have illegal : v26905 s i = 0 := by
    simp [v26905, v26904, v26903, v26902, v26901, v26899, v26898, v26900, v26380, v26379, v10036, v10035, v10034, v10033, v10032, v10031, v9859, v9834, v9858, v9846, v9840, v9838, v9836, v9835, v9837, v9839, v9845, v9843, v9841, v9842, v9844, v9857, v9851, v9849, v9847, v9848, v9850, v9856, v9854, v9852, v9853, v9855, v10030, v9952, v9913, v9900, v9887, v9874, v9873, v9872, v9860, v9871, v9865, v9862, v9861, v9864, v9863, v9870, v9867, v9866, v9869, v9868, v9881, v9878, v9876, v9875, v9877, v9880, v9879, v9886, v9884, v9882, v2750, v9883, v9885, v9899, v9888, v9894, v9891, v9890, v9889, v9893, v9892, v9898, v9896, v9895, v9897, v9912, v9901, v9907, v9904, v9903, v9902, v9906, v9905, v9911, v9909, v9908, v9910, v9951, v9938, v9925, v9914, v9920, v9917, v9916, v9915, v9919, v9918, v9924, v9922, v9921, v9923, v9937, v9926, v9932, v9929, v9928, v9927, v9931, v9930, v9936, v9934, v9933, v9935, v9950, v9939, v9945, v9942, v9941, v9940, v9944, v9943, v9949, v9947, v9946, v9948, v10029, v9990, v9977, v9964, v9953, v9959, v9956, v9955, v9954, v9958, v9957, v9963, v9961, v9960, v9962, v9976, v9965, v9971, v9968, v9967, v9966, v9970, v9969, v9975, v9973, v9972, v9974, v9989, v9978, v9984, v9981, v9980, v9979, v9983, v9982, v9988, v9986, v9985, v9987, v10028, v10015, v10002, v9991, v9997, v9994, v9993, v9992, v9996, v9995, v10001, v9999, v9998, v10000, v10014, v10003, v10009, v10006, v10005, v10004, v10008, v10007, v10013, v10011, v10010, v10012, v10027, v10016, v10022, v10019, v10018, v10017, v10021, v10020, v10026, v10024, v10023, v10025, v10038, v24, v26190, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, hv26554, hv26559, hv26564, hv26569, hv26574, hv26579, hv26584, format]
  exact illegal
#print axioms idu_word_0_srl_legal

theorem idu_word_0_sra_legal (s : State) (i : Inputs)
    (normal : v26384 s i = 0) (matched : IsWordImmediate .sra (v26210 s i)) :
    v26905 s i = 0 := by
  change v26210 s i &&& BitVec.ofNat 64 4261441663 = BitVec.ofNat 64 1073762331 at matched
  have unitOverride : v28077 s i = 0 := normal
  have opOverride : v28454 s i = 0 := normal
  have hv26389 : v26389 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26386, v26388, v26387] using (show v26389 s i = 0 by unfold v26389; exact if_neg miss)
  have hv26394 : v26394 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26391, v26393, v26392] using (show v26394 s i = 0 by unfold v26394; exact if_neg miss)
  have hv26399 : v26399 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26396, v26398, v26397] using (show v26399 s i = 0 by unfold v26399; exact if_neg miss)
  have hv26404 : v26404 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26401, v26403, v26402] using (show v26404 s i = 0 by unfold v26404; exact if_neg miss)
  have hv26409 : v26409 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26406, v26408, v26407] using (show v26409 s i = 0 by unfold v26409; exact if_neg miss)
  have hv26414 : v26414 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26411, v26413, v26412] using (show v26414 s i = 0 by unfold v26414; exact if_neg miss)
  have hv26419 : v26419 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26416, v26418, v26417] using (show v26419 s i = 0 by unfold v26419; exact if_neg miss)
  have hv26424 : v26424 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26421, v26423, v26422] using (show v26424 s i = 0 by unfold v26424; exact if_neg miss)
  have hv26429 : v26429 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 1073762323) (by decide) matched
    simpa only [v26426, v26428, v26427] using (show v26429 s i = 0 by unfold v26429; exact if_neg miss)
  have hv26434 : v26434 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 51) (by decide) matched
    simpa only [v26431, v26433, v26432] using (show v26434 s i = 0 by unfold v26434; exact if_neg miss)
  have hv26439 : v26439 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4147) (by decide) matched
    simpa only [v26436, v26438, v26437] using (show v26439 s i = 0 by unfold v26439; exact if_neg miss)
  have hv26444 : v26444 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 8243) (by decide) matched
    simpa only [v26441, v26443, v26442] using (show v26444 s i = 0 by unfold v26444; exact if_neg miss)
  have hv26449 : v26449 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 12339) (by decide) matched
    simpa only [v26446, v26448, v26447] using (show v26449 s i = 0 by unfold v26449; exact if_neg miss)
  have hv26454 : v26454 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 16435) (by decide) matched
    simpa only [v26451, v26453, v26452] using (show v26454 s i = 0 by unfold v26454; exact if_neg miss)
  have hv26459 : v26459 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 20531) (by decide) matched
    simpa only [v26456, v26458, v26457] using (show v26459 s i = 0 by unfold v26459; exact if_neg miss)
  have hv26464 : v26464 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 24627) (by decide) matched
    simpa only [v26461, v26463, v26462] using (show v26464 s i = 0 by unfold v26464; exact if_neg miss)
  have hv26469 : v26469 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 28723) (by decide) matched
    simpa only [v26466, v26468, v26467] using (show v26469 s i = 0 by unfold v26469; exact if_neg miss)
  have hv26474 : v26474 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073741875) (by decide) matched
    simpa only [v26471, v26473, v26472] using (show v26474 s i = 0 by unfold v26474; exact if_neg miss)
  have hv26479 : v26479 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073762355) (by decide) matched
    simpa only [v26476, v26478, v26477] using (show v26479 s i = 0 by unfold v26479; exact if_neg miss)
  have hv26484 : v26484 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 127) (BitVec.ofNat 64 23) (by decide) matched
    simpa only [v26481, v26483, v26482] using (show v26484 s i = 0 by unfold v26484; exact if_neg miss)
  have hv26489 : v26489 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 127) (BitVec.ofNat 64 55) (by decide) matched
    simpa only [v26486, v26488, v26487] using (show v26489 s i = 0 by unfold v26489; exact if_neg miss)
  have hv26494 : v26494 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 127) (BitVec.ofNat 64 111) (by decide) matched
    simpa only [v26491, v26493, v26492] using (show v26494 s i = 0 by unfold v26494; exact if_neg miss)
  have hv26499 : v26499 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 103) (by decide) matched
    simpa only [v26496, v26498, v26497] using (show v26499 s i = 0 by unfold v26499; exact if_neg miss)
  have hv26504 : v26504 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 99) (by decide) matched
    simpa only [v26501, v26503, v26502] using (show v26504 s i = 0 by unfold v26504; exact if_neg miss)
  have hv26509 : v26509 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4195) (by decide) matched
    simpa only [v26506, v26508, v26507] using (show v26509 s i = 0 by unfold v26509; exact if_neg miss)
  have hv26514 : v26514 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16483) (by decide) matched
    simpa only [v26511, v26513, v26512] using (show v26514 s i = 0 by unfold v26514; exact if_neg miss)
  have hv26519 : v26519 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 20579) (by decide) matched
    simpa only [v26516, v26518, v26517] using (show v26519 s i = 0 by unfold v26519; exact if_neg miss)
  have hv26524 : v26524 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24675) (by decide) matched
    simpa only [v26521, v26523, v26522] using (show v26524 s i = 0 by unfold v26524; exact if_neg miss)
  have hv26529 : v26529 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28771) (by decide) matched
    simpa only [v26526, v26528, v26527] using (show v26529 s i = 0 by unfold v26529; exact if_neg miss)
  have hv26534 : v26534 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 3) (by decide) matched
    simpa only [v26531, v26533, v26532] using (show v26534 s i = 0 by unfold v26534; exact if_neg miss)
  have hv26539 : v26539 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4099) (by decide) matched
    simpa only [v26536, v26538, v26537] using (show v26539 s i = 0 by unfold v26539; exact if_neg miss)
  have hv26544 : v26544 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8195) (by decide) matched
    simpa only [v26541, v26543, v26542] using (show v26544 s i = 0 by unfold v26544; exact if_neg miss)
  have hv26549 : v26549 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16387) (by decide) matched
    simpa only [v26546, v26548, v26547] using (show v26549 s i = 0 by unfold v26549; exact if_neg miss)
  have hv26554 : v26554 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 20483) (by decide) matched
    simpa only [v26551, v26553, v26552] using (show v26554 s i = 0 by unfold v26554; exact if_neg miss)
  have hv26559 : v26559 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 35) (by decide) matched
    simpa only [v26556, v26558, v26557] using (show v26559 s i = 0 by unfold v26559; exact if_neg miss)
  have hv26564 : v26564 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4131) (by decide) matched
    simpa only [v26561, v26563, v26562] using (show v26564 s i = 0 by unfold v26564; exact if_neg miss)
  have hv26569 : v26569 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8227) (by decide) matched
    simpa only [v26566, v26568, v26567] using (show v26569 s i = 0 by unfold v26569; exact if_neg miss)
  have hv26574 : v26574 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 27) (by decide) matched
    simpa only [v26571, v26573, v26572] using (show v26574 s i = 0 by unfold v26574; exact if_neg miss)
  have hv26579 : v26579 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4123) (by decide) matched
    simpa only [v26576, v26578, v26577] using (show v26579 s i = 0 by unfold v26579; exact if_neg miss)
  have hv26584 : v26584 s i = 0 := by
    have miss := instruction_masks_incompatible (v26210 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 20507) (by decide) matched
    simpa only [v26581, v26583, v26582] using (show v26584 s i = 0 by unfold v26584; exact if_neg miss)
  have hv26589 : v26589 s i = 1 := by
    simp [v26589, v26586, v26588, v26587, matched]
  have format : v26897 s i = 4 := by
    simp [v26897, v26385, v26896, v26895, v26894, v26893, v26892, v26891, v26890, v26889, v26888, v26887, v26886, v26885, v26884, v26883, v26882, v26881, v26880, v26879, v26878, v26877, v26876, v26875, v26874, v26873, v26872, v26871, v26870, v26869, v26868, v26867, v26866, v26865, v26864, v26863, v26862, v26861, v26860, v26859, v26858, v26857, v26856, v26590, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, hv26554, hv26559, hv26564, hv26569, hv26574, hv26579, hv26584, hv26589]
  have illegal : v26905 s i = 0 := by
    simp [v26905, v26904, v26903, v26902, v26901, v26899, v26898, v26900, v26380, v26379, v10036, v10035, v10034, v10033, v10032, v10031, v9859, v9834, v9858, v9846, v9840, v9838, v9836, v9835, v9837, v9839, v9845, v9843, v9841, v9842, v9844, v9857, v9851, v9849, v9847, v9848, v9850, v9856, v9854, v9852, v9853, v9855, v10030, v9952, v9913, v9900, v9887, v9874, v9873, v9872, v9860, v9871, v9865, v9862, v9861, v9864, v9863, v9870, v9867, v9866, v9869, v9868, v9881, v9878, v9876, v9875, v9877, v9880, v9879, v9886, v9884, v9882, v2750, v9883, v9885, v9899, v9888, v9894, v9891, v9890, v9889, v9893, v9892, v9898, v9896, v9895, v9897, v9912, v9901, v9907, v9904, v9903, v9902, v9906, v9905, v9911, v9909, v9908, v9910, v9951, v9938, v9925, v9914, v9920, v9917, v9916, v9915, v9919, v9918, v9924, v9922, v9921, v9923, v9937, v9926, v9932, v9929, v9928, v9927, v9931, v9930, v9936, v9934, v9933, v9935, v9950, v9939, v9945, v9942, v9941, v9940, v9944, v9943, v9949, v9947, v9946, v9948, v10029, v9990, v9977, v9964, v9953, v9959, v9956, v9955, v9954, v9958, v9957, v9963, v9961, v9960, v9962, v9976, v9965, v9971, v9968, v9967, v9966, v9970, v9969, v9975, v9973, v9972, v9974, v9989, v9978, v9984, v9981, v9980, v9979, v9983, v9982, v9988, v9986, v9985, v9987, v10028, v10015, v10002, v9991, v9997, v9994, v9993, v9992, v9996, v9995, v10001, v9999, v9998, v10000, v10014, v10003, v10009, v10006, v10005, v10004, v10008, v10007, v10013, v10011, v10010, v10012, v10027, v10016, v10022, v10019, v10018, v10017, v10021, v10020, v10026, v10024, v10023, v10025, v10038, v24, v26190, normal, unitOverride, opOverride, hv26389, hv26394, hv26399, hv26404, hv26409, hv26414, hv26419, hv26424, hv26429, hv26434, hv26439, hv26444, hv26449, hv26454, hv26459, hv26464, hv26469, hv26474, hv26479, hv26484, hv26489, hv26494, hv26499, hv26504, hv26509, hv26514, hv26519, hv26524, hv26529, hv26534, hv26539, hv26544, hv26549, hv26554, hv26559, hv26564, hv26569, hv26574, hv26579, hv26584, hv26589, format]
  exact illegal
#print axioms idu_word_0_sra_legal

theorem idu_word_1_add_legal (s : State) (i : Inputs)
    (normal : v26911 s i = 0) (matched : IsWordImmediate .add (v26223 s i)) :
    v27432 s i = 0 := by
  change v26223 s i &&& BitVec.ofNat 64 28799 = BitVec.ofNat 64 27 at matched
  have unitOverride : v28261 s i = 0 := normal
  have opOverride : v28649 s i = 0 := normal
  have hv26916 : v26916 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26913, v26915, v26914] using (show v26916 s i = 0 by unfold v26916; exact if_neg miss)
  have hv26921 : v26921 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26918, v26920, v26919] using (show v26921 s i = 0 by unfold v26921; exact if_neg miss)
  have hv26926 : v26926 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26923, v26925, v26924] using (show v26926 s i = 0 by unfold v26926; exact if_neg miss)
  have hv26931 : v26931 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26928, v26930, v26929] using (show v26931 s i = 0 by unfold v26931; exact if_neg miss)
  have hv26936 : v26936 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26933, v26935, v26934] using (show v26936 s i = 0 by unfold v26936; exact if_neg miss)
  have hv26941 : v26941 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26938, v26940, v26939] using (show v26941 s i = 0 by unfold v26941; exact if_neg miss)
  have hv26946 : v26946 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26943, v26945, v26944] using (show v26946 s i = 0 by unfold v26946; exact if_neg miss)
  have hv26951 : v26951 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26948, v26950, v26949] using (show v26951 s i = 0 by unfold v26951; exact if_neg miss)
  have hv26956 : v26956 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 1073762323) (by decide) matched
    simpa only [v26953, v26955, v26954] using (show v26956 s i = 0 by unfold v26956; exact if_neg miss)
  have hv26961 : v26961 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 51) (by decide) matched
    simpa only [v26958, v26960, v26959] using (show v26961 s i = 0 by unfold v26961; exact if_neg miss)
  have hv26966 : v26966 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4147) (by decide) matched
    simpa only [v26963, v26965, v26964] using (show v26966 s i = 0 by unfold v26966; exact if_neg miss)
  have hv26971 : v26971 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 8243) (by decide) matched
    simpa only [v26968, v26970, v26969] using (show v26971 s i = 0 by unfold v26971; exact if_neg miss)
  have hv26976 : v26976 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 12339) (by decide) matched
    simpa only [v26973, v26975, v26974] using (show v26976 s i = 0 by unfold v26976; exact if_neg miss)
  have hv26981 : v26981 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 16435) (by decide) matched
    simpa only [v26978, v26980, v26979] using (show v26981 s i = 0 by unfold v26981; exact if_neg miss)
  have hv26986 : v26986 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 20531) (by decide) matched
    simpa only [v26983, v26985, v26984] using (show v26986 s i = 0 by unfold v26986; exact if_neg miss)
  have hv26991 : v26991 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 24627) (by decide) matched
    simpa only [v26988, v26990, v26989] using (show v26991 s i = 0 by unfold v26991; exact if_neg miss)
  have hv26996 : v26996 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 28723) (by decide) matched
    simpa only [v26993, v26995, v26994] using (show v26996 s i = 0 by unfold v26996; exact if_neg miss)
  have hv27001 : v27001 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073741875) (by decide) matched
    simpa only [v26998, v27000, v26999] using (show v27001 s i = 0 by unfold v27001; exact if_neg miss)
  have hv27006 : v27006 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073762355) (by decide) matched
    simpa only [v27003, v27005, v27004] using (show v27006 s i = 0 by unfold v27006; exact if_neg miss)
  have hv27011 : v27011 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 127) (BitVec.ofNat 64 23) (by decide) matched
    simpa only [v27008, v27010, v27009] using (show v27011 s i = 0 by unfold v27011; exact if_neg miss)
  have hv27016 : v27016 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 127) (BitVec.ofNat 64 55) (by decide) matched
    simpa only [v27013, v27015, v27014] using (show v27016 s i = 0 by unfold v27016; exact if_neg miss)
  have hv27021 : v27021 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 127) (BitVec.ofNat 64 111) (by decide) matched
    simpa only [v27018, v27020, v27019] using (show v27021 s i = 0 by unfold v27021; exact if_neg miss)
  have hv27026 : v27026 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 103) (by decide) matched
    simpa only [v27023, v27025, v27024] using (show v27026 s i = 0 by unfold v27026; exact if_neg miss)
  have hv27031 : v27031 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 99) (by decide) matched
    simpa only [v27028, v27030, v27029] using (show v27031 s i = 0 by unfold v27031; exact if_neg miss)
  have hv27036 : v27036 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4195) (by decide) matched
    simpa only [v27033, v27035, v27034] using (show v27036 s i = 0 by unfold v27036; exact if_neg miss)
  have hv27041 : v27041 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16483) (by decide) matched
    simpa only [v27038, v27040, v27039] using (show v27041 s i = 0 by unfold v27041; exact if_neg miss)
  have hv27046 : v27046 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 20579) (by decide) matched
    simpa only [v27043, v27045, v27044] using (show v27046 s i = 0 by unfold v27046; exact if_neg miss)
  have hv27051 : v27051 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24675) (by decide) matched
    simpa only [v27048, v27050, v27049] using (show v27051 s i = 0 by unfold v27051; exact if_neg miss)
  have hv27056 : v27056 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28771) (by decide) matched
    simpa only [v27053, v27055, v27054] using (show v27056 s i = 0 by unfold v27056; exact if_neg miss)
  have hv27061 : v27061 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 3) (by decide) matched
    simpa only [v27058, v27060, v27059] using (show v27061 s i = 0 by unfold v27061; exact if_neg miss)
  have hv27066 : v27066 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4099) (by decide) matched
    simpa only [v27063, v27065, v27064] using (show v27066 s i = 0 by unfold v27066; exact if_neg miss)
  have hv27071 : v27071 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8195) (by decide) matched
    simpa only [v27068, v27070, v27069] using (show v27071 s i = 0 by unfold v27071; exact if_neg miss)
  have hv27076 : v27076 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16387) (by decide) matched
    simpa only [v27073, v27075, v27074] using (show v27076 s i = 0 by unfold v27076; exact if_neg miss)
  have hv27081 : v27081 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 20483) (by decide) matched
    simpa only [v27078, v27080, v27079] using (show v27081 s i = 0 by unfold v27081; exact if_neg miss)
  have hv27086 : v27086 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 35) (by decide) matched
    simpa only [v27083, v27085, v27084] using (show v27086 s i = 0 by unfold v27086; exact if_neg miss)
  have hv27091 : v27091 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4131) (by decide) matched
    simpa only [v27088, v27090, v27089] using (show v27091 s i = 0 by unfold v27091; exact if_neg miss)
  have hv27096 : v27096 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 28799)
      (BitVec.ofNat 64 27) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8227) (by decide) matched
    simpa only [v27093, v27095, v27094] using (show v27096 s i = 0 by unfold v27096; exact if_neg miss)
  have hv27101 : v27101 s i = 1 := by
    simp [v27101, v27098, v27100, v27099, matched]
  have format : v27424 s i = 4 := by
    simp [v27424, v26912, v27423, v27422, v27421, v27420, v27419, v27418, v27417, v27416, v27415, v27414, v27413, v27412, v27411, v27410, v27409, v27408, v27407, v27406, v27405, v27404, v27403, v27402, v27401, v27400, v27399, v27398, v27397, v27396, v27395, v27394, v27393, v27392, v27391, v27390, v27389, v27388, v27387, v27386, v27102, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, hv27081, hv27086, hv27091, hv27096, hv27101]
  have illegal : v27432 s i = 0 := by
    simp [v27432, v27431, v27430, v27429, v27428, v27426, v27425, v27427, v10039, v10037, v10036, v10035, v10034, v10033, v10032, v10031, v9859, v9834, v9858, v9846, v9840, v9838, v9836, v9835, v9837, v9839, v9845, v9843, v9841, v9842, v9844, v9857, v9851, v9849, v9847, v9848, v9850, v9856, v9854, v9852, v9853, v9855, v10030, v9952, v9913, v9900, v9887, v9874, v9873, v9872, v9860, v9871, v9865, v9862, v9861, v9864, v9863, v9870, v9867, v9866, v9869, v9868, v9881, v9878, v9876, v9875, v9877, v9880, v9879, v9886, v9884, v9882, v2750, v9883, v9885, v9899, v9888, v9894, v9891, v9890, v9889, v9893, v9892, v9898, v9896, v9895, v9897, v9912, v9901, v9907, v9904, v9903, v9902, v9906, v9905, v9911, v9909, v9908, v9910, v9951, v9938, v9925, v9914, v9920, v9917, v9916, v9915, v9919, v9918, v9924, v9922, v9921, v9923, v9937, v9926, v9932, v9929, v9928, v9927, v9931, v9930, v9936, v9934, v9933, v9935, v9950, v9939, v9945, v9942, v9941, v9940, v9944, v9943, v9949, v9947, v9946, v9948, v10029, v9990, v9977, v9964, v9953, v9959, v9956, v9955, v9954, v9958, v9957, v9963, v9961, v9960, v9962, v9976, v9965, v9971, v9968, v9967, v9966, v9970, v9969, v9975, v9973, v9972, v9974, v9989, v9978, v9984, v9981, v9980, v9979, v9983, v9982, v9988, v9986, v9985, v9987, v10028, v10015, v10002, v9991, v9997, v9994, v9993, v9992, v9996, v9995, v10001, v9999, v9998, v10000, v10014, v10003, v10009, v10006, v10005, v10004, v10008, v10007, v10013, v10011, v10010, v10012, v10027, v10016, v10022, v10019, v10018, v10017, v10021, v10020, v10026, v10024, v10023, v10025, v10038, v24, v9812, v9811, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, hv27081, hv27086, hv27091, hv27096, hv27101, format]
  exact illegal
#print axioms idu_word_1_add_legal

theorem idu_word_1_sll_legal (s : State) (i : Inputs)
    (normal : v26911 s i = 0) (matched : IsWordImmediate .sll (v26223 s i)) :
    v27432 s i = 0 := by
  change v26223 s i &&& BitVec.ofNat 64 4261441663 = BitVec.ofNat 64 4123 at matched
  have unitOverride : v28261 s i = 0 := normal
  have opOverride : v28649 s i = 0 := normal
  have hv26916 : v26916 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26913, v26915, v26914] using (show v26916 s i = 0 by unfold v26916; exact if_neg miss)
  have hv26921 : v26921 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26918, v26920, v26919] using (show v26921 s i = 0 by unfold v26921; exact if_neg miss)
  have hv26926 : v26926 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26923, v26925, v26924] using (show v26926 s i = 0 by unfold v26926; exact if_neg miss)
  have hv26931 : v26931 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26928, v26930, v26929] using (show v26931 s i = 0 by unfold v26931; exact if_neg miss)
  have hv26936 : v26936 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26933, v26935, v26934] using (show v26936 s i = 0 by unfold v26936; exact if_neg miss)
  have hv26941 : v26941 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26938, v26940, v26939] using (show v26941 s i = 0 by unfold v26941; exact if_neg miss)
  have hv26946 : v26946 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26943, v26945, v26944] using (show v26946 s i = 0 by unfold v26946; exact if_neg miss)
  have hv26951 : v26951 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26948, v26950, v26949] using (show v26951 s i = 0 by unfold v26951; exact if_neg miss)
  have hv26956 : v26956 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 1073762323) (by decide) matched
    simpa only [v26953, v26955, v26954] using (show v26956 s i = 0 by unfold v26956; exact if_neg miss)
  have hv26961 : v26961 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 51) (by decide) matched
    simpa only [v26958, v26960, v26959] using (show v26961 s i = 0 by unfold v26961; exact if_neg miss)
  have hv26966 : v26966 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4147) (by decide) matched
    simpa only [v26963, v26965, v26964] using (show v26966 s i = 0 by unfold v26966; exact if_neg miss)
  have hv26971 : v26971 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 8243) (by decide) matched
    simpa only [v26968, v26970, v26969] using (show v26971 s i = 0 by unfold v26971; exact if_neg miss)
  have hv26976 : v26976 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 12339) (by decide) matched
    simpa only [v26973, v26975, v26974] using (show v26976 s i = 0 by unfold v26976; exact if_neg miss)
  have hv26981 : v26981 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 16435) (by decide) matched
    simpa only [v26978, v26980, v26979] using (show v26981 s i = 0 by unfold v26981; exact if_neg miss)
  have hv26986 : v26986 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 20531) (by decide) matched
    simpa only [v26983, v26985, v26984] using (show v26986 s i = 0 by unfold v26986; exact if_neg miss)
  have hv26991 : v26991 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 24627) (by decide) matched
    simpa only [v26988, v26990, v26989] using (show v26991 s i = 0 by unfold v26991; exact if_neg miss)
  have hv26996 : v26996 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 28723) (by decide) matched
    simpa only [v26993, v26995, v26994] using (show v26996 s i = 0 by unfold v26996; exact if_neg miss)
  have hv27001 : v27001 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073741875) (by decide) matched
    simpa only [v26998, v27000, v26999] using (show v27001 s i = 0 by unfold v27001; exact if_neg miss)
  have hv27006 : v27006 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073762355) (by decide) matched
    simpa only [v27003, v27005, v27004] using (show v27006 s i = 0 by unfold v27006; exact if_neg miss)
  have hv27011 : v27011 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 127) (BitVec.ofNat 64 23) (by decide) matched
    simpa only [v27008, v27010, v27009] using (show v27011 s i = 0 by unfold v27011; exact if_neg miss)
  have hv27016 : v27016 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 127) (BitVec.ofNat 64 55) (by decide) matched
    simpa only [v27013, v27015, v27014] using (show v27016 s i = 0 by unfold v27016; exact if_neg miss)
  have hv27021 : v27021 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 127) (BitVec.ofNat 64 111) (by decide) matched
    simpa only [v27018, v27020, v27019] using (show v27021 s i = 0 by unfold v27021; exact if_neg miss)
  have hv27026 : v27026 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 103) (by decide) matched
    simpa only [v27023, v27025, v27024] using (show v27026 s i = 0 by unfold v27026; exact if_neg miss)
  have hv27031 : v27031 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 99) (by decide) matched
    simpa only [v27028, v27030, v27029] using (show v27031 s i = 0 by unfold v27031; exact if_neg miss)
  have hv27036 : v27036 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4195) (by decide) matched
    simpa only [v27033, v27035, v27034] using (show v27036 s i = 0 by unfold v27036; exact if_neg miss)
  have hv27041 : v27041 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16483) (by decide) matched
    simpa only [v27038, v27040, v27039] using (show v27041 s i = 0 by unfold v27041; exact if_neg miss)
  have hv27046 : v27046 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 20579) (by decide) matched
    simpa only [v27043, v27045, v27044] using (show v27046 s i = 0 by unfold v27046; exact if_neg miss)
  have hv27051 : v27051 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24675) (by decide) matched
    simpa only [v27048, v27050, v27049] using (show v27051 s i = 0 by unfold v27051; exact if_neg miss)
  have hv27056 : v27056 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28771) (by decide) matched
    simpa only [v27053, v27055, v27054] using (show v27056 s i = 0 by unfold v27056; exact if_neg miss)
  have hv27061 : v27061 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 3) (by decide) matched
    simpa only [v27058, v27060, v27059] using (show v27061 s i = 0 by unfold v27061; exact if_neg miss)
  have hv27066 : v27066 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4099) (by decide) matched
    simpa only [v27063, v27065, v27064] using (show v27066 s i = 0 by unfold v27066; exact if_neg miss)
  have hv27071 : v27071 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8195) (by decide) matched
    simpa only [v27068, v27070, v27069] using (show v27071 s i = 0 by unfold v27071; exact if_neg miss)
  have hv27076 : v27076 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16387) (by decide) matched
    simpa only [v27073, v27075, v27074] using (show v27076 s i = 0 by unfold v27076; exact if_neg miss)
  have hv27081 : v27081 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 20483) (by decide) matched
    simpa only [v27078, v27080, v27079] using (show v27081 s i = 0 by unfold v27081; exact if_neg miss)
  have hv27086 : v27086 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 35) (by decide) matched
    simpa only [v27083, v27085, v27084] using (show v27086 s i = 0 by unfold v27086; exact if_neg miss)
  have hv27091 : v27091 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4131) (by decide) matched
    simpa only [v27088, v27090, v27089] using (show v27091 s i = 0 by unfold v27091; exact if_neg miss)
  have hv27096 : v27096 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8227) (by decide) matched
    simpa only [v27093, v27095, v27094] using (show v27096 s i = 0 by unfold v27096; exact if_neg miss)
  have hv27101 : v27101 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 4123) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 27) (by decide) matched
    simpa only [v27098, v27100, v27099] using (show v27101 s i = 0 by unfold v27101; exact if_neg miss)
  have hv27106 : v27106 s i = 1 := by
    simp [v27106, v27103, v27105, v27104, matched]
  have format : v27424 s i = 4 := by
    simp [v27424, v26912, v27423, v27422, v27421, v27420, v27419, v27418, v27417, v27416, v27415, v27414, v27413, v27412, v27411, v27410, v27409, v27408, v27407, v27406, v27405, v27404, v27403, v27402, v27401, v27400, v27399, v27398, v27397, v27396, v27395, v27394, v27393, v27392, v27391, v27390, v27389, v27388, v27387, v27386, v27385, v27107, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, hv27081, hv27086, hv27091, hv27096, hv27101, hv27106]
  have illegal : v27432 s i = 0 := by
    simp [v27432, v27431, v27430, v27429, v27428, v27426, v27425, v27427, v10039, v10037, v10036, v10035, v10034, v10033, v10032, v10031, v9859, v9834, v9858, v9846, v9840, v9838, v9836, v9835, v9837, v9839, v9845, v9843, v9841, v9842, v9844, v9857, v9851, v9849, v9847, v9848, v9850, v9856, v9854, v9852, v9853, v9855, v10030, v9952, v9913, v9900, v9887, v9874, v9873, v9872, v9860, v9871, v9865, v9862, v9861, v9864, v9863, v9870, v9867, v9866, v9869, v9868, v9881, v9878, v9876, v9875, v9877, v9880, v9879, v9886, v9884, v9882, v2750, v9883, v9885, v9899, v9888, v9894, v9891, v9890, v9889, v9893, v9892, v9898, v9896, v9895, v9897, v9912, v9901, v9907, v9904, v9903, v9902, v9906, v9905, v9911, v9909, v9908, v9910, v9951, v9938, v9925, v9914, v9920, v9917, v9916, v9915, v9919, v9918, v9924, v9922, v9921, v9923, v9937, v9926, v9932, v9929, v9928, v9927, v9931, v9930, v9936, v9934, v9933, v9935, v9950, v9939, v9945, v9942, v9941, v9940, v9944, v9943, v9949, v9947, v9946, v9948, v10029, v9990, v9977, v9964, v9953, v9959, v9956, v9955, v9954, v9958, v9957, v9963, v9961, v9960, v9962, v9976, v9965, v9971, v9968, v9967, v9966, v9970, v9969, v9975, v9973, v9972, v9974, v9989, v9978, v9984, v9981, v9980, v9979, v9983, v9982, v9988, v9986, v9985, v9987, v10028, v10015, v10002, v9991, v9997, v9994, v9993, v9992, v9996, v9995, v10001, v9999, v9998, v10000, v10014, v10003, v10009, v10006, v10005, v10004, v10008, v10007, v10013, v10011, v10010, v10012, v10027, v10016, v10022, v10019, v10018, v10017, v10021, v10020, v10026, v10024, v10023, v10025, v10038, v24, v9812, v9811, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, hv27081, hv27086, hv27091, hv27096, hv27101, hv27106, format]
  exact illegal
#print axioms idu_word_1_sll_legal

theorem idu_word_1_srl_legal (s : State) (i : Inputs)
    (normal : v26911 s i = 0) (matched : IsWordImmediate .srl (v26223 s i)) :
    v27432 s i = 0 := by
  change v26223 s i &&& BitVec.ofNat 64 4261441663 = BitVec.ofNat 64 20507 at matched
  have unitOverride : v28261 s i = 0 := normal
  have opOverride : v28649 s i = 0 := normal
  have hv26916 : v26916 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26913, v26915, v26914] using (show v26916 s i = 0 by unfold v26916; exact if_neg miss)
  have hv26921 : v26921 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26918, v26920, v26919] using (show v26921 s i = 0 by unfold v26921; exact if_neg miss)
  have hv26926 : v26926 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26923, v26925, v26924] using (show v26926 s i = 0 by unfold v26926; exact if_neg miss)
  have hv26931 : v26931 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26928, v26930, v26929] using (show v26931 s i = 0 by unfold v26931; exact if_neg miss)
  have hv26936 : v26936 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26933, v26935, v26934] using (show v26936 s i = 0 by unfold v26936; exact if_neg miss)
  have hv26941 : v26941 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26938, v26940, v26939] using (show v26941 s i = 0 by unfold v26941; exact if_neg miss)
  have hv26946 : v26946 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26943, v26945, v26944] using (show v26946 s i = 0 by unfold v26946; exact if_neg miss)
  have hv26951 : v26951 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26948, v26950, v26949] using (show v26951 s i = 0 by unfold v26951; exact if_neg miss)
  have hv26956 : v26956 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 1073762323) (by decide) matched
    simpa only [v26953, v26955, v26954] using (show v26956 s i = 0 by unfold v26956; exact if_neg miss)
  have hv26961 : v26961 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 51) (by decide) matched
    simpa only [v26958, v26960, v26959] using (show v26961 s i = 0 by unfold v26961; exact if_neg miss)
  have hv26966 : v26966 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4147) (by decide) matched
    simpa only [v26963, v26965, v26964] using (show v26966 s i = 0 by unfold v26966; exact if_neg miss)
  have hv26971 : v26971 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 8243) (by decide) matched
    simpa only [v26968, v26970, v26969] using (show v26971 s i = 0 by unfold v26971; exact if_neg miss)
  have hv26976 : v26976 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 12339) (by decide) matched
    simpa only [v26973, v26975, v26974] using (show v26976 s i = 0 by unfold v26976; exact if_neg miss)
  have hv26981 : v26981 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 16435) (by decide) matched
    simpa only [v26978, v26980, v26979] using (show v26981 s i = 0 by unfold v26981; exact if_neg miss)
  have hv26986 : v26986 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 20531) (by decide) matched
    simpa only [v26983, v26985, v26984] using (show v26986 s i = 0 by unfold v26986; exact if_neg miss)
  have hv26991 : v26991 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 24627) (by decide) matched
    simpa only [v26988, v26990, v26989] using (show v26991 s i = 0 by unfold v26991; exact if_neg miss)
  have hv26996 : v26996 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 28723) (by decide) matched
    simpa only [v26993, v26995, v26994] using (show v26996 s i = 0 by unfold v26996; exact if_neg miss)
  have hv27001 : v27001 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073741875) (by decide) matched
    simpa only [v26998, v27000, v26999] using (show v27001 s i = 0 by unfold v27001; exact if_neg miss)
  have hv27006 : v27006 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073762355) (by decide) matched
    simpa only [v27003, v27005, v27004] using (show v27006 s i = 0 by unfold v27006; exact if_neg miss)
  have hv27011 : v27011 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 127) (BitVec.ofNat 64 23) (by decide) matched
    simpa only [v27008, v27010, v27009] using (show v27011 s i = 0 by unfold v27011; exact if_neg miss)
  have hv27016 : v27016 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 127) (BitVec.ofNat 64 55) (by decide) matched
    simpa only [v27013, v27015, v27014] using (show v27016 s i = 0 by unfold v27016; exact if_neg miss)
  have hv27021 : v27021 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 127) (BitVec.ofNat 64 111) (by decide) matched
    simpa only [v27018, v27020, v27019] using (show v27021 s i = 0 by unfold v27021; exact if_neg miss)
  have hv27026 : v27026 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 103) (by decide) matched
    simpa only [v27023, v27025, v27024] using (show v27026 s i = 0 by unfold v27026; exact if_neg miss)
  have hv27031 : v27031 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 99) (by decide) matched
    simpa only [v27028, v27030, v27029] using (show v27031 s i = 0 by unfold v27031; exact if_neg miss)
  have hv27036 : v27036 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4195) (by decide) matched
    simpa only [v27033, v27035, v27034] using (show v27036 s i = 0 by unfold v27036; exact if_neg miss)
  have hv27041 : v27041 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16483) (by decide) matched
    simpa only [v27038, v27040, v27039] using (show v27041 s i = 0 by unfold v27041; exact if_neg miss)
  have hv27046 : v27046 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 20579) (by decide) matched
    simpa only [v27043, v27045, v27044] using (show v27046 s i = 0 by unfold v27046; exact if_neg miss)
  have hv27051 : v27051 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24675) (by decide) matched
    simpa only [v27048, v27050, v27049] using (show v27051 s i = 0 by unfold v27051; exact if_neg miss)
  have hv27056 : v27056 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28771) (by decide) matched
    simpa only [v27053, v27055, v27054] using (show v27056 s i = 0 by unfold v27056; exact if_neg miss)
  have hv27061 : v27061 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 3) (by decide) matched
    simpa only [v27058, v27060, v27059] using (show v27061 s i = 0 by unfold v27061; exact if_neg miss)
  have hv27066 : v27066 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4099) (by decide) matched
    simpa only [v27063, v27065, v27064] using (show v27066 s i = 0 by unfold v27066; exact if_neg miss)
  have hv27071 : v27071 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8195) (by decide) matched
    simpa only [v27068, v27070, v27069] using (show v27071 s i = 0 by unfold v27071; exact if_neg miss)
  have hv27076 : v27076 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16387) (by decide) matched
    simpa only [v27073, v27075, v27074] using (show v27076 s i = 0 by unfold v27076; exact if_neg miss)
  have hv27081 : v27081 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 20483) (by decide) matched
    simpa only [v27078, v27080, v27079] using (show v27081 s i = 0 by unfold v27081; exact if_neg miss)
  have hv27086 : v27086 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 35) (by decide) matched
    simpa only [v27083, v27085, v27084] using (show v27086 s i = 0 by unfold v27086; exact if_neg miss)
  have hv27091 : v27091 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4131) (by decide) matched
    simpa only [v27088, v27090, v27089] using (show v27091 s i = 0 by unfold v27091; exact if_neg miss)
  have hv27096 : v27096 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8227) (by decide) matched
    simpa only [v27093, v27095, v27094] using (show v27096 s i = 0 by unfold v27096; exact if_neg miss)
  have hv27101 : v27101 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 27) (by decide) matched
    simpa only [v27098, v27100, v27099] using (show v27101 s i = 0 by unfold v27101; exact if_neg miss)
  have hv27106 : v27106 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 20507) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4123) (by decide) matched
    simpa only [v27103, v27105, v27104] using (show v27106 s i = 0 by unfold v27106; exact if_neg miss)
  have hv27111 : v27111 s i = 1 := by
    simp [v27111, v27108, v27110, v27109, matched]
  have format : v27424 s i = 4 := by
    simp [v27424, v26912, v27423, v27422, v27421, v27420, v27419, v27418, v27417, v27416, v27415, v27414, v27413, v27412, v27411, v27410, v27409, v27408, v27407, v27406, v27405, v27404, v27403, v27402, v27401, v27400, v27399, v27398, v27397, v27396, v27395, v27394, v27393, v27392, v27391, v27390, v27389, v27388, v27387, v27386, v27385, v27384, v27112, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, hv27081, hv27086, hv27091, hv27096, hv27101, hv27106, hv27111]
  have illegal : v27432 s i = 0 := by
    simp [v27432, v27431, v27430, v27429, v27428, v27426, v27425, v27427, v10039, v10037, v10036, v10035, v10034, v10033, v10032, v10031, v9859, v9834, v9858, v9846, v9840, v9838, v9836, v9835, v9837, v9839, v9845, v9843, v9841, v9842, v9844, v9857, v9851, v9849, v9847, v9848, v9850, v9856, v9854, v9852, v9853, v9855, v10030, v9952, v9913, v9900, v9887, v9874, v9873, v9872, v9860, v9871, v9865, v9862, v9861, v9864, v9863, v9870, v9867, v9866, v9869, v9868, v9881, v9878, v9876, v9875, v9877, v9880, v9879, v9886, v9884, v9882, v2750, v9883, v9885, v9899, v9888, v9894, v9891, v9890, v9889, v9893, v9892, v9898, v9896, v9895, v9897, v9912, v9901, v9907, v9904, v9903, v9902, v9906, v9905, v9911, v9909, v9908, v9910, v9951, v9938, v9925, v9914, v9920, v9917, v9916, v9915, v9919, v9918, v9924, v9922, v9921, v9923, v9937, v9926, v9932, v9929, v9928, v9927, v9931, v9930, v9936, v9934, v9933, v9935, v9950, v9939, v9945, v9942, v9941, v9940, v9944, v9943, v9949, v9947, v9946, v9948, v10029, v9990, v9977, v9964, v9953, v9959, v9956, v9955, v9954, v9958, v9957, v9963, v9961, v9960, v9962, v9976, v9965, v9971, v9968, v9967, v9966, v9970, v9969, v9975, v9973, v9972, v9974, v9989, v9978, v9984, v9981, v9980, v9979, v9983, v9982, v9988, v9986, v9985, v9987, v10028, v10015, v10002, v9991, v9997, v9994, v9993, v9992, v9996, v9995, v10001, v9999, v9998, v10000, v10014, v10003, v10009, v10006, v10005, v10004, v10008, v10007, v10013, v10011, v10010, v10012, v10027, v10016, v10022, v10019, v10018, v10017, v10021, v10020, v10026, v10024, v10023, v10025, v10038, v24, v9812, v9811, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, hv27081, hv27086, hv27091, hv27096, hv27101, hv27106, hv27111, format]
  exact illegal
#print axioms idu_word_1_srl_legal

theorem idu_word_1_sra_legal (s : State) (i : Inputs)
    (normal : v26911 s i = 0) (matched : IsWordImmediate .sra (v26223 s i)) :
    v27432 s i = 0 := by
  change v26223 s i &&& BitVec.ofNat 64 4261441663 = BitVec.ofNat 64 1073762331 at matched
  have unitOverride : v28261 s i = 0 := normal
  have opOverride : v28649 s i = 0 := normal
  have hv26916 : v26916 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 19) (by decide) matched
    simpa only [v26913, v26915, v26914] using (show v26916 s i = 0 by unfold v26916; exact if_neg miss)
  have hv26921 : v26921 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 4115) (by decide) matched
    simpa only [v26918, v26920, v26919] using (show v26921 s i = 0 by unfold v26921; exact if_neg miss)
  have hv26926 : v26926 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8211) (by decide) matched
    simpa only [v26923, v26925, v26924] using (show v26926 s i = 0 by unfold v26926; exact if_neg miss)
  have hv26931 : v26931 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 12307) (by decide) matched
    simpa only [v26928, v26930, v26929] using (show v26931 s i = 0 by unfold v26931; exact if_neg miss)
  have hv26936 : v26936 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16403) (by decide) matched
    simpa only [v26933, v26935, v26934] using (show v26936 s i = 0 by unfold v26936; exact if_neg miss)
  have hv26941 : v26941 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 20499) (by decide) matched
    simpa only [v26938, v26940, v26939] using (show v26941 s i = 0 by unfold v26941; exact if_neg miss)
  have hv26946 : v26946 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24595) (by decide) matched
    simpa only [v26943, v26945, v26944] using (show v26946 s i = 0 by unfold v26946; exact if_neg miss)
  have hv26951 : v26951 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28691) (by decide) matched
    simpa only [v26948, v26950, v26949] using (show v26951 s i = 0 by unfold v26951; exact if_neg miss)
  have hv26956 : v26956 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 4227887231) (BitVec.ofNat 64 1073762323) (by decide) matched
    simpa only [v26953, v26955, v26954] using (show v26956 s i = 0 by unfold v26956; exact if_neg miss)
  have hv26961 : v26961 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 51) (by decide) matched
    simpa only [v26958, v26960, v26959] using (show v26961 s i = 0 by unfold v26961; exact if_neg miss)
  have hv26966 : v26966 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4147) (by decide) matched
    simpa only [v26963, v26965, v26964] using (show v26966 s i = 0 by unfold v26966; exact if_neg miss)
  have hv26971 : v26971 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 8243) (by decide) matched
    simpa only [v26968, v26970, v26969] using (show v26971 s i = 0 by unfold v26971; exact if_neg miss)
  have hv26976 : v26976 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 12339) (by decide) matched
    simpa only [v26973, v26975, v26974] using (show v26976 s i = 0 by unfold v26976; exact if_neg miss)
  have hv26981 : v26981 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 16435) (by decide) matched
    simpa only [v26978, v26980, v26979] using (show v26981 s i = 0 by unfold v26981; exact if_neg miss)
  have hv26986 : v26986 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 20531) (by decide) matched
    simpa only [v26983, v26985, v26984] using (show v26986 s i = 0 by unfold v26986; exact if_neg miss)
  have hv26991 : v26991 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 24627) (by decide) matched
    simpa only [v26988, v26990, v26989] using (show v26991 s i = 0 by unfold v26991; exact if_neg miss)
  have hv26996 : v26996 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 28723) (by decide) matched
    simpa only [v26993, v26995, v26994] using (show v26996 s i = 0 by unfold v26996; exact if_neg miss)
  have hv27001 : v27001 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073741875) (by decide) matched
    simpa only [v26998, v27000, v26999] using (show v27001 s i = 0 by unfold v27001; exact if_neg miss)
  have hv27006 : v27006 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 1073762355) (by decide) matched
    simpa only [v27003, v27005, v27004] using (show v27006 s i = 0 by unfold v27006; exact if_neg miss)
  have hv27011 : v27011 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 127) (BitVec.ofNat 64 23) (by decide) matched
    simpa only [v27008, v27010, v27009] using (show v27011 s i = 0 by unfold v27011; exact if_neg miss)
  have hv27016 : v27016 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 127) (BitVec.ofNat 64 55) (by decide) matched
    simpa only [v27013, v27015, v27014] using (show v27016 s i = 0 by unfold v27016; exact if_neg miss)
  have hv27021 : v27021 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 127) (BitVec.ofNat 64 111) (by decide) matched
    simpa only [v27018, v27020, v27019] using (show v27021 s i = 0 by unfold v27021; exact if_neg miss)
  have hv27026 : v27026 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 103) (by decide) matched
    simpa only [v27023, v27025, v27024] using (show v27026 s i = 0 by unfold v27026; exact if_neg miss)
  have hv27031 : v27031 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 99) (by decide) matched
    simpa only [v27028, v27030, v27029] using (show v27031 s i = 0 by unfold v27031; exact if_neg miss)
  have hv27036 : v27036 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4195) (by decide) matched
    simpa only [v27033, v27035, v27034] using (show v27036 s i = 0 by unfold v27036; exact if_neg miss)
  have hv27041 : v27041 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16483) (by decide) matched
    simpa only [v27038, v27040, v27039] using (show v27041 s i = 0 by unfold v27041; exact if_neg miss)
  have hv27046 : v27046 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 20579) (by decide) matched
    simpa only [v27043, v27045, v27044] using (show v27046 s i = 0 by unfold v27046; exact if_neg miss)
  have hv27051 : v27051 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 24675) (by decide) matched
    simpa only [v27048, v27050, v27049] using (show v27051 s i = 0 by unfold v27051; exact if_neg miss)
  have hv27056 : v27056 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 28771) (by decide) matched
    simpa only [v27053, v27055, v27054] using (show v27056 s i = 0 by unfold v27056; exact if_neg miss)
  have hv27061 : v27061 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 3) (by decide) matched
    simpa only [v27058, v27060, v27059] using (show v27061 s i = 0 by unfold v27061; exact if_neg miss)
  have hv27066 : v27066 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4099) (by decide) matched
    simpa only [v27063, v27065, v27064] using (show v27066 s i = 0 by unfold v27066; exact if_neg miss)
  have hv27071 : v27071 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8195) (by decide) matched
    simpa only [v27068, v27070, v27069] using (show v27071 s i = 0 by unfold v27071; exact if_neg miss)
  have hv27076 : v27076 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 16387) (by decide) matched
    simpa only [v27073, v27075, v27074] using (show v27076 s i = 0 by unfold v27076; exact if_neg miss)
  have hv27081 : v27081 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 20483) (by decide) matched
    simpa only [v27078, v27080, v27079] using (show v27081 s i = 0 by unfold v27081; exact if_neg miss)
  have hv27086 : v27086 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 35) (by decide) matched
    simpa only [v27083, v27085, v27084] using (show v27086 s i = 0 by unfold v27086; exact if_neg miss)
  have hv27091 : v27091 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 4131) (by decide) matched
    simpa only [v27088, v27090, v27089] using (show v27091 s i = 0 by unfold v27091; exact if_neg miss)
  have hv27096 : v27096 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 8227) (by decide) matched
    simpa only [v27093, v27095, v27094] using (show v27096 s i = 0 by unfold v27096; exact if_neg miss)
  have hv27101 : v27101 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 28799) (BitVec.ofNat 64 27) (by decide) matched
    simpa only [v27098, v27100, v27099] using (show v27101 s i = 0 by unfold v27101; exact if_neg miss)
  have hv27106 : v27106 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 4123) (by decide) matched
    simpa only [v27103, v27105, v27104] using (show v27106 s i = 0 by unfold v27106; exact if_neg miss)
  have hv27111 : v27111 s i = 0 := by
    have miss := instruction_masks_incompatible (v26223 s i) (BitVec.ofNat 64 4261441663)
      (BitVec.ofNat 64 1073762331) (BitVec.ofNat 64 4261441663) (BitVec.ofNat 64 20507) (by decide) matched
    simpa only [v27108, v27110, v27109] using (show v27111 s i = 0 by unfold v27111; exact if_neg miss)
  have hv27116 : v27116 s i = 1 := by
    simp [v27116, v27113, v27115, v27114, matched]
  have format : v27424 s i = 4 := by
    simp [v27424, v26912, v27423, v27422, v27421, v27420, v27419, v27418, v27417, v27416, v27415, v27414, v27413, v27412, v27411, v27410, v27409, v27408, v27407, v27406, v27405, v27404, v27403, v27402, v27401, v27400, v27399, v27398, v27397, v27396, v27395, v27394, v27393, v27392, v27391, v27390, v27389, v27388, v27387, v27386, v27385, v27384, v27383, v27117, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, hv27081, hv27086, hv27091, hv27096, hv27101, hv27106, hv27111, hv27116]
  have illegal : v27432 s i = 0 := by
    simp [v27432, v27431, v27430, v27429, v27428, v27426, v27425, v27427, v10039, v10037, v10036, v10035, v10034, v10033, v10032, v10031, v9859, v9834, v9858, v9846, v9840, v9838, v9836, v9835, v9837, v9839, v9845, v9843, v9841, v9842, v9844, v9857, v9851, v9849, v9847, v9848, v9850, v9856, v9854, v9852, v9853, v9855, v10030, v9952, v9913, v9900, v9887, v9874, v9873, v9872, v9860, v9871, v9865, v9862, v9861, v9864, v9863, v9870, v9867, v9866, v9869, v9868, v9881, v9878, v9876, v9875, v9877, v9880, v9879, v9886, v9884, v9882, v2750, v9883, v9885, v9899, v9888, v9894, v9891, v9890, v9889, v9893, v9892, v9898, v9896, v9895, v9897, v9912, v9901, v9907, v9904, v9903, v9902, v9906, v9905, v9911, v9909, v9908, v9910, v9951, v9938, v9925, v9914, v9920, v9917, v9916, v9915, v9919, v9918, v9924, v9922, v9921, v9923, v9937, v9926, v9932, v9929, v9928, v9927, v9931, v9930, v9936, v9934, v9933, v9935, v9950, v9939, v9945, v9942, v9941, v9940, v9944, v9943, v9949, v9947, v9946, v9948, v10029, v9990, v9977, v9964, v9953, v9959, v9956, v9955, v9954, v9958, v9957, v9963, v9961, v9960, v9962, v9976, v9965, v9971, v9968, v9967, v9966, v9970, v9969, v9975, v9973, v9972, v9974, v9989, v9978, v9984, v9981, v9980, v9979, v9983, v9982, v9988, v9986, v9985, v9987, v10028, v10015, v10002, v9991, v9997, v9994, v9993, v9992, v9996, v9995, v10001, v9999, v9998, v10000, v10014, v10003, v10009, v10006, v10005, v10004, v10008, v10007, v10013, v10011, v10010, v10012, v10027, v10016, v10022, v10019, v10018, v10017, v10021, v10020, v10026, v10024, v10023, v10025, v10038, v24, v9812, v9811, normal, unitOverride, opOverride, hv26916, hv26921, hv26926, hv26931, hv26936, hv26941, hv26946, hv26951, hv26956, hv26961, hv26966, hv26971, hv26976, hv26981, hv26986, hv26991, hv26996, hv27001, hv27006, hv27011, hv27016, hv27021, hv27026, hv27031, hv27036, hv27041, hv27046, hv27051, hv27056, hv27061, hv27066, hv27071, hv27076, hv27081, hv27086, hv27091, hv27096, hv27101, hv27106, hv27111, hv27116, format]
  exact illegal
#print axioms idu_word_1_sra_legal

end NutShellProofs

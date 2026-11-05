import Proofs.DecodeBits
import Proofs.BranchAlignmentAssumption
namespace NutShellProofs
open nNutCore
set_option maxRecDepth 4096
theorem atomic_opcode_rejected_by_whitelist (s : State) (i : Inputs)
    (atomic : BitVec.extractLsb' 0 7 (v30884 s i) = 47) : v31090 s i = 0 := by
  have hv30887 : v30887 s i = 0 := by
    have miss : v30883 s i ≠ v30884 s i &&& v30885 s i := by
      intro matched
      have opcode := opcode_of_mask (v30884 s i) (v30885 s i) (v30883 s i) (by unfold v30885; decide) matched
      rw [atomic] at opcode
      have different : BitVec.extractLsb' 0 7 (v30883 s i) ≠ (47 : BitVec 7) := by unfold v30883; decide
      exact different opcode.symm
    exact if_neg miss
  have hv30891 : v30891 s i = 0 := by
    have miss : v30888 s i ≠ v30884 s i &&& v30889 s i := by
      intro matched
      have opcode := opcode_of_mask (v30884 s i) (v30889 s i) (v30888 s i) (by unfold v30889; decide) matched
      rw [atomic] at opcode
      have different : BitVec.extractLsb' 0 7 (v30888 s i) ≠ (47 : BitVec 7) := by unfold v30888; decide
      exact different opcode.symm
    exact if_neg miss
  have hv30896 : v30896 s i = 0 := by
    have miss : v30893 s i ≠ v30884 s i &&& v30894 s i := by
      intro matched
      have opcode := opcode_of_mask (v30884 s i) (v30894 s i) (v30893 s i) (by unfold v30894; decide) matched
      rw [atomic] at opcode
      have different : BitVec.extractLsb' 0 7 (v30893 s i) ≠ (47 : BitVec 7) := by unfold v30893; decide
      exact different opcode.symm
    exact if_neg miss
  have hv30901 : v30901 s i = 0 := by
    have miss : v30898 s i ≠ v30884 s i &&& v30899 s i := by
      intro matched
      have opcode := opcode_of_mask (v30884 s i) (v30899 s i) (v30898 s i) (by unfold v30899; decide) matched
      rw [atomic] at opcode
      have different : BitVec.extractLsb' 0 7 (v30898 s i) ≠ (47 : BitVec 7) := by unfold v30898; decide
      exact different opcode.symm
    exact if_neg miss
  have hv30906 : v30906 s i = 0 := by
    have miss : v30903 s i ≠ v30884 s i &&& v30904 s i := by
      intro matched
      have opcode := opcode_of_mask (v30884 s i) (v30904 s i) (v30903 s i) (by unfold v30904; decide) matched
      rw [atomic] at opcode
      have different : BitVec.extractLsb' 0 7 (v30903 s i) ≠ (47 : BitVec 7) := by unfold v30903; decide
      exact different opcode.symm
    exact if_neg miss
  have hv30911 : v30911 s i = 0 := by
    have miss : v30908 s i ≠ v30884 s i &&& v30909 s i := by
      intro matched
      have opcode := opcode_of_mask (v30884 s i) (v30909 s i) (v30908 s i) (by unfold v30909; decide) matched
      rw [atomic] at opcode
      have different : BitVec.extractLsb' 0 7 (v30908 s i) ≠ (47 : BitVec 7) := by unfold v30908; decide
      exact different opcode.symm
    exact if_neg miss
  have hv30915 : v30915 s i = 0 := by
    have miss : v30913 s i ≠ v30884 s i &&& v14809 s i := by
      intro matched
      have opcode := opcode_of_mask (v30884 s i) (v14809 s i) (v30913 s i) (by unfold v14809; decide) matched
      rw [atomic] at opcode
      have different : BitVec.extractLsb' 0 7 (v30913 s i) ≠ (47 : BitVec 7) := by unfold v30913; decide
      exact different opcode.symm
    exact if_neg miss
  have hv30919 : v30919 s i = 0 := by
    have miss : v30917 s i ≠ v30884 s i &&& v14809 s i := by
      intro matched
      have opcode := opcode_of_mask (v30884 s i) (v14809 s i) (v30917 s i) (by unfold v14809; decide) matched
      rw [atomic] at opcode
      have different : BitVec.extractLsb' 0 7 (v30917 s i) ≠ (47 : BitVec 7) := by unfold v30917; decide
      exact different opcode.symm
    exact if_neg miss
  have hv30923 : v30923 s i = 0 := by
    have miss : v30921 s i ≠ v30884 s i &&& v14809 s i := by
      intro matched
      have opcode := opcode_of_mask (v30884 s i) (v14809 s i) (v30921 s i) (by unfold v14809; decide) matched
      rw [atomic] at opcode
      have different : BitVec.extractLsb' 0 7 (v30921 s i) ≠ (47 : BitVec 7) := by unfold v30921; decide
      exact different opcode.symm
    exact if_neg miss
  have hv30928 : v30928 s i = 0 := by
    have miss : v30925 s i ≠ v30884 s i &&& v30926 s i := by
      intro matched
      have opcode := opcode_of_mask (v30884 s i) (v30926 s i) (v30925 s i) (by unfold v30926; decide) matched
      rw [atomic] at opcode
      have different : BitVec.extractLsb' 0 7 (v30925 s i) ≠ (47 : BitVec 7) := by unfold v30925; decide
      exact different opcode.symm
    exact if_neg miss
  have hv30933 : v30933 s i = 0 := by
    have miss : v30930 s i ≠ v30884 s i &&& v30931 s i := by
      intro matched
      have opcode := opcode_of_mask (v30884 s i) (v30931 s i) (v30930 s i) (by unfold v30931; decide) matched
      rw [atomic] at opcode
      have different : BitVec.extractLsb' 0 7 (v30930 s i) ≠ (47 : BitVec 7) := by unfold v30930; decide
      exact different opcode.symm
    exact if_neg miss
  have hv30938 : v30938 s i = 0 := by
    have miss : v30935 s i ≠ v30884 s i &&& v30936 s i := by
      intro matched
      have opcode := opcode_of_mask (v30884 s i) (v30936 s i) (v30935 s i) (by unfold v30936; decide) matched
      rw [atomic] at opcode
      have different : BitVec.extractLsb' 0 7 (v30935 s i) ≠ (47 : BitVec 7) := by unfold v30935; decide
      exact different opcode.symm
    exact if_neg miss
  have hv30942 : v30942 s i = 0 := by
    have miss : v30940 s i ≠ v30884 s i &&& v14576 s i := by
      intro matched
      have opcode := opcode_of_mask (v30884 s i) (v14576 s i) (v30940 s i) (by unfold v14576; decide) matched
      rw [atomic] at opcode
      have different : BitVec.extractLsb' 0 7 (v30940 s i) ≠ (47 : BitVec 7) := by unfold v30940; decide
      exact different opcode.symm
    exact if_neg miss
  have hv30946 : v30946 s i = 0 := by
    have miss : v30944 s i ≠ v30884 s i &&& v14576 s i := by
      intro matched
      have opcode := opcode_of_mask (v30884 s i) (v14576 s i) (v30944 s i) (by unfold v14576; decide) matched
      rw [atomic] at opcode
      have different : BitVec.extractLsb' 0 7 (v30944 s i) ≠ (47 : BitVec 7) := by unfold v30944; decide
      exact different opcode.symm
    exact if_neg miss
  have hv30950 : v30950 s i = 0 := by
    have miss : v30948 s i ≠ v30884 s i &&& v14576 s i := by
      intro matched
      have opcode := opcode_of_mask (v30884 s i) (v14576 s i) (v30948 s i) (by unfold v14576; decide) matched
      rw [atomic] at opcode
      have different : BitVec.extractLsb' 0 7 (v30948 s i) ≠ (47 : BitVec 7) := by unfold v30948; decide
      exact different opcode.symm
    exact if_neg miss
  have hv30954 : v30954 s i = 0 := by
    have miss : v30952 s i ≠ v30884 s i &&& v14576 s i := by
      intro matched
      have opcode := opcode_of_mask (v30884 s i) (v14576 s i) (v30952 s i) (by unfold v14576; decide) matched
      rw [atomic] at opcode
      have different : BitVec.extractLsb' 0 7 (v30952 s i) ≠ (47 : BitVec 7) := by unfold v30952; decide
      exact different opcode.symm
    exact if_neg miss
  have hv30959 : v30959 s i = 0 := by
    have miss : v30956 s i ≠ v30884 s i &&& v30957 s i := by
      intro matched
      have opcode := opcode_of_mask (v30884 s i) (v30957 s i) (v30956 s i) (by unfold v30957; decide) matched
      rw [atomic] at opcode
      have different : BitVec.extractLsb' 0 7 (v30956 s i) ≠ (47 : BitVec 7) := by unfold v30956; decide
      exact different opcode.symm
    exact if_neg miss
  have hv30963 : v30963 s i = 0 := by
    have miss : v30960 s i ≠ v30884 s i &&& v30961 s i := by
      intro matched
      have opcode := opcode_of_mask (v30884 s i) (v30961 s i) (v30960 s i) (by unfold v30961; decide) matched
      rw [atomic] at opcode
      have different : BitVec.extractLsb' 0 7 (v30960 s i) ≠ (47 : BitVec 7) := by unfold v30960; decide
      exact different opcode.symm
    exact if_neg miss
  have hv30968 : v30968 s i = 0 := by
    have miss : v30965 s i ≠ v30884 s i &&& v30966 s i := by
      intro matched
      have opcode := opcode_of_mask (v30884 s i) (v30966 s i) (v30965 s i) (by unfold v30966; decide) matched
      rw [atomic] at opcode
      have different : BitVec.extractLsb' 0 7 (v30965 s i) ≠ (47 : BitVec 7) := by unfold v30965; decide
      exact different opcode.symm
    exact if_neg miss
  have hv30973 : v30973 s i = 0 := by
    have miss : v30970 s i ≠ v30884 s i &&& v30971 s i := by
      intro matched
      have opcode := opcode_of_mask (v30884 s i) (v30971 s i) (v30970 s i) (by unfold v30971; decide) matched
      rw [atomic] at opcode
      have different : BitVec.extractLsb' 0 7 (v30970 s i) ≠ (47 : BitVec 7) := by unfold v30970; decide
      exact different opcode.symm
    exact if_neg miss
  have hv30978 : v30978 s i = 0 := by
    have miss : v30975 s i ≠ v30884 s i &&& v30976 s i := by
      intro matched
      have opcode := opcode_of_mask (v30884 s i) (v30976 s i) (v30975 s i) (by unfold v30976; decide) matched
      rw [atomic] at opcode
      have different : BitVec.extractLsb' 0 7 (v30975 s i) ≠ (47 : BitVec 7) := by unfold v30975; decide
      exact different opcode.symm
    exact if_neg miss
  have hv30983 : v30983 s i = 0 := by
    have miss : v30980 s i ≠ v30884 s i &&& v30981 s i := by
      intro matched
      have opcode := opcode_of_mask (v30884 s i) (v30981 s i) (v30980 s i) (by unfold v30981; decide) matched
      rw [atomic] at opcode
      have different : BitVec.extractLsb' 0 7 (v30980 s i) ≠ (47 : BitVec 7) := by unfold v30980; decide
      exact different opcode.symm
    exact if_neg miss
  have hv30988 : v30988 s i = 0 := by
    have miss : v30985 s i ≠ v30884 s i &&& v30986 s i := by
      intro matched
      have opcode := opcode_of_mask (v30884 s i) (v30986 s i) (v30985 s i) (by unfold v30986; decide) matched
      rw [atomic] at opcode
      have different : BitVec.extractLsb' 0 7 (v30985 s i) ≠ (47 : BitVec 7) := by unfold v30985; decide
      exact different opcode.symm
    exact if_neg miss
  have hv30993 : v30993 s i = 0 := by
    have miss : v30990 s i ≠ v30884 s i &&& v30991 s i := by
      intro matched
      have opcode := opcode_of_mask (v30884 s i) (v30991 s i) (v30990 s i) (by unfold v30991; decide) matched
      rw [atomic] at opcode
      have different : BitVec.extractLsb' 0 7 (v30990 s i) ≠ (47 : BitVec 7) := by unfold v30990; decide
      exact different opcode.symm
    exact if_neg miss
  have hv30998 : v30998 s i = 0 := by
    have miss : v30995 s i ≠ v30884 s i &&& v30996 s i := by
      intro matched
      have opcode := opcode_of_mask (v30884 s i) (v30996 s i) (v30995 s i) (by unfold v30996; decide) matched
      rw [atomic] at opcode
      have different : BitVec.extractLsb' 0 7 (v30995 s i) ≠ (47 : BitVec 7) := by unfold v30995; decide
      exact different opcode.symm
    exact if_neg miss
  have hv31003 : v31003 s i = 0 := by
    have miss : v31000 s i ≠ v30884 s i &&& v31001 s i := by
      intro matched
      have opcode := opcode_of_mask (v30884 s i) (v31001 s i) (v31000 s i) (by unfold v31001; decide) matched
      rw [atomic] at opcode
      have different : BitVec.extractLsb' 0 7 (v31000 s i) ≠ (47 : BitVec 7) := by unfold v31000; decide
      exact different opcode.symm
    exact if_neg miss
  have hv31008 : v31008 s i = 0 := by
    have miss : v31005 s i ≠ v30884 s i &&& v31006 s i := by
      intro matched
      have opcode := opcode_of_mask (v30884 s i) (v31006 s i) (v31005 s i) (by unfold v31006; decide) matched
      rw [atomic] at opcode
      have different : BitVec.extractLsb' 0 7 (v31005 s i) ≠ (47 : BitVec 7) := by unfold v31005; decide
      exact different opcode.symm
    exact if_neg miss
  have hv31013 : v31013 s i = 0 := by
    have miss : v31011 s i ≠ v30884 s i &&& v14576 s i := by
      intro matched
      have opcode := opcode_of_mask (v30884 s i) (v14576 s i) (v31011 s i) (by unfold v14576; decide) matched
      rw [atomic] at opcode
      have different : BitVec.extractLsb' 0 7 (v31011 s i) ≠ (47 : BitVec 7) := by unfold v31011; decide
      exact different opcode.symm
    exact if_neg miss
  have hv31016 : v31016 s i = 0 := by
    have miss : v31014 s i ≠ v30884 s i &&& v14576 s i := by
      intro matched
      have opcode := opcode_of_mask (v30884 s i) (v14576 s i) (v31014 s i) (by unfold v14576; decide) matched
      rw [atomic] at opcode
      have different : BitVec.extractLsb' 0 7 (v31014 s i) ≠ (47 : BitVec 7) := by unfold v31014; decide
      exact different opcode.symm
    exact if_neg miss
  have hv31020 : v31020 s i = 0 := by
    have miss : v31018 s i ≠ v30884 s i &&& v14576 s i := by
      intro matched
      have opcode := opcode_of_mask (v30884 s i) (v14576 s i) (v31018 s i) (by unfold v14576; decide) matched
      rw [atomic] at opcode
      have different : BitVec.extractLsb' 0 7 (v31018 s i) ≠ (47 : BitVec 7) := by unfold v31018; decide
      exact different opcode.symm
    exact if_neg miss
  have hv31024 : v31024 s i = 0 := by
    have miss : v31022 s i ≠ v30884 s i &&& v14576 s i := by
      intro matched
      have opcode := opcode_of_mask (v30884 s i) (v14576 s i) (v31022 s i) (by unfold v14576; decide) matched
      rw [atomic] at opcode
      have different : BitVec.extractLsb' 0 7 (v31022 s i) ≠ (47 : BitVec 7) := by unfold v31022; decide
      exact different opcode.symm
    exact if_neg miss
  have hv31028 : v31028 s i = 0 := by
    have miss : v31026 s i ≠ v30884 s i &&& v14576 s i := by
      intro matched
      have opcode := opcode_of_mask (v30884 s i) (v14576 s i) (v31026 s i) (by unfold v14576; decide) matched
      rw [atomic] at opcode
      have different : BitVec.extractLsb' 0 7 (v31026 s i) ≠ (47 : BitVec 7) := by unfold v31026; decide
      exact different opcode.symm
    exact if_neg miss
  have hv31032 : v31032 s i = 0 := by
    have miss : v31030 s i ≠ v30884 s i &&& v14576 s i := by
      intro matched
      have opcode := opcode_of_mask (v30884 s i) (v14576 s i) (v31030 s i) (by unfold v14576; decide) matched
      rw [atomic] at opcode
      have different : BitVec.extractLsb' 0 7 (v31030 s i) ≠ (47 : BitVec 7) := by unfold v31030; decide
      exact different opcode.symm
    exact if_neg miss
  have hv31036 : v31036 s i = 0 := by
    have miss : v31034 s i ≠ v30884 s i &&& v14576 s i := by
      intro matched
      have opcode := opcode_of_mask (v30884 s i) (v14576 s i) (v31034 s i) (by unfold v14576; decide) matched
      rw [atomic] at opcode
      have different : BitVec.extractLsb' 0 7 (v31034 s i) ≠ (47 : BitVec 7) := by unfold v31034; decide
      exact different opcode.symm
    exact if_neg miss
  have hv31040 : v31040 s i = 0 := by
    have miss : v31038 s i ≠ v30884 s i &&& v14576 s i := by
      intro matched
      have opcode := opcode_of_mask (v30884 s i) (v14576 s i) (v31038 s i) (by unfold v14576; decide) matched
      rw [atomic] at opcode
      have different : BitVec.extractLsb' 0 7 (v31038 s i) ≠ (47 : BitVec 7) := by unfold v31038; decide
      exact different opcode.symm
    exact if_neg miss
  have hv31044 : v31044 s i = 0 := by
    have miss : v31042 s i ≠ v30884 s i &&& v14576 s i := by
      intro matched
      have opcode := opcode_of_mask (v30884 s i) (v14576 s i) (v31042 s i) (by unfold v14576; decide) matched
      rw [atomic] at opcode
      have different : BitVec.extractLsb' 0 7 (v31042 s i) ≠ (47 : BitVec 7) := by unfold v31042; decide
      exact different opcode.symm
    exact if_neg miss
  have hv31048 : v31048 s i = 0 := by
    have miss : v31046 s i ≠ v30884 s i &&& v14576 s i := by
      intro matched
      have opcode := opcode_of_mask (v30884 s i) (v14576 s i) (v31046 s i) (by unfold v14576; decide) matched
      rw [atomic] at opcode
      have different : BitVec.extractLsb' 0 7 (v31046 s i) ≠ (47 : BitVec 7) := by unfold v31046; decide
      exact different opcode.symm
    exact if_neg miss
  have hv31054 : v31054 s i = 0 := by
    have miss : v31051 s i ≠ v30884 s i &&& v31052 s i := by
      intro matched
      have opcode := opcode_of_mask (v30884 s i) (v31052 s i) (v31051 s i) (by unfold v31052; decide) matched
      rw [atomic] at opcode
      have different : BitVec.extractLsb' 0 7 (v31051 s i) ≠ (47 : BitVec 7) := by unfold v31051; decide
      exact different opcode.symm
    exact if_neg miss
  have hv31058 : v31058 s i = 0 := by
    have miss : v31055 s i ≠ v30884 s i &&& v31056 s i := by
      intro matched
      have opcode := opcode_of_mask (v30884 s i) (v31056 s i) (v31055 s i) (by unfold v31056; decide) matched
      rw [atomic] at opcode
      have different : BitVec.extractLsb' 0 7 (v31055 s i) ≠ (47 : BitVec 7) := by unfold v31055; decide
      exact different opcode.symm
    exact if_neg miss
  have hv31063 : v31063 s i = 0 := by
    have miss : v31060 s i ≠ v30884 s i &&& v31061 s i := by
      intro matched
      have opcode := opcode_of_mask (v30884 s i) (v31061 s i) (v31060 s i) (by unfold v31061; decide) matched
      rw [atomic] at opcode
      have different : BitVec.extractLsb' 0 7 (v31060 s i) ≠ (47 : BitVec 7) := by unfold v31060; decide
      exact different opcode.symm
    exact if_neg miss
  have hv31068 : v31068 s i = 0 := by
    have miss : v31065 s i ≠ v30884 s i &&& v31066 s i := by
      intro matched
      have opcode := opcode_of_mask (v30884 s i) (v31066 s i) (v31065 s i) (by unfold v31066; decide) matched
      rw [atomic] at opcode
      have different : BitVec.extractLsb' 0 7 (v31065 s i) ≠ (47 : BitVec 7) := by unfold v31065; decide
      exact different opcode.symm
    exact if_neg miss
  have hv31073 : v31073 s i = 0 := by
    have miss : v31070 s i ≠ v30884 s i &&& v31071 s i := by
      intro matched
      have opcode := opcode_of_mask (v30884 s i) (v31071 s i) (v31070 s i) (by unfold v31071; decide) matched
      rw [atomic] at opcode
      have different : BitVec.extractLsb' 0 7 (v31070 s i) ≠ (47 : BitVec 7) := by unfold v31070; decide
      exact different opcode.symm
    exact if_neg miss
  have hv31078 : v31078 s i = 0 := by
    have miss : v31075 s i ≠ v30884 s i &&& v31076 s i := by
      intro matched
      have opcode := opcode_of_mask (v30884 s i) (v31076 s i) (v31075 s i) (by unfold v31076; decide) matched
      rw [atomic] at opcode
      have different : BitVec.extractLsb' 0 7 (v31075 s i) ≠ (47 : BitVec 7) := by unfold v31075; decide
      exact different opcode.symm
    exact if_neg miss
  have hv31083 : v31083 s i = 0 := by
    have miss : v31080 s i ≠ v30884 s i &&& v31081 s i := by
      intro matched
      have opcode := opcode_of_mask (v30884 s i) (v31081 s i) (v31080 s i) (by unfold v31081; decide) matched
      rw [atomic] at opcode
      have different : BitVec.extractLsb' 0 7 (v31080 s i) ≠ (47 : BitVec 7) := by unfold v31080; decide
      exact different opcode.symm
    exact if_neg miss
  have hv31088 : v31088 s i = 0 := by
    have miss : v31085 s i ≠ v30884 s i &&& v31086 s i := by
      intro matched
      have opcode := opcode_of_mask (v30884 s i) (v31086 s i) (v31085 s i) (by unfold v31086; decide) matched
      rw [atomic] at opcode
      have different : BitVec.extractLsb' 0 7 (v31085 s i) ≠ (47 : BitVec 7) := by unfold v31085; decide
      exact different opcode.symm
    exact if_neg miss
  simp [v31090, v31050, v31010, v30955, v30951, v30947, v30943, v30939, v30934, v30929, v30924, v30920, v30916, v30912, v30907, v30902, v30897, v30892, v31009, v31004, v30999, v30994, v30989, v30984, v30979, v30974, v30969, v30964, v31049, v31045, v31041, v31037, v31033, v31029, v31025, v31021, v31017, v31089, v31084, v31079, v31074, v31069, v31064, v31059, hv30887, hv30891, hv30896, hv30901, hv30906, hv30911, hv30915, hv30919, hv30923, hv30928, hv30933, hv30938, hv30942, hv30946, hv30950, hv30954, hv30959, hv30963, hv30968, hv30973, hv30978, hv30983, hv30988, hv30993, hv30998, hv31003, hv31008, hv31013, hv31016, hv31020, hv31024, hv31028, hv31032, hv31036, hv31040, hv31044, hv31048, hv31054, hv31058, hv31063, hv31068, hv31073, hv31078, hv31083, hv31088]

theorem original_whitelist_excludes_atomic (s : State) (i : Inputs)
    (environment : assumes s i) (reset : i.g0.nreset = 0)
    (valid : v10100 s i = 1) : BitVec.extractLsb' 0 7 (v30884 s i) ≠ 47 := by
  have all : (assumptionChecks0 s i).all id = true := environment
  simp only [assumptionChecks0, List.all_cons, List.all_nil, Bool.and_eq_true,
    Bool.true_and, Bool.and_true] at all
  have check : v31092 s i ≠ 1 ∨ v31090 s i = 1 := of_decide_eq_true all.1
  have gate : v31092 s i = 1 := by
    simp [v31092, v31091, v0, v24, reset, valid]
  have allowed := check.resolve_left (not_not_intro gate)
  intro atomic
  have rejected := atomic_opcode_rejected_by_whitelist s i atomic
  rw [rejected] at allowed
  contradiction

#print axioms atomic_opcode_rejected_by_whitelist
#print axioms original_whitelist_excludes_atomic
end NutShellProofs

import Proofs.DecodeBits
import Proofs.RegisterReads2
namespace NutShellProofs
open nNutCore
set_option maxHeartbeats 1000000
theorem reference_lui_rs1_address (s : State) (i : Inputs)
    (lui : BitVec.extractLsb' 0 7 (v14575 s i) = 55) : v15551 s i = 0 := by
  have hv14583 : v14583 s i = 0 := by
    have miss : v14580 s i ≠ v14582 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v14581 s i) (v14580 s i) (by unfold v14581; decide) matched
      have val : BitVec.extractLsb' 0 7 (v14580 s i) = 115 := by unfold v14580; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 115) op
    rw [v14583, if_neg miss]
  have hv14589 : v14589 s i = 0 := by
    have miss : v14588 s i ≠ v14575 s i := by
      intro matched
      have op := (congrArg (BitVec.extractLsb' 0 7) matched).symm
      have val : BitVec.extractLsb' 0 7 (v14588 s i) = 115 := by unfold v14588; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 115) op
    rw [v14589, if_neg miss]
  have hv14595 : v14595 s i = 0 := by
    have miss : v14594 s i ≠ v14575 s i := by
      intro matched
      have op := (congrArg (BitVec.extractLsb' 0 7) matched).symm
      have val : BitVec.extractLsb' 0 7 (v14594 s i) = 115 := by unfold v14594; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 115) op
    rw [v14595, if_neg miss]
  have hv14601 : v14601 s i = 0 := by
    have miss : v14600 s i ≠ v14575 s i := by
      intro matched
      have op := (congrArg (BitVec.extractLsb' 0 7) matched).symm
      have val : BitVec.extractLsb' 0 7 (v14600 s i) = 115 := by unfold v14600; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 115) op
    rw [v14601, if_neg miss]
  have hv14578 : v14578 s i = 0 := by
    have miss : v14568 s i ≠ v14577 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v14576 s i) (v14568 s i) (by unfold v14576; decide) matched
      have val : BitVec.extractLsb' 0 7 (v14568 s i) = 59 := by unfold v14568; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 59) op
    rw [v14578, if_neg miss]
  have hv14613 : v14613 s i = 0 := by
    have miss : v14611 s i ≠ v14612 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v14576 s i) (v14611 s i) (by unfold v14576; decide) matched
      have val : BitVec.extractLsb' 0 7 (v14611 s i) = 59 := by unfold v14611; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 59) op
    rw [v14613, if_neg miss]
  have hv14621 : v14621 s i = 0 := by
    have miss : v14619 s i ≠ v14620 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v14576 s i) (v14619 s i) (by unfold v14576; decide) matched
      have val : BitVec.extractLsb' 0 7 (v14619 s i) = 59 := by unfold v14619; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 59) op
    rw [v14621, if_neg miss]
  have hv14629 : v14629 s i = 0 := by
    have miss : v14627 s i ≠ v14628 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v14576 s i) (v14627 s i) (by unfold v14576; decide) matched
      have val : BitVec.extractLsb' 0 7 (v14627 s i) = 59 := by unfold v14627; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 59) op
    rw [v14629, if_neg miss]
  have hv14637 : v14637 s i = 0 := by
    have miss : v14635 s i ≠ v14636 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v14576 s i) (v14635 s i) (by unfold v14576; decide) matched
      have val : BitVec.extractLsb' 0 7 (v14635 s i) = 59 := by unfold v14635; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 59) op
    rw [v14637, if_neg miss]
  have hv14645 : v14645 s i = 0 := by
    have miss : v14643 s i ≠ v14644 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v14576 s i) (v14643 s i) (by unfold v14576; decide) matched
      have val : BitVec.extractLsb' 0 7 (v14643 s i) = 51 := by unfold v14643; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 51) op
    rw [v14645, if_neg miss]
  have hv14653 : v14653 s i = 0 := by
    have miss : v14651 s i ≠ v14652 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v14576 s i) (v14651 s i) (by unfold v14576; decide) matched
      have val : BitVec.extractLsb' 0 7 (v14651 s i) = 51 := by unfold v14651; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 51) op
    rw [v14653, if_neg miss]
  have hv14661 : v14661 s i = 0 := by
    have miss : v14659 s i ≠ v14660 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v14576 s i) (v14659 s i) (by unfold v14576; decide) matched
      have val : BitVec.extractLsb' 0 7 (v14659 s i) = 51 := by unfold v14659; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 51) op
    rw [v14661, if_neg miss]
  have hv14669 : v14669 s i = 0 := by
    have miss : v14667 s i ≠ v14668 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v14576 s i) (v14667 s i) (by unfold v14576; decide) matched
      have val : BitVec.extractLsb' 0 7 (v14667 s i) = 51 := by unfold v14667; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 51) op
    rw [v14669, if_neg miss]
  have hv14677 : v14677 s i = 0 := by
    have miss : v14675 s i ≠ v14676 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v14576 s i) (v14675 s i) (by unfold v14576; decide) matched
      have val : BitVec.extractLsb' 0 7 (v14675 s i) = 51 := by unfold v14675; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 51) op
    rw [v14677, if_neg miss]
  have hv14685 : v14685 s i = 0 := by
    have miss : v14683 s i ≠ v14684 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v14576 s i) (v14683 s i) (by unfold v14576; decide) matched
      have val : BitVec.extractLsb' 0 7 (v14683 s i) = 51 := by unfold v14683; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 51) op
    rw [v14685, if_neg miss]
  have hv14693 : v14693 s i = 0 := by
    have miss : v14691 s i ≠ v14692 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v14576 s i) (v14691 s i) (by unfold v14576; decide) matched
      have val : BitVec.extractLsb' 0 7 (v14691 s i) = 51 := by unfold v14691; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 51) op
    rw [v14693, if_neg miss]
  have hv14701 : v14701 s i = 0 := by
    have miss : v14699 s i ≠ v14700 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v14576 s i) (v14699 s i) (by unfold v14576; decide) matched
      have val : BitVec.extractLsb' 0 7 (v14699 s i) = 51 := by unfold v14699; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 51) op
    rw [v14701, if_neg miss]
  have hv15160 : v15160 s i = 0 := by
    have miss : v15157 s i ≠ v15159 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v15158 s i) (v15157 s i) (by unfold v15158; decide) matched
      have val : BitVec.extractLsb' 0 7 (v15157 s i) = 35 := by unfold v15157; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 35) op
    rw [v15160, if_neg miss]
  have hv14710 : v14710 s i = 0 := by
    have miss : v14707 s i ≠ v14709 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v14708 s i) (v14707 s i) (by unfold v14708; decide) matched
      have val : BitVec.extractLsb' 0 7 (v14707 s i) = 3 := by unfold v14707; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 3) op
    rw [v14710, if_neg miss]
  have hv14718 : v14718 s i = 0 := by
    have miss : v14715 s i ≠ v14717 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v14716 s i) (v14715 s i) (by unfold v14716; decide) matched
      have val : BitVec.extractLsb' 0 7 (v14715 s i) = 3 := by unfold v14715; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 3) op
    rw [v14718, if_neg miss]
  have hv14725 : v14725 s i = 0 := by
    have miss : v14723 s i ≠ v14724 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v14576 s i) (v14723 s i) (by unfold v14576; decide) matched
      have val : BitVec.extractLsb' 0 7 (v14723 s i) = 59 := by unfold v14723; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 59) op
    rw [v14725, if_neg miss]
  have hv14733 : v14733 s i = 0 := by
    have miss : v14731 s i ≠ v14732 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v14576 s i) (v14731 s i) (by unfold v14576; decide) matched
      have val : BitVec.extractLsb' 0 7 (v14731 s i) = 59 := by unfold v14731; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 59) op
    rw [v14733, if_neg miss]
  have hv14741 : v14741 s i = 0 := by
    have miss : v14739 s i ≠ v14740 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v14576 s i) (v14739 s i) (by unfold v14576; decide) matched
      have val : BitVec.extractLsb' 0 7 (v14739 s i) = 59 := by unfold v14739; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 59) op
    rw [v14741, if_neg miss]
  have hv14749 : v14749 s i = 0 := by
    have miss : v14747 s i ≠ v14748 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v14576 s i) (v14747 s i) (by unfold v14576; decide) matched
      have val : BitVec.extractLsb' 0 7 (v14747 s i) = 59 := by unfold v14747; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 59) op
    rw [v14749, if_neg miss]
  have hv14757 : v14757 s i = 0 := by
    have miss : v14755 s i ≠ v14756 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v14576 s i) (v14755 s i) (by unfold v14576; decide) matched
      have val : BitVec.extractLsb' 0 7 (v14755 s i) = 59 := by unfold v14755; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 59) op
    rw [v14757, if_neg miss]
  have hv14765 : v14765 s i = 0 := by
    have miss : v14763 s i ≠ v14764 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v14576 s i) (v14763 s i) (by unfold v14576; decide) matched
      have val : BitVec.extractLsb' 0 7 (v14763 s i) = 51 := by unfold v14763; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 51) op
    rw [v14765, if_neg miss]
  have hv14773 : v14773 s i = 0 := by
    have miss : v14771 s i ≠ v14772 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v14576 s i) (v14771 s i) (by unfold v14576; decide) matched
      have val : BitVec.extractLsb' 0 7 (v14771 s i) = 51 := by unfold v14771; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 51) op
    rw [v14773, if_neg miss]
  have hv14781 : v14781 s i = 0 := by
    have miss : v14779 s i ≠ v14780 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v14576 s i) (v14779 s i) (by unfold v14576; decide) matched
      have val : BitVec.extractLsb' 0 7 (v14779 s i) = 51 := by unfold v14779; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 51) op
    rw [v14781, if_neg miss]
  have hv14789 : v14789 s i = 0 := by
    have miss : v14787 s i ≠ v14788 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v14576 s i) (v14787 s i) (by unfold v14576; decide) matched
      have val : BitVec.extractLsb' 0 7 (v14787 s i) = 27 := by unfold v14787; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 27) op
    rw [v14789, if_neg miss]
  have hv14796 : v14796 s i = 0 := by
    have miss : v14794 s i ≠ v14795 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v14576 s i) (v14794 s i) (by unfold v14576; decide) matched
      have val : BitVec.extractLsb' 0 7 (v14794 s i) = 27 := by unfold v14794; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 27) op
    rw [v14796, if_neg miss]
  have hv14803 : v14803 s i = 0 := by
    have miss : v14801 s i ≠ v14802 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v14576 s i) (v14801 s i) (by unfold v14576; decide) matched
      have val : BitVec.extractLsb' 0 7 (v14801 s i) = 27 := by unfold v14801; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 27) op
    rw [v14803, if_neg miss]
  have hv14811 : v14811 s i = 0 := by
    have miss : v14808 s i ≠ v14810 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v14809 s i) (v14808 s i) (by unfold v14809; decide) matched
      have val : BitVec.extractLsb' 0 7 (v14808 s i) = 19 := by unfold v14808; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 19) op
    rw [v14811, if_neg miss]
  have hv14818 : v14818 s i = 0 := by
    have miss : v14816 s i ≠ v14817 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v14809 s i) (v14816 s i) (by unfold v14809; decide) matched
      have val : BitVec.extractLsb' 0 7 (v14816 s i) = 19 := by unfold v14816; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 19) op
    rw [v14818, if_neg miss]
  have hv14825 : v14825 s i = 0 := by
    have miss : v14823 s i ≠ v14824 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v14809 s i) (v14823 s i) (by unfold v14809; decide) matched
      have val : BitVec.extractLsb' 0 7 (v14823 s i) = 19 := by unfold v14823; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 19) op
    rw [v14825, if_neg miss]
  have hv14833 : v14833 s i = 0 := by
    have miss : v14830 s i ≠ v14832 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v14831 s i) (v14830 s i) (by unfold v14831; decide) matched
      have val : BitVec.extractLsb' 0 7 (v14830 s i) = 27 := by unfold v14830; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 27) op
    rw [v14833, if_neg miss]
  have hv14841 : v14841 s i = 0 := by
    have miss : v14838 s i ≠ v14840 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v14839 s i) (v14838 s i) (by unfold v14839; decide) matched
      have val : BitVec.extractLsb' 0 7 (v14838 s i) = 15 := by unfold v14838; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 15) op
    rw [v14841, if_neg miss]
  have hv14847 : v14847 s i = 0 := by
    have miss : v14846 s i ≠ v14575 s i := by
      intro matched
      have op := (congrArg (BitVec.extractLsb' 0 7) matched).symm
      have val : BitVec.extractLsb' 0 7 (v14846 s i) = 115 := by unfold v14846; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 115) op
    rw [v14847, if_neg miss]
  have hv14853 : v14853 s i = 0 := by
    have miss : v14852 s i ≠ v14575 s i := by
      intro matched
      have op := (congrArg (BitVec.extractLsb' 0 7) matched).symm
      have val : BitVec.extractLsb' 0 7 (v14852 s i) = 115 := by unfold v14852; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 115) op
    rw [v14853, if_neg miss]
  have hv15174 : v15174 s i = 0 := by
    have miss : v15171 s i ≠ v15173 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v15172 s i) (v15171 s i) (by unfold v15172; decide) matched
      have val : BitVec.extractLsb' 0 7 (v15171 s i) = 35 := by unfold v15171; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 35) op
    rw [v15174, if_neg miss]
  have hv15180 : v15180 s i = 0 := by
    have miss : v15177 s i ≠ v15179 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v15178 s i) (v15177 s i) (by unfold v15178; decide) matched
      have val : BitVec.extractLsb' 0 7 (v15177 s i) = 35 := by unfold v15177; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 35) op
    rw [v15180, if_neg miss]
  have hv15186 : v15186 s i = 0 := by
    have miss : v15183 s i ≠ v15185 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v15184 s i) (v15183 s i) (by unfold v15184; decide) matched
      have val : BitVec.extractLsb' 0 7 (v15183 s i) = 35 := by unfold v15183; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 35) op
    rw [v15186, if_neg miss]
  have hv14861 : v14861 s i = 0 := by
    have miss : v14858 s i ≠ v14860 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v14859 s i) (v14858 s i) (by unfold v14859; decide) matched
      have val : BitVec.extractLsb' 0 7 (v14858 s i) = 3 := by unfold v14858; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 3) op
    rw [v14861, if_neg miss]
  have hv14869 : v14869 s i = 0 := by
    have miss : v14866 s i ≠ v14868 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v14867 s i) (v14866 s i) (by unfold v14867; decide) matched
      have val : BitVec.extractLsb' 0 7 (v14866 s i) = 3 := by unfold v14866; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 3) op
    rw [v14869, if_neg miss]
  have hv14877 : v14877 s i = 0 := by
    have miss : v14874 s i ≠ v14876 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v14875 s i) (v14874 s i) (by unfold v14875; decide) matched
      have val : BitVec.extractLsb' 0 7 (v14874 s i) = 3 := by unfold v14874; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 3) op
    rw [v14877, if_neg miss]
  have hv14885 : v14885 s i = 0 := by
    have miss : v14882 s i ≠ v14884 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v14883 s i) (v14882 s i) (by unfold v14883; decide) matched
      have val : BitVec.extractLsb' 0 7 (v14882 s i) = 3 := by unfold v14882; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 3) op
    rw [v14885, if_neg miss]
  have hv14893 : v14893 s i = 0 := by
    have miss : v14890 s i ≠ v14892 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v14891 s i) (v14890 s i) (by unfold v14891; decide) matched
      have val : BitVec.extractLsb' 0 7 (v14890 s i) = 3 := by unfold v14890; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 3) op
    rw [v14893, if_neg miss]
  have hv15192 : v15192 s i = 0 := by
    have miss : v15189 s i ≠ v15191 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v15190 s i) (v15189 s i) (by unfold v15190; decide) matched
      have val : BitVec.extractLsb' 0 7 (v15189 s i) = 99 := by unfold v15189; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 99) op
    rw [v15192, if_neg miss]
  have hv15199 : v15199 s i = 0 := by
    have miss : v15196 s i ≠ v15198 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v15197 s i) (v15196 s i) (by unfold v15197; decide) matched
      have val : BitVec.extractLsb' 0 7 (v15196 s i) = 99 := by unfold v15196; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 99) op
    rw [v15199, if_neg miss]
  have hv15206 : v15206 s i = 0 := by
    have miss : v15203 s i ≠ v15205 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v15204 s i) (v15203 s i) (by unfold v15204; decide) matched
      have val : BitVec.extractLsb' 0 7 (v15203 s i) = 99 := by unfold v15203; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 99) op
    rw [v15206, if_neg miss]
  have hv15213 : v15213 s i = 0 := by
    have miss : v15210 s i ≠ v15212 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v15211 s i) (v15210 s i) (by unfold v15211; decide) matched
      have val : BitVec.extractLsb' 0 7 (v15210 s i) = 99 := by unfold v15210; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 99) op
    rw [v15213, if_neg miss]
  have hv15220 : v15220 s i = 0 := by
    have miss : v15217 s i ≠ v15219 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v15218 s i) (v15217 s i) (by unfold v15218; decide) matched
      have val : BitVec.extractLsb' 0 7 (v15217 s i) = 99 := by unfold v15217; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 99) op
    rw [v15220, if_neg miss]
  have hv15227 : v15227 s i = 0 := by
    have miss : v15224 s i ≠ v15226 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v15225 s i) (v15224 s i) (by unfold v15225; decide) matched
      have val : BitVec.extractLsb' 0 7 (v15224 s i) = 99 := by unfold v15224; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 99) op
    rw [v15227, if_neg miss]
  have hv14901 : v14901 s i = 0 := by
    have miss : v14898 s i ≠ v14900 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v14899 s i) (v14898 s i) (by unfold v14899; decide) matched
      have val : BitVec.extractLsb' 0 7 (v14898 s i) = 103 := by unfold v14898; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 103) op
    rw [v14901, if_neg miss]
  have hv14917 : v14917 s i = 0 := by
    have miss : v14915 s i ≠ v14916 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v14576 s i) (v14915 s i) (by unfold v14576; decide) matched
      have val : BitVec.extractLsb' 0 7 (v14915 s i) = 51 := by unfold v14915; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 51) op
    rw [v14917, if_neg miss]
  have hv14925 : v14925 s i = 0 := by
    have miss : v14923 s i ≠ v14924 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v14576 s i) (v14923 s i) (by unfold v14576; decide) matched
      have val : BitVec.extractLsb' 0 7 (v14923 s i) = 51 := by unfold v14923; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 51) op
    rw [v14925, if_neg miss]
  have hv14933 : v14933 s i = 0 := by
    have miss : v14931 s i ≠ v14932 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v14576 s i) (v14931 s i) (by unfold v14576; decide) matched
      have val : BitVec.extractLsb' 0 7 (v14931 s i) = 51 := by unfold v14931; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 51) op
    rw [v14933, if_neg miss]
  have hv14941 : v14941 s i = 0 := by
    have miss : v14939 s i ≠ v14940 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v14576 s i) (v14939 s i) (by unfold v14576; decide) matched
      have val : BitVec.extractLsb' 0 7 (v14939 s i) = 51 := by unfold v14939; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 51) op
    rw [v14941, if_neg miss]
  have hv14949 : v14949 s i = 0 := by
    have miss : v14947 s i ≠ v14948 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v14576 s i) (v14947 s i) (by unfold v14576; decide) matched
      have val : BitVec.extractLsb' 0 7 (v14947 s i) = 51 := by unfold v14947; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 51) op
    rw [v14949, if_neg miss]
  have hv14957 : v14957 s i = 0 := by
    have miss : v14955 s i ≠ v14956 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v14576 s i) (v14955 s i) (by unfold v14576; decide) matched
      have val : BitVec.extractLsb' 0 7 (v14955 s i) = 51 := by unfold v14955; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 51) op
    rw [v14957, if_neg miss]
  have hv14965 : v14965 s i = 0 := by
    have miss : v14963 s i ≠ v14964 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v14576 s i) (v14963 s i) (by unfold v14576; decide) matched
      have val : BitVec.extractLsb' 0 7 (v14963 s i) = 51 := by unfold v14963; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 51) op
    rw [v14965, if_neg miss]
  have hv14973 : v14973 s i = 0 := by
    have miss : v14971 s i ≠ v14972 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v14576 s i) (v14971 s i) (by unfold v14576; decide) matched
      have val : BitVec.extractLsb' 0 7 (v14971 s i) = 51 := by unfold v14971; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 51) op
    rw [v14973, if_neg miss]
  have hv14981 : v14981 s i = 0 := by
    have miss : v14979 s i ≠ v14980 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v14576 s i) (v14979 s i) (by unfold v14576; decide) matched
      have val : BitVec.extractLsb' 0 7 (v14979 s i) = 51 := by unfold v14979; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 51) op
    rw [v14981, if_neg miss]
  have hv14989 : v14989 s i = 0 := by
    have miss : v14987 s i ≠ v14988 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v14576 s i) (v14987 s i) (by unfold v14576; decide) matched
      have val : BitVec.extractLsb' 0 7 (v14987 s i) = 51 := by unfold v14987; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 51) op
    rw [v14989, if_neg miss]
  have hv15009 : v15009 s i = 0 := by
    have miss : v15007 s i ≠ v15008 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v14809 s i) (v15007 s i) (by unfold v14809; decide) matched
      have val : BitVec.extractLsb' 0 7 (v15007 s i) = 19 := by unfold v15007; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 19) op
    rw [v15009, if_neg miss]
  have hv15016 : v15016 s i = 0 := by
    have miss : v15014 s i ≠ v15015 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v14809 s i) (v15014 s i) (by unfold v14809; decide) matched
      have val : BitVec.extractLsb' 0 7 (v15014 s i) = 19 := by unfold v15014; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 19) op
    rw [v15016, if_neg miss]
  have hv15023 : v15023 s i = 0 := by
    have miss : v15021 s i ≠ v15022 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v14809 s i) (v15021 s i) (by unfold v14809; decide) matched
      have val : BitVec.extractLsb' 0 7 (v15021 s i) = 19 := by unfold v15021; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 19) op
    rw [v15023, if_neg miss]
  have hv15031 : v15031 s i = 0 := by
    have miss : v15028 s i ≠ v15030 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v15029 s i) (v15028 s i) (by unfold v15029; decide) matched
      have val : BitVec.extractLsb' 0 7 (v15028 s i) = 19 := by unfold v15028; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 19) op
    rw [v15031, if_neg miss]
  have hv15039 : v15039 s i = 0 := by
    have miss : v15036 s i ≠ v15038 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v15037 s i) (v15036 s i) (by unfold v15037; decide) matched
      have val : BitVec.extractLsb' 0 7 (v15036 s i) = 19 := by unfold v15036; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 19) op
    rw [v15039, if_neg miss]
  have hv15047 : v15047 s i = 0 := by
    have miss : v15044 s i ≠ v15046 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v15045 s i) (v15044 s i) (by unfold v15045; decide) matched
      have val : BitVec.extractLsb' 0 7 (v15044 s i) = 19 := by unfold v15044; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 19) op
    rw [v15047, if_neg miss]
  have hv15055 : v15055 s i = 0 := by
    have miss : v15052 s i ≠ v15054 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v15053 s i) (v15052 s i) (by unfold v15053; decide) matched
      have val : BitVec.extractLsb' 0 7 (v15052 s i) = 19 := by unfold v15052; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 19) op
    rw [v15055, if_neg miss]
  have hv15063 : v15063 s i = 0 := by
    have miss : v15060 s i ≠ v15062 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v15061 s i) (v15060 s i) (by unfold v15061; decide) matched
      have val : BitVec.extractLsb' 0 7 (v15060 s i) = 19 := by unfold v15060; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 19) op
    rw [v15063, if_neg miss]
  have hv15071 : v15071 s i = 0 := by
    have miss : v15068 s i ≠ v15070 s i := by
      intro matched
      have op := opcode_of_mask (v14575 s i) (v15069 s i) (v15068 s i) (by unfold v15069; decide) matched
      have val : BitVec.extractLsb' 0 7 (v15068 s i) = 19 := by unfold v15068; decide
      rw [lui, val] at op
      exact (by decide : (55 : BitVec 7) ≠ 19) op
    rw [v15071, if_neg miss]
  have ne : (0 : BitVec 1) ≠ 1 := by decide
  simp only [v15551, v15550, v15549, v15548, v15547, v15546, v15545, v15544, v15543, v15542, v15541, v15540, v15539, v15538, v15537, v15536, v15535, v15534, v15533, v15532, v15531, v15530, v15529, v15528, v15527, v15526, v15525, v15524, v15523, v15522, v15521, v15520, v15519, v15518, v15517, v15516, v15515, v15514, v15513, v15512, v15511, v15510, v15509, v15508, v15507, v15506, v15505, v15504, v15503, v15502, v15501, v15500, v15499, v15498, v15497, v15496, v15495, v15494, v15493, v15492, v15491, v15490, v15489, v15488, v15487, v15486, v15485, v15484, v15483, v15482, v15481, v15480, v15479, hv14583, hv14589, hv14595, hv14601, hv14578, hv14613, hv14621, hv14629, hv14637, hv14645, hv14653, hv14661, hv14669, hv14677, hv14685, hv14693, hv14701, hv15160, hv14710, hv14718, hv14725, hv14733, hv14741, hv14749, hv14757, hv14765, hv14773, hv14781, hv14789, hv14796, hv14803, hv14811, hv14818, hv14825, hv14833, hv14841, hv14847, hv14853, hv15174, hv15180, hv15186, hv14861, hv14869, hv14877, hv14885, hv14893, hv15192, hv15199, hv15206, hv15213, hv15220, hv15227, hv14901, hv14917, hv14925, hv14933, hv14941, hv14949, hv14957, hv14965, hv14973, hv14981, hv14989, hv15009, hv15016, hv15023, hv15031, hv15039, hv15047, hv15055, hv15063, hv15071, v15076, ne, ↓reduceIte, ite_self]
  all_goals rfl

theorem reference_lui_rs1_zero (s : State) (i : Inputs) (zero : ReferenceZero s)
    (lui : BitVec.extractLsb' 0 7 (v14575 s i) = 55) : v15632 s i = 0 := by
  rw [specRead2.actual, reference_lui_rs1_address s i lui, specRead2.read_0]
  exact zero

#print axioms reference_lui_rs1_zero
end NutShellProofs

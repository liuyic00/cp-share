From Coq Require Import ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From SmallMultiplier Require Import Model GlobalStable GlobalWidths GlobalProgressTypes GlobalFieldSteps GlobalScalarSteps GlobalProgress.
Local Open Scope N_scope.
From SmallMultiplier Require Import GlobalTypeProgress.
Lemma global_rank_chunk_3 invalid snapshot final v level (prior:global_ranked v level snapshot) (sizes:global_leaf_sizes v)
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 List.Forall (fun index => (global_rank_at index <= S level)%coq_nat -> global_value_at index final = Some (global_target_at index v)) (List.seq 600 200).
Proof.
 constructor.
 - intro enough. exact (global_progress_600 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_601 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_602 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_603 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_604 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_605 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_606 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_607 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_608 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_609 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_610 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_611 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_612 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_613 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_614 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_615 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_616 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_617 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_618 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_619 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_620 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_621 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_622 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_623 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_624 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_625 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_626 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_627 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_628 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_629 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_630 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_631 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_632 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_633 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_634 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_635 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_636 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_637 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_638 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_639 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_640 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_641 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_642 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_643 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_644 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_645 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_646 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_647 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_648 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_649 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_650 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_651 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_652 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_653 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_654 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_655 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_656 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_657 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_658 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_659 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_660 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_661 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_662 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_663 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_664 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_665 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_666 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_667 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_668 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_669 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_670 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_671 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_672 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_673 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_674 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_675 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_676 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_677 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_678 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_679 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_680 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_681 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_682 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_683 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_684 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_685 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_686 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_687 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_688 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_689 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_690 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_691 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_692 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_693 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_694 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_695 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_696 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_697 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_698 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_699 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_700 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_701 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_702 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_703 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_704 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_705 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_706 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_707 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_708 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_709 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_710 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_711 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_712 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_713 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_714 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_715 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_716 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_717 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_718 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_719 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_720 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_721 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_722 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_723 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_724 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_725 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_726 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_727 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_728 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_729 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_730 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_731 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_732 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_733 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_734 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_735 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_736 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_737 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_738 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_739 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_740 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_741 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_742 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_743 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_744 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_745 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_746 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_747 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_748 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_749 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_750 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_751 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_752 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_753 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_754 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_755 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_756 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_757 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_758 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_759 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_760 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_761 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_762 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_763 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_764 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_765 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_766 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_767 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_768 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_769 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_770 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_771 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_772 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_773 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_774 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_775 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_776 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_777 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_778 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_779 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_780 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_781 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_782 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_783 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_784 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_785 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_786 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_787 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_788 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_789 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_790 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_791 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_792 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_793 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_794 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_795 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_796 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_797 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_798 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_799 invalid snapshot final v level prior types sizes enough ran).
 constructor.
Qed.
Lemma global_type_chunk_3 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 List.Forall (fun index => global_port_at index=true -> option_map type_of_val (global_value_at index final)=Some(Gtyp(global_type_at index))) (List.seq 600 200).
Proof.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_601 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_604 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_607 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_618 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_621 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_625 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_628 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_632 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_635 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_638 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_641 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_644 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_646 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_649 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_651 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_654 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_656 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_667 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_670 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_673 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_676 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_687 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_690 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_694 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_697 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_701 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_704 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_707 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_710 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_713 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_715 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_718 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_720 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_723 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_725 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_736 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_739 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_742 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_745 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_756 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_759 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_763 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_766 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_770 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_773 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_776 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_779 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_782 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_784 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_787 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_789 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_792 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_794 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
Qed.

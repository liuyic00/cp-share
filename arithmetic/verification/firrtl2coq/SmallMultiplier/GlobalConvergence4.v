From Coq Require Import ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From SmallMultiplier Require Import Model GlobalStable GlobalWidths GlobalProgressTypes GlobalFieldSteps GlobalScalarSteps GlobalProgress.
Local Open Scope N_scope.
From SmallMultiplier Require Import GlobalTypeProgress.
Lemma global_rank_chunk_4 invalid snapshot final v level (prior:global_ranked v level snapshot) (sizes:global_leaf_sizes v)
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 List.Forall (fun index => (global_rank_at index <= S level)%coq_nat -> global_value_at index final = Some (global_target_at index v)) (List.seq 800 200).
Proof.
 constructor.
 - intro enough. exact (global_progress_800 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_801 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_802 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_803 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_804 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_805 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_806 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_807 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_808 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_809 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_810 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_811 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_812 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_813 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_814 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_815 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_816 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_817 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_818 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_819 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_820 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_821 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_822 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_823 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_824 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_825 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_826 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_827 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_828 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_829 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_830 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_831 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_832 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_833 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_834 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_835 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_836 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_837 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_838 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_839 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_840 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_841 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_842 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_843 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_844 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_845 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_846 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_847 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_848 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_849 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_850 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_851 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_852 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_853 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_854 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_855 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_856 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_857 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_858 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_859 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_860 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_861 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_862 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_863 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_864 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_865 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_866 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_867 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_868 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_869 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_870 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_871 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_872 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_873 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_874 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_875 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_876 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_877 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_878 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_879 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_880 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_881 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_882 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_883 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_884 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_885 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_886 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_887 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_888 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_889 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_890 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_891 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_892 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_893 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_894 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_895 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_896 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_897 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_898 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_899 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_900 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_901 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_902 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_903 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_904 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_905 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_906 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_907 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_908 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_909 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_910 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_911 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_912 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_913 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_914 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_915 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_916 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_917 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_918 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_919 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_920 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_921 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_922 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_923 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_924 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_925 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_926 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_927 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_928 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_929 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_930 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_931 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_932 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_933 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_934 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_935 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_936 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_937 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_938 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_939 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_940 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_941 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_942 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_943 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_944 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_945 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_946 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_947 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_948 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_949 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_950 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_951 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_952 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_953 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_954 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_955 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_956 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_957 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_958 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_959 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_960 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_961 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_962 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_963 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_964 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_965 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_966 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_967 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_968 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_969 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_970 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_971 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_972 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_973 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_974 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_975 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_976 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_977 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_978 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_979 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_980 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_981 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_982 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_983 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_984 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_985 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_986 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_987 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_988 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_989 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_990 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_991 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_992 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_993 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_994 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_995 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_996 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_997 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_998 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_999 invalid snapshot final v level prior types sizes enough ran).
 constructor.
Qed.
Lemma global_type_chunk_4 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 List.Forall (fun index => global_port_at index=true -> option_map type_of_val (global_value_at index final)=Some(Gtyp(global_type_at index))) (List.seq 800 200).
Proof.
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
 - intro included. exact (global_type_progress_805 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_808 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_811 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_814 invalid snapshot final types ran).
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
 - intro included. exact (global_type_progress_825 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_828 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_832 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_835 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_839 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_842 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_845 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_848 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_851 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_853 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_856 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_858 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_861 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_863 invalid snapshot final types ran).
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
 - intro included. exact (global_type_progress_874 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_877 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_880 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_883 invalid snapshot final types ran).
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
 - intro included. exact (global_type_progress_894 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_897 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_901 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_904 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_908 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_911 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_914 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_917 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_920 invalid snapshot final types ran).
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
 - intro included. exact (global_type_progress_931 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_935 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_938 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_941 invalid snapshot final types ran).
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
 - intro included. exact (global_type_progress_949 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_953 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_956 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_959 invalid snapshot final types ran).
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
 - intro included. exact (global_type_progress_967 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_971 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_974 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_977 invalid snapshot final types ran).
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
 - intro included. exact (global_type_progress_985 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_989 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_992 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_995 invalid snapshot final types ran).
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

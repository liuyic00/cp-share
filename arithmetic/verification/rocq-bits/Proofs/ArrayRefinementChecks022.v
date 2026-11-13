From Stdlib Require Import ZArith List Bool Zmod.Bits.
From BitsProofs Require Import ArrayRefinementNodes045.
Import ListNotations.
Open Scope Z_scope.
Local Opaque R.v44700 N.v44700 R.v44701 N.v44701 R.v44715 N.v44715 R.v44716 N.v44716 R.v44727 N.v44727 R.v44728 N.v44728 R.v44739 N.v44739 R.v44740 N.v44740 R.v44754 N.v44754 R.v44755 N.v44755 R.v44766 N.v44766 R.v44767 N.v44767 R.v44778 N.v44778 R.v44779 N.v44779 R.v44787 N.v44787 R.v44788 N.v44788 R.v44802 N.v44802 R.v44803 N.v44803 R.v44814 N.v44814 R.v44815 N.v44815 R.v44826 N.v44826 R.v44827 N.v44827 R.v44841 N.v44841 R.v44842 N.v44842 R.v44853 N.v44853 R.v44854 N.v44854 R.v44865 N.v44865 R.v44866 N.v44866 R.v44880 N.v44880 R.v44881 N.v44881 R.v44892 N.v44892 R.v44893 N.v44893 R.v44904 N.v44904 R.v44905 N.v44905 R.v44913 N.v44913 R.v44914 N.v44914 R.v44928 N.v44928 R.v44929 N.v44929 R.v44940 N.v44940 R.v44941 N.v44941 R.v44952 N.v44952 R.v44953 N.v44953 R.v44967 N.v44967 R.v44968 N.v44968 R.v44979 N.v44979 R.v44980 N.v44980 R.v44991 N.v44991 R.v44992 N.v44992 R.v45006 N.v45006 R.v45007 N.v45007 R.v45018 N.v45018 R.v45019 N.v45019 R.v45030 N.v45030 R.v45031 N.v45031 R.v45042 N.v45042 R.v45043 N.v45043 R.v45057 N.v45057 R.v45058 N.v45058 R.v45069 N.v45069 R.v45070 N.v45070 R.v45081 N.v45081 R.v45082 N.v45082 R.v45096 N.v45096 R.v45097 N.v45097 R.v45108 N.v45108 R.v45109 N.v45109 R.v45120 N.v45120 R.v45121 N.v45121 R.v45135 N.v45135 R.v45136 N.v45136 R.v45147 N.v45147 R.v45148 N.v45148 R.v45159 N.v45159 R.v45160 N.v45160 R.v45168 N.v45168 R.v45169 N.v45169 R.v45183 N.v45183 R.v45184 N.v45184 R.v45195 N.v45195 R.v45196 N.v45196 R.v45207 N.v45207 R.v45208 N.v45208 R.v45222 N.v45222 R.v45223 N.v45223 R.v45234 N.v45234 R.v45235 N.v45235 R.v45246 N.v45246 R.v45247 N.v45247 R.v45261 N.v45261 R.v45262 N.v45262 R.v45273 N.v45273 R.v45274 N.v45274 R.v45285 N.v45285 R.v45286 N.v45286 R.v45294 N.v45294 R.v45295 N.v45295 R.v45309 N.v45309 R.v45310 N.v45310 R.v45321 N.v45321 R.v45322 N.v45322 R.v45333 N.v45333 R.v45334 N.v45334 R.v45348 N.v45348 R.v45349 N.v45349 R.v45360 N.v45360 R.v45361 N.v45361 R.v45372 N.v45372 R.v45373 N.v45373 R.v45387 N.v45387 R.v45388 N.v45388 R.v45399 N.v45399 R.v45400 N.v45400 R.v45411 N.v45411 R.v45412 N.v45412 R.v45420 N.v45420 R.v45421 N.v45421 R.v45435 N.v45435 R.v45436 N.v45436 R.v45447 N.v45447 R.v45448 N.v45448 R.v45459 N.v45459 R.v45460 N.v45460 R.v45474 N.v45474 R.v45475 N.v45475 R.v45486 N.v45486 R.v45487 N.v45487 R.v45498 N.v45498 R.v45499 N.v45499 R.v45513 N.v45513 R.v45514 N.v45514 R.v45525 N.v45525 R.v45526 N.v45526 R.v45537 N.v45537 R.v45538 N.v45538 R.v45546 N.v45546 R.v45547 N.v45547 R.v45561 N.v45561 R.v45562 N.v45562 R.v45573 N.v45573 R.v45574 N.v45574 R.v45585 N.v45585 R.v45586 N.v45586 R.v45600 N.v45600 R.v45601 N.v45601 R.v45612 N.v45612 R.v45613 N.v45613 R.v45624 N.v45624 R.v45625 N.v45625 R.v45639 N.v45639 R.v45640 N.v45640 R.v45651 N.v45651 R.v45652 N.v45652 R.v45663 N.v45663 R.v45664 N.v45664 R.v45678 N.v45678 R.v45679 N.v45679 R.v45690 N.v45690 R.v45691 N.v45691 R.v45702 N.v45702 R.v45703 N.v45703 R.v45717 N.v45717 R.v45718 N.v45718 R.v45729 N.v45729 R.v45730 N.v45730 R.v45741 N.v45741 R.v45742 N.v45742 R.v45756 N.v45756 R.v45757 N.v45757 R.v45768 N.v45768 R.v45769 N.v45769 R.v45780 N.v45780 R.v45781 N.v45781 R.v45795 N.v45795 R.v45796 N.v45796 R.v45807 N.v45807 R.v45808 N.v45808 R.v45819 N.v45819 R.v45820 N.v45820 R.v45834 N.v45834 R.v45835 N.v45835 R.v45846 N.v45846 R.v45847 N.v45847 R.v45858 N.v45858 R.v45859 N.v45859 R.v45873 N.v45873 R.v45874 N.v45874 R.v45885 N.v45885 R.v45886 N.v45886 R.v45897 N.v45897 R.v45898 N.v45898 R.v45912 N.v45912 R.v45913 N.v45913 R.v45924 N.v45924 R.v45925 N.v45925 R.v45936 N.v45936 R.v45937 N.v45937 R.v45951 N.v45951 R.v45952 N.v45952 R.v45963 N.v45963 R.v45964 N.v45964.
Definition reference_checks_22 (s : N.State) (i : N.Inputs) : list bool := [
orb (negb (Z.eqb (R.v44701 (state s) (inputs i)) 1)) (Z.eqb (R.v44700 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44716 (state s) (inputs i)) 1)) (Z.eqb (R.v44715 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44728 (state s) (inputs i)) 1)) (Z.eqb (R.v44727 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44740 (state s) (inputs i)) 1)) (Z.eqb (R.v44739 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44755 (state s) (inputs i)) 1)) (Z.eqb (R.v44754 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44767 (state s) (inputs i)) 1)) (Z.eqb (R.v44766 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44779 (state s) (inputs i)) 1)) (Z.eqb (R.v44778 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44788 (state s) (inputs i)) 1)) (Z.eqb (R.v44787 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44803 (state s) (inputs i)) 1)) (Z.eqb (R.v44802 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44815 (state s) (inputs i)) 1)) (Z.eqb (R.v44814 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44827 (state s) (inputs i)) 1)) (Z.eqb (R.v44826 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44842 (state s) (inputs i)) 1)) (Z.eqb (R.v44841 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44854 (state s) (inputs i)) 1)) (Z.eqb (R.v44853 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44866 (state s) (inputs i)) 1)) (Z.eqb (R.v44865 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44881 (state s) (inputs i)) 1)) (Z.eqb (R.v44880 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44893 (state s) (inputs i)) 1)) (Z.eqb (R.v44892 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44905 (state s) (inputs i)) 1)) (Z.eqb (R.v44904 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44914 (state s) (inputs i)) 1)) (Z.eqb (R.v44913 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44929 (state s) (inputs i)) 1)) (Z.eqb (R.v44928 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44941 (state s) (inputs i)) 1)) (Z.eqb (R.v44940 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44953 (state s) (inputs i)) 1)) (Z.eqb (R.v44952 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44968 (state s) (inputs i)) 1)) (Z.eqb (R.v44967 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44980 (state s) (inputs i)) 1)) (Z.eqb (R.v44979 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44992 (state s) (inputs i)) 1)) (Z.eqb (R.v44991 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45007 (state s) (inputs i)) 1)) (Z.eqb (R.v45006 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45019 (state s) (inputs i)) 1)) (Z.eqb (R.v45018 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45031 (state s) (inputs i)) 1)) (Z.eqb (R.v45030 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45043 (state s) (inputs i)) 1)) (Z.eqb (R.v45042 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45058 (state s) (inputs i)) 1)) (Z.eqb (R.v45057 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45070 (state s) (inputs i)) 1)) (Z.eqb (R.v45069 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45082 (state s) (inputs i)) 1)) (Z.eqb (R.v45081 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45097 (state s) (inputs i)) 1)) (Z.eqb (R.v45096 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45109 (state s) (inputs i)) 1)) (Z.eqb (R.v45108 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45121 (state s) (inputs i)) 1)) (Z.eqb (R.v45120 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45136 (state s) (inputs i)) 1)) (Z.eqb (R.v45135 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45148 (state s) (inputs i)) 1)) (Z.eqb (R.v45147 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45160 (state s) (inputs i)) 1)) (Z.eqb (R.v45159 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45169 (state s) (inputs i)) 1)) (Z.eqb (R.v45168 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45184 (state s) (inputs i)) 1)) (Z.eqb (R.v45183 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45196 (state s) (inputs i)) 1)) (Z.eqb (R.v45195 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45208 (state s) (inputs i)) 1)) (Z.eqb (R.v45207 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45223 (state s) (inputs i)) 1)) (Z.eqb (R.v45222 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45235 (state s) (inputs i)) 1)) (Z.eqb (R.v45234 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45247 (state s) (inputs i)) 1)) (Z.eqb (R.v45246 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45262 (state s) (inputs i)) 1)) (Z.eqb (R.v45261 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45274 (state s) (inputs i)) 1)) (Z.eqb (R.v45273 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45286 (state s) (inputs i)) 1)) (Z.eqb (R.v45285 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45295 (state s) (inputs i)) 1)) (Z.eqb (R.v45294 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45310 (state s) (inputs i)) 1)) (Z.eqb (R.v45309 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45322 (state s) (inputs i)) 1)) (Z.eqb (R.v45321 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45334 (state s) (inputs i)) 1)) (Z.eqb (R.v45333 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45349 (state s) (inputs i)) 1)) (Z.eqb (R.v45348 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45361 (state s) (inputs i)) 1)) (Z.eqb (R.v45360 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45373 (state s) (inputs i)) 1)) (Z.eqb (R.v45372 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45388 (state s) (inputs i)) 1)) (Z.eqb (R.v45387 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45400 (state s) (inputs i)) 1)) (Z.eqb (R.v45399 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45412 (state s) (inputs i)) 1)) (Z.eqb (R.v45411 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45421 (state s) (inputs i)) 1)) (Z.eqb (R.v45420 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45436 (state s) (inputs i)) 1)) (Z.eqb (R.v45435 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45448 (state s) (inputs i)) 1)) (Z.eqb (R.v45447 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45460 (state s) (inputs i)) 1)) (Z.eqb (R.v45459 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45475 (state s) (inputs i)) 1)) (Z.eqb (R.v45474 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45487 (state s) (inputs i)) 1)) (Z.eqb (R.v45486 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45499 (state s) (inputs i)) 1)) (Z.eqb (R.v45498 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45514 (state s) (inputs i)) 1)) (Z.eqb (R.v45513 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45526 (state s) (inputs i)) 1)) (Z.eqb (R.v45525 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45538 (state s) (inputs i)) 1)) (Z.eqb (R.v45537 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45547 (state s) (inputs i)) 1)) (Z.eqb (R.v45546 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45562 (state s) (inputs i)) 1)) (Z.eqb (R.v45561 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45574 (state s) (inputs i)) 1)) (Z.eqb (R.v45573 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45586 (state s) (inputs i)) 1)) (Z.eqb (R.v45585 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45601 (state s) (inputs i)) 1)) (Z.eqb (R.v45600 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45613 (state s) (inputs i)) 1)) (Z.eqb (R.v45612 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45625 (state s) (inputs i)) 1)) (Z.eqb (R.v45624 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45640 (state s) (inputs i)) 1)) (Z.eqb (R.v45639 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45652 (state s) (inputs i)) 1)) (Z.eqb (R.v45651 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45664 (state s) (inputs i)) 1)) (Z.eqb (R.v45663 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45679 (state s) (inputs i)) 1)) (Z.eqb (R.v45678 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45691 (state s) (inputs i)) 1)) (Z.eqb (R.v45690 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45703 (state s) (inputs i)) 1)) (Z.eqb (R.v45702 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45718 (state s) (inputs i)) 1)) (Z.eqb (R.v45717 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45730 (state s) (inputs i)) 1)) (Z.eqb (R.v45729 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45742 (state s) (inputs i)) 1)) (Z.eqb (R.v45741 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45757 (state s) (inputs i)) 1)) (Z.eqb (R.v45756 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45769 (state s) (inputs i)) 1)) (Z.eqb (R.v45768 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45781 (state s) (inputs i)) 1)) (Z.eqb (R.v45780 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45796 (state s) (inputs i)) 1)) (Z.eqb (R.v45795 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45808 (state s) (inputs i)) 1)) (Z.eqb (R.v45807 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45820 (state s) (inputs i)) 1)) (Z.eqb (R.v45819 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45835 (state s) (inputs i)) 1)) (Z.eqb (R.v45834 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45847 (state s) (inputs i)) 1)) (Z.eqb (R.v45846 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45859 (state s) (inputs i)) 1)) (Z.eqb (R.v45858 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45874 (state s) (inputs i)) 1)) (Z.eqb (R.v45873 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45886 (state s) (inputs i)) 1)) (Z.eqb (R.v45885 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45898 (state s) (inputs i)) 1)) (Z.eqb (R.v45897 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45913 (state s) (inputs i)) 1)) (Z.eqb (R.v45912 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45925 (state s) (inputs i)) 1)) (Z.eqb (R.v45924 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45937 (state s) (inputs i)) 1)) (Z.eqb (R.v45936 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45952 (state s) (inputs i)) 1)) (Z.eqb (R.v45951 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v45964 (state s) (inputs i)) 1)) (Z.eqb (R.v45963 (state s) (inputs i)) 1)
].
Definition native_checks_22 (s : N.State) (i : N.Inputs) : list bool := [
orb (negb (Zmod.eqb (N.v44701 s i) Zmod.one)) (Zmod.eqb (N.v44700 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44716 s i) Zmod.one)) (Zmod.eqb (N.v44715 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44728 s i) Zmod.one)) (Zmod.eqb (N.v44727 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44740 s i) Zmod.one)) (Zmod.eqb (N.v44739 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44755 s i) Zmod.one)) (Zmod.eqb (N.v44754 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44767 s i) Zmod.one)) (Zmod.eqb (N.v44766 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44779 s i) Zmod.one)) (Zmod.eqb (N.v44778 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44788 s i) Zmod.one)) (Zmod.eqb (N.v44787 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44803 s i) Zmod.one)) (Zmod.eqb (N.v44802 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44815 s i) Zmod.one)) (Zmod.eqb (N.v44814 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44827 s i) Zmod.one)) (Zmod.eqb (N.v44826 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44842 s i) Zmod.one)) (Zmod.eqb (N.v44841 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44854 s i) Zmod.one)) (Zmod.eqb (N.v44853 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44866 s i) Zmod.one)) (Zmod.eqb (N.v44865 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44881 s i) Zmod.one)) (Zmod.eqb (N.v44880 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44893 s i) Zmod.one)) (Zmod.eqb (N.v44892 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44905 s i) Zmod.one)) (Zmod.eqb (N.v44904 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44914 s i) Zmod.one)) (Zmod.eqb (N.v44913 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44929 s i) Zmod.one)) (Zmod.eqb (N.v44928 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44941 s i) Zmod.one)) (Zmod.eqb (N.v44940 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44953 s i) Zmod.one)) (Zmod.eqb (N.v44952 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44968 s i) Zmod.one)) (Zmod.eqb (N.v44967 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44980 s i) Zmod.one)) (Zmod.eqb (N.v44979 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44992 s i) Zmod.one)) (Zmod.eqb (N.v44991 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45007 s i) Zmod.one)) (Zmod.eqb (N.v45006 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45019 s i) Zmod.one)) (Zmod.eqb (N.v45018 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45031 s i) Zmod.one)) (Zmod.eqb (N.v45030 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45043 s i) Zmod.one)) (Zmod.eqb (N.v45042 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45058 s i) Zmod.one)) (Zmod.eqb (N.v45057 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45070 s i) Zmod.one)) (Zmod.eqb (N.v45069 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45082 s i) Zmod.one)) (Zmod.eqb (N.v45081 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45097 s i) Zmod.one)) (Zmod.eqb (N.v45096 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45109 s i) Zmod.one)) (Zmod.eqb (N.v45108 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45121 s i) Zmod.one)) (Zmod.eqb (N.v45120 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45136 s i) Zmod.one)) (Zmod.eqb (N.v45135 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45148 s i) Zmod.one)) (Zmod.eqb (N.v45147 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45160 s i) Zmod.one)) (Zmod.eqb (N.v45159 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45169 s i) Zmod.one)) (Zmod.eqb (N.v45168 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45184 s i) Zmod.one)) (Zmod.eqb (N.v45183 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45196 s i) Zmod.one)) (Zmod.eqb (N.v45195 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45208 s i) Zmod.one)) (Zmod.eqb (N.v45207 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45223 s i) Zmod.one)) (Zmod.eqb (N.v45222 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45235 s i) Zmod.one)) (Zmod.eqb (N.v45234 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45247 s i) Zmod.one)) (Zmod.eqb (N.v45246 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45262 s i) Zmod.one)) (Zmod.eqb (N.v45261 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45274 s i) Zmod.one)) (Zmod.eqb (N.v45273 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45286 s i) Zmod.one)) (Zmod.eqb (N.v45285 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45295 s i) Zmod.one)) (Zmod.eqb (N.v45294 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45310 s i) Zmod.one)) (Zmod.eqb (N.v45309 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45322 s i) Zmod.one)) (Zmod.eqb (N.v45321 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45334 s i) Zmod.one)) (Zmod.eqb (N.v45333 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45349 s i) Zmod.one)) (Zmod.eqb (N.v45348 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45361 s i) Zmod.one)) (Zmod.eqb (N.v45360 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45373 s i) Zmod.one)) (Zmod.eqb (N.v45372 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45388 s i) Zmod.one)) (Zmod.eqb (N.v45387 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45400 s i) Zmod.one)) (Zmod.eqb (N.v45399 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45412 s i) Zmod.one)) (Zmod.eqb (N.v45411 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45421 s i) Zmod.one)) (Zmod.eqb (N.v45420 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45436 s i) Zmod.one)) (Zmod.eqb (N.v45435 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45448 s i) Zmod.one)) (Zmod.eqb (N.v45447 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45460 s i) Zmod.one)) (Zmod.eqb (N.v45459 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45475 s i) Zmod.one)) (Zmod.eqb (N.v45474 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45487 s i) Zmod.one)) (Zmod.eqb (N.v45486 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45499 s i) Zmod.one)) (Zmod.eqb (N.v45498 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45514 s i) Zmod.one)) (Zmod.eqb (N.v45513 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45526 s i) Zmod.one)) (Zmod.eqb (N.v45525 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45538 s i) Zmod.one)) (Zmod.eqb (N.v45537 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45547 s i) Zmod.one)) (Zmod.eqb (N.v45546 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45562 s i) Zmod.one)) (Zmod.eqb (N.v45561 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45574 s i) Zmod.one)) (Zmod.eqb (N.v45573 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45586 s i) Zmod.one)) (Zmod.eqb (N.v45585 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45601 s i) Zmod.one)) (Zmod.eqb (N.v45600 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45613 s i) Zmod.one)) (Zmod.eqb (N.v45612 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45625 s i) Zmod.one)) (Zmod.eqb (N.v45624 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45640 s i) Zmod.one)) (Zmod.eqb (N.v45639 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45652 s i) Zmod.one)) (Zmod.eqb (N.v45651 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45664 s i) Zmod.one)) (Zmod.eqb (N.v45663 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45679 s i) Zmod.one)) (Zmod.eqb (N.v45678 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45691 s i) Zmod.one)) (Zmod.eqb (N.v45690 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45703 s i) Zmod.one)) (Zmod.eqb (N.v45702 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45718 s i) Zmod.one)) (Zmod.eqb (N.v45717 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45730 s i) Zmod.one)) (Zmod.eqb (N.v45729 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45742 s i) Zmod.one)) (Zmod.eqb (N.v45741 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45757 s i) Zmod.one)) (Zmod.eqb (N.v45756 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45769 s i) Zmod.one)) (Zmod.eqb (N.v45768 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45781 s i) Zmod.one)) (Zmod.eqb (N.v45780 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45796 s i) Zmod.one)) (Zmod.eqb (N.v45795 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45808 s i) Zmod.one)) (Zmod.eqb (N.v45807 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45820 s i) Zmod.one)) (Zmod.eqb (N.v45819 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45835 s i) Zmod.one)) (Zmod.eqb (N.v45834 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45847 s i) Zmod.one)) (Zmod.eqb (N.v45846 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45859 s i) Zmod.one)) (Zmod.eqb (N.v45858 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45874 s i) Zmod.one)) (Zmod.eqb (N.v45873 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45886 s i) Zmod.one)) (Zmod.eqb (N.v45885 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45898 s i) Zmod.one)) (Zmod.eqb (N.v45897 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45913 s i) Zmod.one)) (Zmod.eqb (N.v45912 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45925 s i) Zmod.one)) (Zmod.eqb (N.v45924 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45937 s i) Zmod.one)) (Zmod.eqb (N.v45936 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45952 s i) Zmod.one)) (Zmod.eqb (N.v45951 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v45964 s i) Zmod.one)) (Zmod.eqb (N.v45963 s i) Zmod.one)
].
Lemma checks_22 s i : reference_checks_22 s i = native_checks_22 s i.
Proof. unfold reference_checks_22, native_checks_22.
  rewrite ?node_44700.
  rewrite ?node_44701.
  rewrite ?node_44715.
  rewrite ?node_44716.
  rewrite ?node_44727.
  rewrite ?node_44728.
  rewrite ?node_44739.
  rewrite ?node_44740.
  rewrite ?node_44754.
  rewrite ?node_44755.
  rewrite ?node_44766.
  rewrite ?node_44767.
  rewrite ?node_44778.
  rewrite ?node_44779.
  rewrite ?node_44787.
  rewrite ?node_44788.
  rewrite ?node_44802.
  rewrite ?node_44803.
  rewrite ?node_44814.
  rewrite ?node_44815.
  rewrite ?node_44826.
  rewrite ?node_44827.
  rewrite ?node_44841.
  rewrite ?node_44842.
  rewrite ?node_44853.
  rewrite ?node_44854.
  rewrite ?node_44865.
  rewrite ?node_44866.
  rewrite ?node_44880.
  rewrite ?node_44881.
  rewrite ?node_44892.
  rewrite ?node_44893.
  rewrite ?node_44904.
  rewrite ?node_44905.
  rewrite ?node_44913.
  rewrite ?node_44914.
  rewrite ?node_44928.
  rewrite ?node_44929.
  rewrite ?node_44940.
  rewrite ?node_44941.
  rewrite ?node_44952.
  rewrite ?node_44953.
  rewrite ?node_44967.
  rewrite ?node_44968.
  rewrite ?node_44979.
  rewrite ?node_44980.
  rewrite ?node_44991.
  rewrite ?node_44992.
  rewrite ?node_45006.
  rewrite ?node_45007.
  rewrite ?node_45018.
  rewrite ?node_45019.
  rewrite ?node_45030.
  rewrite ?node_45031.
  rewrite ?node_45042.
  rewrite ?node_45043.
  rewrite ?node_45057.
  rewrite ?node_45058.
  rewrite ?node_45069.
  rewrite ?node_45070.
  rewrite ?node_45081.
  rewrite ?node_45082.
  rewrite ?node_45096.
  rewrite ?node_45097.
  rewrite ?node_45108.
  rewrite ?node_45109.
  rewrite ?node_45120.
  rewrite ?node_45121.
  rewrite ?node_45135.
  rewrite ?node_45136.
  rewrite ?node_45147.
  rewrite ?node_45148.
  rewrite ?node_45159.
  rewrite ?node_45160.
  rewrite ?node_45168.
  rewrite ?node_45169.
  rewrite ?node_45183.
  rewrite ?node_45184.
  rewrite ?node_45195.
  rewrite ?node_45196.
  rewrite ?node_45207.
  rewrite ?node_45208.
  rewrite ?node_45222.
  rewrite ?node_45223.
  rewrite ?node_45234.
  rewrite ?node_45235.
  rewrite ?node_45246.
  rewrite ?node_45247.
  rewrite ?node_45261.
  rewrite ?node_45262.
  rewrite ?node_45273.
  rewrite ?node_45274.
  rewrite ?node_45285.
  rewrite ?node_45286.
  rewrite ?node_45294.
  rewrite ?node_45295.
  rewrite ?node_45309.
  rewrite ?node_45310.
  rewrite ?node_45321.
  rewrite ?node_45322.
  rewrite ?node_45333.
  rewrite ?node_45334.
  rewrite ?node_45348.
  rewrite ?node_45349.
  rewrite ?node_45360.
  rewrite ?node_45361.
  rewrite ?node_45372.
  rewrite ?node_45373.
  rewrite ?node_45387.
  rewrite ?node_45388.
  rewrite ?node_45399.
  rewrite ?node_45400.
  rewrite ?node_45411.
  rewrite ?node_45412.
  rewrite ?node_45420.
  rewrite ?node_45421.
  rewrite ?node_45435.
  rewrite ?node_45436.
  rewrite ?node_45447.
  rewrite ?node_45448.
  rewrite ?node_45459.
  rewrite ?node_45460.
  rewrite ?node_45474.
  rewrite ?node_45475.
  rewrite ?node_45486.
  rewrite ?node_45487.
  rewrite ?node_45498.
  rewrite ?node_45499.
  rewrite ?node_45513.
  rewrite ?node_45514.
  rewrite ?node_45525.
  rewrite ?node_45526.
  rewrite ?node_45537.
  rewrite ?node_45538.
  rewrite ?node_45546.
  rewrite ?node_45547.
  rewrite ?node_45561.
  rewrite ?node_45562.
  rewrite ?node_45573.
  rewrite ?node_45574.
  rewrite ?node_45585.
  rewrite ?node_45586.
  rewrite ?node_45600.
  rewrite ?node_45601.
  rewrite ?node_45612.
  rewrite ?node_45613.
  rewrite ?node_45624.
  rewrite ?node_45625.
  rewrite ?node_45639.
  rewrite ?node_45640.
  rewrite ?node_45651.
  rewrite ?node_45652.
  rewrite ?node_45663.
  rewrite ?node_45664.
  rewrite ?node_45678.
  rewrite ?node_45679.
  rewrite ?node_45690.
  rewrite ?node_45691.
  rewrite ?node_45702.
  rewrite ?node_45703.
  rewrite ?node_45717.
  rewrite ?node_45718.
  rewrite ?node_45729.
  rewrite ?node_45730.
  rewrite ?node_45741.
  rewrite ?node_45742.
  rewrite ?node_45756.
  rewrite ?node_45757.
  rewrite ?node_45768.
  rewrite ?node_45769.
  rewrite ?node_45780.
  rewrite ?node_45781.
  rewrite ?node_45795.
  rewrite ?node_45796.
  rewrite ?node_45807.
  rewrite ?node_45808.
  rewrite ?node_45819.
  rewrite ?node_45820.
  rewrite ?node_45834.
  rewrite ?node_45835.
  rewrite ?node_45846.
  rewrite ?node_45847.
  rewrite ?node_45858.
  rewrite ?node_45859.
  rewrite ?node_45873.
  rewrite ?node_45874.
  rewrite ?node_45885.
  rewrite ?node_45886.
  rewrite ?node_45897.
  rewrite ?node_45898.
  rewrite ?node_45912.
  rewrite ?node_45913.
  rewrite ?node_45924.
  rewrite ?node_45925.
  rewrite ?node_45936.
  rewrite ?node_45937.
  rewrite ?node_45951.
  rewrite ?node_45952.
  rewrite ?node_45963.
  rewrite ?node_45964.
  reflexivity.
Qed.

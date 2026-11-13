From Stdlib Require Import ZArith List Bool Zmod.Bits.
From BitsProofs Require Import ArrayRefinementNodes028.
Import ListNotations.
Open Scope Z_scope.
Local Opaque R.v26767 N.v26767 R.v26768 N.v26768 R.v26779 N.v26779 R.v26780 N.v26780 R.v26791 N.v26791 R.v26792 N.v26792 R.v26806 N.v26806 R.v26807 N.v26807 R.v26818 N.v26818 R.v26819 N.v26819 R.v26830 N.v26830 R.v26831 N.v26831 R.v26845 N.v26845 R.v26846 N.v26846 R.v26857 N.v26857 R.v26858 N.v26858 R.v26869 N.v26869 R.v26870 N.v26870 R.v26884 N.v26884 R.v26885 N.v26885 R.v26896 N.v26896 R.v26897 N.v26897 R.v26908 N.v26908 R.v26909 N.v26909 R.v26923 N.v26923 R.v26924 N.v26924 R.v26935 N.v26935 R.v26936 N.v26936 R.v26947 N.v26947 R.v26948 N.v26948 R.v26962 N.v26962 R.v26963 N.v26963 R.v26974 N.v26974 R.v26975 N.v26975 R.v26986 N.v26986 R.v26987 N.v26987 R.v27001 N.v27001 R.v27002 N.v27002 R.v27013 N.v27013 R.v27014 N.v27014 R.v27025 N.v27025 R.v27026 N.v27026 R.v27040 N.v27040 R.v27041 N.v27041 R.v27052 N.v27052 R.v27053 N.v27053 R.v27064 N.v27064 R.v27065 N.v27065 R.v27073 N.v27073 R.v27074 N.v27074 R.v27088 N.v27088 R.v27089 N.v27089 R.v27100 N.v27100 R.v27101 N.v27101 R.v27112 N.v27112 R.v27113 N.v27113 R.v27127 N.v27127 R.v27128 N.v27128 R.v27139 N.v27139 R.v27140 N.v27140 R.v27151 N.v27151 R.v27152 N.v27152 R.v27166 N.v27166 R.v27167 N.v27167 R.v27178 N.v27178 R.v27179 N.v27179 R.v27190 N.v27190 R.v27191 N.v27191 R.v27205 N.v27205 R.v27206 N.v27206 R.v27217 N.v27217 R.v27218 N.v27218 R.v27229 N.v27229 R.v27230 N.v27230 R.v27244 N.v27244 R.v27245 N.v27245 R.v27256 N.v27256 R.v27257 N.v27257 R.v27268 N.v27268 R.v27269 N.v27269 R.v27283 N.v27283 R.v27284 N.v27284 R.v27295 N.v27295 R.v27296 N.v27296 R.v27307 N.v27307 R.v27308 N.v27308 R.v27322 N.v27322 R.v27323 N.v27323 R.v27334 N.v27334 R.v27335 N.v27335 R.v27346 N.v27346 R.v27347 N.v27347 R.v27361 N.v27361 R.v27362 N.v27362 R.v27373 N.v27373 R.v27374 N.v27374 R.v27385 N.v27385 R.v27386 N.v27386 R.v27394 N.v27394 R.v27395 N.v27395 R.v27409 N.v27409 R.v27410 N.v27410 R.v27421 N.v27421 R.v27422 N.v27422 R.v27433 N.v27433 R.v27434 N.v27434 R.v27448 N.v27448 R.v27449 N.v27449 R.v27460 N.v27460 R.v27461 N.v27461 R.v27472 N.v27472 R.v27473 N.v27473 R.v27487 N.v27487 R.v27488 N.v27488 R.v27499 N.v27499 R.v27500 N.v27500 R.v27511 N.v27511 R.v27512 N.v27512 R.v27526 N.v27526 R.v27527 N.v27527 R.v27538 N.v27538 R.v27539 N.v27539 R.v27550 N.v27550 R.v27551 N.v27551 R.v27565 N.v27565 R.v27566 N.v27566 R.v27577 N.v27577 R.v27578 N.v27578 R.v27589 N.v27589 R.v27590 N.v27590 R.v27604 N.v27604 R.v27605 N.v27605 R.v27616 N.v27616 R.v27617 N.v27617 R.v27628 N.v27628 R.v27629 N.v27629 R.v27643 N.v27643 R.v27644 N.v27644 R.v27655 N.v27655 R.v27656 N.v27656 R.v27667 N.v27667 R.v27668 N.v27668 R.v27682 N.v27682 R.v27683 N.v27683 R.v27694 N.v27694 R.v27695 N.v27695 R.v27706 N.v27706 R.v27707 N.v27707 R.v27721 N.v27721 R.v27722 N.v27722 R.v27733 N.v27733 R.v27734 N.v27734 R.v27745 N.v27745 R.v27746 N.v27746 R.v27760 N.v27760 R.v27761 N.v27761 R.v27772 N.v27772 R.v27773 N.v27773 R.v27784 N.v27784 R.v27785 N.v27785 R.v27799 N.v27799 R.v27800 N.v27800 R.v27811 N.v27811 R.v27812 N.v27812 R.v27823 N.v27823 R.v27824 N.v27824 R.v27838 N.v27838 R.v27839 N.v27839 R.v27850 N.v27850 R.v27851 N.v27851 R.v27862 N.v27862 R.v27863 N.v27863 R.v27877 N.v27877 R.v27878 N.v27878 R.v27889 N.v27889 R.v27890 N.v27890 R.v27901 N.v27901 R.v27902 N.v27902 R.v27916 N.v27916 R.v27917 N.v27917 R.v27928 N.v27928 R.v27929 N.v27929 R.v27940 N.v27940 R.v27941 N.v27941 R.v27955 N.v27955 R.v27956 N.v27956 R.v27967 N.v27967 R.v27968 N.v27968 R.v27979 N.v27979 R.v27980 N.v27980 R.v27994 N.v27994 R.v27995 N.v27995 R.v28006 N.v28006 R.v28007 N.v28007 R.v28018 N.v28018 R.v28019 N.v28019 R.v28033 N.v28033 R.v28034 N.v28034 R.v28045 N.v28045 R.v28046 N.v28046.
Definition reference_checks_8 (s : N.State) (i : N.Inputs) : list bool := [
orb (negb (Z.eqb (R.v26768 (state s) (inputs i)) 1)) (Z.eqb (R.v26767 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v26780 (state s) (inputs i)) 1)) (Z.eqb (R.v26779 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v26792 (state s) (inputs i)) 1)) (Z.eqb (R.v26791 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v26807 (state s) (inputs i)) 1)) (Z.eqb (R.v26806 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v26819 (state s) (inputs i)) 1)) (Z.eqb (R.v26818 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v26831 (state s) (inputs i)) 1)) (Z.eqb (R.v26830 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v26846 (state s) (inputs i)) 1)) (Z.eqb (R.v26845 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v26858 (state s) (inputs i)) 1)) (Z.eqb (R.v26857 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v26870 (state s) (inputs i)) 1)) (Z.eqb (R.v26869 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v26885 (state s) (inputs i)) 1)) (Z.eqb (R.v26884 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v26897 (state s) (inputs i)) 1)) (Z.eqb (R.v26896 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v26909 (state s) (inputs i)) 1)) (Z.eqb (R.v26908 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v26924 (state s) (inputs i)) 1)) (Z.eqb (R.v26923 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v26936 (state s) (inputs i)) 1)) (Z.eqb (R.v26935 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v26948 (state s) (inputs i)) 1)) (Z.eqb (R.v26947 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v26963 (state s) (inputs i)) 1)) (Z.eqb (R.v26962 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v26975 (state s) (inputs i)) 1)) (Z.eqb (R.v26974 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v26987 (state s) (inputs i)) 1)) (Z.eqb (R.v26986 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27002 (state s) (inputs i)) 1)) (Z.eqb (R.v27001 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27014 (state s) (inputs i)) 1)) (Z.eqb (R.v27013 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27026 (state s) (inputs i)) 1)) (Z.eqb (R.v27025 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27041 (state s) (inputs i)) 1)) (Z.eqb (R.v27040 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27053 (state s) (inputs i)) 1)) (Z.eqb (R.v27052 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27065 (state s) (inputs i)) 1)) (Z.eqb (R.v27064 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27074 (state s) (inputs i)) 1)) (Z.eqb (R.v27073 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27089 (state s) (inputs i)) 1)) (Z.eqb (R.v27088 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27101 (state s) (inputs i)) 1)) (Z.eqb (R.v27100 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27113 (state s) (inputs i)) 1)) (Z.eqb (R.v27112 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27128 (state s) (inputs i)) 1)) (Z.eqb (R.v27127 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27140 (state s) (inputs i)) 1)) (Z.eqb (R.v27139 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27152 (state s) (inputs i)) 1)) (Z.eqb (R.v27151 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27167 (state s) (inputs i)) 1)) (Z.eqb (R.v27166 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27179 (state s) (inputs i)) 1)) (Z.eqb (R.v27178 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27191 (state s) (inputs i)) 1)) (Z.eqb (R.v27190 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27206 (state s) (inputs i)) 1)) (Z.eqb (R.v27205 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27218 (state s) (inputs i)) 1)) (Z.eqb (R.v27217 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27230 (state s) (inputs i)) 1)) (Z.eqb (R.v27229 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27245 (state s) (inputs i)) 1)) (Z.eqb (R.v27244 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27257 (state s) (inputs i)) 1)) (Z.eqb (R.v27256 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27269 (state s) (inputs i)) 1)) (Z.eqb (R.v27268 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27284 (state s) (inputs i)) 1)) (Z.eqb (R.v27283 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27296 (state s) (inputs i)) 1)) (Z.eqb (R.v27295 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27308 (state s) (inputs i)) 1)) (Z.eqb (R.v27307 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27323 (state s) (inputs i)) 1)) (Z.eqb (R.v27322 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27335 (state s) (inputs i)) 1)) (Z.eqb (R.v27334 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27347 (state s) (inputs i)) 1)) (Z.eqb (R.v27346 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27362 (state s) (inputs i)) 1)) (Z.eqb (R.v27361 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27374 (state s) (inputs i)) 1)) (Z.eqb (R.v27373 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27386 (state s) (inputs i)) 1)) (Z.eqb (R.v27385 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27395 (state s) (inputs i)) 1)) (Z.eqb (R.v27394 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27410 (state s) (inputs i)) 1)) (Z.eqb (R.v27409 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27422 (state s) (inputs i)) 1)) (Z.eqb (R.v27421 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27434 (state s) (inputs i)) 1)) (Z.eqb (R.v27433 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27449 (state s) (inputs i)) 1)) (Z.eqb (R.v27448 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27461 (state s) (inputs i)) 1)) (Z.eqb (R.v27460 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27473 (state s) (inputs i)) 1)) (Z.eqb (R.v27472 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27488 (state s) (inputs i)) 1)) (Z.eqb (R.v27487 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27500 (state s) (inputs i)) 1)) (Z.eqb (R.v27499 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27512 (state s) (inputs i)) 1)) (Z.eqb (R.v27511 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27527 (state s) (inputs i)) 1)) (Z.eqb (R.v27526 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27539 (state s) (inputs i)) 1)) (Z.eqb (R.v27538 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27551 (state s) (inputs i)) 1)) (Z.eqb (R.v27550 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27566 (state s) (inputs i)) 1)) (Z.eqb (R.v27565 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27578 (state s) (inputs i)) 1)) (Z.eqb (R.v27577 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27590 (state s) (inputs i)) 1)) (Z.eqb (R.v27589 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27605 (state s) (inputs i)) 1)) (Z.eqb (R.v27604 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27617 (state s) (inputs i)) 1)) (Z.eqb (R.v27616 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27629 (state s) (inputs i)) 1)) (Z.eqb (R.v27628 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27644 (state s) (inputs i)) 1)) (Z.eqb (R.v27643 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27656 (state s) (inputs i)) 1)) (Z.eqb (R.v27655 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27668 (state s) (inputs i)) 1)) (Z.eqb (R.v27667 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27683 (state s) (inputs i)) 1)) (Z.eqb (R.v27682 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27695 (state s) (inputs i)) 1)) (Z.eqb (R.v27694 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27707 (state s) (inputs i)) 1)) (Z.eqb (R.v27706 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27722 (state s) (inputs i)) 1)) (Z.eqb (R.v27721 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27734 (state s) (inputs i)) 1)) (Z.eqb (R.v27733 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27746 (state s) (inputs i)) 1)) (Z.eqb (R.v27745 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27761 (state s) (inputs i)) 1)) (Z.eqb (R.v27760 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27773 (state s) (inputs i)) 1)) (Z.eqb (R.v27772 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27785 (state s) (inputs i)) 1)) (Z.eqb (R.v27784 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27800 (state s) (inputs i)) 1)) (Z.eqb (R.v27799 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27812 (state s) (inputs i)) 1)) (Z.eqb (R.v27811 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27824 (state s) (inputs i)) 1)) (Z.eqb (R.v27823 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27839 (state s) (inputs i)) 1)) (Z.eqb (R.v27838 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27851 (state s) (inputs i)) 1)) (Z.eqb (R.v27850 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27863 (state s) (inputs i)) 1)) (Z.eqb (R.v27862 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27878 (state s) (inputs i)) 1)) (Z.eqb (R.v27877 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27890 (state s) (inputs i)) 1)) (Z.eqb (R.v27889 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27902 (state s) (inputs i)) 1)) (Z.eqb (R.v27901 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27917 (state s) (inputs i)) 1)) (Z.eqb (R.v27916 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27929 (state s) (inputs i)) 1)) (Z.eqb (R.v27928 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27941 (state s) (inputs i)) 1)) (Z.eqb (R.v27940 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27956 (state s) (inputs i)) 1)) (Z.eqb (R.v27955 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27968 (state s) (inputs i)) 1)) (Z.eqb (R.v27967 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27980 (state s) (inputs i)) 1)) (Z.eqb (R.v27979 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v27995 (state s) (inputs i)) 1)) (Z.eqb (R.v27994 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28007 (state s) (inputs i)) 1)) (Z.eqb (R.v28006 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28019 (state s) (inputs i)) 1)) (Z.eqb (R.v28018 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28034 (state s) (inputs i)) 1)) (Z.eqb (R.v28033 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28046 (state s) (inputs i)) 1)) (Z.eqb (R.v28045 (state s) (inputs i)) 1)
].
Definition native_checks_8 (s : N.State) (i : N.Inputs) : list bool := [
orb (negb (Zmod.eqb (N.v26768 s i) Zmod.one)) (Zmod.eqb (N.v26767 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v26780 s i) Zmod.one)) (Zmod.eqb (N.v26779 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v26792 s i) Zmod.one)) (Zmod.eqb (N.v26791 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v26807 s i) Zmod.one)) (Zmod.eqb (N.v26806 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v26819 s i) Zmod.one)) (Zmod.eqb (N.v26818 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v26831 s i) Zmod.one)) (Zmod.eqb (N.v26830 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v26846 s i) Zmod.one)) (Zmod.eqb (N.v26845 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v26858 s i) Zmod.one)) (Zmod.eqb (N.v26857 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v26870 s i) Zmod.one)) (Zmod.eqb (N.v26869 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v26885 s i) Zmod.one)) (Zmod.eqb (N.v26884 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v26897 s i) Zmod.one)) (Zmod.eqb (N.v26896 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v26909 s i) Zmod.one)) (Zmod.eqb (N.v26908 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v26924 s i) Zmod.one)) (Zmod.eqb (N.v26923 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v26936 s i) Zmod.one)) (Zmod.eqb (N.v26935 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v26948 s i) Zmod.one)) (Zmod.eqb (N.v26947 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v26963 s i) Zmod.one)) (Zmod.eqb (N.v26962 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v26975 s i) Zmod.one)) (Zmod.eqb (N.v26974 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v26987 s i) Zmod.one)) (Zmod.eqb (N.v26986 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27002 s i) Zmod.one)) (Zmod.eqb (N.v27001 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27014 s i) Zmod.one)) (Zmod.eqb (N.v27013 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27026 s i) Zmod.one)) (Zmod.eqb (N.v27025 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27041 s i) Zmod.one)) (Zmod.eqb (N.v27040 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27053 s i) Zmod.one)) (Zmod.eqb (N.v27052 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27065 s i) Zmod.one)) (Zmod.eqb (N.v27064 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27074 s i) Zmod.one)) (Zmod.eqb (N.v27073 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27089 s i) Zmod.one)) (Zmod.eqb (N.v27088 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27101 s i) Zmod.one)) (Zmod.eqb (N.v27100 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27113 s i) Zmod.one)) (Zmod.eqb (N.v27112 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27128 s i) Zmod.one)) (Zmod.eqb (N.v27127 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27140 s i) Zmod.one)) (Zmod.eqb (N.v27139 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27152 s i) Zmod.one)) (Zmod.eqb (N.v27151 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27167 s i) Zmod.one)) (Zmod.eqb (N.v27166 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27179 s i) Zmod.one)) (Zmod.eqb (N.v27178 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27191 s i) Zmod.one)) (Zmod.eqb (N.v27190 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27206 s i) Zmod.one)) (Zmod.eqb (N.v27205 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27218 s i) Zmod.one)) (Zmod.eqb (N.v27217 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27230 s i) Zmod.one)) (Zmod.eqb (N.v27229 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27245 s i) Zmod.one)) (Zmod.eqb (N.v27244 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27257 s i) Zmod.one)) (Zmod.eqb (N.v27256 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27269 s i) Zmod.one)) (Zmod.eqb (N.v27268 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27284 s i) Zmod.one)) (Zmod.eqb (N.v27283 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27296 s i) Zmod.one)) (Zmod.eqb (N.v27295 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27308 s i) Zmod.one)) (Zmod.eqb (N.v27307 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27323 s i) Zmod.one)) (Zmod.eqb (N.v27322 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27335 s i) Zmod.one)) (Zmod.eqb (N.v27334 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27347 s i) Zmod.one)) (Zmod.eqb (N.v27346 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27362 s i) Zmod.one)) (Zmod.eqb (N.v27361 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27374 s i) Zmod.one)) (Zmod.eqb (N.v27373 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27386 s i) Zmod.one)) (Zmod.eqb (N.v27385 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27395 s i) Zmod.one)) (Zmod.eqb (N.v27394 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27410 s i) Zmod.one)) (Zmod.eqb (N.v27409 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27422 s i) Zmod.one)) (Zmod.eqb (N.v27421 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27434 s i) Zmod.one)) (Zmod.eqb (N.v27433 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27449 s i) Zmod.one)) (Zmod.eqb (N.v27448 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27461 s i) Zmod.one)) (Zmod.eqb (N.v27460 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27473 s i) Zmod.one)) (Zmod.eqb (N.v27472 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27488 s i) Zmod.one)) (Zmod.eqb (N.v27487 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27500 s i) Zmod.one)) (Zmod.eqb (N.v27499 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27512 s i) Zmod.one)) (Zmod.eqb (N.v27511 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27527 s i) Zmod.one)) (Zmod.eqb (N.v27526 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27539 s i) Zmod.one)) (Zmod.eqb (N.v27538 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27551 s i) Zmod.one)) (Zmod.eqb (N.v27550 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27566 s i) Zmod.one)) (Zmod.eqb (N.v27565 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27578 s i) Zmod.one)) (Zmod.eqb (N.v27577 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27590 s i) Zmod.one)) (Zmod.eqb (N.v27589 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27605 s i) Zmod.one)) (Zmod.eqb (N.v27604 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27617 s i) Zmod.one)) (Zmod.eqb (N.v27616 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27629 s i) Zmod.one)) (Zmod.eqb (N.v27628 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27644 s i) Zmod.one)) (Zmod.eqb (N.v27643 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27656 s i) Zmod.one)) (Zmod.eqb (N.v27655 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27668 s i) Zmod.one)) (Zmod.eqb (N.v27667 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27683 s i) Zmod.one)) (Zmod.eqb (N.v27682 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27695 s i) Zmod.one)) (Zmod.eqb (N.v27694 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27707 s i) Zmod.one)) (Zmod.eqb (N.v27706 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27722 s i) Zmod.one)) (Zmod.eqb (N.v27721 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27734 s i) Zmod.one)) (Zmod.eqb (N.v27733 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27746 s i) Zmod.one)) (Zmod.eqb (N.v27745 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27761 s i) Zmod.one)) (Zmod.eqb (N.v27760 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27773 s i) Zmod.one)) (Zmod.eqb (N.v27772 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27785 s i) Zmod.one)) (Zmod.eqb (N.v27784 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27800 s i) Zmod.one)) (Zmod.eqb (N.v27799 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27812 s i) Zmod.one)) (Zmod.eqb (N.v27811 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27824 s i) Zmod.one)) (Zmod.eqb (N.v27823 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27839 s i) Zmod.one)) (Zmod.eqb (N.v27838 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27851 s i) Zmod.one)) (Zmod.eqb (N.v27850 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27863 s i) Zmod.one)) (Zmod.eqb (N.v27862 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27878 s i) Zmod.one)) (Zmod.eqb (N.v27877 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27890 s i) Zmod.one)) (Zmod.eqb (N.v27889 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27902 s i) Zmod.one)) (Zmod.eqb (N.v27901 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27917 s i) Zmod.one)) (Zmod.eqb (N.v27916 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27929 s i) Zmod.one)) (Zmod.eqb (N.v27928 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27941 s i) Zmod.one)) (Zmod.eqb (N.v27940 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27956 s i) Zmod.one)) (Zmod.eqb (N.v27955 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27968 s i) Zmod.one)) (Zmod.eqb (N.v27967 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27980 s i) Zmod.one)) (Zmod.eqb (N.v27979 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v27995 s i) Zmod.one)) (Zmod.eqb (N.v27994 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28007 s i) Zmod.one)) (Zmod.eqb (N.v28006 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28019 s i) Zmod.one)) (Zmod.eqb (N.v28018 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28034 s i) Zmod.one)) (Zmod.eqb (N.v28033 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28046 s i) Zmod.one)) (Zmod.eqb (N.v28045 s i) Zmod.one)
].
Lemma checks_8 s i : reference_checks_8 s i = native_checks_8 s i.
Proof. unfold reference_checks_8, native_checks_8.
  rewrite ?node_26767.
  rewrite ?node_26768.
  rewrite ?node_26779.
  rewrite ?node_26780.
  rewrite ?node_26791.
  rewrite ?node_26792.
  rewrite ?node_26806.
  rewrite ?node_26807.
  rewrite ?node_26818.
  rewrite ?node_26819.
  rewrite ?node_26830.
  rewrite ?node_26831.
  rewrite ?node_26845.
  rewrite ?node_26846.
  rewrite ?node_26857.
  rewrite ?node_26858.
  rewrite ?node_26869.
  rewrite ?node_26870.
  rewrite ?node_26884.
  rewrite ?node_26885.
  rewrite ?node_26896.
  rewrite ?node_26897.
  rewrite ?node_26908.
  rewrite ?node_26909.
  rewrite ?node_26923.
  rewrite ?node_26924.
  rewrite ?node_26935.
  rewrite ?node_26936.
  rewrite ?node_26947.
  rewrite ?node_26948.
  rewrite ?node_26962.
  rewrite ?node_26963.
  rewrite ?node_26974.
  rewrite ?node_26975.
  rewrite ?node_26986.
  rewrite ?node_26987.
  rewrite ?node_27001.
  rewrite ?node_27002.
  rewrite ?node_27013.
  rewrite ?node_27014.
  rewrite ?node_27025.
  rewrite ?node_27026.
  rewrite ?node_27040.
  rewrite ?node_27041.
  rewrite ?node_27052.
  rewrite ?node_27053.
  rewrite ?node_27064.
  rewrite ?node_27065.
  rewrite ?node_27073.
  rewrite ?node_27074.
  rewrite ?node_27088.
  rewrite ?node_27089.
  rewrite ?node_27100.
  rewrite ?node_27101.
  rewrite ?node_27112.
  rewrite ?node_27113.
  rewrite ?node_27127.
  rewrite ?node_27128.
  rewrite ?node_27139.
  rewrite ?node_27140.
  rewrite ?node_27151.
  rewrite ?node_27152.
  rewrite ?node_27166.
  rewrite ?node_27167.
  rewrite ?node_27178.
  rewrite ?node_27179.
  rewrite ?node_27190.
  rewrite ?node_27191.
  rewrite ?node_27205.
  rewrite ?node_27206.
  rewrite ?node_27217.
  rewrite ?node_27218.
  rewrite ?node_27229.
  rewrite ?node_27230.
  rewrite ?node_27244.
  rewrite ?node_27245.
  rewrite ?node_27256.
  rewrite ?node_27257.
  rewrite ?node_27268.
  rewrite ?node_27269.
  rewrite ?node_27283.
  rewrite ?node_27284.
  rewrite ?node_27295.
  rewrite ?node_27296.
  rewrite ?node_27307.
  rewrite ?node_27308.
  rewrite ?node_27322.
  rewrite ?node_27323.
  rewrite ?node_27334.
  rewrite ?node_27335.
  rewrite ?node_27346.
  rewrite ?node_27347.
  rewrite ?node_27361.
  rewrite ?node_27362.
  rewrite ?node_27373.
  rewrite ?node_27374.
  rewrite ?node_27385.
  rewrite ?node_27386.
  rewrite ?node_27394.
  rewrite ?node_27395.
  rewrite ?node_27409.
  rewrite ?node_27410.
  rewrite ?node_27421.
  rewrite ?node_27422.
  rewrite ?node_27433.
  rewrite ?node_27434.
  rewrite ?node_27448.
  rewrite ?node_27449.
  rewrite ?node_27460.
  rewrite ?node_27461.
  rewrite ?node_27472.
  rewrite ?node_27473.
  rewrite ?node_27487.
  rewrite ?node_27488.
  rewrite ?node_27499.
  rewrite ?node_27500.
  rewrite ?node_27511.
  rewrite ?node_27512.
  rewrite ?node_27526.
  rewrite ?node_27527.
  rewrite ?node_27538.
  rewrite ?node_27539.
  rewrite ?node_27550.
  rewrite ?node_27551.
  rewrite ?node_27565.
  rewrite ?node_27566.
  rewrite ?node_27577.
  rewrite ?node_27578.
  rewrite ?node_27589.
  rewrite ?node_27590.
  rewrite ?node_27604.
  rewrite ?node_27605.
  rewrite ?node_27616.
  rewrite ?node_27617.
  rewrite ?node_27628.
  rewrite ?node_27629.
  rewrite ?node_27643.
  rewrite ?node_27644.
  rewrite ?node_27655.
  rewrite ?node_27656.
  rewrite ?node_27667.
  rewrite ?node_27668.
  rewrite ?node_27682.
  rewrite ?node_27683.
  rewrite ?node_27694.
  rewrite ?node_27695.
  rewrite ?node_27706.
  rewrite ?node_27707.
  rewrite ?node_27721.
  rewrite ?node_27722.
  rewrite ?node_27733.
  rewrite ?node_27734.
  rewrite ?node_27745.
  rewrite ?node_27746.
  rewrite ?node_27760.
  rewrite ?node_27761.
  rewrite ?node_27772.
  rewrite ?node_27773.
  rewrite ?node_27784.
  rewrite ?node_27785.
  rewrite ?node_27799.
  rewrite ?node_27800.
  rewrite ?node_27811.
  rewrite ?node_27812.
  rewrite ?node_27823.
  rewrite ?node_27824.
  rewrite ?node_27838.
  rewrite ?node_27839.
  rewrite ?node_27850.
  rewrite ?node_27851.
  rewrite ?node_27862.
  rewrite ?node_27863.
  rewrite ?node_27877.
  rewrite ?node_27878.
  rewrite ?node_27889.
  rewrite ?node_27890.
  rewrite ?node_27901.
  rewrite ?node_27902.
  rewrite ?node_27916.
  rewrite ?node_27917.
  rewrite ?node_27928.
  rewrite ?node_27929.
  rewrite ?node_27940.
  rewrite ?node_27941.
  rewrite ?node_27955.
  rewrite ?node_27956.
  rewrite ?node_27967.
  rewrite ?node_27968.
  rewrite ?node_27979.
  rewrite ?node_27980.
  rewrite ?node_27994.
  rewrite ?node_27995.
  rewrite ?node_28006.
  rewrite ?node_28007.
  rewrite ?node_28018.
  rewrite ?node_28019.
  rewrite ?node_28033.
  rewrite ?node_28034.
  rewrite ?node_28045.
  rewrite ?node_28046.
  reflexivity.
Qed.

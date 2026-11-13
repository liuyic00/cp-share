From Stdlib Require Import ZArith List Bool Zmod.Bits.
From BitsProofs Require Import ArrayRefinementNodes020.
Import ListNotations.
Open Scope Z_scope.
Local Opaque R.v19022 N.v19022 R.v19023 N.v19023 R.v19034 N.v19034 R.v19035 N.v19035 R.v19049 N.v19049 R.v19050 N.v19050 R.v19061 N.v19061 R.v19062 N.v19062 R.v19073 N.v19073 R.v19074 N.v19074 R.v19088 N.v19088 R.v19089 N.v19089 R.v19100 N.v19100 R.v19101 N.v19101 R.v19112 N.v19112 R.v19113 N.v19113 R.v19127 N.v19127 R.v19128 N.v19128 R.v19139 N.v19139 R.v19140 N.v19140 R.v19151 N.v19151 R.v19152 N.v19152 R.v19166 N.v19166 R.v19167 N.v19167 R.v19178 N.v19178 R.v19179 N.v19179 R.v19190 N.v19190 R.v19191 N.v19191 R.v19205 N.v19205 R.v19206 N.v19206 R.v19217 N.v19217 R.v19218 N.v19218 R.v19229 N.v19229 R.v19230 N.v19230 R.v19244 N.v19244 R.v19245 N.v19245 R.v19256 N.v19256 R.v19257 N.v19257 R.v19268 N.v19268 R.v19269 N.v19269 R.v19277 N.v19277 R.v19278 N.v19278 R.v19292 N.v19292 R.v19293 N.v19293 R.v19304 N.v19304 R.v19305 N.v19305 R.v19316 N.v19316 R.v19317 N.v19317 R.v19331 N.v19331 R.v19332 N.v19332 R.v19343 N.v19343 R.v19344 N.v19344 R.v19355 N.v19355 R.v19356 N.v19356 R.v19370 N.v19370 R.v19371 N.v19371 R.v19382 N.v19382 R.v19383 N.v19383 R.v19394 N.v19394 R.v19395 N.v19395 R.v19409 N.v19409 R.v19410 N.v19410 R.v19421 N.v19421 R.v19422 N.v19422 R.v19433 N.v19433 R.v19434 N.v19434 R.v19442 N.v19442 R.v19443 N.v19443 R.v19457 N.v19457 R.v19458 N.v19458 R.v19469 N.v19469 R.v19470 N.v19470 R.v19481 N.v19481 R.v19482 N.v19482 R.v19496 N.v19496 R.v19497 N.v19497 R.v19508 N.v19508 R.v19509 N.v19509 R.v19520 N.v19520 R.v19521 N.v19521 R.v19535 N.v19535 R.v19536 N.v19536 R.v19547 N.v19547 R.v19548 N.v19548 R.v19559 N.v19559 R.v19560 N.v19560 R.v19574 N.v19574 R.v19575 N.v19575 R.v19586 N.v19586 R.v19587 N.v19587 R.v19598 N.v19598 R.v19599 N.v19599 R.v19610 N.v19610 R.v19611 N.v19611 R.v19625 N.v19625 R.v19626 N.v19626 R.v19637 N.v19637 R.v19638 N.v19638 R.v19649 N.v19649 R.v19650 N.v19650 R.v19664 N.v19664 R.v19665 N.v19665 R.v19676 N.v19676 R.v19677 N.v19677 R.v19688 N.v19688 R.v19689 N.v19689 R.v19703 N.v19703 R.v19704 N.v19704 R.v19715 N.v19715 R.v19716 N.v19716 R.v19727 N.v19727 R.v19728 N.v19728 R.v19742 N.v19742 R.v19743 N.v19743 R.v19754 N.v19754 R.v19755 N.v19755 R.v19766 N.v19766 R.v19767 N.v19767 R.v19778 N.v19778 R.v19779 N.v19779 R.v19793 N.v19793 R.v19794 N.v19794 R.v19805 N.v19805 R.v19806 N.v19806 R.v19817 N.v19817 R.v19818 N.v19818 R.v19832 N.v19832 R.v19833 N.v19833 R.v19844 N.v19844 R.v19845 N.v19845 R.v19856 N.v19856 R.v19857 N.v19857 R.v19871 N.v19871 R.v19872 N.v19872 R.v19883 N.v19883 R.v19884 N.v19884 R.v19895 N.v19895 R.v19896 N.v19896 R.v19910 N.v19910 R.v19911 N.v19911 R.v19922 N.v19922 R.v19923 N.v19923 R.v19934 N.v19934 R.v19935 N.v19935 R.v19948 N.v19948 R.v19949 N.v19949 R.v19960 N.v19960 R.v19961 N.v19961 R.v19969 N.v19969 R.v19970 N.v19970 R.v19984 N.v19984 R.v19985 N.v19985 R.v19996 N.v19996 R.v19997 N.v19997 R.v20008 N.v20008 R.v20009 N.v20009 R.v20023 N.v20023 R.v20024 N.v20024 R.v20035 N.v20035 R.v20036 N.v20036 R.v20047 N.v20047 R.v20048 N.v20048 R.v20062 N.v20062 R.v20063 N.v20063 R.v20074 N.v20074 R.v20075 N.v20075 R.v20086 N.v20086 R.v20087 N.v20087 R.v20101 N.v20101 R.v20102 N.v20102 R.v20113 N.v20113 R.v20114 N.v20114 R.v20125 N.v20125 R.v20126 N.v20126 R.v20140 N.v20140 R.v20141 N.v20141 R.v20152 N.v20152 R.v20153 N.v20153 R.v20164 N.v20164 R.v20165 N.v20165 R.v20179 N.v20179 R.v20180 N.v20180 R.v20191 N.v20191 R.v20192 N.v20192 R.v20203 N.v20203 R.v20204 N.v20204 R.v20218 N.v20218 R.v20219 N.v20219 R.v20230 N.v20230 R.v20231 N.v20231 R.v20242 N.v20242 R.v20243 N.v20243 R.v20257 N.v20257 R.v20258 N.v20258 R.v20269 N.v20269 R.v20270 N.v20270 R.v20281 N.v20281 R.v20282 N.v20282 R.v20296 N.v20296 R.v20297 N.v20297.
Definition reference_checks_2 (s : N.State) (i : N.Inputs) : list bool := [
orb (negb (Z.eqb (R.v19023 (state s) (inputs i)) 1)) (Z.eqb (R.v19022 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19035 (state s) (inputs i)) 1)) (Z.eqb (R.v19034 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19050 (state s) (inputs i)) 1)) (Z.eqb (R.v19049 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19062 (state s) (inputs i)) 1)) (Z.eqb (R.v19061 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19074 (state s) (inputs i)) 1)) (Z.eqb (R.v19073 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19089 (state s) (inputs i)) 1)) (Z.eqb (R.v19088 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19101 (state s) (inputs i)) 1)) (Z.eqb (R.v19100 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19113 (state s) (inputs i)) 1)) (Z.eqb (R.v19112 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19128 (state s) (inputs i)) 1)) (Z.eqb (R.v19127 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19140 (state s) (inputs i)) 1)) (Z.eqb (R.v19139 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19152 (state s) (inputs i)) 1)) (Z.eqb (R.v19151 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19167 (state s) (inputs i)) 1)) (Z.eqb (R.v19166 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19179 (state s) (inputs i)) 1)) (Z.eqb (R.v19178 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19191 (state s) (inputs i)) 1)) (Z.eqb (R.v19190 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19206 (state s) (inputs i)) 1)) (Z.eqb (R.v19205 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19218 (state s) (inputs i)) 1)) (Z.eqb (R.v19217 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19230 (state s) (inputs i)) 1)) (Z.eqb (R.v19229 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19245 (state s) (inputs i)) 1)) (Z.eqb (R.v19244 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19257 (state s) (inputs i)) 1)) (Z.eqb (R.v19256 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19269 (state s) (inputs i)) 1)) (Z.eqb (R.v19268 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19278 (state s) (inputs i)) 1)) (Z.eqb (R.v19277 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19293 (state s) (inputs i)) 1)) (Z.eqb (R.v19292 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19305 (state s) (inputs i)) 1)) (Z.eqb (R.v19304 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19317 (state s) (inputs i)) 1)) (Z.eqb (R.v19316 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19332 (state s) (inputs i)) 1)) (Z.eqb (R.v19331 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19344 (state s) (inputs i)) 1)) (Z.eqb (R.v19343 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19356 (state s) (inputs i)) 1)) (Z.eqb (R.v19355 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19371 (state s) (inputs i)) 1)) (Z.eqb (R.v19370 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19383 (state s) (inputs i)) 1)) (Z.eqb (R.v19382 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19395 (state s) (inputs i)) 1)) (Z.eqb (R.v19394 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19410 (state s) (inputs i)) 1)) (Z.eqb (R.v19409 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19422 (state s) (inputs i)) 1)) (Z.eqb (R.v19421 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19434 (state s) (inputs i)) 1)) (Z.eqb (R.v19433 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19443 (state s) (inputs i)) 1)) (Z.eqb (R.v19442 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19458 (state s) (inputs i)) 1)) (Z.eqb (R.v19457 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19470 (state s) (inputs i)) 1)) (Z.eqb (R.v19469 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19482 (state s) (inputs i)) 1)) (Z.eqb (R.v19481 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19497 (state s) (inputs i)) 1)) (Z.eqb (R.v19496 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19509 (state s) (inputs i)) 1)) (Z.eqb (R.v19508 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19521 (state s) (inputs i)) 1)) (Z.eqb (R.v19520 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19536 (state s) (inputs i)) 1)) (Z.eqb (R.v19535 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19548 (state s) (inputs i)) 1)) (Z.eqb (R.v19547 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19560 (state s) (inputs i)) 1)) (Z.eqb (R.v19559 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19575 (state s) (inputs i)) 1)) (Z.eqb (R.v19574 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19587 (state s) (inputs i)) 1)) (Z.eqb (R.v19586 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19599 (state s) (inputs i)) 1)) (Z.eqb (R.v19598 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19611 (state s) (inputs i)) 1)) (Z.eqb (R.v19610 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19626 (state s) (inputs i)) 1)) (Z.eqb (R.v19625 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19638 (state s) (inputs i)) 1)) (Z.eqb (R.v19637 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19650 (state s) (inputs i)) 1)) (Z.eqb (R.v19649 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19665 (state s) (inputs i)) 1)) (Z.eqb (R.v19664 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19677 (state s) (inputs i)) 1)) (Z.eqb (R.v19676 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19689 (state s) (inputs i)) 1)) (Z.eqb (R.v19688 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19704 (state s) (inputs i)) 1)) (Z.eqb (R.v19703 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19716 (state s) (inputs i)) 1)) (Z.eqb (R.v19715 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19728 (state s) (inputs i)) 1)) (Z.eqb (R.v19727 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19743 (state s) (inputs i)) 1)) (Z.eqb (R.v19742 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19755 (state s) (inputs i)) 1)) (Z.eqb (R.v19754 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19767 (state s) (inputs i)) 1)) (Z.eqb (R.v19766 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19779 (state s) (inputs i)) 1)) (Z.eqb (R.v19778 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19794 (state s) (inputs i)) 1)) (Z.eqb (R.v19793 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19806 (state s) (inputs i)) 1)) (Z.eqb (R.v19805 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19818 (state s) (inputs i)) 1)) (Z.eqb (R.v19817 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19833 (state s) (inputs i)) 1)) (Z.eqb (R.v19832 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19845 (state s) (inputs i)) 1)) (Z.eqb (R.v19844 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19857 (state s) (inputs i)) 1)) (Z.eqb (R.v19856 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19872 (state s) (inputs i)) 1)) (Z.eqb (R.v19871 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19884 (state s) (inputs i)) 1)) (Z.eqb (R.v19883 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19896 (state s) (inputs i)) 1)) (Z.eqb (R.v19895 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19911 (state s) (inputs i)) 1)) (Z.eqb (R.v19910 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19923 (state s) (inputs i)) 1)) (Z.eqb (R.v19922 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19935 (state s) (inputs i)) 1)) (Z.eqb (R.v19934 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19949 (state s) (inputs i)) 1)) (Z.eqb (R.v19948 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19961 (state s) (inputs i)) 1)) (Z.eqb (R.v19960 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19970 (state s) (inputs i)) 1)) (Z.eqb (R.v19969 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19985 (state s) (inputs i)) 1)) (Z.eqb (R.v19984 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19997 (state s) (inputs i)) 1)) (Z.eqb (R.v19996 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20009 (state s) (inputs i)) 1)) (Z.eqb (R.v20008 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20024 (state s) (inputs i)) 1)) (Z.eqb (R.v20023 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20036 (state s) (inputs i)) 1)) (Z.eqb (R.v20035 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20048 (state s) (inputs i)) 1)) (Z.eqb (R.v20047 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20063 (state s) (inputs i)) 1)) (Z.eqb (R.v20062 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20075 (state s) (inputs i)) 1)) (Z.eqb (R.v20074 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20087 (state s) (inputs i)) 1)) (Z.eqb (R.v20086 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20102 (state s) (inputs i)) 1)) (Z.eqb (R.v20101 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20114 (state s) (inputs i)) 1)) (Z.eqb (R.v20113 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20126 (state s) (inputs i)) 1)) (Z.eqb (R.v20125 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20141 (state s) (inputs i)) 1)) (Z.eqb (R.v20140 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20153 (state s) (inputs i)) 1)) (Z.eqb (R.v20152 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20165 (state s) (inputs i)) 1)) (Z.eqb (R.v20164 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20180 (state s) (inputs i)) 1)) (Z.eqb (R.v20179 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20192 (state s) (inputs i)) 1)) (Z.eqb (R.v20191 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20204 (state s) (inputs i)) 1)) (Z.eqb (R.v20203 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20219 (state s) (inputs i)) 1)) (Z.eqb (R.v20218 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20231 (state s) (inputs i)) 1)) (Z.eqb (R.v20230 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20243 (state s) (inputs i)) 1)) (Z.eqb (R.v20242 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20258 (state s) (inputs i)) 1)) (Z.eqb (R.v20257 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20270 (state s) (inputs i)) 1)) (Z.eqb (R.v20269 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20282 (state s) (inputs i)) 1)) (Z.eqb (R.v20281 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20297 (state s) (inputs i)) 1)) (Z.eqb (R.v20296 (state s) (inputs i)) 1)
].
Definition native_checks_2 (s : N.State) (i : N.Inputs) : list bool := [
orb (negb (Zmod.eqb (N.v19023 s i) Zmod.one)) (Zmod.eqb (N.v19022 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19035 s i) Zmod.one)) (Zmod.eqb (N.v19034 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19050 s i) Zmod.one)) (Zmod.eqb (N.v19049 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19062 s i) Zmod.one)) (Zmod.eqb (N.v19061 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19074 s i) Zmod.one)) (Zmod.eqb (N.v19073 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19089 s i) Zmod.one)) (Zmod.eqb (N.v19088 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19101 s i) Zmod.one)) (Zmod.eqb (N.v19100 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19113 s i) Zmod.one)) (Zmod.eqb (N.v19112 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19128 s i) Zmod.one)) (Zmod.eqb (N.v19127 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19140 s i) Zmod.one)) (Zmod.eqb (N.v19139 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19152 s i) Zmod.one)) (Zmod.eqb (N.v19151 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19167 s i) Zmod.one)) (Zmod.eqb (N.v19166 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19179 s i) Zmod.one)) (Zmod.eqb (N.v19178 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19191 s i) Zmod.one)) (Zmod.eqb (N.v19190 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19206 s i) Zmod.one)) (Zmod.eqb (N.v19205 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19218 s i) Zmod.one)) (Zmod.eqb (N.v19217 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19230 s i) Zmod.one)) (Zmod.eqb (N.v19229 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19245 s i) Zmod.one)) (Zmod.eqb (N.v19244 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19257 s i) Zmod.one)) (Zmod.eqb (N.v19256 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19269 s i) Zmod.one)) (Zmod.eqb (N.v19268 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19278 s i) Zmod.one)) (Zmod.eqb (N.v19277 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19293 s i) Zmod.one)) (Zmod.eqb (N.v19292 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19305 s i) Zmod.one)) (Zmod.eqb (N.v19304 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19317 s i) Zmod.one)) (Zmod.eqb (N.v19316 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19332 s i) Zmod.one)) (Zmod.eqb (N.v19331 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19344 s i) Zmod.one)) (Zmod.eqb (N.v19343 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19356 s i) Zmod.one)) (Zmod.eqb (N.v19355 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19371 s i) Zmod.one)) (Zmod.eqb (N.v19370 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19383 s i) Zmod.one)) (Zmod.eqb (N.v19382 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19395 s i) Zmod.one)) (Zmod.eqb (N.v19394 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19410 s i) Zmod.one)) (Zmod.eqb (N.v19409 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19422 s i) Zmod.one)) (Zmod.eqb (N.v19421 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19434 s i) Zmod.one)) (Zmod.eqb (N.v19433 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19443 s i) Zmod.one)) (Zmod.eqb (N.v19442 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19458 s i) Zmod.one)) (Zmod.eqb (N.v19457 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19470 s i) Zmod.one)) (Zmod.eqb (N.v19469 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19482 s i) Zmod.one)) (Zmod.eqb (N.v19481 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19497 s i) Zmod.one)) (Zmod.eqb (N.v19496 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19509 s i) Zmod.one)) (Zmod.eqb (N.v19508 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19521 s i) Zmod.one)) (Zmod.eqb (N.v19520 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19536 s i) Zmod.one)) (Zmod.eqb (N.v19535 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19548 s i) Zmod.one)) (Zmod.eqb (N.v19547 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19560 s i) Zmod.one)) (Zmod.eqb (N.v19559 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19575 s i) Zmod.one)) (Zmod.eqb (N.v19574 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19587 s i) Zmod.one)) (Zmod.eqb (N.v19586 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19599 s i) Zmod.one)) (Zmod.eqb (N.v19598 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19611 s i) Zmod.one)) (Zmod.eqb (N.v19610 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19626 s i) Zmod.one)) (Zmod.eqb (N.v19625 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19638 s i) Zmod.one)) (Zmod.eqb (N.v19637 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19650 s i) Zmod.one)) (Zmod.eqb (N.v19649 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19665 s i) Zmod.one)) (Zmod.eqb (N.v19664 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19677 s i) Zmod.one)) (Zmod.eqb (N.v19676 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19689 s i) Zmod.one)) (Zmod.eqb (N.v19688 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19704 s i) Zmod.one)) (Zmod.eqb (N.v19703 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19716 s i) Zmod.one)) (Zmod.eqb (N.v19715 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19728 s i) Zmod.one)) (Zmod.eqb (N.v19727 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19743 s i) Zmod.one)) (Zmod.eqb (N.v19742 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19755 s i) Zmod.one)) (Zmod.eqb (N.v19754 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19767 s i) Zmod.one)) (Zmod.eqb (N.v19766 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19779 s i) Zmod.one)) (Zmod.eqb (N.v19778 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19794 s i) Zmod.one)) (Zmod.eqb (N.v19793 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19806 s i) Zmod.one)) (Zmod.eqb (N.v19805 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19818 s i) Zmod.one)) (Zmod.eqb (N.v19817 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19833 s i) Zmod.one)) (Zmod.eqb (N.v19832 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19845 s i) Zmod.one)) (Zmod.eqb (N.v19844 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19857 s i) Zmod.one)) (Zmod.eqb (N.v19856 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19872 s i) Zmod.one)) (Zmod.eqb (N.v19871 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19884 s i) Zmod.one)) (Zmod.eqb (N.v19883 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19896 s i) Zmod.one)) (Zmod.eqb (N.v19895 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19911 s i) Zmod.one)) (Zmod.eqb (N.v19910 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19923 s i) Zmod.one)) (Zmod.eqb (N.v19922 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19935 s i) Zmod.one)) (Zmod.eqb (N.v19934 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19949 s i) Zmod.one)) (Zmod.eqb (N.v19948 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19961 s i) Zmod.one)) (Zmod.eqb (N.v19960 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19970 s i) Zmod.one)) (Zmod.eqb (N.v19969 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19985 s i) Zmod.one)) (Zmod.eqb (N.v19984 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19997 s i) Zmod.one)) (Zmod.eqb (N.v19996 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20009 s i) Zmod.one)) (Zmod.eqb (N.v20008 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20024 s i) Zmod.one)) (Zmod.eqb (N.v20023 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20036 s i) Zmod.one)) (Zmod.eqb (N.v20035 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20048 s i) Zmod.one)) (Zmod.eqb (N.v20047 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20063 s i) Zmod.one)) (Zmod.eqb (N.v20062 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20075 s i) Zmod.one)) (Zmod.eqb (N.v20074 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20087 s i) Zmod.one)) (Zmod.eqb (N.v20086 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20102 s i) Zmod.one)) (Zmod.eqb (N.v20101 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20114 s i) Zmod.one)) (Zmod.eqb (N.v20113 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20126 s i) Zmod.one)) (Zmod.eqb (N.v20125 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20141 s i) Zmod.one)) (Zmod.eqb (N.v20140 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20153 s i) Zmod.one)) (Zmod.eqb (N.v20152 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20165 s i) Zmod.one)) (Zmod.eqb (N.v20164 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20180 s i) Zmod.one)) (Zmod.eqb (N.v20179 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20192 s i) Zmod.one)) (Zmod.eqb (N.v20191 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20204 s i) Zmod.one)) (Zmod.eqb (N.v20203 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20219 s i) Zmod.one)) (Zmod.eqb (N.v20218 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20231 s i) Zmod.one)) (Zmod.eqb (N.v20230 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20243 s i) Zmod.one)) (Zmod.eqb (N.v20242 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20258 s i) Zmod.one)) (Zmod.eqb (N.v20257 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20270 s i) Zmod.one)) (Zmod.eqb (N.v20269 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20282 s i) Zmod.one)) (Zmod.eqb (N.v20281 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20297 s i) Zmod.one)) (Zmod.eqb (N.v20296 s i) Zmod.one)
].
Lemma checks_2 s i : reference_checks_2 s i = native_checks_2 s i.
Proof. unfold reference_checks_2, native_checks_2.
  rewrite ?node_19022.
  rewrite ?node_19023.
  rewrite ?node_19034.
  rewrite ?node_19035.
  rewrite ?node_19049.
  rewrite ?node_19050.
  rewrite ?node_19061.
  rewrite ?node_19062.
  rewrite ?node_19073.
  rewrite ?node_19074.
  rewrite ?node_19088.
  rewrite ?node_19089.
  rewrite ?node_19100.
  rewrite ?node_19101.
  rewrite ?node_19112.
  rewrite ?node_19113.
  rewrite ?node_19127.
  rewrite ?node_19128.
  rewrite ?node_19139.
  rewrite ?node_19140.
  rewrite ?node_19151.
  rewrite ?node_19152.
  rewrite ?node_19166.
  rewrite ?node_19167.
  rewrite ?node_19178.
  rewrite ?node_19179.
  rewrite ?node_19190.
  rewrite ?node_19191.
  rewrite ?node_19205.
  rewrite ?node_19206.
  rewrite ?node_19217.
  rewrite ?node_19218.
  rewrite ?node_19229.
  rewrite ?node_19230.
  rewrite ?node_19244.
  rewrite ?node_19245.
  rewrite ?node_19256.
  rewrite ?node_19257.
  rewrite ?node_19268.
  rewrite ?node_19269.
  rewrite ?node_19277.
  rewrite ?node_19278.
  rewrite ?node_19292.
  rewrite ?node_19293.
  rewrite ?node_19304.
  rewrite ?node_19305.
  rewrite ?node_19316.
  rewrite ?node_19317.
  rewrite ?node_19331.
  rewrite ?node_19332.
  rewrite ?node_19343.
  rewrite ?node_19344.
  rewrite ?node_19355.
  rewrite ?node_19356.
  rewrite ?node_19370.
  rewrite ?node_19371.
  rewrite ?node_19382.
  rewrite ?node_19383.
  rewrite ?node_19394.
  rewrite ?node_19395.
  rewrite ?node_19409.
  rewrite ?node_19410.
  rewrite ?node_19421.
  rewrite ?node_19422.
  rewrite ?node_19433.
  rewrite ?node_19434.
  rewrite ?node_19442.
  rewrite ?node_19443.
  rewrite ?node_19457.
  rewrite ?node_19458.
  rewrite ?node_19469.
  rewrite ?node_19470.
  rewrite ?node_19481.
  rewrite ?node_19482.
  rewrite ?node_19496.
  rewrite ?node_19497.
  rewrite ?node_19508.
  rewrite ?node_19509.
  rewrite ?node_19520.
  rewrite ?node_19521.
  rewrite ?node_19535.
  rewrite ?node_19536.
  rewrite ?node_19547.
  rewrite ?node_19548.
  rewrite ?node_19559.
  rewrite ?node_19560.
  rewrite ?node_19574.
  rewrite ?node_19575.
  rewrite ?node_19586.
  rewrite ?node_19587.
  rewrite ?node_19598.
  rewrite ?node_19599.
  rewrite ?node_19610.
  rewrite ?node_19611.
  rewrite ?node_19625.
  rewrite ?node_19626.
  rewrite ?node_19637.
  rewrite ?node_19638.
  rewrite ?node_19649.
  rewrite ?node_19650.
  rewrite ?node_19664.
  rewrite ?node_19665.
  rewrite ?node_19676.
  rewrite ?node_19677.
  rewrite ?node_19688.
  rewrite ?node_19689.
  rewrite ?node_19703.
  rewrite ?node_19704.
  rewrite ?node_19715.
  rewrite ?node_19716.
  rewrite ?node_19727.
  rewrite ?node_19728.
  rewrite ?node_19742.
  rewrite ?node_19743.
  rewrite ?node_19754.
  rewrite ?node_19755.
  rewrite ?node_19766.
  rewrite ?node_19767.
  rewrite ?node_19778.
  rewrite ?node_19779.
  rewrite ?node_19793.
  rewrite ?node_19794.
  rewrite ?node_19805.
  rewrite ?node_19806.
  rewrite ?node_19817.
  rewrite ?node_19818.
  rewrite ?node_19832.
  rewrite ?node_19833.
  rewrite ?node_19844.
  rewrite ?node_19845.
  rewrite ?node_19856.
  rewrite ?node_19857.
  rewrite ?node_19871.
  rewrite ?node_19872.
  rewrite ?node_19883.
  rewrite ?node_19884.
  rewrite ?node_19895.
  rewrite ?node_19896.
  rewrite ?node_19910.
  rewrite ?node_19911.
  rewrite ?node_19922.
  rewrite ?node_19923.
  rewrite ?node_19934.
  rewrite ?node_19935.
  rewrite ?node_19948.
  rewrite ?node_19949.
  rewrite ?node_19960.
  rewrite ?node_19961.
  rewrite ?node_19969.
  rewrite ?node_19970.
  rewrite ?node_19984.
  rewrite ?node_19985.
  rewrite ?node_19996.
  rewrite ?node_19997.
  rewrite ?node_20008.
  rewrite ?node_20009.
  rewrite ?node_20023.
  rewrite ?node_20024.
  rewrite ?node_20035.
  rewrite ?node_20036.
  rewrite ?node_20047.
  rewrite ?node_20048.
  rewrite ?node_20062.
  rewrite ?node_20063.
  rewrite ?node_20074.
  rewrite ?node_20075.
  rewrite ?node_20086.
  rewrite ?node_20087.
  rewrite ?node_20101.
  rewrite ?node_20102.
  rewrite ?node_20113.
  rewrite ?node_20114.
  rewrite ?node_20125.
  rewrite ?node_20126.
  rewrite ?node_20140.
  rewrite ?node_20141.
  rewrite ?node_20152.
  rewrite ?node_20153.
  rewrite ?node_20164.
  rewrite ?node_20165.
  rewrite ?node_20179.
  rewrite ?node_20180.
  rewrite ?node_20191.
  rewrite ?node_20192.
  rewrite ?node_20203.
  rewrite ?node_20204.
  rewrite ?node_20218.
  rewrite ?node_20219.
  rewrite ?node_20230.
  rewrite ?node_20231.
  rewrite ?node_20242.
  rewrite ?node_20243.
  rewrite ?node_20257.
  rewrite ?node_20258.
  rewrite ?node_20269.
  rewrite ?node_20270.
  rewrite ?node_20281.
  rewrite ?node_20282.
  rewrite ?node_20296.
  rewrite ?node_20297.
  reflexivity.
Qed.

From Stdlib Require Import ZArith List Bool Zmod.Bits.
From BitsProofs Require Import ArrayRefinementNodes058.
Import ListNotations.
Open Scope Z_scope.
Local Opaque R.v57236 N.v57236 R.v57237 N.v57237 R.v57245 N.v57245 R.v57246 N.v57246 R.v57254 N.v57254 R.v57255 N.v57255 R.v57266 N.v57266 R.v57267 N.v57267 R.v57275 N.v57275 R.v57276 N.v57276 R.v57284 N.v57284 R.v57285 N.v57285 R.v57293 N.v57293 R.v57294 N.v57294 R.v57302 N.v57302 R.v57303 N.v57303 R.v57311 N.v57311 R.v57312 N.v57312 R.v57320 N.v57320 R.v57321 N.v57321 R.v57329 N.v57329 R.v57330 N.v57330 R.v57338 N.v57338 R.v57339 N.v57339 R.v57350 N.v57350 R.v57351 N.v57351 R.v57359 N.v57359 R.v57360 N.v57360 R.v57368 N.v57368 R.v57369 N.v57369 R.v57377 N.v57377 R.v57378 N.v57378 R.v57386 N.v57386 R.v57387 N.v57387 R.v57395 N.v57395 R.v57396 N.v57396 R.v57404 N.v57404 R.v57405 N.v57405 R.v57413 N.v57413 R.v57414 N.v57414 R.v57422 N.v57422 R.v57423 N.v57423 R.v57431 N.v57431 R.v57432 N.v57432 R.v57440 N.v57440 R.v57441 N.v57441 R.v57449 N.v57449 R.v57450 N.v57450 R.v57458 N.v57458 R.v57459 N.v57459 R.v57468 N.v57468 R.v57469 N.v57469 R.v57477 N.v57477 R.v57478 N.v57478 R.v57486 N.v57486 R.v57487 N.v57487 R.v57495 N.v57495 R.v57496 N.v57496 R.v57504 N.v57504 R.v57505 N.v57505 R.v57513 N.v57513 R.v57514 N.v57514 R.v57522 N.v57522 R.v57523 N.v57523 R.v57531 N.v57531 R.v57532 N.v57532 R.v57540 N.v57540 R.v57541 N.v57541 R.v57549 N.v57549 R.v57550 N.v57550 R.v57558 N.v57558 R.v57559 N.v57559 R.v57567 N.v57567 R.v57568 N.v57568 R.v57576 N.v57576 R.v57577 N.v57577 R.v57585 N.v57585 R.v57586 N.v57586 R.v57594 N.v57594 R.v57595 N.v57595 R.v57603 N.v57603 R.v57604 N.v57604 R.v57612 N.v57612 R.v57613 N.v57613 R.v57621 N.v57621 R.v57622 N.v57622 R.v57630 N.v57630 R.v57631 N.v57631 R.v57639 N.v57639 R.v57640 N.v57640 R.v57648 N.v57648 R.v57649 N.v57649 R.v57657 N.v57657 R.v57658 N.v57658 R.v57666 N.v57666 R.v57667 N.v57667 R.v57675 N.v57675 R.v57676 N.v57676 R.v57684 N.v57684 R.v57685 N.v57685 R.v57693 N.v57693 R.v57694 N.v57694 R.v57702 N.v57702 R.v57703 N.v57703 R.v57711 N.v57711 R.v57712 N.v57712 R.v57720 N.v57720 R.v57721 N.v57721 R.v57729 N.v57729 R.v57730 N.v57730 R.v57738 N.v57738 R.v57739 N.v57739 R.v57747 N.v57747 R.v57748 N.v57748 R.v57756 N.v57756 R.v57757 N.v57757 R.v57765 N.v57765 R.v57766 N.v57766 R.v57774 N.v57774 R.v57775 N.v57775 R.v57783 N.v57783 R.v57784 N.v57784 R.v57792 N.v57792 R.v57793 N.v57793 R.v57801 N.v57801 R.v57802 N.v57802 R.v57810 N.v57810 R.v57811 N.v57811 R.v57819 N.v57819 R.v57820 N.v57820 R.v57828 N.v57828 R.v57829 N.v57829 R.v57837 N.v57837 R.v57838 N.v57838 R.v57846 N.v57846 R.v57847 N.v57847 R.v57855 N.v57855 R.v57856 N.v57856 R.v57864 N.v57864 R.v57865 N.v57865 R.v57873 N.v57873 R.v57874 N.v57874 R.v57882 N.v57882 R.v57883 N.v57883 R.v57891 N.v57891 R.v57892 N.v57892 R.v57900 N.v57900 R.v57901 N.v57901 R.v57909 N.v57909 R.v57910 N.v57910 R.v57918 N.v57918 R.v57919 N.v57919 R.v57927 N.v57927 R.v57928 N.v57928 R.v57936 N.v57936 R.v57937 N.v57937 R.v57945 N.v57945 R.v57946 N.v57946 R.v57954 N.v57954 R.v57955 N.v57955 R.v57963 N.v57963 R.v57964 N.v57964 R.v57972 N.v57972 R.v57973 N.v57973 R.v57981 N.v57981 R.v57982 N.v57982 R.v57990 N.v57990 R.v57991 N.v57991 R.v58002 N.v58002 R.v58003 N.v58003 R.v58014 N.v58014 R.v58015 N.v58015 R.v58026 N.v58026 R.v58027 N.v58027 R.v58038 N.v58038 R.v58039 N.v58039 R.v58050 N.v58050 R.v58051 N.v58051 R.v58062 N.v58062 R.v58063 N.v58063 R.v58076 N.v58076 R.v58077 N.v58077 R.v58088 N.v58088 R.v58089 N.v58089 R.v58097 N.v58097 R.v58098 N.v58098 R.v58109 N.v58109 R.v58110 N.v58110 R.v58121 N.v58121 R.v58122 N.v58122 R.v58130 N.v58130 R.v58131 N.v58131 R.v58139 N.v58139 R.v58140 N.v58140 R.v58148 N.v58148 R.v58149 N.v58149 R.v58157 N.v58157 R.v58158 N.v58158 R.v58169 N.v58169 R.v58170 N.v58170.
Definition reference_checks_32 (s : N.State) (i : N.Inputs) : list bool := [
orb (negb (Z.eqb (R.v57237 (state s) (inputs i)) 1)) (Z.eqb (R.v57236 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57246 (state s) (inputs i)) 1)) (Z.eqb (R.v57245 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57255 (state s) (inputs i)) 1)) (Z.eqb (R.v57254 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57267 (state s) (inputs i)) 1)) (Z.eqb (R.v57266 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57276 (state s) (inputs i)) 1)) (Z.eqb (R.v57275 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57285 (state s) (inputs i)) 1)) (Z.eqb (R.v57284 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57294 (state s) (inputs i)) 1)) (Z.eqb (R.v57293 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57303 (state s) (inputs i)) 1)) (Z.eqb (R.v57302 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57312 (state s) (inputs i)) 1)) (Z.eqb (R.v57311 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57321 (state s) (inputs i)) 1)) (Z.eqb (R.v57320 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57330 (state s) (inputs i)) 1)) (Z.eqb (R.v57329 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57339 (state s) (inputs i)) 1)) (Z.eqb (R.v57338 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57351 (state s) (inputs i)) 1)) (Z.eqb (R.v57350 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57360 (state s) (inputs i)) 1)) (Z.eqb (R.v57359 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57369 (state s) (inputs i)) 1)) (Z.eqb (R.v57368 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57378 (state s) (inputs i)) 1)) (Z.eqb (R.v57377 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57387 (state s) (inputs i)) 1)) (Z.eqb (R.v57386 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57396 (state s) (inputs i)) 1)) (Z.eqb (R.v57395 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57405 (state s) (inputs i)) 1)) (Z.eqb (R.v57404 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57414 (state s) (inputs i)) 1)) (Z.eqb (R.v57413 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57423 (state s) (inputs i)) 1)) (Z.eqb (R.v57422 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57432 (state s) (inputs i)) 1)) (Z.eqb (R.v57431 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57441 (state s) (inputs i)) 1)) (Z.eqb (R.v57440 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57450 (state s) (inputs i)) 1)) (Z.eqb (R.v57449 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57459 (state s) (inputs i)) 1)) (Z.eqb (R.v57458 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57469 (state s) (inputs i)) 1)) (Z.eqb (R.v57468 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57478 (state s) (inputs i)) 1)) (Z.eqb (R.v57477 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57487 (state s) (inputs i)) 1)) (Z.eqb (R.v57486 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57496 (state s) (inputs i)) 1)) (Z.eqb (R.v57495 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57505 (state s) (inputs i)) 1)) (Z.eqb (R.v57504 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57514 (state s) (inputs i)) 1)) (Z.eqb (R.v57513 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57523 (state s) (inputs i)) 1)) (Z.eqb (R.v57522 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57532 (state s) (inputs i)) 1)) (Z.eqb (R.v57531 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57541 (state s) (inputs i)) 1)) (Z.eqb (R.v57540 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57550 (state s) (inputs i)) 1)) (Z.eqb (R.v57549 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57559 (state s) (inputs i)) 1)) (Z.eqb (R.v57558 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57568 (state s) (inputs i)) 1)) (Z.eqb (R.v57567 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57577 (state s) (inputs i)) 1)) (Z.eqb (R.v57576 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57586 (state s) (inputs i)) 1)) (Z.eqb (R.v57585 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57595 (state s) (inputs i)) 1)) (Z.eqb (R.v57594 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57604 (state s) (inputs i)) 1)) (Z.eqb (R.v57603 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57613 (state s) (inputs i)) 1)) (Z.eqb (R.v57612 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57622 (state s) (inputs i)) 1)) (Z.eqb (R.v57621 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57631 (state s) (inputs i)) 1)) (Z.eqb (R.v57630 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57640 (state s) (inputs i)) 1)) (Z.eqb (R.v57639 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57649 (state s) (inputs i)) 1)) (Z.eqb (R.v57648 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57658 (state s) (inputs i)) 1)) (Z.eqb (R.v57657 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57667 (state s) (inputs i)) 1)) (Z.eqb (R.v57666 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57676 (state s) (inputs i)) 1)) (Z.eqb (R.v57675 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57685 (state s) (inputs i)) 1)) (Z.eqb (R.v57684 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57694 (state s) (inputs i)) 1)) (Z.eqb (R.v57693 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57703 (state s) (inputs i)) 1)) (Z.eqb (R.v57702 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57712 (state s) (inputs i)) 1)) (Z.eqb (R.v57711 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57721 (state s) (inputs i)) 1)) (Z.eqb (R.v57720 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57730 (state s) (inputs i)) 1)) (Z.eqb (R.v57729 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57739 (state s) (inputs i)) 1)) (Z.eqb (R.v57738 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57748 (state s) (inputs i)) 1)) (Z.eqb (R.v57747 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57757 (state s) (inputs i)) 1)) (Z.eqb (R.v57756 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57766 (state s) (inputs i)) 1)) (Z.eqb (R.v57765 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57775 (state s) (inputs i)) 1)) (Z.eqb (R.v57774 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57784 (state s) (inputs i)) 1)) (Z.eqb (R.v57783 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57793 (state s) (inputs i)) 1)) (Z.eqb (R.v57792 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57802 (state s) (inputs i)) 1)) (Z.eqb (R.v57801 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57811 (state s) (inputs i)) 1)) (Z.eqb (R.v57810 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57820 (state s) (inputs i)) 1)) (Z.eqb (R.v57819 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57829 (state s) (inputs i)) 1)) (Z.eqb (R.v57828 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57838 (state s) (inputs i)) 1)) (Z.eqb (R.v57837 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57847 (state s) (inputs i)) 1)) (Z.eqb (R.v57846 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57856 (state s) (inputs i)) 1)) (Z.eqb (R.v57855 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57865 (state s) (inputs i)) 1)) (Z.eqb (R.v57864 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57874 (state s) (inputs i)) 1)) (Z.eqb (R.v57873 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57883 (state s) (inputs i)) 1)) (Z.eqb (R.v57882 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57892 (state s) (inputs i)) 1)) (Z.eqb (R.v57891 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57901 (state s) (inputs i)) 1)) (Z.eqb (R.v57900 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57910 (state s) (inputs i)) 1)) (Z.eqb (R.v57909 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57919 (state s) (inputs i)) 1)) (Z.eqb (R.v57918 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57928 (state s) (inputs i)) 1)) (Z.eqb (R.v57927 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57937 (state s) (inputs i)) 1)) (Z.eqb (R.v57936 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57946 (state s) (inputs i)) 1)) (Z.eqb (R.v57945 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57955 (state s) (inputs i)) 1)) (Z.eqb (R.v57954 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57964 (state s) (inputs i)) 1)) (Z.eqb (R.v57963 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57973 (state s) (inputs i)) 1)) (Z.eqb (R.v57972 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57982 (state s) (inputs i)) 1)) (Z.eqb (R.v57981 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v57991 (state s) (inputs i)) 1)) (Z.eqb (R.v57990 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v58003 (state s) (inputs i)) 1)) (Z.eqb (R.v58002 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v58015 (state s) (inputs i)) 1)) (Z.eqb (R.v58014 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v58027 (state s) (inputs i)) 1)) (Z.eqb (R.v58026 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v58039 (state s) (inputs i)) 1)) (Z.eqb (R.v58038 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v58051 (state s) (inputs i)) 1)) (Z.eqb (R.v58050 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v58063 (state s) (inputs i)) 1)) (Z.eqb (R.v58062 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v58077 (state s) (inputs i)) 1)) (Z.eqb (R.v58076 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v58089 (state s) (inputs i)) 1)) (Z.eqb (R.v58088 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v58098 (state s) (inputs i)) 1)) (Z.eqb (R.v58097 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v58110 (state s) (inputs i)) 1)) (Z.eqb (R.v58109 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v58122 (state s) (inputs i)) 1)) (Z.eqb (R.v58121 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v58131 (state s) (inputs i)) 1)) (Z.eqb (R.v58130 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v58140 (state s) (inputs i)) 1)) (Z.eqb (R.v58139 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v58149 (state s) (inputs i)) 1)) (Z.eqb (R.v58148 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v58158 (state s) (inputs i)) 1)) (Z.eqb (R.v58157 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v58170 (state s) (inputs i)) 1)) (Z.eqb (R.v58169 (state s) (inputs i)) 1)
].
Definition native_checks_32 (s : N.State) (i : N.Inputs) : list bool := [
orb (negb (Zmod.eqb (N.v57237 s i) Zmod.one)) (Zmod.eqb (N.v57236 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57246 s i) Zmod.one)) (Zmod.eqb (N.v57245 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57255 s i) Zmod.one)) (Zmod.eqb (N.v57254 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57267 s i) Zmod.one)) (Zmod.eqb (N.v57266 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57276 s i) Zmod.one)) (Zmod.eqb (N.v57275 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57285 s i) Zmod.one)) (Zmod.eqb (N.v57284 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57294 s i) Zmod.one)) (Zmod.eqb (N.v57293 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57303 s i) Zmod.one)) (Zmod.eqb (N.v57302 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57312 s i) Zmod.one)) (Zmod.eqb (N.v57311 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57321 s i) Zmod.one)) (Zmod.eqb (N.v57320 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57330 s i) Zmod.one)) (Zmod.eqb (N.v57329 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57339 s i) Zmod.one)) (Zmod.eqb (N.v57338 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57351 s i) Zmod.one)) (Zmod.eqb (N.v57350 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57360 s i) Zmod.one)) (Zmod.eqb (N.v57359 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57369 s i) Zmod.one)) (Zmod.eqb (N.v57368 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57378 s i) Zmod.one)) (Zmod.eqb (N.v57377 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57387 s i) Zmod.one)) (Zmod.eqb (N.v57386 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57396 s i) Zmod.one)) (Zmod.eqb (N.v57395 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57405 s i) Zmod.one)) (Zmod.eqb (N.v57404 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57414 s i) Zmod.one)) (Zmod.eqb (N.v57413 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57423 s i) Zmod.one)) (Zmod.eqb (N.v57422 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57432 s i) Zmod.one)) (Zmod.eqb (N.v57431 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57441 s i) Zmod.one)) (Zmod.eqb (N.v57440 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57450 s i) Zmod.one)) (Zmod.eqb (N.v57449 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57459 s i) Zmod.one)) (Zmod.eqb (N.v57458 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57469 s i) Zmod.one)) (Zmod.eqb (N.v57468 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57478 s i) Zmod.one)) (Zmod.eqb (N.v57477 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57487 s i) Zmod.one)) (Zmod.eqb (N.v57486 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57496 s i) Zmod.one)) (Zmod.eqb (N.v57495 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57505 s i) Zmod.one)) (Zmod.eqb (N.v57504 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57514 s i) Zmod.one)) (Zmod.eqb (N.v57513 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57523 s i) Zmod.one)) (Zmod.eqb (N.v57522 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57532 s i) Zmod.one)) (Zmod.eqb (N.v57531 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57541 s i) Zmod.one)) (Zmod.eqb (N.v57540 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57550 s i) Zmod.one)) (Zmod.eqb (N.v57549 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57559 s i) Zmod.one)) (Zmod.eqb (N.v57558 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57568 s i) Zmod.one)) (Zmod.eqb (N.v57567 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57577 s i) Zmod.one)) (Zmod.eqb (N.v57576 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57586 s i) Zmod.one)) (Zmod.eqb (N.v57585 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57595 s i) Zmod.one)) (Zmod.eqb (N.v57594 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57604 s i) Zmod.one)) (Zmod.eqb (N.v57603 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57613 s i) Zmod.one)) (Zmod.eqb (N.v57612 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57622 s i) Zmod.one)) (Zmod.eqb (N.v57621 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57631 s i) Zmod.one)) (Zmod.eqb (N.v57630 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57640 s i) Zmod.one)) (Zmod.eqb (N.v57639 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57649 s i) Zmod.one)) (Zmod.eqb (N.v57648 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57658 s i) Zmod.one)) (Zmod.eqb (N.v57657 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57667 s i) Zmod.one)) (Zmod.eqb (N.v57666 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57676 s i) Zmod.one)) (Zmod.eqb (N.v57675 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57685 s i) Zmod.one)) (Zmod.eqb (N.v57684 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57694 s i) Zmod.one)) (Zmod.eqb (N.v57693 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57703 s i) Zmod.one)) (Zmod.eqb (N.v57702 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57712 s i) Zmod.one)) (Zmod.eqb (N.v57711 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57721 s i) Zmod.one)) (Zmod.eqb (N.v57720 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57730 s i) Zmod.one)) (Zmod.eqb (N.v57729 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57739 s i) Zmod.one)) (Zmod.eqb (N.v57738 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57748 s i) Zmod.one)) (Zmod.eqb (N.v57747 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57757 s i) Zmod.one)) (Zmod.eqb (N.v57756 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57766 s i) Zmod.one)) (Zmod.eqb (N.v57765 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57775 s i) Zmod.one)) (Zmod.eqb (N.v57774 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57784 s i) Zmod.one)) (Zmod.eqb (N.v57783 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57793 s i) Zmod.one)) (Zmod.eqb (N.v57792 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57802 s i) Zmod.one)) (Zmod.eqb (N.v57801 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57811 s i) Zmod.one)) (Zmod.eqb (N.v57810 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57820 s i) Zmod.one)) (Zmod.eqb (N.v57819 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57829 s i) Zmod.one)) (Zmod.eqb (N.v57828 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57838 s i) Zmod.one)) (Zmod.eqb (N.v57837 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57847 s i) Zmod.one)) (Zmod.eqb (N.v57846 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57856 s i) Zmod.one)) (Zmod.eqb (N.v57855 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57865 s i) Zmod.one)) (Zmod.eqb (N.v57864 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57874 s i) Zmod.one)) (Zmod.eqb (N.v57873 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57883 s i) Zmod.one)) (Zmod.eqb (N.v57882 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57892 s i) Zmod.one)) (Zmod.eqb (N.v57891 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57901 s i) Zmod.one)) (Zmod.eqb (N.v57900 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57910 s i) Zmod.one)) (Zmod.eqb (N.v57909 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57919 s i) Zmod.one)) (Zmod.eqb (N.v57918 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57928 s i) Zmod.one)) (Zmod.eqb (N.v57927 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57937 s i) Zmod.one)) (Zmod.eqb (N.v57936 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57946 s i) Zmod.one)) (Zmod.eqb (N.v57945 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57955 s i) Zmod.one)) (Zmod.eqb (N.v57954 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57964 s i) Zmod.one)) (Zmod.eqb (N.v57963 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57973 s i) Zmod.one)) (Zmod.eqb (N.v57972 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57982 s i) Zmod.one)) (Zmod.eqb (N.v57981 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v57991 s i) Zmod.one)) (Zmod.eqb (N.v57990 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v58003 s i) Zmod.one)) (Zmod.eqb (N.v58002 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v58015 s i) Zmod.one)) (Zmod.eqb (N.v58014 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v58027 s i) Zmod.one)) (Zmod.eqb (N.v58026 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v58039 s i) Zmod.one)) (Zmod.eqb (N.v58038 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v58051 s i) Zmod.one)) (Zmod.eqb (N.v58050 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v58063 s i) Zmod.one)) (Zmod.eqb (N.v58062 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v58077 s i) Zmod.one)) (Zmod.eqb (N.v58076 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v58089 s i) Zmod.one)) (Zmod.eqb (N.v58088 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v58098 s i) Zmod.one)) (Zmod.eqb (N.v58097 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v58110 s i) Zmod.one)) (Zmod.eqb (N.v58109 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v58122 s i) Zmod.one)) (Zmod.eqb (N.v58121 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v58131 s i) Zmod.one)) (Zmod.eqb (N.v58130 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v58140 s i) Zmod.one)) (Zmod.eqb (N.v58139 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v58149 s i) Zmod.one)) (Zmod.eqb (N.v58148 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v58158 s i) Zmod.one)) (Zmod.eqb (N.v58157 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v58170 s i) Zmod.one)) (Zmod.eqb (N.v58169 s i) Zmod.one)
].
Lemma checks_32 s i : reference_checks_32 s i = native_checks_32 s i.
Proof. unfold reference_checks_32, native_checks_32.
  rewrite ?node_57236.
  rewrite ?node_57237.
  rewrite ?node_57245.
  rewrite ?node_57246.
  rewrite ?node_57254.
  rewrite ?node_57255.
  rewrite ?node_57266.
  rewrite ?node_57267.
  rewrite ?node_57275.
  rewrite ?node_57276.
  rewrite ?node_57284.
  rewrite ?node_57285.
  rewrite ?node_57293.
  rewrite ?node_57294.
  rewrite ?node_57302.
  rewrite ?node_57303.
  rewrite ?node_57311.
  rewrite ?node_57312.
  rewrite ?node_57320.
  rewrite ?node_57321.
  rewrite ?node_57329.
  rewrite ?node_57330.
  rewrite ?node_57338.
  rewrite ?node_57339.
  rewrite ?node_57350.
  rewrite ?node_57351.
  rewrite ?node_57359.
  rewrite ?node_57360.
  rewrite ?node_57368.
  rewrite ?node_57369.
  rewrite ?node_57377.
  rewrite ?node_57378.
  rewrite ?node_57386.
  rewrite ?node_57387.
  rewrite ?node_57395.
  rewrite ?node_57396.
  rewrite ?node_57404.
  rewrite ?node_57405.
  rewrite ?node_57413.
  rewrite ?node_57414.
  rewrite ?node_57422.
  rewrite ?node_57423.
  rewrite ?node_57431.
  rewrite ?node_57432.
  rewrite ?node_57440.
  rewrite ?node_57441.
  rewrite ?node_57449.
  rewrite ?node_57450.
  rewrite ?node_57458.
  rewrite ?node_57459.
  rewrite ?node_57468.
  rewrite ?node_57469.
  rewrite ?node_57477.
  rewrite ?node_57478.
  rewrite ?node_57486.
  rewrite ?node_57487.
  rewrite ?node_57495.
  rewrite ?node_57496.
  rewrite ?node_57504.
  rewrite ?node_57505.
  rewrite ?node_57513.
  rewrite ?node_57514.
  rewrite ?node_57522.
  rewrite ?node_57523.
  rewrite ?node_57531.
  rewrite ?node_57532.
  rewrite ?node_57540.
  rewrite ?node_57541.
  rewrite ?node_57549.
  rewrite ?node_57550.
  rewrite ?node_57558.
  rewrite ?node_57559.
  rewrite ?node_57567.
  rewrite ?node_57568.
  rewrite ?node_57576.
  rewrite ?node_57577.
  rewrite ?node_57585.
  rewrite ?node_57586.
  rewrite ?node_57594.
  rewrite ?node_57595.
  rewrite ?node_57603.
  rewrite ?node_57604.
  rewrite ?node_57612.
  rewrite ?node_57613.
  rewrite ?node_57621.
  rewrite ?node_57622.
  rewrite ?node_57630.
  rewrite ?node_57631.
  rewrite ?node_57639.
  rewrite ?node_57640.
  rewrite ?node_57648.
  rewrite ?node_57649.
  rewrite ?node_57657.
  rewrite ?node_57658.
  rewrite ?node_57666.
  rewrite ?node_57667.
  rewrite ?node_57675.
  rewrite ?node_57676.
  rewrite ?node_57684.
  rewrite ?node_57685.
  rewrite ?node_57693.
  rewrite ?node_57694.
  rewrite ?node_57702.
  rewrite ?node_57703.
  rewrite ?node_57711.
  rewrite ?node_57712.
  rewrite ?node_57720.
  rewrite ?node_57721.
  rewrite ?node_57729.
  rewrite ?node_57730.
  rewrite ?node_57738.
  rewrite ?node_57739.
  rewrite ?node_57747.
  rewrite ?node_57748.
  rewrite ?node_57756.
  rewrite ?node_57757.
  rewrite ?node_57765.
  rewrite ?node_57766.
  rewrite ?node_57774.
  rewrite ?node_57775.
  rewrite ?node_57783.
  rewrite ?node_57784.
  rewrite ?node_57792.
  rewrite ?node_57793.
  rewrite ?node_57801.
  rewrite ?node_57802.
  rewrite ?node_57810.
  rewrite ?node_57811.
  rewrite ?node_57819.
  rewrite ?node_57820.
  rewrite ?node_57828.
  rewrite ?node_57829.
  rewrite ?node_57837.
  rewrite ?node_57838.
  rewrite ?node_57846.
  rewrite ?node_57847.
  rewrite ?node_57855.
  rewrite ?node_57856.
  rewrite ?node_57864.
  rewrite ?node_57865.
  rewrite ?node_57873.
  rewrite ?node_57874.
  rewrite ?node_57882.
  rewrite ?node_57883.
  rewrite ?node_57891.
  rewrite ?node_57892.
  rewrite ?node_57900.
  rewrite ?node_57901.
  rewrite ?node_57909.
  rewrite ?node_57910.
  rewrite ?node_57918.
  rewrite ?node_57919.
  rewrite ?node_57927.
  rewrite ?node_57928.
  rewrite ?node_57936.
  rewrite ?node_57937.
  rewrite ?node_57945.
  rewrite ?node_57946.
  rewrite ?node_57954.
  rewrite ?node_57955.
  rewrite ?node_57963.
  rewrite ?node_57964.
  rewrite ?node_57972.
  rewrite ?node_57973.
  rewrite ?node_57981.
  rewrite ?node_57982.
  rewrite ?node_57990.
  rewrite ?node_57991.
  rewrite ?node_58002.
  rewrite ?node_58003.
  rewrite ?node_58014.
  rewrite ?node_58015.
  rewrite ?node_58026.
  rewrite ?node_58027.
  rewrite ?node_58038.
  rewrite ?node_58039.
  rewrite ?node_58050.
  rewrite ?node_58051.
  rewrite ?node_58062.
  rewrite ?node_58063.
  rewrite ?node_58076.
  rewrite ?node_58077.
  rewrite ?node_58088.
  rewrite ?node_58089.
  rewrite ?node_58097.
  rewrite ?node_58098.
  rewrite ?node_58109.
  rewrite ?node_58110.
  rewrite ?node_58121.
  rewrite ?node_58122.
  rewrite ?node_58130.
  rewrite ?node_58131.
  rewrite ?node_58139.
  rewrite ?node_58140.
  rewrite ?node_58148.
  rewrite ?node_58149.
  rewrite ?node_58157.
  rewrite ?node_58158.
  rewrite ?node_58169.
  rewrite ?node_58170.
  reflexivity.
Qed.

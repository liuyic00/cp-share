From Stdlib Require Import ZArith List Bool Zmod.Bits.
From BitsProofs Require Import ArrayRefinementNodes033.
Import ListNotations.
Open Scope Z_scope.
Local Opaque R.v31925 N.v31925 R.v31926 N.v31926 R.v31937 N.v31937 R.v31938 N.v31938 R.v31949 N.v31949 R.v31950 N.v31950 R.v31964 N.v31964 R.v31965 N.v31965 R.v31976 N.v31976 R.v31977 N.v31977 R.v31988 N.v31988 R.v31989 N.v31989 R.v32003 N.v32003 R.v32004 N.v32004 R.v32015 N.v32015 R.v32016 N.v32016 R.v32027 N.v32027 R.v32028 N.v32028 R.v32042 N.v32042 R.v32043 N.v32043 R.v32054 N.v32054 R.v32055 N.v32055 R.v32066 N.v32066 R.v32067 N.v32067 R.v32080 N.v32080 R.v32081 N.v32081 R.v32091 N.v32091 R.v32092 N.v32092 R.v32103 N.v32103 R.v32104 N.v32104 R.v32118 N.v32118 R.v32119 N.v32119 R.v32130 N.v32130 R.v32131 N.v32131 R.v32142 N.v32142 R.v32143 N.v32143 R.v32157 N.v32157 R.v32158 N.v32158 R.v32169 N.v32169 R.v32170 N.v32170 R.v32181 N.v32181 R.v32182 N.v32182 R.v32196 N.v32196 R.v32197 N.v32197 R.v32208 N.v32208 R.v32209 N.v32209 R.v32220 N.v32220 R.v32221 N.v32221 R.v32235 N.v32235 R.v32236 N.v32236 R.v32247 N.v32247 R.v32248 N.v32248 R.v32259 N.v32259 R.v32260 N.v32260 R.v32274 N.v32274 R.v32275 N.v32275 R.v32286 N.v32286 R.v32287 N.v32287 R.v32298 N.v32298 R.v32299 N.v32299 R.v32313 N.v32313 R.v32314 N.v32314 R.v32325 N.v32325 R.v32326 N.v32326 R.v32337 N.v32337 R.v32338 N.v32338 R.v32352 N.v32352 R.v32353 N.v32353 R.v32364 N.v32364 R.v32365 N.v32365 R.v32376 N.v32376 R.v32377 N.v32377 R.v32391 N.v32391 R.v32392 N.v32392 R.v32403 N.v32403 R.v32404 N.v32404 R.v32415 N.v32415 R.v32416 N.v32416 R.v32430 N.v32430 R.v32431 N.v32431 R.v32442 N.v32442 R.v32443 N.v32443 R.v32454 N.v32454 R.v32455 N.v32455 R.v32469 N.v32469 R.v32470 N.v32470 R.v32481 N.v32481 R.v32482 N.v32482 R.v32493 N.v32493 R.v32494 N.v32494 R.v32508 N.v32508 R.v32509 N.v32509 R.v32520 N.v32520 R.v32521 N.v32521 R.v32532 N.v32532 R.v32533 N.v32533 R.v32546 N.v32546 R.v32547 N.v32547 R.v32557 N.v32557 R.v32558 N.v32558 R.v32569 N.v32569 R.v32570 N.v32570 R.v32584 N.v32584 R.v32585 N.v32585 R.v32596 N.v32596 R.v32597 N.v32597 R.v32608 N.v32608 R.v32609 N.v32609 R.v32623 N.v32623 R.v32624 N.v32624 R.v32635 N.v32635 R.v32636 N.v32636 R.v32647 N.v32647 R.v32648 N.v32648 R.v32662 N.v32662 R.v32663 N.v32663 R.v32674 N.v32674 R.v32675 N.v32675 R.v32686 N.v32686 R.v32687 N.v32687 R.v32701 N.v32701 R.v32702 N.v32702 R.v32713 N.v32713 R.v32714 N.v32714 R.v32725 N.v32725 R.v32726 N.v32726 R.v32740 N.v32740 R.v32741 N.v32741 R.v32752 N.v32752 R.v32753 N.v32753 R.v32764 N.v32764 R.v32765 N.v32765 R.v32779 N.v32779 R.v32780 N.v32780 R.v32791 N.v32791 R.v32792 N.v32792 R.v32803 N.v32803 R.v32804 N.v32804 R.v32818 N.v32818 R.v32819 N.v32819 R.v32830 N.v32830 R.v32831 N.v32831 R.v32842 N.v32842 R.v32843 N.v32843 R.v32857 N.v32857 R.v32858 N.v32858 R.v32869 N.v32869 R.v32870 N.v32870 R.v32881 N.v32881 R.v32882 N.v32882 R.v32896 N.v32896 R.v32897 N.v32897 R.v32908 N.v32908 R.v32909 N.v32909 R.v32920 N.v32920 R.v32921 N.v32921 R.v32935 N.v32935 R.v32936 N.v32936 R.v32947 N.v32947 R.v32948 N.v32948 R.v32959 N.v32959 R.v32960 N.v32960 R.v32971 N.v32971 R.v32972 N.v32972 R.v32985 N.v32985 R.v32986 N.v32986 R.v32996 N.v32996 R.v32997 N.v32997 R.v33008 N.v33008 R.v33009 N.v33009 R.v33023 N.v33023 R.v33024 N.v33024 R.v33035 N.v33035 R.v33036 N.v33036 R.v33047 N.v33047 R.v33048 N.v33048 R.v33062 N.v33062 R.v33063 N.v33063 R.v33074 N.v33074 R.v33075 N.v33075 R.v33086 N.v33086 R.v33087 N.v33087 R.v33101 N.v33101 R.v33102 N.v33102 R.v33113 N.v33113 R.v33114 N.v33114 R.v33125 N.v33125 R.v33126 N.v33126 R.v33140 N.v33140 R.v33141 N.v33141 R.v33152 N.v33152 R.v33153 N.v33153 R.v33164 N.v33164 R.v33165 N.v33165 R.v33176 N.v33176 R.v33177 N.v33177 R.v33191 N.v33191 R.v33192 N.v33192 R.v33203 N.v33203 R.v33204 N.v33204.
Definition reference_checks_12 (s : N.State) (i : N.Inputs) : list bool := [
orb (negb (Z.eqb (R.v31926 (state s) (inputs i)) 1)) (Z.eqb (R.v31925 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v31938 (state s) (inputs i)) 1)) (Z.eqb (R.v31937 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v31950 (state s) (inputs i)) 1)) (Z.eqb (R.v31949 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v31965 (state s) (inputs i)) 1)) (Z.eqb (R.v31964 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v31977 (state s) (inputs i)) 1)) (Z.eqb (R.v31976 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v31989 (state s) (inputs i)) 1)) (Z.eqb (R.v31988 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32004 (state s) (inputs i)) 1)) (Z.eqb (R.v32003 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32016 (state s) (inputs i)) 1)) (Z.eqb (R.v32015 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32028 (state s) (inputs i)) 1)) (Z.eqb (R.v32027 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32043 (state s) (inputs i)) 1)) (Z.eqb (R.v32042 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32055 (state s) (inputs i)) 1)) (Z.eqb (R.v32054 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32067 (state s) (inputs i)) 1)) (Z.eqb (R.v32066 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32081 (state s) (inputs i)) 1)) (Z.eqb (R.v32080 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32092 (state s) (inputs i)) 1)) (Z.eqb (R.v32091 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32104 (state s) (inputs i)) 1)) (Z.eqb (R.v32103 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32119 (state s) (inputs i)) 1)) (Z.eqb (R.v32118 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32131 (state s) (inputs i)) 1)) (Z.eqb (R.v32130 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32143 (state s) (inputs i)) 1)) (Z.eqb (R.v32142 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32158 (state s) (inputs i)) 1)) (Z.eqb (R.v32157 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32170 (state s) (inputs i)) 1)) (Z.eqb (R.v32169 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32182 (state s) (inputs i)) 1)) (Z.eqb (R.v32181 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32197 (state s) (inputs i)) 1)) (Z.eqb (R.v32196 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32209 (state s) (inputs i)) 1)) (Z.eqb (R.v32208 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32221 (state s) (inputs i)) 1)) (Z.eqb (R.v32220 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32236 (state s) (inputs i)) 1)) (Z.eqb (R.v32235 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32248 (state s) (inputs i)) 1)) (Z.eqb (R.v32247 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32260 (state s) (inputs i)) 1)) (Z.eqb (R.v32259 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32275 (state s) (inputs i)) 1)) (Z.eqb (R.v32274 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32287 (state s) (inputs i)) 1)) (Z.eqb (R.v32286 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32299 (state s) (inputs i)) 1)) (Z.eqb (R.v32298 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32314 (state s) (inputs i)) 1)) (Z.eqb (R.v32313 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32326 (state s) (inputs i)) 1)) (Z.eqb (R.v32325 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32338 (state s) (inputs i)) 1)) (Z.eqb (R.v32337 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32353 (state s) (inputs i)) 1)) (Z.eqb (R.v32352 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32365 (state s) (inputs i)) 1)) (Z.eqb (R.v32364 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32377 (state s) (inputs i)) 1)) (Z.eqb (R.v32376 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32392 (state s) (inputs i)) 1)) (Z.eqb (R.v32391 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32404 (state s) (inputs i)) 1)) (Z.eqb (R.v32403 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32416 (state s) (inputs i)) 1)) (Z.eqb (R.v32415 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32431 (state s) (inputs i)) 1)) (Z.eqb (R.v32430 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32443 (state s) (inputs i)) 1)) (Z.eqb (R.v32442 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32455 (state s) (inputs i)) 1)) (Z.eqb (R.v32454 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32470 (state s) (inputs i)) 1)) (Z.eqb (R.v32469 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32482 (state s) (inputs i)) 1)) (Z.eqb (R.v32481 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32494 (state s) (inputs i)) 1)) (Z.eqb (R.v32493 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32509 (state s) (inputs i)) 1)) (Z.eqb (R.v32508 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32521 (state s) (inputs i)) 1)) (Z.eqb (R.v32520 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32533 (state s) (inputs i)) 1)) (Z.eqb (R.v32532 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32547 (state s) (inputs i)) 1)) (Z.eqb (R.v32546 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32558 (state s) (inputs i)) 1)) (Z.eqb (R.v32557 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32570 (state s) (inputs i)) 1)) (Z.eqb (R.v32569 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32585 (state s) (inputs i)) 1)) (Z.eqb (R.v32584 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32597 (state s) (inputs i)) 1)) (Z.eqb (R.v32596 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32609 (state s) (inputs i)) 1)) (Z.eqb (R.v32608 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32624 (state s) (inputs i)) 1)) (Z.eqb (R.v32623 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32636 (state s) (inputs i)) 1)) (Z.eqb (R.v32635 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32648 (state s) (inputs i)) 1)) (Z.eqb (R.v32647 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32663 (state s) (inputs i)) 1)) (Z.eqb (R.v32662 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32675 (state s) (inputs i)) 1)) (Z.eqb (R.v32674 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32687 (state s) (inputs i)) 1)) (Z.eqb (R.v32686 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32702 (state s) (inputs i)) 1)) (Z.eqb (R.v32701 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32714 (state s) (inputs i)) 1)) (Z.eqb (R.v32713 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32726 (state s) (inputs i)) 1)) (Z.eqb (R.v32725 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32741 (state s) (inputs i)) 1)) (Z.eqb (R.v32740 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32753 (state s) (inputs i)) 1)) (Z.eqb (R.v32752 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32765 (state s) (inputs i)) 1)) (Z.eqb (R.v32764 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32780 (state s) (inputs i)) 1)) (Z.eqb (R.v32779 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32792 (state s) (inputs i)) 1)) (Z.eqb (R.v32791 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32804 (state s) (inputs i)) 1)) (Z.eqb (R.v32803 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32819 (state s) (inputs i)) 1)) (Z.eqb (R.v32818 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32831 (state s) (inputs i)) 1)) (Z.eqb (R.v32830 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32843 (state s) (inputs i)) 1)) (Z.eqb (R.v32842 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32858 (state s) (inputs i)) 1)) (Z.eqb (R.v32857 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32870 (state s) (inputs i)) 1)) (Z.eqb (R.v32869 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32882 (state s) (inputs i)) 1)) (Z.eqb (R.v32881 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32897 (state s) (inputs i)) 1)) (Z.eqb (R.v32896 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32909 (state s) (inputs i)) 1)) (Z.eqb (R.v32908 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32921 (state s) (inputs i)) 1)) (Z.eqb (R.v32920 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32936 (state s) (inputs i)) 1)) (Z.eqb (R.v32935 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32948 (state s) (inputs i)) 1)) (Z.eqb (R.v32947 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32960 (state s) (inputs i)) 1)) (Z.eqb (R.v32959 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32972 (state s) (inputs i)) 1)) (Z.eqb (R.v32971 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32986 (state s) (inputs i)) 1)) (Z.eqb (R.v32985 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v32997 (state s) (inputs i)) 1)) (Z.eqb (R.v32996 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v33009 (state s) (inputs i)) 1)) (Z.eqb (R.v33008 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v33024 (state s) (inputs i)) 1)) (Z.eqb (R.v33023 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v33036 (state s) (inputs i)) 1)) (Z.eqb (R.v33035 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v33048 (state s) (inputs i)) 1)) (Z.eqb (R.v33047 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v33063 (state s) (inputs i)) 1)) (Z.eqb (R.v33062 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v33075 (state s) (inputs i)) 1)) (Z.eqb (R.v33074 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v33087 (state s) (inputs i)) 1)) (Z.eqb (R.v33086 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v33102 (state s) (inputs i)) 1)) (Z.eqb (R.v33101 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v33114 (state s) (inputs i)) 1)) (Z.eqb (R.v33113 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v33126 (state s) (inputs i)) 1)) (Z.eqb (R.v33125 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v33141 (state s) (inputs i)) 1)) (Z.eqb (R.v33140 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v33153 (state s) (inputs i)) 1)) (Z.eqb (R.v33152 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v33165 (state s) (inputs i)) 1)) (Z.eqb (R.v33164 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v33177 (state s) (inputs i)) 1)) (Z.eqb (R.v33176 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v33192 (state s) (inputs i)) 1)) (Z.eqb (R.v33191 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v33204 (state s) (inputs i)) 1)) (Z.eqb (R.v33203 (state s) (inputs i)) 1)
].
Definition native_checks_12 (s : N.State) (i : N.Inputs) : list bool := [
orb (negb (Zmod.eqb (N.v31926 s i) Zmod.one)) (Zmod.eqb (N.v31925 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v31938 s i) Zmod.one)) (Zmod.eqb (N.v31937 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v31950 s i) Zmod.one)) (Zmod.eqb (N.v31949 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v31965 s i) Zmod.one)) (Zmod.eqb (N.v31964 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v31977 s i) Zmod.one)) (Zmod.eqb (N.v31976 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v31989 s i) Zmod.one)) (Zmod.eqb (N.v31988 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32004 s i) Zmod.one)) (Zmod.eqb (N.v32003 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32016 s i) Zmod.one)) (Zmod.eqb (N.v32015 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32028 s i) Zmod.one)) (Zmod.eqb (N.v32027 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32043 s i) Zmod.one)) (Zmod.eqb (N.v32042 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32055 s i) Zmod.one)) (Zmod.eqb (N.v32054 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32067 s i) Zmod.one)) (Zmod.eqb (N.v32066 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32081 s i) Zmod.one)) (Zmod.eqb (N.v32080 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32092 s i) Zmod.one)) (Zmod.eqb (N.v32091 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32104 s i) Zmod.one)) (Zmod.eqb (N.v32103 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32119 s i) Zmod.one)) (Zmod.eqb (N.v32118 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32131 s i) Zmod.one)) (Zmod.eqb (N.v32130 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32143 s i) Zmod.one)) (Zmod.eqb (N.v32142 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32158 s i) Zmod.one)) (Zmod.eqb (N.v32157 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32170 s i) Zmod.one)) (Zmod.eqb (N.v32169 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32182 s i) Zmod.one)) (Zmod.eqb (N.v32181 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32197 s i) Zmod.one)) (Zmod.eqb (N.v32196 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32209 s i) Zmod.one)) (Zmod.eqb (N.v32208 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32221 s i) Zmod.one)) (Zmod.eqb (N.v32220 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32236 s i) Zmod.one)) (Zmod.eqb (N.v32235 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32248 s i) Zmod.one)) (Zmod.eqb (N.v32247 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32260 s i) Zmod.one)) (Zmod.eqb (N.v32259 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32275 s i) Zmod.one)) (Zmod.eqb (N.v32274 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32287 s i) Zmod.one)) (Zmod.eqb (N.v32286 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32299 s i) Zmod.one)) (Zmod.eqb (N.v32298 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32314 s i) Zmod.one)) (Zmod.eqb (N.v32313 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32326 s i) Zmod.one)) (Zmod.eqb (N.v32325 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32338 s i) Zmod.one)) (Zmod.eqb (N.v32337 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32353 s i) Zmod.one)) (Zmod.eqb (N.v32352 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32365 s i) Zmod.one)) (Zmod.eqb (N.v32364 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32377 s i) Zmod.one)) (Zmod.eqb (N.v32376 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32392 s i) Zmod.one)) (Zmod.eqb (N.v32391 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32404 s i) Zmod.one)) (Zmod.eqb (N.v32403 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32416 s i) Zmod.one)) (Zmod.eqb (N.v32415 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32431 s i) Zmod.one)) (Zmod.eqb (N.v32430 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32443 s i) Zmod.one)) (Zmod.eqb (N.v32442 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32455 s i) Zmod.one)) (Zmod.eqb (N.v32454 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32470 s i) Zmod.one)) (Zmod.eqb (N.v32469 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32482 s i) Zmod.one)) (Zmod.eqb (N.v32481 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32494 s i) Zmod.one)) (Zmod.eqb (N.v32493 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32509 s i) Zmod.one)) (Zmod.eqb (N.v32508 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32521 s i) Zmod.one)) (Zmod.eqb (N.v32520 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32533 s i) Zmod.one)) (Zmod.eqb (N.v32532 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32547 s i) Zmod.one)) (Zmod.eqb (N.v32546 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32558 s i) Zmod.one)) (Zmod.eqb (N.v32557 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32570 s i) Zmod.one)) (Zmod.eqb (N.v32569 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32585 s i) Zmod.one)) (Zmod.eqb (N.v32584 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32597 s i) Zmod.one)) (Zmod.eqb (N.v32596 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32609 s i) Zmod.one)) (Zmod.eqb (N.v32608 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32624 s i) Zmod.one)) (Zmod.eqb (N.v32623 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32636 s i) Zmod.one)) (Zmod.eqb (N.v32635 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32648 s i) Zmod.one)) (Zmod.eqb (N.v32647 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32663 s i) Zmod.one)) (Zmod.eqb (N.v32662 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32675 s i) Zmod.one)) (Zmod.eqb (N.v32674 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32687 s i) Zmod.one)) (Zmod.eqb (N.v32686 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32702 s i) Zmod.one)) (Zmod.eqb (N.v32701 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32714 s i) Zmod.one)) (Zmod.eqb (N.v32713 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32726 s i) Zmod.one)) (Zmod.eqb (N.v32725 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32741 s i) Zmod.one)) (Zmod.eqb (N.v32740 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32753 s i) Zmod.one)) (Zmod.eqb (N.v32752 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32765 s i) Zmod.one)) (Zmod.eqb (N.v32764 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32780 s i) Zmod.one)) (Zmod.eqb (N.v32779 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32792 s i) Zmod.one)) (Zmod.eqb (N.v32791 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32804 s i) Zmod.one)) (Zmod.eqb (N.v32803 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32819 s i) Zmod.one)) (Zmod.eqb (N.v32818 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32831 s i) Zmod.one)) (Zmod.eqb (N.v32830 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32843 s i) Zmod.one)) (Zmod.eqb (N.v32842 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32858 s i) Zmod.one)) (Zmod.eqb (N.v32857 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32870 s i) Zmod.one)) (Zmod.eqb (N.v32869 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32882 s i) Zmod.one)) (Zmod.eqb (N.v32881 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32897 s i) Zmod.one)) (Zmod.eqb (N.v32896 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32909 s i) Zmod.one)) (Zmod.eqb (N.v32908 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32921 s i) Zmod.one)) (Zmod.eqb (N.v32920 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32936 s i) Zmod.one)) (Zmod.eqb (N.v32935 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32948 s i) Zmod.one)) (Zmod.eqb (N.v32947 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32960 s i) Zmod.one)) (Zmod.eqb (N.v32959 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32972 s i) Zmod.one)) (Zmod.eqb (N.v32971 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32986 s i) Zmod.one)) (Zmod.eqb (N.v32985 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v32997 s i) Zmod.one)) (Zmod.eqb (N.v32996 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v33009 s i) Zmod.one)) (Zmod.eqb (N.v33008 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v33024 s i) Zmod.one)) (Zmod.eqb (N.v33023 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v33036 s i) Zmod.one)) (Zmod.eqb (N.v33035 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v33048 s i) Zmod.one)) (Zmod.eqb (N.v33047 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v33063 s i) Zmod.one)) (Zmod.eqb (N.v33062 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v33075 s i) Zmod.one)) (Zmod.eqb (N.v33074 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v33087 s i) Zmod.one)) (Zmod.eqb (N.v33086 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v33102 s i) Zmod.one)) (Zmod.eqb (N.v33101 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v33114 s i) Zmod.one)) (Zmod.eqb (N.v33113 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v33126 s i) Zmod.one)) (Zmod.eqb (N.v33125 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v33141 s i) Zmod.one)) (Zmod.eqb (N.v33140 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v33153 s i) Zmod.one)) (Zmod.eqb (N.v33152 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v33165 s i) Zmod.one)) (Zmod.eqb (N.v33164 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v33177 s i) Zmod.one)) (Zmod.eqb (N.v33176 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v33192 s i) Zmod.one)) (Zmod.eqb (N.v33191 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v33204 s i) Zmod.one)) (Zmod.eqb (N.v33203 s i) Zmod.one)
].
Lemma checks_12 s i : reference_checks_12 s i = native_checks_12 s i.
Proof. unfold reference_checks_12, native_checks_12.
  rewrite ?node_31925.
  rewrite ?node_31926.
  rewrite ?node_31937.
  rewrite ?node_31938.
  rewrite ?node_31949.
  rewrite ?node_31950.
  rewrite ?node_31964.
  rewrite ?node_31965.
  rewrite ?node_31976.
  rewrite ?node_31977.
  rewrite ?node_31988.
  rewrite ?node_31989.
  rewrite ?node_32003.
  rewrite ?node_32004.
  rewrite ?node_32015.
  rewrite ?node_32016.
  rewrite ?node_32027.
  rewrite ?node_32028.
  rewrite ?node_32042.
  rewrite ?node_32043.
  rewrite ?node_32054.
  rewrite ?node_32055.
  rewrite ?node_32066.
  rewrite ?node_32067.
  rewrite ?node_32080.
  rewrite ?node_32081.
  rewrite ?node_32091.
  rewrite ?node_32092.
  rewrite ?node_32103.
  rewrite ?node_32104.
  rewrite ?node_32118.
  rewrite ?node_32119.
  rewrite ?node_32130.
  rewrite ?node_32131.
  rewrite ?node_32142.
  rewrite ?node_32143.
  rewrite ?node_32157.
  rewrite ?node_32158.
  rewrite ?node_32169.
  rewrite ?node_32170.
  rewrite ?node_32181.
  rewrite ?node_32182.
  rewrite ?node_32196.
  rewrite ?node_32197.
  rewrite ?node_32208.
  rewrite ?node_32209.
  rewrite ?node_32220.
  rewrite ?node_32221.
  rewrite ?node_32235.
  rewrite ?node_32236.
  rewrite ?node_32247.
  rewrite ?node_32248.
  rewrite ?node_32259.
  rewrite ?node_32260.
  rewrite ?node_32274.
  rewrite ?node_32275.
  rewrite ?node_32286.
  rewrite ?node_32287.
  rewrite ?node_32298.
  rewrite ?node_32299.
  rewrite ?node_32313.
  rewrite ?node_32314.
  rewrite ?node_32325.
  rewrite ?node_32326.
  rewrite ?node_32337.
  rewrite ?node_32338.
  rewrite ?node_32352.
  rewrite ?node_32353.
  rewrite ?node_32364.
  rewrite ?node_32365.
  rewrite ?node_32376.
  rewrite ?node_32377.
  rewrite ?node_32391.
  rewrite ?node_32392.
  rewrite ?node_32403.
  rewrite ?node_32404.
  rewrite ?node_32415.
  rewrite ?node_32416.
  rewrite ?node_32430.
  rewrite ?node_32431.
  rewrite ?node_32442.
  rewrite ?node_32443.
  rewrite ?node_32454.
  rewrite ?node_32455.
  rewrite ?node_32469.
  rewrite ?node_32470.
  rewrite ?node_32481.
  rewrite ?node_32482.
  rewrite ?node_32493.
  rewrite ?node_32494.
  rewrite ?node_32508.
  rewrite ?node_32509.
  rewrite ?node_32520.
  rewrite ?node_32521.
  rewrite ?node_32532.
  rewrite ?node_32533.
  rewrite ?node_32546.
  rewrite ?node_32547.
  rewrite ?node_32557.
  rewrite ?node_32558.
  rewrite ?node_32569.
  rewrite ?node_32570.
  rewrite ?node_32584.
  rewrite ?node_32585.
  rewrite ?node_32596.
  rewrite ?node_32597.
  rewrite ?node_32608.
  rewrite ?node_32609.
  rewrite ?node_32623.
  rewrite ?node_32624.
  rewrite ?node_32635.
  rewrite ?node_32636.
  rewrite ?node_32647.
  rewrite ?node_32648.
  rewrite ?node_32662.
  rewrite ?node_32663.
  rewrite ?node_32674.
  rewrite ?node_32675.
  rewrite ?node_32686.
  rewrite ?node_32687.
  rewrite ?node_32701.
  rewrite ?node_32702.
  rewrite ?node_32713.
  rewrite ?node_32714.
  rewrite ?node_32725.
  rewrite ?node_32726.
  rewrite ?node_32740.
  rewrite ?node_32741.
  rewrite ?node_32752.
  rewrite ?node_32753.
  rewrite ?node_32764.
  rewrite ?node_32765.
  rewrite ?node_32779.
  rewrite ?node_32780.
  rewrite ?node_32791.
  rewrite ?node_32792.
  rewrite ?node_32803.
  rewrite ?node_32804.
  rewrite ?node_32818.
  rewrite ?node_32819.
  rewrite ?node_32830.
  rewrite ?node_32831.
  rewrite ?node_32842.
  rewrite ?node_32843.
  rewrite ?node_32857.
  rewrite ?node_32858.
  rewrite ?node_32869.
  rewrite ?node_32870.
  rewrite ?node_32881.
  rewrite ?node_32882.
  rewrite ?node_32896.
  rewrite ?node_32897.
  rewrite ?node_32908.
  rewrite ?node_32909.
  rewrite ?node_32920.
  rewrite ?node_32921.
  rewrite ?node_32935.
  rewrite ?node_32936.
  rewrite ?node_32947.
  rewrite ?node_32948.
  rewrite ?node_32959.
  rewrite ?node_32960.
  rewrite ?node_32971.
  rewrite ?node_32972.
  rewrite ?node_32985.
  rewrite ?node_32986.
  rewrite ?node_32996.
  rewrite ?node_32997.
  rewrite ?node_33008.
  rewrite ?node_33009.
  rewrite ?node_33023.
  rewrite ?node_33024.
  rewrite ?node_33035.
  rewrite ?node_33036.
  rewrite ?node_33047.
  rewrite ?node_33048.
  rewrite ?node_33062.
  rewrite ?node_33063.
  rewrite ?node_33074.
  rewrite ?node_33075.
  rewrite ?node_33086.
  rewrite ?node_33087.
  rewrite ?node_33101.
  rewrite ?node_33102.
  rewrite ?node_33113.
  rewrite ?node_33114.
  rewrite ?node_33125.
  rewrite ?node_33126.
  rewrite ?node_33140.
  rewrite ?node_33141.
  rewrite ?node_33152.
  rewrite ?node_33153.
  rewrite ?node_33164.
  rewrite ?node_33165.
  rewrite ?node_33176.
  rewrite ?node_33177.
  rewrite ?node_33191.
  rewrite ?node_33192.
  rewrite ?node_33203.
  rewrite ?node_33204.
  reflexivity.
Qed.

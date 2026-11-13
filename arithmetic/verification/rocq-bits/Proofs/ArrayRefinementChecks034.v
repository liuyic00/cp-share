From Stdlib Require Import ZArith List Bool Zmod.Bits.
From BitsProofs Require Import ArrayRefinementNodes059.
Import ListNotations.
Open Scope Z_scope.
Local Opaque R.v59085 N.v59085 R.v59086 N.v59086 R.v59094 N.v59094 R.v59095 N.v59095 R.v59103 N.v59103 R.v59104 N.v59104 R.v59112 N.v59112 R.v59113 N.v59113 R.v59121 N.v59121 R.v59122 N.v59122 R.v59130 N.v59130 R.v59131 N.v59131 R.v59139 N.v59139 R.v59140 N.v59140 R.v59148 N.v59148 R.v59149 N.v59149 R.v59157 N.v59157 R.v59158 N.v59158 R.v59166 N.v59166 R.v59167 N.v59167 R.v59175 N.v59175 R.v59176 N.v59176 R.v59184 N.v59184 R.v59185 N.v59185 R.v59193 N.v59193 R.v59194 N.v59194 R.v59202 N.v59202 R.v59203 N.v59203 R.v59211 N.v59211 R.v59212 N.v59212 R.v59220 N.v59220 R.v59221 N.v59221 R.v59229 N.v59229 R.v59230 N.v59230 R.v59238 N.v59238 R.v59239 N.v59239 R.v59250 N.v59250 R.v59251 N.v59251 R.v59259 N.v59259 R.v59260 N.v59260 R.v59268 N.v59268 R.v59269 N.v59269 R.v59277 N.v59277 R.v59278 N.v59278 R.v59286 N.v59286 R.v59287 N.v59287 R.v59295 N.v59295 R.v59296 N.v59296 R.v59304 N.v59304 R.v59305 N.v59305 R.v59313 N.v59313 R.v59314 N.v59314 R.v59322 N.v59322 R.v59323 N.v59323 R.v59331 N.v59331 R.v59332 N.v59332 R.v59340 N.v59340 R.v59341 N.v59341 R.v59349 N.v59349 R.v59350 N.v59350 R.v59358 N.v59358 R.v59359 N.v59359 R.v59367 N.v59367 R.v59368 N.v59368 R.v59376 N.v59376 R.v59377 N.v59377 R.v59385 N.v59385 R.v59386 N.v59386 R.v59394 N.v59394 R.v59395 N.v59395 R.v59403 N.v59403 R.v59404 N.v59404 R.v59412 N.v59412 R.v59413 N.v59413 R.v59421 N.v59421 R.v59422 N.v59422 R.v59430 N.v59430 R.v59431 N.v59431 R.v59439 N.v59439 R.v59440 N.v59440 R.v59448 N.v59448 R.v59449 N.v59449 R.v59457 N.v59457 R.v59458 N.v59458 R.v59466 N.v59466 R.v59467 N.v59467 R.v59475 N.v59475 R.v59476 N.v59476 R.v59484 N.v59484 R.v59485 N.v59485 R.v59493 N.v59493 R.v59494 N.v59494 R.v59502 N.v59502 R.v59503 N.v59503 R.v59511 N.v59511 R.v59512 N.v59512 R.v59520 N.v59520 R.v59521 N.v59521 R.v59529 N.v59529 R.v59530 N.v59530 R.v59538 N.v59538 R.v59539 N.v59539 R.v59547 N.v59547 R.v59548 N.v59548 R.v59556 N.v59556 R.v59557 N.v59557 R.v59565 N.v59565 R.v59566 N.v59566 R.v59574 N.v59574 R.v59575 N.v59575 R.v59583 N.v59583 R.v59584 N.v59584 R.v59592 N.v59592 R.v59593 N.v59593 R.v59601 N.v59601 R.v59602 N.v59602 R.v59610 N.v59610 R.v59611 N.v59611 R.v59619 N.v59619 R.v59620 N.v59620 R.v59628 N.v59628 R.v59629 N.v59629 R.v59637 N.v59637 R.v59638 N.v59638 R.v59646 N.v59646 R.v59647 N.v59647 R.v59655 N.v59655 R.v59656 N.v59656 R.v59664 N.v59664 R.v59665 N.v59665 R.v59673 N.v59673 R.v59674 N.v59674 R.v59682 N.v59682 R.v59683 N.v59683 R.v59691 N.v59691 R.v59692 N.v59692 R.v59700 N.v59700 R.v59701 N.v59701 R.v59709 N.v59709 R.v59710 N.v59710 R.v59718 N.v59718 R.v59719 N.v59719 R.v59727 N.v59727 R.v59728 N.v59728 R.v59736 N.v59736 R.v59737 N.v59737 R.v59745 N.v59745 R.v59746 N.v59746 R.v59754 N.v59754 R.v59755 N.v59755 R.v59763 N.v59763 R.v59764 N.v59764 R.v59772 N.v59772 R.v59773 N.v59773 R.v59781 N.v59781 R.v59782 N.v59782 R.v59791 N.v59791 R.v59792 N.v59792 R.v59793 N.v59793 R.v59795 N.v59795 R.v59796 N.v59796 R.v59797 N.v59797.
Definition reference_checks_34 (s : N.State) (i : N.Inputs) : list bool := [
orb (negb (Z.eqb (R.v59086 (state s) (inputs i)) 1)) (Z.eqb (R.v59085 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59095 (state s) (inputs i)) 1)) (Z.eqb (R.v59094 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59104 (state s) (inputs i)) 1)) (Z.eqb (R.v59103 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59113 (state s) (inputs i)) 1)) (Z.eqb (R.v59112 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59122 (state s) (inputs i)) 1)) (Z.eqb (R.v59121 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59131 (state s) (inputs i)) 1)) (Z.eqb (R.v59130 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59140 (state s) (inputs i)) 1)) (Z.eqb (R.v59139 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59149 (state s) (inputs i)) 1)) (Z.eqb (R.v59148 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59158 (state s) (inputs i)) 1)) (Z.eqb (R.v59157 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59167 (state s) (inputs i)) 1)) (Z.eqb (R.v59166 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59176 (state s) (inputs i)) 1)) (Z.eqb (R.v59175 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59185 (state s) (inputs i)) 1)) (Z.eqb (R.v59184 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59194 (state s) (inputs i)) 1)) (Z.eqb (R.v59193 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59203 (state s) (inputs i)) 1)) (Z.eqb (R.v59202 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59212 (state s) (inputs i)) 1)) (Z.eqb (R.v59211 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59221 (state s) (inputs i)) 1)) (Z.eqb (R.v59220 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59230 (state s) (inputs i)) 1)) (Z.eqb (R.v59229 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59239 (state s) (inputs i)) 1)) (Z.eqb (R.v59238 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59251 (state s) (inputs i)) 1)) (Z.eqb (R.v59250 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59260 (state s) (inputs i)) 1)) (Z.eqb (R.v59259 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59269 (state s) (inputs i)) 1)) (Z.eqb (R.v59268 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59278 (state s) (inputs i)) 1)) (Z.eqb (R.v59277 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59287 (state s) (inputs i)) 1)) (Z.eqb (R.v59286 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59296 (state s) (inputs i)) 1)) (Z.eqb (R.v59295 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59305 (state s) (inputs i)) 1)) (Z.eqb (R.v59304 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59314 (state s) (inputs i)) 1)) (Z.eqb (R.v59313 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59323 (state s) (inputs i)) 1)) (Z.eqb (R.v59322 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59332 (state s) (inputs i)) 1)) (Z.eqb (R.v59331 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59341 (state s) (inputs i)) 1)) (Z.eqb (R.v59340 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59350 (state s) (inputs i)) 1)) (Z.eqb (R.v59349 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59359 (state s) (inputs i)) 1)) (Z.eqb (R.v59358 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59368 (state s) (inputs i)) 1)) (Z.eqb (R.v59367 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59377 (state s) (inputs i)) 1)) (Z.eqb (R.v59376 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59386 (state s) (inputs i)) 1)) (Z.eqb (R.v59385 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59395 (state s) (inputs i)) 1)) (Z.eqb (R.v59394 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59404 (state s) (inputs i)) 1)) (Z.eqb (R.v59403 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59413 (state s) (inputs i)) 1)) (Z.eqb (R.v59412 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59422 (state s) (inputs i)) 1)) (Z.eqb (R.v59421 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59431 (state s) (inputs i)) 1)) (Z.eqb (R.v59430 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59440 (state s) (inputs i)) 1)) (Z.eqb (R.v59439 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59449 (state s) (inputs i)) 1)) (Z.eqb (R.v59448 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59458 (state s) (inputs i)) 1)) (Z.eqb (R.v59457 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59467 (state s) (inputs i)) 1)) (Z.eqb (R.v59466 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59476 (state s) (inputs i)) 1)) (Z.eqb (R.v59475 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59485 (state s) (inputs i)) 1)) (Z.eqb (R.v59484 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59494 (state s) (inputs i)) 1)) (Z.eqb (R.v59493 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59503 (state s) (inputs i)) 1)) (Z.eqb (R.v59502 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59512 (state s) (inputs i)) 1)) (Z.eqb (R.v59511 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59521 (state s) (inputs i)) 1)) (Z.eqb (R.v59520 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59530 (state s) (inputs i)) 1)) (Z.eqb (R.v59529 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59539 (state s) (inputs i)) 1)) (Z.eqb (R.v59538 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59548 (state s) (inputs i)) 1)) (Z.eqb (R.v59547 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59557 (state s) (inputs i)) 1)) (Z.eqb (R.v59556 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59566 (state s) (inputs i)) 1)) (Z.eqb (R.v59565 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59575 (state s) (inputs i)) 1)) (Z.eqb (R.v59574 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59584 (state s) (inputs i)) 1)) (Z.eqb (R.v59583 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59593 (state s) (inputs i)) 1)) (Z.eqb (R.v59592 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59602 (state s) (inputs i)) 1)) (Z.eqb (R.v59601 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59611 (state s) (inputs i)) 1)) (Z.eqb (R.v59610 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59620 (state s) (inputs i)) 1)) (Z.eqb (R.v59619 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59629 (state s) (inputs i)) 1)) (Z.eqb (R.v59628 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59638 (state s) (inputs i)) 1)) (Z.eqb (R.v59637 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59647 (state s) (inputs i)) 1)) (Z.eqb (R.v59646 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59656 (state s) (inputs i)) 1)) (Z.eqb (R.v59655 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59665 (state s) (inputs i)) 1)) (Z.eqb (R.v59664 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59674 (state s) (inputs i)) 1)) (Z.eqb (R.v59673 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59683 (state s) (inputs i)) 1)) (Z.eqb (R.v59682 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59692 (state s) (inputs i)) 1)) (Z.eqb (R.v59691 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59701 (state s) (inputs i)) 1)) (Z.eqb (R.v59700 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59710 (state s) (inputs i)) 1)) (Z.eqb (R.v59709 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59719 (state s) (inputs i)) 1)) (Z.eqb (R.v59718 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59728 (state s) (inputs i)) 1)) (Z.eqb (R.v59727 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59737 (state s) (inputs i)) 1)) (Z.eqb (R.v59736 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59746 (state s) (inputs i)) 1)) (Z.eqb (R.v59745 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59755 (state s) (inputs i)) 1)) (Z.eqb (R.v59754 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59764 (state s) (inputs i)) 1)) (Z.eqb (R.v59763 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59773 (state s) (inputs i)) 1)) (Z.eqb (R.v59772 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59782 (state s) (inputs i)) 1)) (Z.eqb (R.v59781 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59792 (state s) (inputs i)) 1)) (Z.eqb (R.v59791 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59795 (state s) (inputs i)) 1)) (Z.eqb (R.v59793 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v59797 (state s) (inputs i)) 1)) (Z.eqb (R.v59796 (state s) (inputs i)) 1)
].
Definition native_checks_34 (s : N.State) (i : N.Inputs) : list bool := [
orb (negb (Zmod.eqb (N.v59086 s i) Zmod.one)) (Zmod.eqb (N.v59085 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59095 s i) Zmod.one)) (Zmod.eqb (N.v59094 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59104 s i) Zmod.one)) (Zmod.eqb (N.v59103 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59113 s i) Zmod.one)) (Zmod.eqb (N.v59112 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59122 s i) Zmod.one)) (Zmod.eqb (N.v59121 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59131 s i) Zmod.one)) (Zmod.eqb (N.v59130 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59140 s i) Zmod.one)) (Zmod.eqb (N.v59139 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59149 s i) Zmod.one)) (Zmod.eqb (N.v59148 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59158 s i) Zmod.one)) (Zmod.eqb (N.v59157 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59167 s i) Zmod.one)) (Zmod.eqb (N.v59166 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59176 s i) Zmod.one)) (Zmod.eqb (N.v59175 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59185 s i) Zmod.one)) (Zmod.eqb (N.v59184 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59194 s i) Zmod.one)) (Zmod.eqb (N.v59193 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59203 s i) Zmod.one)) (Zmod.eqb (N.v59202 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59212 s i) Zmod.one)) (Zmod.eqb (N.v59211 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59221 s i) Zmod.one)) (Zmod.eqb (N.v59220 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59230 s i) Zmod.one)) (Zmod.eqb (N.v59229 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59239 s i) Zmod.one)) (Zmod.eqb (N.v59238 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59251 s i) Zmod.one)) (Zmod.eqb (N.v59250 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59260 s i) Zmod.one)) (Zmod.eqb (N.v59259 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59269 s i) Zmod.one)) (Zmod.eqb (N.v59268 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59278 s i) Zmod.one)) (Zmod.eqb (N.v59277 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59287 s i) Zmod.one)) (Zmod.eqb (N.v59286 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59296 s i) Zmod.one)) (Zmod.eqb (N.v59295 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59305 s i) Zmod.one)) (Zmod.eqb (N.v59304 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59314 s i) Zmod.one)) (Zmod.eqb (N.v59313 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59323 s i) Zmod.one)) (Zmod.eqb (N.v59322 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59332 s i) Zmod.one)) (Zmod.eqb (N.v59331 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59341 s i) Zmod.one)) (Zmod.eqb (N.v59340 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59350 s i) Zmod.one)) (Zmod.eqb (N.v59349 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59359 s i) Zmod.one)) (Zmod.eqb (N.v59358 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59368 s i) Zmod.one)) (Zmod.eqb (N.v59367 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59377 s i) Zmod.one)) (Zmod.eqb (N.v59376 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59386 s i) Zmod.one)) (Zmod.eqb (N.v59385 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59395 s i) Zmod.one)) (Zmod.eqb (N.v59394 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59404 s i) Zmod.one)) (Zmod.eqb (N.v59403 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59413 s i) Zmod.one)) (Zmod.eqb (N.v59412 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59422 s i) Zmod.one)) (Zmod.eqb (N.v59421 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59431 s i) Zmod.one)) (Zmod.eqb (N.v59430 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59440 s i) Zmod.one)) (Zmod.eqb (N.v59439 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59449 s i) Zmod.one)) (Zmod.eqb (N.v59448 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59458 s i) Zmod.one)) (Zmod.eqb (N.v59457 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59467 s i) Zmod.one)) (Zmod.eqb (N.v59466 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59476 s i) Zmod.one)) (Zmod.eqb (N.v59475 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59485 s i) Zmod.one)) (Zmod.eqb (N.v59484 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59494 s i) Zmod.one)) (Zmod.eqb (N.v59493 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59503 s i) Zmod.one)) (Zmod.eqb (N.v59502 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59512 s i) Zmod.one)) (Zmod.eqb (N.v59511 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59521 s i) Zmod.one)) (Zmod.eqb (N.v59520 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59530 s i) Zmod.one)) (Zmod.eqb (N.v59529 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59539 s i) Zmod.one)) (Zmod.eqb (N.v59538 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59548 s i) Zmod.one)) (Zmod.eqb (N.v59547 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59557 s i) Zmod.one)) (Zmod.eqb (N.v59556 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59566 s i) Zmod.one)) (Zmod.eqb (N.v59565 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59575 s i) Zmod.one)) (Zmod.eqb (N.v59574 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59584 s i) Zmod.one)) (Zmod.eqb (N.v59583 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59593 s i) Zmod.one)) (Zmod.eqb (N.v59592 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59602 s i) Zmod.one)) (Zmod.eqb (N.v59601 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59611 s i) Zmod.one)) (Zmod.eqb (N.v59610 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59620 s i) Zmod.one)) (Zmod.eqb (N.v59619 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59629 s i) Zmod.one)) (Zmod.eqb (N.v59628 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59638 s i) Zmod.one)) (Zmod.eqb (N.v59637 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59647 s i) Zmod.one)) (Zmod.eqb (N.v59646 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59656 s i) Zmod.one)) (Zmod.eqb (N.v59655 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59665 s i) Zmod.one)) (Zmod.eqb (N.v59664 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59674 s i) Zmod.one)) (Zmod.eqb (N.v59673 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59683 s i) Zmod.one)) (Zmod.eqb (N.v59682 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59692 s i) Zmod.one)) (Zmod.eqb (N.v59691 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59701 s i) Zmod.one)) (Zmod.eqb (N.v59700 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59710 s i) Zmod.one)) (Zmod.eqb (N.v59709 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59719 s i) Zmod.one)) (Zmod.eqb (N.v59718 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59728 s i) Zmod.one)) (Zmod.eqb (N.v59727 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59737 s i) Zmod.one)) (Zmod.eqb (N.v59736 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59746 s i) Zmod.one)) (Zmod.eqb (N.v59745 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59755 s i) Zmod.one)) (Zmod.eqb (N.v59754 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59764 s i) Zmod.one)) (Zmod.eqb (N.v59763 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59773 s i) Zmod.one)) (Zmod.eqb (N.v59772 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59782 s i) Zmod.one)) (Zmod.eqb (N.v59781 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59792 s i) Zmod.one)) (Zmod.eqb (N.v59791 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59795 s i) Zmod.one)) (Zmod.eqb (N.v59793 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v59797 s i) Zmod.one)) (Zmod.eqb (N.v59796 s i) Zmod.one)
].
Lemma checks_34 s i : reference_checks_34 s i = native_checks_34 s i.
Proof. unfold reference_checks_34, native_checks_34.
  rewrite ?node_59085.
  rewrite ?node_59086.
  rewrite ?node_59094.
  rewrite ?node_59095.
  rewrite ?node_59103.
  rewrite ?node_59104.
  rewrite ?node_59112.
  rewrite ?node_59113.
  rewrite ?node_59121.
  rewrite ?node_59122.
  rewrite ?node_59130.
  rewrite ?node_59131.
  rewrite ?node_59139.
  rewrite ?node_59140.
  rewrite ?node_59148.
  rewrite ?node_59149.
  rewrite ?node_59157.
  rewrite ?node_59158.
  rewrite ?node_59166.
  rewrite ?node_59167.
  rewrite ?node_59175.
  rewrite ?node_59176.
  rewrite ?node_59184.
  rewrite ?node_59185.
  rewrite ?node_59193.
  rewrite ?node_59194.
  rewrite ?node_59202.
  rewrite ?node_59203.
  rewrite ?node_59211.
  rewrite ?node_59212.
  rewrite ?node_59220.
  rewrite ?node_59221.
  rewrite ?node_59229.
  rewrite ?node_59230.
  rewrite ?node_59238.
  rewrite ?node_59239.
  rewrite ?node_59250.
  rewrite ?node_59251.
  rewrite ?node_59259.
  rewrite ?node_59260.
  rewrite ?node_59268.
  rewrite ?node_59269.
  rewrite ?node_59277.
  rewrite ?node_59278.
  rewrite ?node_59286.
  rewrite ?node_59287.
  rewrite ?node_59295.
  rewrite ?node_59296.
  rewrite ?node_59304.
  rewrite ?node_59305.
  rewrite ?node_59313.
  rewrite ?node_59314.
  rewrite ?node_59322.
  rewrite ?node_59323.
  rewrite ?node_59331.
  rewrite ?node_59332.
  rewrite ?node_59340.
  rewrite ?node_59341.
  rewrite ?node_59349.
  rewrite ?node_59350.
  rewrite ?node_59358.
  rewrite ?node_59359.
  rewrite ?node_59367.
  rewrite ?node_59368.
  rewrite ?node_59376.
  rewrite ?node_59377.
  rewrite ?node_59385.
  rewrite ?node_59386.
  rewrite ?node_59394.
  rewrite ?node_59395.
  rewrite ?node_59403.
  rewrite ?node_59404.
  rewrite ?node_59412.
  rewrite ?node_59413.
  rewrite ?node_59421.
  rewrite ?node_59422.
  rewrite ?node_59430.
  rewrite ?node_59431.
  rewrite ?node_59439.
  rewrite ?node_59440.
  rewrite ?node_59448.
  rewrite ?node_59449.
  rewrite ?node_59457.
  rewrite ?node_59458.
  rewrite ?node_59466.
  rewrite ?node_59467.
  rewrite ?node_59475.
  rewrite ?node_59476.
  rewrite ?node_59484.
  rewrite ?node_59485.
  rewrite ?node_59493.
  rewrite ?node_59494.
  rewrite ?node_59502.
  rewrite ?node_59503.
  rewrite ?node_59511.
  rewrite ?node_59512.
  rewrite ?node_59520.
  rewrite ?node_59521.
  rewrite ?node_59529.
  rewrite ?node_59530.
  rewrite ?node_59538.
  rewrite ?node_59539.
  rewrite ?node_59547.
  rewrite ?node_59548.
  rewrite ?node_59556.
  rewrite ?node_59557.
  rewrite ?node_59565.
  rewrite ?node_59566.
  rewrite ?node_59574.
  rewrite ?node_59575.
  rewrite ?node_59583.
  rewrite ?node_59584.
  rewrite ?node_59592.
  rewrite ?node_59593.
  rewrite ?node_59601.
  rewrite ?node_59602.
  rewrite ?node_59610.
  rewrite ?node_59611.
  rewrite ?node_59619.
  rewrite ?node_59620.
  rewrite ?node_59628.
  rewrite ?node_59629.
  rewrite ?node_59637.
  rewrite ?node_59638.
  rewrite ?node_59646.
  rewrite ?node_59647.
  rewrite ?node_59655.
  rewrite ?node_59656.
  rewrite ?node_59664.
  rewrite ?node_59665.
  rewrite ?node_59673.
  rewrite ?node_59674.
  rewrite ?node_59682.
  rewrite ?node_59683.
  rewrite ?node_59691.
  rewrite ?node_59692.
  rewrite ?node_59700.
  rewrite ?node_59701.
  rewrite ?node_59709.
  rewrite ?node_59710.
  rewrite ?node_59718.
  rewrite ?node_59719.
  rewrite ?node_59727.
  rewrite ?node_59728.
  rewrite ?node_59736.
  rewrite ?node_59737.
  rewrite ?node_59745.
  rewrite ?node_59746.
  rewrite ?node_59754.
  rewrite ?node_59755.
  rewrite ?node_59763.
  rewrite ?node_59764.
  rewrite ?node_59772.
  rewrite ?node_59773.
  rewrite ?node_59781.
  rewrite ?node_59782.
  rewrite ?node_59791.
  rewrite ?node_59792.
  rewrite ?node_59793.
  rewrite ?node_59795.
  rewrite ?node_59796.
  rewrite ?node_59797.
  reflexivity.
Qed.

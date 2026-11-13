From Stdlib Require Import ZArith List Bool Zmod.Bits.
From BitsProofs Require Import ArrayRefinementNodes050.
Import ListNotations.
Open Scope Z_scope.
Local Opaque R.v49719 N.v49719 R.v49720 N.v49720 R.v49731 N.v49731 R.v49732 N.v49732 R.v49740 N.v49740 R.v49741 N.v49741 R.v49755 N.v49755 R.v49756 N.v49756 R.v49767 N.v49767 R.v49768 N.v49768 R.v49779 N.v49779 R.v49780 N.v49780 R.v49788 N.v49788 R.v49789 N.v49789 R.v49803 N.v49803 R.v49804 N.v49804 R.v49815 N.v49815 R.v49816 N.v49816 R.v49827 N.v49827 R.v49828 N.v49828 R.v49836 N.v49836 R.v49837 N.v49837 R.v49851 N.v49851 R.v49852 N.v49852 R.v49863 N.v49863 R.v49864 N.v49864 R.v49875 N.v49875 R.v49876 N.v49876 R.v49884 N.v49884 R.v49885 N.v49885 R.v49899 N.v49899 R.v49900 N.v49900 R.v49911 N.v49911 R.v49912 N.v49912 R.v49923 N.v49923 R.v49924 N.v49924 R.v49932 N.v49932 R.v49933 N.v49933 R.v49947 N.v49947 R.v49948 N.v49948 R.v49959 N.v49959 R.v49960 N.v49960 R.v49971 N.v49971 R.v49972 N.v49972 R.v49983 N.v49983 R.v49984 N.v49984 R.v49998 N.v49998 R.v49999 N.v49999 R.v50010 N.v50010 R.v50011 N.v50011 R.v50022 N.v50022 R.v50023 N.v50023 R.v50034 N.v50034 R.v50035 N.v50035 R.v50049 N.v50049 R.v50050 N.v50050 R.v50061 N.v50061 R.v50062 N.v50062 R.v50073 N.v50073 R.v50074 N.v50074 R.v50085 N.v50085 R.v50086 N.v50086 R.v50100 N.v50100 R.v50101 N.v50101 R.v50112 N.v50112 R.v50113 N.v50113 R.v50124 N.v50124 R.v50125 N.v50125 R.v50136 N.v50136 R.v50137 N.v50137 R.v50151 N.v50151 R.v50152 N.v50152 R.v50163 N.v50163 R.v50164 N.v50164 R.v50175 N.v50175 R.v50176 N.v50176 R.v50189 N.v50189 R.v50190 N.v50190 R.v50201 N.v50201 R.v50202 N.v50202 R.v50210 N.v50210 R.v50211 N.v50211 R.v50225 N.v50225 R.v50226 N.v50226 R.v50237 N.v50237 R.v50238 N.v50238 R.v50249 N.v50249 R.v50250 N.v50250 R.v50264 N.v50264 R.v50265 N.v50265 R.v50276 N.v50276 R.v50277 N.v50277 R.v50288 N.v50288 R.v50289 N.v50289 R.v50303 N.v50303 R.v50304 N.v50304 R.v50315 N.v50315 R.v50316 N.v50316 R.v50327 N.v50327 R.v50328 N.v50328 R.v50342 N.v50342 R.v50343 N.v50343 R.v50354 N.v50354 R.v50355 N.v50355 R.v50366 N.v50366 R.v50367 N.v50367 R.v50381 N.v50381 R.v50382 N.v50382 R.v50393 N.v50393 R.v50394 N.v50394 R.v50405 N.v50405 R.v50406 N.v50406 R.v50420 N.v50420 R.v50421 N.v50421 R.v50432 N.v50432 R.v50433 N.v50433 R.v50444 N.v50444 R.v50445 N.v50445 R.v50459 N.v50459 R.v50460 N.v50460 R.v50471 N.v50471 R.v50472 N.v50472 R.v50483 N.v50483 R.v50484 N.v50484 R.v50498 N.v50498 R.v50499 N.v50499 R.v50510 N.v50510 R.v50511 N.v50511 R.v50522 N.v50522 R.v50523 N.v50523 R.v50537 N.v50537 R.v50538 N.v50538 R.v50549 N.v50549 R.v50550 N.v50550 R.v50561 N.v50561 R.v50562 N.v50562 R.v50576 N.v50576 R.v50577 N.v50577 R.v50588 N.v50588 R.v50589 N.v50589 R.v50600 N.v50600 R.v50601 N.v50601 R.v50615 N.v50615 R.v50616 N.v50616 R.v50627 N.v50627 R.v50628 N.v50628 R.v50639 N.v50639 R.v50640 N.v50640 R.v50654 N.v50654 R.v50655 N.v50655 R.v50666 N.v50666 R.v50667 N.v50667 R.v50678 N.v50678 R.v50679 N.v50679 R.v50693 N.v50693 R.v50694 N.v50694 R.v50705 N.v50705 R.v50706 N.v50706 R.v50717 N.v50717 R.v50718 N.v50718 R.v50732 N.v50732 R.v50733 N.v50733 R.v50744 N.v50744 R.v50745 N.v50745 R.v50756 N.v50756 R.v50757 N.v50757 R.v50771 N.v50771 R.v50772 N.v50772 R.v50783 N.v50783 R.v50784 N.v50784 R.v50795 N.v50795 R.v50796 N.v50796 R.v50810 N.v50810 R.v50811 N.v50811 R.v50822 N.v50822 R.v50823 N.v50823 R.v50834 N.v50834 R.v50835 N.v50835 R.v50849 N.v50849 R.v50850 N.v50850 R.v50861 N.v50861 R.v50862 N.v50862 R.v50873 N.v50873 R.v50874 N.v50874 R.v50888 N.v50888 R.v50889 N.v50889 R.v50900 N.v50900 R.v50901 N.v50901 R.v50912 N.v50912 R.v50913 N.v50913 R.v50927 N.v50927 R.v50928 N.v50928 R.v50939 N.v50939 R.v50940 N.v50940 R.v50951 N.v50951 R.v50952 N.v50952 R.v50966 N.v50966 R.v50967 N.v50967 R.v50978 N.v50978 R.v50979 N.v50979.
Definition reference_checks_26 (s : N.State) (i : N.Inputs) : list bool := [
orb (negb (Z.eqb (R.v49720 (state s) (inputs i)) 1)) (Z.eqb (R.v49719 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v49732 (state s) (inputs i)) 1)) (Z.eqb (R.v49731 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v49741 (state s) (inputs i)) 1)) (Z.eqb (R.v49740 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v49756 (state s) (inputs i)) 1)) (Z.eqb (R.v49755 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v49768 (state s) (inputs i)) 1)) (Z.eqb (R.v49767 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v49780 (state s) (inputs i)) 1)) (Z.eqb (R.v49779 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v49789 (state s) (inputs i)) 1)) (Z.eqb (R.v49788 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v49804 (state s) (inputs i)) 1)) (Z.eqb (R.v49803 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v49816 (state s) (inputs i)) 1)) (Z.eqb (R.v49815 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v49828 (state s) (inputs i)) 1)) (Z.eqb (R.v49827 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v49837 (state s) (inputs i)) 1)) (Z.eqb (R.v49836 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v49852 (state s) (inputs i)) 1)) (Z.eqb (R.v49851 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v49864 (state s) (inputs i)) 1)) (Z.eqb (R.v49863 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v49876 (state s) (inputs i)) 1)) (Z.eqb (R.v49875 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v49885 (state s) (inputs i)) 1)) (Z.eqb (R.v49884 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v49900 (state s) (inputs i)) 1)) (Z.eqb (R.v49899 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v49912 (state s) (inputs i)) 1)) (Z.eqb (R.v49911 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v49924 (state s) (inputs i)) 1)) (Z.eqb (R.v49923 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v49933 (state s) (inputs i)) 1)) (Z.eqb (R.v49932 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v49948 (state s) (inputs i)) 1)) (Z.eqb (R.v49947 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v49960 (state s) (inputs i)) 1)) (Z.eqb (R.v49959 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v49972 (state s) (inputs i)) 1)) (Z.eqb (R.v49971 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v49984 (state s) (inputs i)) 1)) (Z.eqb (R.v49983 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v49999 (state s) (inputs i)) 1)) (Z.eqb (R.v49998 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50011 (state s) (inputs i)) 1)) (Z.eqb (R.v50010 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50023 (state s) (inputs i)) 1)) (Z.eqb (R.v50022 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50035 (state s) (inputs i)) 1)) (Z.eqb (R.v50034 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50050 (state s) (inputs i)) 1)) (Z.eqb (R.v50049 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50062 (state s) (inputs i)) 1)) (Z.eqb (R.v50061 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50074 (state s) (inputs i)) 1)) (Z.eqb (R.v50073 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50086 (state s) (inputs i)) 1)) (Z.eqb (R.v50085 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50101 (state s) (inputs i)) 1)) (Z.eqb (R.v50100 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50113 (state s) (inputs i)) 1)) (Z.eqb (R.v50112 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50125 (state s) (inputs i)) 1)) (Z.eqb (R.v50124 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50137 (state s) (inputs i)) 1)) (Z.eqb (R.v50136 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50152 (state s) (inputs i)) 1)) (Z.eqb (R.v50151 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50164 (state s) (inputs i)) 1)) (Z.eqb (R.v50163 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50176 (state s) (inputs i)) 1)) (Z.eqb (R.v50175 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50190 (state s) (inputs i)) 1)) (Z.eqb (R.v50189 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50202 (state s) (inputs i)) 1)) (Z.eqb (R.v50201 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50211 (state s) (inputs i)) 1)) (Z.eqb (R.v50210 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50226 (state s) (inputs i)) 1)) (Z.eqb (R.v50225 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50238 (state s) (inputs i)) 1)) (Z.eqb (R.v50237 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50250 (state s) (inputs i)) 1)) (Z.eqb (R.v50249 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50265 (state s) (inputs i)) 1)) (Z.eqb (R.v50264 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50277 (state s) (inputs i)) 1)) (Z.eqb (R.v50276 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50289 (state s) (inputs i)) 1)) (Z.eqb (R.v50288 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50304 (state s) (inputs i)) 1)) (Z.eqb (R.v50303 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50316 (state s) (inputs i)) 1)) (Z.eqb (R.v50315 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50328 (state s) (inputs i)) 1)) (Z.eqb (R.v50327 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50343 (state s) (inputs i)) 1)) (Z.eqb (R.v50342 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50355 (state s) (inputs i)) 1)) (Z.eqb (R.v50354 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50367 (state s) (inputs i)) 1)) (Z.eqb (R.v50366 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50382 (state s) (inputs i)) 1)) (Z.eqb (R.v50381 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50394 (state s) (inputs i)) 1)) (Z.eqb (R.v50393 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50406 (state s) (inputs i)) 1)) (Z.eqb (R.v50405 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50421 (state s) (inputs i)) 1)) (Z.eqb (R.v50420 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50433 (state s) (inputs i)) 1)) (Z.eqb (R.v50432 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50445 (state s) (inputs i)) 1)) (Z.eqb (R.v50444 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50460 (state s) (inputs i)) 1)) (Z.eqb (R.v50459 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50472 (state s) (inputs i)) 1)) (Z.eqb (R.v50471 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50484 (state s) (inputs i)) 1)) (Z.eqb (R.v50483 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50499 (state s) (inputs i)) 1)) (Z.eqb (R.v50498 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50511 (state s) (inputs i)) 1)) (Z.eqb (R.v50510 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50523 (state s) (inputs i)) 1)) (Z.eqb (R.v50522 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50538 (state s) (inputs i)) 1)) (Z.eqb (R.v50537 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50550 (state s) (inputs i)) 1)) (Z.eqb (R.v50549 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50562 (state s) (inputs i)) 1)) (Z.eqb (R.v50561 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50577 (state s) (inputs i)) 1)) (Z.eqb (R.v50576 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50589 (state s) (inputs i)) 1)) (Z.eqb (R.v50588 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50601 (state s) (inputs i)) 1)) (Z.eqb (R.v50600 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50616 (state s) (inputs i)) 1)) (Z.eqb (R.v50615 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50628 (state s) (inputs i)) 1)) (Z.eqb (R.v50627 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50640 (state s) (inputs i)) 1)) (Z.eqb (R.v50639 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50655 (state s) (inputs i)) 1)) (Z.eqb (R.v50654 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50667 (state s) (inputs i)) 1)) (Z.eqb (R.v50666 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50679 (state s) (inputs i)) 1)) (Z.eqb (R.v50678 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50694 (state s) (inputs i)) 1)) (Z.eqb (R.v50693 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50706 (state s) (inputs i)) 1)) (Z.eqb (R.v50705 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50718 (state s) (inputs i)) 1)) (Z.eqb (R.v50717 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50733 (state s) (inputs i)) 1)) (Z.eqb (R.v50732 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50745 (state s) (inputs i)) 1)) (Z.eqb (R.v50744 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50757 (state s) (inputs i)) 1)) (Z.eqb (R.v50756 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50772 (state s) (inputs i)) 1)) (Z.eqb (R.v50771 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50784 (state s) (inputs i)) 1)) (Z.eqb (R.v50783 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50796 (state s) (inputs i)) 1)) (Z.eqb (R.v50795 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50811 (state s) (inputs i)) 1)) (Z.eqb (R.v50810 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50823 (state s) (inputs i)) 1)) (Z.eqb (R.v50822 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50835 (state s) (inputs i)) 1)) (Z.eqb (R.v50834 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50850 (state s) (inputs i)) 1)) (Z.eqb (R.v50849 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50862 (state s) (inputs i)) 1)) (Z.eqb (R.v50861 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50874 (state s) (inputs i)) 1)) (Z.eqb (R.v50873 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50889 (state s) (inputs i)) 1)) (Z.eqb (R.v50888 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50901 (state s) (inputs i)) 1)) (Z.eqb (R.v50900 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50913 (state s) (inputs i)) 1)) (Z.eqb (R.v50912 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50928 (state s) (inputs i)) 1)) (Z.eqb (R.v50927 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50940 (state s) (inputs i)) 1)) (Z.eqb (R.v50939 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50952 (state s) (inputs i)) 1)) (Z.eqb (R.v50951 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50967 (state s) (inputs i)) 1)) (Z.eqb (R.v50966 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v50979 (state s) (inputs i)) 1)) (Z.eqb (R.v50978 (state s) (inputs i)) 1)
].
Definition native_checks_26 (s : N.State) (i : N.Inputs) : list bool := [
orb (negb (Zmod.eqb (N.v49720 s i) Zmod.one)) (Zmod.eqb (N.v49719 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v49732 s i) Zmod.one)) (Zmod.eqb (N.v49731 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v49741 s i) Zmod.one)) (Zmod.eqb (N.v49740 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v49756 s i) Zmod.one)) (Zmod.eqb (N.v49755 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v49768 s i) Zmod.one)) (Zmod.eqb (N.v49767 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v49780 s i) Zmod.one)) (Zmod.eqb (N.v49779 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v49789 s i) Zmod.one)) (Zmod.eqb (N.v49788 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v49804 s i) Zmod.one)) (Zmod.eqb (N.v49803 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v49816 s i) Zmod.one)) (Zmod.eqb (N.v49815 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v49828 s i) Zmod.one)) (Zmod.eqb (N.v49827 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v49837 s i) Zmod.one)) (Zmod.eqb (N.v49836 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v49852 s i) Zmod.one)) (Zmod.eqb (N.v49851 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v49864 s i) Zmod.one)) (Zmod.eqb (N.v49863 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v49876 s i) Zmod.one)) (Zmod.eqb (N.v49875 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v49885 s i) Zmod.one)) (Zmod.eqb (N.v49884 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v49900 s i) Zmod.one)) (Zmod.eqb (N.v49899 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v49912 s i) Zmod.one)) (Zmod.eqb (N.v49911 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v49924 s i) Zmod.one)) (Zmod.eqb (N.v49923 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v49933 s i) Zmod.one)) (Zmod.eqb (N.v49932 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v49948 s i) Zmod.one)) (Zmod.eqb (N.v49947 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v49960 s i) Zmod.one)) (Zmod.eqb (N.v49959 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v49972 s i) Zmod.one)) (Zmod.eqb (N.v49971 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v49984 s i) Zmod.one)) (Zmod.eqb (N.v49983 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v49999 s i) Zmod.one)) (Zmod.eqb (N.v49998 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50011 s i) Zmod.one)) (Zmod.eqb (N.v50010 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50023 s i) Zmod.one)) (Zmod.eqb (N.v50022 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50035 s i) Zmod.one)) (Zmod.eqb (N.v50034 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50050 s i) Zmod.one)) (Zmod.eqb (N.v50049 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50062 s i) Zmod.one)) (Zmod.eqb (N.v50061 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50074 s i) Zmod.one)) (Zmod.eqb (N.v50073 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50086 s i) Zmod.one)) (Zmod.eqb (N.v50085 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50101 s i) Zmod.one)) (Zmod.eqb (N.v50100 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50113 s i) Zmod.one)) (Zmod.eqb (N.v50112 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50125 s i) Zmod.one)) (Zmod.eqb (N.v50124 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50137 s i) Zmod.one)) (Zmod.eqb (N.v50136 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50152 s i) Zmod.one)) (Zmod.eqb (N.v50151 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50164 s i) Zmod.one)) (Zmod.eqb (N.v50163 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50176 s i) Zmod.one)) (Zmod.eqb (N.v50175 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50190 s i) Zmod.one)) (Zmod.eqb (N.v50189 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50202 s i) Zmod.one)) (Zmod.eqb (N.v50201 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50211 s i) Zmod.one)) (Zmod.eqb (N.v50210 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50226 s i) Zmod.one)) (Zmod.eqb (N.v50225 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50238 s i) Zmod.one)) (Zmod.eqb (N.v50237 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50250 s i) Zmod.one)) (Zmod.eqb (N.v50249 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50265 s i) Zmod.one)) (Zmod.eqb (N.v50264 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50277 s i) Zmod.one)) (Zmod.eqb (N.v50276 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50289 s i) Zmod.one)) (Zmod.eqb (N.v50288 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50304 s i) Zmod.one)) (Zmod.eqb (N.v50303 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50316 s i) Zmod.one)) (Zmod.eqb (N.v50315 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50328 s i) Zmod.one)) (Zmod.eqb (N.v50327 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50343 s i) Zmod.one)) (Zmod.eqb (N.v50342 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50355 s i) Zmod.one)) (Zmod.eqb (N.v50354 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50367 s i) Zmod.one)) (Zmod.eqb (N.v50366 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50382 s i) Zmod.one)) (Zmod.eqb (N.v50381 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50394 s i) Zmod.one)) (Zmod.eqb (N.v50393 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50406 s i) Zmod.one)) (Zmod.eqb (N.v50405 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50421 s i) Zmod.one)) (Zmod.eqb (N.v50420 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50433 s i) Zmod.one)) (Zmod.eqb (N.v50432 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50445 s i) Zmod.one)) (Zmod.eqb (N.v50444 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50460 s i) Zmod.one)) (Zmod.eqb (N.v50459 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50472 s i) Zmod.one)) (Zmod.eqb (N.v50471 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50484 s i) Zmod.one)) (Zmod.eqb (N.v50483 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50499 s i) Zmod.one)) (Zmod.eqb (N.v50498 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50511 s i) Zmod.one)) (Zmod.eqb (N.v50510 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50523 s i) Zmod.one)) (Zmod.eqb (N.v50522 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50538 s i) Zmod.one)) (Zmod.eqb (N.v50537 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50550 s i) Zmod.one)) (Zmod.eqb (N.v50549 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50562 s i) Zmod.one)) (Zmod.eqb (N.v50561 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50577 s i) Zmod.one)) (Zmod.eqb (N.v50576 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50589 s i) Zmod.one)) (Zmod.eqb (N.v50588 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50601 s i) Zmod.one)) (Zmod.eqb (N.v50600 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50616 s i) Zmod.one)) (Zmod.eqb (N.v50615 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50628 s i) Zmod.one)) (Zmod.eqb (N.v50627 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50640 s i) Zmod.one)) (Zmod.eqb (N.v50639 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50655 s i) Zmod.one)) (Zmod.eqb (N.v50654 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50667 s i) Zmod.one)) (Zmod.eqb (N.v50666 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50679 s i) Zmod.one)) (Zmod.eqb (N.v50678 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50694 s i) Zmod.one)) (Zmod.eqb (N.v50693 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50706 s i) Zmod.one)) (Zmod.eqb (N.v50705 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50718 s i) Zmod.one)) (Zmod.eqb (N.v50717 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50733 s i) Zmod.one)) (Zmod.eqb (N.v50732 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50745 s i) Zmod.one)) (Zmod.eqb (N.v50744 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50757 s i) Zmod.one)) (Zmod.eqb (N.v50756 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50772 s i) Zmod.one)) (Zmod.eqb (N.v50771 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50784 s i) Zmod.one)) (Zmod.eqb (N.v50783 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50796 s i) Zmod.one)) (Zmod.eqb (N.v50795 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50811 s i) Zmod.one)) (Zmod.eqb (N.v50810 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50823 s i) Zmod.one)) (Zmod.eqb (N.v50822 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50835 s i) Zmod.one)) (Zmod.eqb (N.v50834 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50850 s i) Zmod.one)) (Zmod.eqb (N.v50849 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50862 s i) Zmod.one)) (Zmod.eqb (N.v50861 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50874 s i) Zmod.one)) (Zmod.eqb (N.v50873 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50889 s i) Zmod.one)) (Zmod.eqb (N.v50888 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50901 s i) Zmod.one)) (Zmod.eqb (N.v50900 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50913 s i) Zmod.one)) (Zmod.eqb (N.v50912 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50928 s i) Zmod.one)) (Zmod.eqb (N.v50927 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50940 s i) Zmod.one)) (Zmod.eqb (N.v50939 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50952 s i) Zmod.one)) (Zmod.eqb (N.v50951 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50967 s i) Zmod.one)) (Zmod.eqb (N.v50966 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v50979 s i) Zmod.one)) (Zmod.eqb (N.v50978 s i) Zmod.one)
].
Lemma checks_26 s i : reference_checks_26 s i = native_checks_26 s i.
Proof. unfold reference_checks_26, native_checks_26.
  rewrite ?node_49719.
  rewrite ?node_49720.
  rewrite ?node_49731.
  rewrite ?node_49732.
  rewrite ?node_49740.
  rewrite ?node_49741.
  rewrite ?node_49755.
  rewrite ?node_49756.
  rewrite ?node_49767.
  rewrite ?node_49768.
  rewrite ?node_49779.
  rewrite ?node_49780.
  rewrite ?node_49788.
  rewrite ?node_49789.
  rewrite ?node_49803.
  rewrite ?node_49804.
  rewrite ?node_49815.
  rewrite ?node_49816.
  rewrite ?node_49827.
  rewrite ?node_49828.
  rewrite ?node_49836.
  rewrite ?node_49837.
  rewrite ?node_49851.
  rewrite ?node_49852.
  rewrite ?node_49863.
  rewrite ?node_49864.
  rewrite ?node_49875.
  rewrite ?node_49876.
  rewrite ?node_49884.
  rewrite ?node_49885.
  rewrite ?node_49899.
  rewrite ?node_49900.
  rewrite ?node_49911.
  rewrite ?node_49912.
  rewrite ?node_49923.
  rewrite ?node_49924.
  rewrite ?node_49932.
  rewrite ?node_49933.
  rewrite ?node_49947.
  rewrite ?node_49948.
  rewrite ?node_49959.
  rewrite ?node_49960.
  rewrite ?node_49971.
  rewrite ?node_49972.
  rewrite ?node_49983.
  rewrite ?node_49984.
  rewrite ?node_49998.
  rewrite ?node_49999.
  rewrite ?node_50010.
  rewrite ?node_50011.
  rewrite ?node_50022.
  rewrite ?node_50023.
  rewrite ?node_50034.
  rewrite ?node_50035.
  rewrite ?node_50049.
  rewrite ?node_50050.
  rewrite ?node_50061.
  rewrite ?node_50062.
  rewrite ?node_50073.
  rewrite ?node_50074.
  rewrite ?node_50085.
  rewrite ?node_50086.
  rewrite ?node_50100.
  rewrite ?node_50101.
  rewrite ?node_50112.
  rewrite ?node_50113.
  rewrite ?node_50124.
  rewrite ?node_50125.
  rewrite ?node_50136.
  rewrite ?node_50137.
  rewrite ?node_50151.
  rewrite ?node_50152.
  rewrite ?node_50163.
  rewrite ?node_50164.
  rewrite ?node_50175.
  rewrite ?node_50176.
  rewrite ?node_50189.
  rewrite ?node_50190.
  rewrite ?node_50201.
  rewrite ?node_50202.
  rewrite ?node_50210.
  rewrite ?node_50211.
  rewrite ?node_50225.
  rewrite ?node_50226.
  rewrite ?node_50237.
  rewrite ?node_50238.
  rewrite ?node_50249.
  rewrite ?node_50250.
  rewrite ?node_50264.
  rewrite ?node_50265.
  rewrite ?node_50276.
  rewrite ?node_50277.
  rewrite ?node_50288.
  rewrite ?node_50289.
  rewrite ?node_50303.
  rewrite ?node_50304.
  rewrite ?node_50315.
  rewrite ?node_50316.
  rewrite ?node_50327.
  rewrite ?node_50328.
  rewrite ?node_50342.
  rewrite ?node_50343.
  rewrite ?node_50354.
  rewrite ?node_50355.
  rewrite ?node_50366.
  rewrite ?node_50367.
  rewrite ?node_50381.
  rewrite ?node_50382.
  rewrite ?node_50393.
  rewrite ?node_50394.
  rewrite ?node_50405.
  rewrite ?node_50406.
  rewrite ?node_50420.
  rewrite ?node_50421.
  rewrite ?node_50432.
  rewrite ?node_50433.
  rewrite ?node_50444.
  rewrite ?node_50445.
  rewrite ?node_50459.
  rewrite ?node_50460.
  rewrite ?node_50471.
  rewrite ?node_50472.
  rewrite ?node_50483.
  rewrite ?node_50484.
  rewrite ?node_50498.
  rewrite ?node_50499.
  rewrite ?node_50510.
  rewrite ?node_50511.
  rewrite ?node_50522.
  rewrite ?node_50523.
  rewrite ?node_50537.
  rewrite ?node_50538.
  rewrite ?node_50549.
  rewrite ?node_50550.
  rewrite ?node_50561.
  rewrite ?node_50562.
  rewrite ?node_50576.
  rewrite ?node_50577.
  rewrite ?node_50588.
  rewrite ?node_50589.
  rewrite ?node_50600.
  rewrite ?node_50601.
  rewrite ?node_50615.
  rewrite ?node_50616.
  rewrite ?node_50627.
  rewrite ?node_50628.
  rewrite ?node_50639.
  rewrite ?node_50640.
  rewrite ?node_50654.
  rewrite ?node_50655.
  rewrite ?node_50666.
  rewrite ?node_50667.
  rewrite ?node_50678.
  rewrite ?node_50679.
  rewrite ?node_50693.
  rewrite ?node_50694.
  rewrite ?node_50705.
  rewrite ?node_50706.
  rewrite ?node_50717.
  rewrite ?node_50718.
  rewrite ?node_50732.
  rewrite ?node_50733.
  rewrite ?node_50744.
  rewrite ?node_50745.
  rewrite ?node_50756.
  rewrite ?node_50757.
  rewrite ?node_50771.
  rewrite ?node_50772.
  rewrite ?node_50783.
  rewrite ?node_50784.
  rewrite ?node_50795.
  rewrite ?node_50796.
  rewrite ?node_50810.
  rewrite ?node_50811.
  rewrite ?node_50822.
  rewrite ?node_50823.
  rewrite ?node_50834.
  rewrite ?node_50835.
  rewrite ?node_50849.
  rewrite ?node_50850.
  rewrite ?node_50861.
  rewrite ?node_50862.
  rewrite ?node_50873.
  rewrite ?node_50874.
  rewrite ?node_50888.
  rewrite ?node_50889.
  rewrite ?node_50900.
  rewrite ?node_50901.
  rewrite ?node_50912.
  rewrite ?node_50913.
  rewrite ?node_50927.
  rewrite ?node_50928.
  rewrite ?node_50939.
  rewrite ?node_50940.
  rewrite ?node_50951.
  rewrite ?node_50952.
  rewrite ?node_50966.
  rewrite ?node_50967.
  rewrite ?node_50978.
  rewrite ?node_50979.
  reflexivity.
Qed.

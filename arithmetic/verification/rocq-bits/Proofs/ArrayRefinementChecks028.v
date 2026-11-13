From Stdlib Require Import ZArith List Bool Zmod.Bits.
From BitsProofs Require Import ArrayRefinementNodes053.
Import ListNotations.
Open Scope Z_scope.
Local Opaque R.v52283 N.v52283 R.v52284 N.v52284 R.v52295 N.v52295 R.v52296 N.v52296 R.v52310 N.v52310 R.v52311 N.v52311 R.v52322 N.v52322 R.v52323 N.v52323 R.v52334 N.v52334 R.v52335 N.v52335 R.v52349 N.v52349 R.v52350 N.v52350 R.v52361 N.v52361 R.v52362 N.v52362 R.v52373 N.v52373 R.v52374 N.v52374 R.v52388 N.v52388 R.v52389 N.v52389 R.v52400 N.v52400 R.v52401 N.v52401 R.v52412 N.v52412 R.v52413 N.v52413 R.v52427 N.v52427 R.v52428 N.v52428 R.v52439 N.v52439 R.v52440 N.v52440 R.v52451 N.v52451 R.v52452 N.v52452 R.v52466 N.v52466 R.v52467 N.v52467 R.v52478 N.v52478 R.v52479 N.v52479 R.v52490 N.v52490 R.v52491 N.v52491 R.v52505 N.v52505 R.v52506 N.v52506 R.v52517 N.v52517 R.v52518 N.v52518 R.v52529 N.v52529 R.v52530 N.v52530 R.v52544 N.v52544 R.v52545 N.v52545 R.v52556 N.v52556 R.v52557 N.v52557 R.v52568 N.v52568 R.v52569 N.v52569 R.v52583 N.v52583 R.v52584 N.v52584 R.v52595 N.v52595 R.v52596 N.v52596 R.v52607 N.v52607 R.v52608 N.v52608 R.v52622 N.v52622 R.v52623 N.v52623 R.v52634 N.v52634 R.v52635 N.v52635 R.v52646 N.v52646 R.v52647 N.v52647 R.v52661 N.v52661 R.v52662 N.v52662 R.v52673 N.v52673 R.v52674 N.v52674 R.v52685 N.v52685 R.v52686 N.v52686 R.v52700 N.v52700 R.v52701 N.v52701 R.v52712 N.v52712 R.v52713 N.v52713 R.v52724 N.v52724 R.v52725 N.v52725 R.v52739 N.v52739 R.v52740 N.v52740 R.v52751 N.v52751 R.v52752 N.v52752 R.v52763 N.v52763 R.v52764 N.v52764 R.v52778 N.v52778 R.v52779 N.v52779 R.v52790 N.v52790 R.v52791 N.v52791 R.v52802 N.v52802 R.v52803 N.v52803 R.v52817 N.v52817 R.v52818 N.v52818 R.v52829 N.v52829 R.v52830 N.v52830 R.v52841 N.v52841 R.v52842 N.v52842 R.v52850 N.v52850 R.v52851 N.v52851 R.v52865 N.v52865 R.v52866 N.v52866 R.v52877 N.v52877 R.v52878 N.v52878 R.v52889 N.v52889 R.v52890 N.v52890 R.v52898 N.v52898 R.v52899 N.v52899 R.v52913 N.v52913 R.v52914 N.v52914 R.v52925 N.v52925 R.v52926 N.v52926 R.v52937 N.v52937 R.v52938 N.v52938 R.v52949 N.v52949 R.v52950 N.v52950 R.v52964 N.v52964 R.v52965 N.v52965 R.v52976 N.v52976 R.v52977 N.v52977 R.v52988 N.v52988 R.v52989 N.v52989 R.v52997 N.v52997 R.v52998 N.v52998 R.v53012 N.v53012 R.v53013 N.v53013 R.v53024 N.v53024 R.v53025 N.v53025 R.v53036 N.v53036 R.v53037 N.v53037 R.v53045 N.v53045 R.v53046 N.v53046 R.v53060 N.v53060 R.v53061 N.v53061 R.v53072 N.v53072 R.v53073 N.v53073 R.v53084 N.v53084 R.v53085 N.v53085 R.v53093 N.v53093 R.v53094 N.v53094 R.v53108 N.v53108 R.v53109 N.v53109 R.v53120 N.v53120 R.v53121 N.v53121 R.v53132 N.v53132 R.v53133 N.v53133 R.v53141 N.v53141 R.v53142 N.v53142 R.v53156 N.v53156 R.v53157 N.v53157 R.v53168 N.v53168 R.v53169 N.v53169 R.v53180 N.v53180 R.v53181 N.v53181 R.v53192 N.v53192 R.v53193 N.v53193 R.v53207 N.v53207 R.v53208 N.v53208 R.v53219 N.v53219 R.v53220 N.v53220 R.v53231 N.v53231 R.v53232 N.v53232 R.v53240 N.v53240 R.v53241 N.v53241 R.v53255 N.v53255 R.v53256 N.v53256 R.v53267 N.v53267 R.v53268 N.v53268 R.v53279 N.v53279 R.v53280 N.v53280 R.v53288 N.v53288 R.v53289 N.v53289 R.v53303 N.v53303 R.v53304 N.v53304 R.v53315 N.v53315 R.v53316 N.v53316 R.v53327 N.v53327 R.v53328 N.v53328 R.v53336 N.v53336 R.v53337 N.v53337 R.v53351 N.v53351 R.v53352 N.v53352 R.v53363 N.v53363 R.v53364 N.v53364 R.v53375 N.v53375 R.v53376 N.v53376 R.v53384 N.v53384 R.v53385 N.v53385 R.v53399 N.v53399 R.v53400 N.v53400 R.v53411 N.v53411 R.v53412 N.v53412 R.v53423 N.v53423 R.v53424 N.v53424 R.v53432 N.v53432 R.v53433 N.v53433 R.v53447 N.v53447 R.v53448 N.v53448 R.v53459 N.v53459 R.v53460 N.v53460 R.v53471 N.v53471 R.v53472 N.v53472 R.v53480 N.v53480 R.v53481 N.v53481 R.v53495 N.v53495 R.v53496 N.v53496 R.v53507 N.v53507 R.v53508 N.v53508 R.v53519 N.v53519 R.v53520 N.v53520.
Definition reference_checks_28 (s : N.State) (i : N.Inputs) : list bool := [
orb (negb (Z.eqb (R.v52284 (state s) (inputs i)) 1)) (Z.eqb (R.v52283 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52296 (state s) (inputs i)) 1)) (Z.eqb (R.v52295 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52311 (state s) (inputs i)) 1)) (Z.eqb (R.v52310 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52323 (state s) (inputs i)) 1)) (Z.eqb (R.v52322 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52335 (state s) (inputs i)) 1)) (Z.eqb (R.v52334 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52350 (state s) (inputs i)) 1)) (Z.eqb (R.v52349 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52362 (state s) (inputs i)) 1)) (Z.eqb (R.v52361 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52374 (state s) (inputs i)) 1)) (Z.eqb (R.v52373 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52389 (state s) (inputs i)) 1)) (Z.eqb (R.v52388 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52401 (state s) (inputs i)) 1)) (Z.eqb (R.v52400 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52413 (state s) (inputs i)) 1)) (Z.eqb (R.v52412 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52428 (state s) (inputs i)) 1)) (Z.eqb (R.v52427 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52440 (state s) (inputs i)) 1)) (Z.eqb (R.v52439 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52452 (state s) (inputs i)) 1)) (Z.eqb (R.v52451 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52467 (state s) (inputs i)) 1)) (Z.eqb (R.v52466 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52479 (state s) (inputs i)) 1)) (Z.eqb (R.v52478 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52491 (state s) (inputs i)) 1)) (Z.eqb (R.v52490 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52506 (state s) (inputs i)) 1)) (Z.eqb (R.v52505 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52518 (state s) (inputs i)) 1)) (Z.eqb (R.v52517 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52530 (state s) (inputs i)) 1)) (Z.eqb (R.v52529 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52545 (state s) (inputs i)) 1)) (Z.eqb (R.v52544 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52557 (state s) (inputs i)) 1)) (Z.eqb (R.v52556 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52569 (state s) (inputs i)) 1)) (Z.eqb (R.v52568 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52584 (state s) (inputs i)) 1)) (Z.eqb (R.v52583 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52596 (state s) (inputs i)) 1)) (Z.eqb (R.v52595 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52608 (state s) (inputs i)) 1)) (Z.eqb (R.v52607 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52623 (state s) (inputs i)) 1)) (Z.eqb (R.v52622 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52635 (state s) (inputs i)) 1)) (Z.eqb (R.v52634 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52647 (state s) (inputs i)) 1)) (Z.eqb (R.v52646 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52662 (state s) (inputs i)) 1)) (Z.eqb (R.v52661 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52674 (state s) (inputs i)) 1)) (Z.eqb (R.v52673 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52686 (state s) (inputs i)) 1)) (Z.eqb (R.v52685 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52701 (state s) (inputs i)) 1)) (Z.eqb (R.v52700 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52713 (state s) (inputs i)) 1)) (Z.eqb (R.v52712 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52725 (state s) (inputs i)) 1)) (Z.eqb (R.v52724 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52740 (state s) (inputs i)) 1)) (Z.eqb (R.v52739 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52752 (state s) (inputs i)) 1)) (Z.eqb (R.v52751 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52764 (state s) (inputs i)) 1)) (Z.eqb (R.v52763 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52779 (state s) (inputs i)) 1)) (Z.eqb (R.v52778 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52791 (state s) (inputs i)) 1)) (Z.eqb (R.v52790 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52803 (state s) (inputs i)) 1)) (Z.eqb (R.v52802 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52818 (state s) (inputs i)) 1)) (Z.eqb (R.v52817 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52830 (state s) (inputs i)) 1)) (Z.eqb (R.v52829 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52842 (state s) (inputs i)) 1)) (Z.eqb (R.v52841 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52851 (state s) (inputs i)) 1)) (Z.eqb (R.v52850 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52866 (state s) (inputs i)) 1)) (Z.eqb (R.v52865 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52878 (state s) (inputs i)) 1)) (Z.eqb (R.v52877 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52890 (state s) (inputs i)) 1)) (Z.eqb (R.v52889 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52899 (state s) (inputs i)) 1)) (Z.eqb (R.v52898 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52914 (state s) (inputs i)) 1)) (Z.eqb (R.v52913 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52926 (state s) (inputs i)) 1)) (Z.eqb (R.v52925 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52938 (state s) (inputs i)) 1)) (Z.eqb (R.v52937 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52950 (state s) (inputs i)) 1)) (Z.eqb (R.v52949 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52965 (state s) (inputs i)) 1)) (Z.eqb (R.v52964 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52977 (state s) (inputs i)) 1)) (Z.eqb (R.v52976 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52989 (state s) (inputs i)) 1)) (Z.eqb (R.v52988 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52998 (state s) (inputs i)) 1)) (Z.eqb (R.v52997 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v53013 (state s) (inputs i)) 1)) (Z.eqb (R.v53012 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v53025 (state s) (inputs i)) 1)) (Z.eqb (R.v53024 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v53037 (state s) (inputs i)) 1)) (Z.eqb (R.v53036 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v53046 (state s) (inputs i)) 1)) (Z.eqb (R.v53045 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v53061 (state s) (inputs i)) 1)) (Z.eqb (R.v53060 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v53073 (state s) (inputs i)) 1)) (Z.eqb (R.v53072 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v53085 (state s) (inputs i)) 1)) (Z.eqb (R.v53084 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v53094 (state s) (inputs i)) 1)) (Z.eqb (R.v53093 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v53109 (state s) (inputs i)) 1)) (Z.eqb (R.v53108 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v53121 (state s) (inputs i)) 1)) (Z.eqb (R.v53120 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v53133 (state s) (inputs i)) 1)) (Z.eqb (R.v53132 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v53142 (state s) (inputs i)) 1)) (Z.eqb (R.v53141 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v53157 (state s) (inputs i)) 1)) (Z.eqb (R.v53156 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v53169 (state s) (inputs i)) 1)) (Z.eqb (R.v53168 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v53181 (state s) (inputs i)) 1)) (Z.eqb (R.v53180 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v53193 (state s) (inputs i)) 1)) (Z.eqb (R.v53192 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v53208 (state s) (inputs i)) 1)) (Z.eqb (R.v53207 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v53220 (state s) (inputs i)) 1)) (Z.eqb (R.v53219 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v53232 (state s) (inputs i)) 1)) (Z.eqb (R.v53231 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v53241 (state s) (inputs i)) 1)) (Z.eqb (R.v53240 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v53256 (state s) (inputs i)) 1)) (Z.eqb (R.v53255 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v53268 (state s) (inputs i)) 1)) (Z.eqb (R.v53267 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v53280 (state s) (inputs i)) 1)) (Z.eqb (R.v53279 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v53289 (state s) (inputs i)) 1)) (Z.eqb (R.v53288 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v53304 (state s) (inputs i)) 1)) (Z.eqb (R.v53303 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v53316 (state s) (inputs i)) 1)) (Z.eqb (R.v53315 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v53328 (state s) (inputs i)) 1)) (Z.eqb (R.v53327 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v53337 (state s) (inputs i)) 1)) (Z.eqb (R.v53336 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v53352 (state s) (inputs i)) 1)) (Z.eqb (R.v53351 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v53364 (state s) (inputs i)) 1)) (Z.eqb (R.v53363 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v53376 (state s) (inputs i)) 1)) (Z.eqb (R.v53375 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v53385 (state s) (inputs i)) 1)) (Z.eqb (R.v53384 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v53400 (state s) (inputs i)) 1)) (Z.eqb (R.v53399 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v53412 (state s) (inputs i)) 1)) (Z.eqb (R.v53411 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v53424 (state s) (inputs i)) 1)) (Z.eqb (R.v53423 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v53433 (state s) (inputs i)) 1)) (Z.eqb (R.v53432 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v53448 (state s) (inputs i)) 1)) (Z.eqb (R.v53447 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v53460 (state s) (inputs i)) 1)) (Z.eqb (R.v53459 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v53472 (state s) (inputs i)) 1)) (Z.eqb (R.v53471 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v53481 (state s) (inputs i)) 1)) (Z.eqb (R.v53480 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v53496 (state s) (inputs i)) 1)) (Z.eqb (R.v53495 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v53508 (state s) (inputs i)) 1)) (Z.eqb (R.v53507 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v53520 (state s) (inputs i)) 1)) (Z.eqb (R.v53519 (state s) (inputs i)) 1)
].
Definition native_checks_28 (s : N.State) (i : N.Inputs) : list bool := [
orb (negb (Zmod.eqb (N.v52284 s i) Zmod.one)) (Zmod.eqb (N.v52283 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52296 s i) Zmod.one)) (Zmod.eqb (N.v52295 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52311 s i) Zmod.one)) (Zmod.eqb (N.v52310 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52323 s i) Zmod.one)) (Zmod.eqb (N.v52322 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52335 s i) Zmod.one)) (Zmod.eqb (N.v52334 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52350 s i) Zmod.one)) (Zmod.eqb (N.v52349 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52362 s i) Zmod.one)) (Zmod.eqb (N.v52361 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52374 s i) Zmod.one)) (Zmod.eqb (N.v52373 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52389 s i) Zmod.one)) (Zmod.eqb (N.v52388 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52401 s i) Zmod.one)) (Zmod.eqb (N.v52400 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52413 s i) Zmod.one)) (Zmod.eqb (N.v52412 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52428 s i) Zmod.one)) (Zmod.eqb (N.v52427 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52440 s i) Zmod.one)) (Zmod.eqb (N.v52439 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52452 s i) Zmod.one)) (Zmod.eqb (N.v52451 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52467 s i) Zmod.one)) (Zmod.eqb (N.v52466 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52479 s i) Zmod.one)) (Zmod.eqb (N.v52478 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52491 s i) Zmod.one)) (Zmod.eqb (N.v52490 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52506 s i) Zmod.one)) (Zmod.eqb (N.v52505 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52518 s i) Zmod.one)) (Zmod.eqb (N.v52517 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52530 s i) Zmod.one)) (Zmod.eqb (N.v52529 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52545 s i) Zmod.one)) (Zmod.eqb (N.v52544 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52557 s i) Zmod.one)) (Zmod.eqb (N.v52556 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52569 s i) Zmod.one)) (Zmod.eqb (N.v52568 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52584 s i) Zmod.one)) (Zmod.eqb (N.v52583 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52596 s i) Zmod.one)) (Zmod.eqb (N.v52595 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52608 s i) Zmod.one)) (Zmod.eqb (N.v52607 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52623 s i) Zmod.one)) (Zmod.eqb (N.v52622 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52635 s i) Zmod.one)) (Zmod.eqb (N.v52634 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52647 s i) Zmod.one)) (Zmod.eqb (N.v52646 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52662 s i) Zmod.one)) (Zmod.eqb (N.v52661 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52674 s i) Zmod.one)) (Zmod.eqb (N.v52673 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52686 s i) Zmod.one)) (Zmod.eqb (N.v52685 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52701 s i) Zmod.one)) (Zmod.eqb (N.v52700 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52713 s i) Zmod.one)) (Zmod.eqb (N.v52712 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52725 s i) Zmod.one)) (Zmod.eqb (N.v52724 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52740 s i) Zmod.one)) (Zmod.eqb (N.v52739 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52752 s i) Zmod.one)) (Zmod.eqb (N.v52751 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52764 s i) Zmod.one)) (Zmod.eqb (N.v52763 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52779 s i) Zmod.one)) (Zmod.eqb (N.v52778 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52791 s i) Zmod.one)) (Zmod.eqb (N.v52790 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52803 s i) Zmod.one)) (Zmod.eqb (N.v52802 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52818 s i) Zmod.one)) (Zmod.eqb (N.v52817 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52830 s i) Zmod.one)) (Zmod.eqb (N.v52829 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52842 s i) Zmod.one)) (Zmod.eqb (N.v52841 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52851 s i) Zmod.one)) (Zmod.eqb (N.v52850 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52866 s i) Zmod.one)) (Zmod.eqb (N.v52865 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52878 s i) Zmod.one)) (Zmod.eqb (N.v52877 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52890 s i) Zmod.one)) (Zmod.eqb (N.v52889 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52899 s i) Zmod.one)) (Zmod.eqb (N.v52898 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52914 s i) Zmod.one)) (Zmod.eqb (N.v52913 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52926 s i) Zmod.one)) (Zmod.eqb (N.v52925 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52938 s i) Zmod.one)) (Zmod.eqb (N.v52937 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52950 s i) Zmod.one)) (Zmod.eqb (N.v52949 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52965 s i) Zmod.one)) (Zmod.eqb (N.v52964 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52977 s i) Zmod.one)) (Zmod.eqb (N.v52976 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52989 s i) Zmod.one)) (Zmod.eqb (N.v52988 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52998 s i) Zmod.one)) (Zmod.eqb (N.v52997 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v53013 s i) Zmod.one)) (Zmod.eqb (N.v53012 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v53025 s i) Zmod.one)) (Zmod.eqb (N.v53024 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v53037 s i) Zmod.one)) (Zmod.eqb (N.v53036 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v53046 s i) Zmod.one)) (Zmod.eqb (N.v53045 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v53061 s i) Zmod.one)) (Zmod.eqb (N.v53060 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v53073 s i) Zmod.one)) (Zmod.eqb (N.v53072 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v53085 s i) Zmod.one)) (Zmod.eqb (N.v53084 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v53094 s i) Zmod.one)) (Zmod.eqb (N.v53093 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v53109 s i) Zmod.one)) (Zmod.eqb (N.v53108 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v53121 s i) Zmod.one)) (Zmod.eqb (N.v53120 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v53133 s i) Zmod.one)) (Zmod.eqb (N.v53132 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v53142 s i) Zmod.one)) (Zmod.eqb (N.v53141 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v53157 s i) Zmod.one)) (Zmod.eqb (N.v53156 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v53169 s i) Zmod.one)) (Zmod.eqb (N.v53168 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v53181 s i) Zmod.one)) (Zmod.eqb (N.v53180 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v53193 s i) Zmod.one)) (Zmod.eqb (N.v53192 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v53208 s i) Zmod.one)) (Zmod.eqb (N.v53207 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v53220 s i) Zmod.one)) (Zmod.eqb (N.v53219 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v53232 s i) Zmod.one)) (Zmod.eqb (N.v53231 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v53241 s i) Zmod.one)) (Zmod.eqb (N.v53240 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v53256 s i) Zmod.one)) (Zmod.eqb (N.v53255 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v53268 s i) Zmod.one)) (Zmod.eqb (N.v53267 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v53280 s i) Zmod.one)) (Zmod.eqb (N.v53279 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v53289 s i) Zmod.one)) (Zmod.eqb (N.v53288 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v53304 s i) Zmod.one)) (Zmod.eqb (N.v53303 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v53316 s i) Zmod.one)) (Zmod.eqb (N.v53315 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v53328 s i) Zmod.one)) (Zmod.eqb (N.v53327 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v53337 s i) Zmod.one)) (Zmod.eqb (N.v53336 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v53352 s i) Zmod.one)) (Zmod.eqb (N.v53351 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v53364 s i) Zmod.one)) (Zmod.eqb (N.v53363 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v53376 s i) Zmod.one)) (Zmod.eqb (N.v53375 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v53385 s i) Zmod.one)) (Zmod.eqb (N.v53384 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v53400 s i) Zmod.one)) (Zmod.eqb (N.v53399 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v53412 s i) Zmod.one)) (Zmod.eqb (N.v53411 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v53424 s i) Zmod.one)) (Zmod.eqb (N.v53423 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v53433 s i) Zmod.one)) (Zmod.eqb (N.v53432 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v53448 s i) Zmod.one)) (Zmod.eqb (N.v53447 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v53460 s i) Zmod.one)) (Zmod.eqb (N.v53459 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v53472 s i) Zmod.one)) (Zmod.eqb (N.v53471 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v53481 s i) Zmod.one)) (Zmod.eqb (N.v53480 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v53496 s i) Zmod.one)) (Zmod.eqb (N.v53495 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v53508 s i) Zmod.one)) (Zmod.eqb (N.v53507 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v53520 s i) Zmod.one)) (Zmod.eqb (N.v53519 s i) Zmod.one)
].
Lemma checks_28 s i : reference_checks_28 s i = native_checks_28 s i.
Proof. unfold reference_checks_28, native_checks_28.
  rewrite ?node_52283.
  rewrite ?node_52284.
  rewrite ?node_52295.
  rewrite ?node_52296.
  rewrite ?node_52310.
  rewrite ?node_52311.
  rewrite ?node_52322.
  rewrite ?node_52323.
  rewrite ?node_52334.
  rewrite ?node_52335.
  rewrite ?node_52349.
  rewrite ?node_52350.
  rewrite ?node_52361.
  rewrite ?node_52362.
  rewrite ?node_52373.
  rewrite ?node_52374.
  rewrite ?node_52388.
  rewrite ?node_52389.
  rewrite ?node_52400.
  rewrite ?node_52401.
  rewrite ?node_52412.
  rewrite ?node_52413.
  rewrite ?node_52427.
  rewrite ?node_52428.
  rewrite ?node_52439.
  rewrite ?node_52440.
  rewrite ?node_52451.
  rewrite ?node_52452.
  rewrite ?node_52466.
  rewrite ?node_52467.
  rewrite ?node_52478.
  rewrite ?node_52479.
  rewrite ?node_52490.
  rewrite ?node_52491.
  rewrite ?node_52505.
  rewrite ?node_52506.
  rewrite ?node_52517.
  rewrite ?node_52518.
  rewrite ?node_52529.
  rewrite ?node_52530.
  rewrite ?node_52544.
  rewrite ?node_52545.
  rewrite ?node_52556.
  rewrite ?node_52557.
  rewrite ?node_52568.
  rewrite ?node_52569.
  rewrite ?node_52583.
  rewrite ?node_52584.
  rewrite ?node_52595.
  rewrite ?node_52596.
  rewrite ?node_52607.
  rewrite ?node_52608.
  rewrite ?node_52622.
  rewrite ?node_52623.
  rewrite ?node_52634.
  rewrite ?node_52635.
  rewrite ?node_52646.
  rewrite ?node_52647.
  rewrite ?node_52661.
  rewrite ?node_52662.
  rewrite ?node_52673.
  rewrite ?node_52674.
  rewrite ?node_52685.
  rewrite ?node_52686.
  rewrite ?node_52700.
  rewrite ?node_52701.
  rewrite ?node_52712.
  rewrite ?node_52713.
  rewrite ?node_52724.
  rewrite ?node_52725.
  rewrite ?node_52739.
  rewrite ?node_52740.
  rewrite ?node_52751.
  rewrite ?node_52752.
  rewrite ?node_52763.
  rewrite ?node_52764.
  rewrite ?node_52778.
  rewrite ?node_52779.
  rewrite ?node_52790.
  rewrite ?node_52791.
  rewrite ?node_52802.
  rewrite ?node_52803.
  rewrite ?node_52817.
  rewrite ?node_52818.
  rewrite ?node_52829.
  rewrite ?node_52830.
  rewrite ?node_52841.
  rewrite ?node_52842.
  rewrite ?node_52850.
  rewrite ?node_52851.
  rewrite ?node_52865.
  rewrite ?node_52866.
  rewrite ?node_52877.
  rewrite ?node_52878.
  rewrite ?node_52889.
  rewrite ?node_52890.
  rewrite ?node_52898.
  rewrite ?node_52899.
  rewrite ?node_52913.
  rewrite ?node_52914.
  rewrite ?node_52925.
  rewrite ?node_52926.
  rewrite ?node_52937.
  rewrite ?node_52938.
  rewrite ?node_52949.
  rewrite ?node_52950.
  rewrite ?node_52964.
  rewrite ?node_52965.
  rewrite ?node_52976.
  rewrite ?node_52977.
  rewrite ?node_52988.
  rewrite ?node_52989.
  rewrite ?node_52997.
  rewrite ?node_52998.
  rewrite ?node_53012.
  rewrite ?node_53013.
  rewrite ?node_53024.
  rewrite ?node_53025.
  rewrite ?node_53036.
  rewrite ?node_53037.
  rewrite ?node_53045.
  rewrite ?node_53046.
  rewrite ?node_53060.
  rewrite ?node_53061.
  rewrite ?node_53072.
  rewrite ?node_53073.
  rewrite ?node_53084.
  rewrite ?node_53085.
  rewrite ?node_53093.
  rewrite ?node_53094.
  rewrite ?node_53108.
  rewrite ?node_53109.
  rewrite ?node_53120.
  rewrite ?node_53121.
  rewrite ?node_53132.
  rewrite ?node_53133.
  rewrite ?node_53141.
  rewrite ?node_53142.
  rewrite ?node_53156.
  rewrite ?node_53157.
  rewrite ?node_53168.
  rewrite ?node_53169.
  rewrite ?node_53180.
  rewrite ?node_53181.
  rewrite ?node_53192.
  rewrite ?node_53193.
  rewrite ?node_53207.
  rewrite ?node_53208.
  rewrite ?node_53219.
  rewrite ?node_53220.
  rewrite ?node_53231.
  rewrite ?node_53232.
  rewrite ?node_53240.
  rewrite ?node_53241.
  rewrite ?node_53255.
  rewrite ?node_53256.
  rewrite ?node_53267.
  rewrite ?node_53268.
  rewrite ?node_53279.
  rewrite ?node_53280.
  rewrite ?node_53288.
  rewrite ?node_53289.
  rewrite ?node_53303.
  rewrite ?node_53304.
  rewrite ?node_53315.
  rewrite ?node_53316.
  rewrite ?node_53327.
  rewrite ?node_53328.
  rewrite ?node_53336.
  rewrite ?node_53337.
  rewrite ?node_53351.
  rewrite ?node_53352.
  rewrite ?node_53363.
  rewrite ?node_53364.
  rewrite ?node_53375.
  rewrite ?node_53376.
  rewrite ?node_53384.
  rewrite ?node_53385.
  rewrite ?node_53399.
  rewrite ?node_53400.
  rewrite ?node_53411.
  rewrite ?node_53412.
  rewrite ?node_53423.
  rewrite ?node_53424.
  rewrite ?node_53432.
  rewrite ?node_53433.
  rewrite ?node_53447.
  rewrite ?node_53448.
  rewrite ?node_53459.
  rewrite ?node_53460.
  rewrite ?node_53471.
  rewrite ?node_53472.
  rewrite ?node_53480.
  rewrite ?node_53481.
  rewrite ?node_53495.
  rewrite ?node_53496.
  rewrite ?node_53507.
  rewrite ?node_53508.
  rewrite ?node_53519.
  rewrite ?node_53520.
  reflexivity.
Qed.

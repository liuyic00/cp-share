From Stdlib Require Import ZArith List Bool Zmod.Bits.
From BitsProofs Require Import ArrayRefinementNodes048.
Import ListNotations.
Open Scope Z_scope.
Local Opaque R.v47250 N.v47250 R.v47251 N.v47251 R.v47262 N.v47262 R.v47263 N.v47263 R.v47277 N.v47277 R.v47278 N.v47278 R.v47289 N.v47289 R.v47290 N.v47290 R.v47301 N.v47301 R.v47302 N.v47302 R.v47316 N.v47316 R.v47317 N.v47317 R.v47328 N.v47328 R.v47329 N.v47329 R.v47340 N.v47340 R.v47341 N.v47341 R.v47355 N.v47355 R.v47356 N.v47356 R.v47367 N.v47367 R.v47368 N.v47368 R.v47379 N.v47379 R.v47380 N.v47380 R.v47394 N.v47394 R.v47395 N.v47395 R.v47406 N.v47406 R.v47407 N.v47407 R.v47418 N.v47418 R.v47419 N.v47419 R.v47433 N.v47433 R.v47434 N.v47434 R.v47445 N.v47445 R.v47446 N.v47446 R.v47457 N.v47457 R.v47458 N.v47458 R.v47472 N.v47472 R.v47473 N.v47473 R.v47484 N.v47484 R.v47485 N.v47485 R.v47496 N.v47496 R.v47497 N.v47497 R.v47511 N.v47511 R.v47512 N.v47512 R.v47523 N.v47523 R.v47524 N.v47524 R.v47535 N.v47535 R.v47536 N.v47536 R.v47550 N.v47550 R.v47551 N.v47551 R.v47562 N.v47562 R.v47563 N.v47563 R.v47574 N.v47574 R.v47575 N.v47575 R.v47589 N.v47589 R.v47590 N.v47590 R.v47601 N.v47601 R.v47602 N.v47602 R.v47613 N.v47613 R.v47614 N.v47614 R.v47628 N.v47628 R.v47629 N.v47629 R.v47640 N.v47640 R.v47641 N.v47641 R.v47652 N.v47652 R.v47653 N.v47653 R.v47667 N.v47667 R.v47668 N.v47668 R.v47679 N.v47679 R.v47680 N.v47680 R.v47691 N.v47691 R.v47692 N.v47692 R.v47706 N.v47706 R.v47707 N.v47707 R.v47718 N.v47718 R.v47719 N.v47719 R.v47730 N.v47730 R.v47731 N.v47731 R.v47745 N.v47745 R.v47746 N.v47746 R.v47757 N.v47757 R.v47758 N.v47758 R.v47769 N.v47769 R.v47770 N.v47770 R.v47784 N.v47784 R.v47785 N.v47785 R.v47796 N.v47796 R.v47797 N.v47797 R.v47808 N.v47808 R.v47809 N.v47809 R.v47823 N.v47823 R.v47824 N.v47824 R.v47835 N.v47835 R.v47836 N.v47836 R.v47847 N.v47847 R.v47848 N.v47848 R.v47859 N.v47859 R.v47860 N.v47860 R.v47874 N.v47874 R.v47875 N.v47875 R.v47886 N.v47886 R.v47887 N.v47887 R.v47898 N.v47898 R.v47899 N.v47899 R.v47907 N.v47907 R.v47908 N.v47908 R.v47922 N.v47922 R.v47923 N.v47923 R.v47934 N.v47934 R.v47935 N.v47935 R.v47946 N.v47946 R.v47947 N.v47947 R.v47955 N.v47955 R.v47956 N.v47956 R.v47970 N.v47970 R.v47971 N.v47971 R.v47982 N.v47982 R.v47983 N.v47983 R.v47994 N.v47994 R.v47995 N.v47995 R.v48006 N.v48006 R.v48007 N.v48007 R.v48021 N.v48021 R.v48022 N.v48022 R.v48033 N.v48033 R.v48034 N.v48034 R.v48045 N.v48045 R.v48046 N.v48046 R.v48054 N.v48054 R.v48055 N.v48055 R.v48069 N.v48069 R.v48070 N.v48070 R.v48081 N.v48081 R.v48082 N.v48082 R.v48093 N.v48093 R.v48094 N.v48094 R.v48102 N.v48102 R.v48103 N.v48103 R.v48117 N.v48117 R.v48118 N.v48118 R.v48129 N.v48129 R.v48130 N.v48130 R.v48141 N.v48141 R.v48142 N.v48142 R.v48150 N.v48150 R.v48151 N.v48151 R.v48165 N.v48165 R.v48166 N.v48166 R.v48177 N.v48177 R.v48178 N.v48178 R.v48189 N.v48189 R.v48190 N.v48190 R.v48198 N.v48198 R.v48199 N.v48199 R.v48213 N.v48213 R.v48214 N.v48214 R.v48225 N.v48225 R.v48226 N.v48226 R.v48237 N.v48237 R.v48238 N.v48238 R.v48252 N.v48252 R.v48253 N.v48253 R.v48264 N.v48264 R.v48265 N.v48265 R.v48276 N.v48276 R.v48277 N.v48277 R.v48291 N.v48291 R.v48292 N.v48292 R.v48303 N.v48303 R.v48304 N.v48304 R.v48315 N.v48315 R.v48316 N.v48316 R.v48330 N.v48330 R.v48331 N.v48331 R.v48342 N.v48342 R.v48343 N.v48343 R.v48354 N.v48354 R.v48355 N.v48355 R.v48369 N.v48369 R.v48370 N.v48370 R.v48381 N.v48381 R.v48382 N.v48382 R.v48393 N.v48393 R.v48394 N.v48394 R.v48408 N.v48408 R.v48409 N.v48409 R.v48420 N.v48420 R.v48421 N.v48421 R.v48432 N.v48432 R.v48433 N.v48433 R.v48447 N.v48447 R.v48448 N.v48448 R.v48459 N.v48459 R.v48460 N.v48460 R.v48471 N.v48471 R.v48472 N.v48472 R.v48486 N.v48486 R.v48487 N.v48487 R.v48498 N.v48498 R.v48499 N.v48499 R.v48510 N.v48510 R.v48511 N.v48511.
Definition reference_checks_24 (s : N.State) (i : N.Inputs) : list bool := [
orb (negb (Z.eqb (R.v47251 (state s) (inputs i)) 1)) (Z.eqb (R.v47250 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47263 (state s) (inputs i)) 1)) (Z.eqb (R.v47262 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47278 (state s) (inputs i)) 1)) (Z.eqb (R.v47277 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47290 (state s) (inputs i)) 1)) (Z.eqb (R.v47289 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47302 (state s) (inputs i)) 1)) (Z.eqb (R.v47301 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47317 (state s) (inputs i)) 1)) (Z.eqb (R.v47316 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47329 (state s) (inputs i)) 1)) (Z.eqb (R.v47328 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47341 (state s) (inputs i)) 1)) (Z.eqb (R.v47340 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47356 (state s) (inputs i)) 1)) (Z.eqb (R.v47355 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47368 (state s) (inputs i)) 1)) (Z.eqb (R.v47367 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47380 (state s) (inputs i)) 1)) (Z.eqb (R.v47379 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47395 (state s) (inputs i)) 1)) (Z.eqb (R.v47394 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47407 (state s) (inputs i)) 1)) (Z.eqb (R.v47406 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47419 (state s) (inputs i)) 1)) (Z.eqb (R.v47418 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47434 (state s) (inputs i)) 1)) (Z.eqb (R.v47433 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47446 (state s) (inputs i)) 1)) (Z.eqb (R.v47445 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47458 (state s) (inputs i)) 1)) (Z.eqb (R.v47457 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47473 (state s) (inputs i)) 1)) (Z.eqb (R.v47472 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47485 (state s) (inputs i)) 1)) (Z.eqb (R.v47484 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47497 (state s) (inputs i)) 1)) (Z.eqb (R.v47496 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47512 (state s) (inputs i)) 1)) (Z.eqb (R.v47511 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47524 (state s) (inputs i)) 1)) (Z.eqb (R.v47523 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47536 (state s) (inputs i)) 1)) (Z.eqb (R.v47535 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47551 (state s) (inputs i)) 1)) (Z.eqb (R.v47550 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47563 (state s) (inputs i)) 1)) (Z.eqb (R.v47562 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47575 (state s) (inputs i)) 1)) (Z.eqb (R.v47574 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47590 (state s) (inputs i)) 1)) (Z.eqb (R.v47589 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47602 (state s) (inputs i)) 1)) (Z.eqb (R.v47601 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47614 (state s) (inputs i)) 1)) (Z.eqb (R.v47613 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47629 (state s) (inputs i)) 1)) (Z.eqb (R.v47628 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47641 (state s) (inputs i)) 1)) (Z.eqb (R.v47640 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47653 (state s) (inputs i)) 1)) (Z.eqb (R.v47652 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47668 (state s) (inputs i)) 1)) (Z.eqb (R.v47667 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47680 (state s) (inputs i)) 1)) (Z.eqb (R.v47679 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47692 (state s) (inputs i)) 1)) (Z.eqb (R.v47691 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47707 (state s) (inputs i)) 1)) (Z.eqb (R.v47706 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47719 (state s) (inputs i)) 1)) (Z.eqb (R.v47718 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47731 (state s) (inputs i)) 1)) (Z.eqb (R.v47730 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47746 (state s) (inputs i)) 1)) (Z.eqb (R.v47745 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47758 (state s) (inputs i)) 1)) (Z.eqb (R.v47757 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47770 (state s) (inputs i)) 1)) (Z.eqb (R.v47769 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47785 (state s) (inputs i)) 1)) (Z.eqb (R.v47784 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47797 (state s) (inputs i)) 1)) (Z.eqb (R.v47796 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47809 (state s) (inputs i)) 1)) (Z.eqb (R.v47808 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47824 (state s) (inputs i)) 1)) (Z.eqb (R.v47823 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47836 (state s) (inputs i)) 1)) (Z.eqb (R.v47835 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47848 (state s) (inputs i)) 1)) (Z.eqb (R.v47847 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47860 (state s) (inputs i)) 1)) (Z.eqb (R.v47859 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47875 (state s) (inputs i)) 1)) (Z.eqb (R.v47874 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47887 (state s) (inputs i)) 1)) (Z.eqb (R.v47886 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47899 (state s) (inputs i)) 1)) (Z.eqb (R.v47898 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47908 (state s) (inputs i)) 1)) (Z.eqb (R.v47907 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47923 (state s) (inputs i)) 1)) (Z.eqb (R.v47922 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47935 (state s) (inputs i)) 1)) (Z.eqb (R.v47934 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47947 (state s) (inputs i)) 1)) (Z.eqb (R.v47946 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47956 (state s) (inputs i)) 1)) (Z.eqb (R.v47955 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47971 (state s) (inputs i)) 1)) (Z.eqb (R.v47970 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47983 (state s) (inputs i)) 1)) (Z.eqb (R.v47982 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v47995 (state s) (inputs i)) 1)) (Z.eqb (R.v47994 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v48007 (state s) (inputs i)) 1)) (Z.eqb (R.v48006 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v48022 (state s) (inputs i)) 1)) (Z.eqb (R.v48021 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v48034 (state s) (inputs i)) 1)) (Z.eqb (R.v48033 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v48046 (state s) (inputs i)) 1)) (Z.eqb (R.v48045 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v48055 (state s) (inputs i)) 1)) (Z.eqb (R.v48054 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v48070 (state s) (inputs i)) 1)) (Z.eqb (R.v48069 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v48082 (state s) (inputs i)) 1)) (Z.eqb (R.v48081 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v48094 (state s) (inputs i)) 1)) (Z.eqb (R.v48093 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v48103 (state s) (inputs i)) 1)) (Z.eqb (R.v48102 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v48118 (state s) (inputs i)) 1)) (Z.eqb (R.v48117 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v48130 (state s) (inputs i)) 1)) (Z.eqb (R.v48129 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v48142 (state s) (inputs i)) 1)) (Z.eqb (R.v48141 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v48151 (state s) (inputs i)) 1)) (Z.eqb (R.v48150 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v48166 (state s) (inputs i)) 1)) (Z.eqb (R.v48165 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v48178 (state s) (inputs i)) 1)) (Z.eqb (R.v48177 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v48190 (state s) (inputs i)) 1)) (Z.eqb (R.v48189 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v48199 (state s) (inputs i)) 1)) (Z.eqb (R.v48198 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v48214 (state s) (inputs i)) 1)) (Z.eqb (R.v48213 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v48226 (state s) (inputs i)) 1)) (Z.eqb (R.v48225 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v48238 (state s) (inputs i)) 1)) (Z.eqb (R.v48237 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v48253 (state s) (inputs i)) 1)) (Z.eqb (R.v48252 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v48265 (state s) (inputs i)) 1)) (Z.eqb (R.v48264 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v48277 (state s) (inputs i)) 1)) (Z.eqb (R.v48276 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v48292 (state s) (inputs i)) 1)) (Z.eqb (R.v48291 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v48304 (state s) (inputs i)) 1)) (Z.eqb (R.v48303 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v48316 (state s) (inputs i)) 1)) (Z.eqb (R.v48315 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v48331 (state s) (inputs i)) 1)) (Z.eqb (R.v48330 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v48343 (state s) (inputs i)) 1)) (Z.eqb (R.v48342 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v48355 (state s) (inputs i)) 1)) (Z.eqb (R.v48354 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v48370 (state s) (inputs i)) 1)) (Z.eqb (R.v48369 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v48382 (state s) (inputs i)) 1)) (Z.eqb (R.v48381 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v48394 (state s) (inputs i)) 1)) (Z.eqb (R.v48393 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v48409 (state s) (inputs i)) 1)) (Z.eqb (R.v48408 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v48421 (state s) (inputs i)) 1)) (Z.eqb (R.v48420 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v48433 (state s) (inputs i)) 1)) (Z.eqb (R.v48432 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v48448 (state s) (inputs i)) 1)) (Z.eqb (R.v48447 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v48460 (state s) (inputs i)) 1)) (Z.eqb (R.v48459 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v48472 (state s) (inputs i)) 1)) (Z.eqb (R.v48471 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v48487 (state s) (inputs i)) 1)) (Z.eqb (R.v48486 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v48499 (state s) (inputs i)) 1)) (Z.eqb (R.v48498 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v48511 (state s) (inputs i)) 1)) (Z.eqb (R.v48510 (state s) (inputs i)) 1)
].
Definition native_checks_24 (s : N.State) (i : N.Inputs) : list bool := [
orb (negb (Zmod.eqb (N.v47251 s i) Zmod.one)) (Zmod.eqb (N.v47250 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47263 s i) Zmod.one)) (Zmod.eqb (N.v47262 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47278 s i) Zmod.one)) (Zmod.eqb (N.v47277 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47290 s i) Zmod.one)) (Zmod.eqb (N.v47289 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47302 s i) Zmod.one)) (Zmod.eqb (N.v47301 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47317 s i) Zmod.one)) (Zmod.eqb (N.v47316 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47329 s i) Zmod.one)) (Zmod.eqb (N.v47328 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47341 s i) Zmod.one)) (Zmod.eqb (N.v47340 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47356 s i) Zmod.one)) (Zmod.eqb (N.v47355 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47368 s i) Zmod.one)) (Zmod.eqb (N.v47367 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47380 s i) Zmod.one)) (Zmod.eqb (N.v47379 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47395 s i) Zmod.one)) (Zmod.eqb (N.v47394 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47407 s i) Zmod.one)) (Zmod.eqb (N.v47406 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47419 s i) Zmod.one)) (Zmod.eqb (N.v47418 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47434 s i) Zmod.one)) (Zmod.eqb (N.v47433 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47446 s i) Zmod.one)) (Zmod.eqb (N.v47445 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47458 s i) Zmod.one)) (Zmod.eqb (N.v47457 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47473 s i) Zmod.one)) (Zmod.eqb (N.v47472 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47485 s i) Zmod.one)) (Zmod.eqb (N.v47484 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47497 s i) Zmod.one)) (Zmod.eqb (N.v47496 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47512 s i) Zmod.one)) (Zmod.eqb (N.v47511 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47524 s i) Zmod.one)) (Zmod.eqb (N.v47523 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47536 s i) Zmod.one)) (Zmod.eqb (N.v47535 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47551 s i) Zmod.one)) (Zmod.eqb (N.v47550 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47563 s i) Zmod.one)) (Zmod.eqb (N.v47562 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47575 s i) Zmod.one)) (Zmod.eqb (N.v47574 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47590 s i) Zmod.one)) (Zmod.eqb (N.v47589 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47602 s i) Zmod.one)) (Zmod.eqb (N.v47601 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47614 s i) Zmod.one)) (Zmod.eqb (N.v47613 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47629 s i) Zmod.one)) (Zmod.eqb (N.v47628 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47641 s i) Zmod.one)) (Zmod.eqb (N.v47640 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47653 s i) Zmod.one)) (Zmod.eqb (N.v47652 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47668 s i) Zmod.one)) (Zmod.eqb (N.v47667 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47680 s i) Zmod.one)) (Zmod.eqb (N.v47679 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47692 s i) Zmod.one)) (Zmod.eqb (N.v47691 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47707 s i) Zmod.one)) (Zmod.eqb (N.v47706 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47719 s i) Zmod.one)) (Zmod.eqb (N.v47718 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47731 s i) Zmod.one)) (Zmod.eqb (N.v47730 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47746 s i) Zmod.one)) (Zmod.eqb (N.v47745 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47758 s i) Zmod.one)) (Zmod.eqb (N.v47757 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47770 s i) Zmod.one)) (Zmod.eqb (N.v47769 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47785 s i) Zmod.one)) (Zmod.eqb (N.v47784 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47797 s i) Zmod.one)) (Zmod.eqb (N.v47796 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47809 s i) Zmod.one)) (Zmod.eqb (N.v47808 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47824 s i) Zmod.one)) (Zmod.eqb (N.v47823 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47836 s i) Zmod.one)) (Zmod.eqb (N.v47835 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47848 s i) Zmod.one)) (Zmod.eqb (N.v47847 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47860 s i) Zmod.one)) (Zmod.eqb (N.v47859 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47875 s i) Zmod.one)) (Zmod.eqb (N.v47874 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47887 s i) Zmod.one)) (Zmod.eqb (N.v47886 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47899 s i) Zmod.one)) (Zmod.eqb (N.v47898 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47908 s i) Zmod.one)) (Zmod.eqb (N.v47907 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47923 s i) Zmod.one)) (Zmod.eqb (N.v47922 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47935 s i) Zmod.one)) (Zmod.eqb (N.v47934 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47947 s i) Zmod.one)) (Zmod.eqb (N.v47946 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47956 s i) Zmod.one)) (Zmod.eqb (N.v47955 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47971 s i) Zmod.one)) (Zmod.eqb (N.v47970 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47983 s i) Zmod.one)) (Zmod.eqb (N.v47982 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v47995 s i) Zmod.one)) (Zmod.eqb (N.v47994 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v48007 s i) Zmod.one)) (Zmod.eqb (N.v48006 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v48022 s i) Zmod.one)) (Zmod.eqb (N.v48021 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v48034 s i) Zmod.one)) (Zmod.eqb (N.v48033 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v48046 s i) Zmod.one)) (Zmod.eqb (N.v48045 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v48055 s i) Zmod.one)) (Zmod.eqb (N.v48054 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v48070 s i) Zmod.one)) (Zmod.eqb (N.v48069 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v48082 s i) Zmod.one)) (Zmod.eqb (N.v48081 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v48094 s i) Zmod.one)) (Zmod.eqb (N.v48093 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v48103 s i) Zmod.one)) (Zmod.eqb (N.v48102 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v48118 s i) Zmod.one)) (Zmod.eqb (N.v48117 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v48130 s i) Zmod.one)) (Zmod.eqb (N.v48129 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v48142 s i) Zmod.one)) (Zmod.eqb (N.v48141 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v48151 s i) Zmod.one)) (Zmod.eqb (N.v48150 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v48166 s i) Zmod.one)) (Zmod.eqb (N.v48165 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v48178 s i) Zmod.one)) (Zmod.eqb (N.v48177 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v48190 s i) Zmod.one)) (Zmod.eqb (N.v48189 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v48199 s i) Zmod.one)) (Zmod.eqb (N.v48198 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v48214 s i) Zmod.one)) (Zmod.eqb (N.v48213 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v48226 s i) Zmod.one)) (Zmod.eqb (N.v48225 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v48238 s i) Zmod.one)) (Zmod.eqb (N.v48237 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v48253 s i) Zmod.one)) (Zmod.eqb (N.v48252 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v48265 s i) Zmod.one)) (Zmod.eqb (N.v48264 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v48277 s i) Zmod.one)) (Zmod.eqb (N.v48276 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v48292 s i) Zmod.one)) (Zmod.eqb (N.v48291 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v48304 s i) Zmod.one)) (Zmod.eqb (N.v48303 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v48316 s i) Zmod.one)) (Zmod.eqb (N.v48315 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v48331 s i) Zmod.one)) (Zmod.eqb (N.v48330 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v48343 s i) Zmod.one)) (Zmod.eqb (N.v48342 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v48355 s i) Zmod.one)) (Zmod.eqb (N.v48354 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v48370 s i) Zmod.one)) (Zmod.eqb (N.v48369 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v48382 s i) Zmod.one)) (Zmod.eqb (N.v48381 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v48394 s i) Zmod.one)) (Zmod.eqb (N.v48393 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v48409 s i) Zmod.one)) (Zmod.eqb (N.v48408 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v48421 s i) Zmod.one)) (Zmod.eqb (N.v48420 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v48433 s i) Zmod.one)) (Zmod.eqb (N.v48432 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v48448 s i) Zmod.one)) (Zmod.eqb (N.v48447 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v48460 s i) Zmod.one)) (Zmod.eqb (N.v48459 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v48472 s i) Zmod.one)) (Zmod.eqb (N.v48471 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v48487 s i) Zmod.one)) (Zmod.eqb (N.v48486 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v48499 s i) Zmod.one)) (Zmod.eqb (N.v48498 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v48511 s i) Zmod.one)) (Zmod.eqb (N.v48510 s i) Zmod.one)
].
Lemma checks_24 s i : reference_checks_24 s i = native_checks_24 s i.
Proof. unfold reference_checks_24, native_checks_24.
  rewrite ?node_47250.
  rewrite ?node_47251.
  rewrite ?node_47262.
  rewrite ?node_47263.
  rewrite ?node_47277.
  rewrite ?node_47278.
  rewrite ?node_47289.
  rewrite ?node_47290.
  rewrite ?node_47301.
  rewrite ?node_47302.
  rewrite ?node_47316.
  rewrite ?node_47317.
  rewrite ?node_47328.
  rewrite ?node_47329.
  rewrite ?node_47340.
  rewrite ?node_47341.
  rewrite ?node_47355.
  rewrite ?node_47356.
  rewrite ?node_47367.
  rewrite ?node_47368.
  rewrite ?node_47379.
  rewrite ?node_47380.
  rewrite ?node_47394.
  rewrite ?node_47395.
  rewrite ?node_47406.
  rewrite ?node_47407.
  rewrite ?node_47418.
  rewrite ?node_47419.
  rewrite ?node_47433.
  rewrite ?node_47434.
  rewrite ?node_47445.
  rewrite ?node_47446.
  rewrite ?node_47457.
  rewrite ?node_47458.
  rewrite ?node_47472.
  rewrite ?node_47473.
  rewrite ?node_47484.
  rewrite ?node_47485.
  rewrite ?node_47496.
  rewrite ?node_47497.
  rewrite ?node_47511.
  rewrite ?node_47512.
  rewrite ?node_47523.
  rewrite ?node_47524.
  rewrite ?node_47535.
  rewrite ?node_47536.
  rewrite ?node_47550.
  rewrite ?node_47551.
  rewrite ?node_47562.
  rewrite ?node_47563.
  rewrite ?node_47574.
  rewrite ?node_47575.
  rewrite ?node_47589.
  rewrite ?node_47590.
  rewrite ?node_47601.
  rewrite ?node_47602.
  rewrite ?node_47613.
  rewrite ?node_47614.
  rewrite ?node_47628.
  rewrite ?node_47629.
  rewrite ?node_47640.
  rewrite ?node_47641.
  rewrite ?node_47652.
  rewrite ?node_47653.
  rewrite ?node_47667.
  rewrite ?node_47668.
  rewrite ?node_47679.
  rewrite ?node_47680.
  rewrite ?node_47691.
  rewrite ?node_47692.
  rewrite ?node_47706.
  rewrite ?node_47707.
  rewrite ?node_47718.
  rewrite ?node_47719.
  rewrite ?node_47730.
  rewrite ?node_47731.
  rewrite ?node_47745.
  rewrite ?node_47746.
  rewrite ?node_47757.
  rewrite ?node_47758.
  rewrite ?node_47769.
  rewrite ?node_47770.
  rewrite ?node_47784.
  rewrite ?node_47785.
  rewrite ?node_47796.
  rewrite ?node_47797.
  rewrite ?node_47808.
  rewrite ?node_47809.
  rewrite ?node_47823.
  rewrite ?node_47824.
  rewrite ?node_47835.
  rewrite ?node_47836.
  rewrite ?node_47847.
  rewrite ?node_47848.
  rewrite ?node_47859.
  rewrite ?node_47860.
  rewrite ?node_47874.
  rewrite ?node_47875.
  rewrite ?node_47886.
  rewrite ?node_47887.
  rewrite ?node_47898.
  rewrite ?node_47899.
  rewrite ?node_47907.
  rewrite ?node_47908.
  rewrite ?node_47922.
  rewrite ?node_47923.
  rewrite ?node_47934.
  rewrite ?node_47935.
  rewrite ?node_47946.
  rewrite ?node_47947.
  rewrite ?node_47955.
  rewrite ?node_47956.
  rewrite ?node_47970.
  rewrite ?node_47971.
  rewrite ?node_47982.
  rewrite ?node_47983.
  rewrite ?node_47994.
  rewrite ?node_47995.
  rewrite ?node_48006.
  rewrite ?node_48007.
  rewrite ?node_48021.
  rewrite ?node_48022.
  rewrite ?node_48033.
  rewrite ?node_48034.
  rewrite ?node_48045.
  rewrite ?node_48046.
  rewrite ?node_48054.
  rewrite ?node_48055.
  rewrite ?node_48069.
  rewrite ?node_48070.
  rewrite ?node_48081.
  rewrite ?node_48082.
  rewrite ?node_48093.
  rewrite ?node_48094.
  rewrite ?node_48102.
  rewrite ?node_48103.
  rewrite ?node_48117.
  rewrite ?node_48118.
  rewrite ?node_48129.
  rewrite ?node_48130.
  rewrite ?node_48141.
  rewrite ?node_48142.
  rewrite ?node_48150.
  rewrite ?node_48151.
  rewrite ?node_48165.
  rewrite ?node_48166.
  rewrite ?node_48177.
  rewrite ?node_48178.
  rewrite ?node_48189.
  rewrite ?node_48190.
  rewrite ?node_48198.
  rewrite ?node_48199.
  rewrite ?node_48213.
  rewrite ?node_48214.
  rewrite ?node_48225.
  rewrite ?node_48226.
  rewrite ?node_48237.
  rewrite ?node_48238.
  rewrite ?node_48252.
  rewrite ?node_48253.
  rewrite ?node_48264.
  rewrite ?node_48265.
  rewrite ?node_48276.
  rewrite ?node_48277.
  rewrite ?node_48291.
  rewrite ?node_48292.
  rewrite ?node_48303.
  rewrite ?node_48304.
  rewrite ?node_48315.
  rewrite ?node_48316.
  rewrite ?node_48330.
  rewrite ?node_48331.
  rewrite ?node_48342.
  rewrite ?node_48343.
  rewrite ?node_48354.
  rewrite ?node_48355.
  rewrite ?node_48369.
  rewrite ?node_48370.
  rewrite ?node_48381.
  rewrite ?node_48382.
  rewrite ?node_48393.
  rewrite ?node_48394.
  rewrite ?node_48408.
  rewrite ?node_48409.
  rewrite ?node_48420.
  rewrite ?node_48421.
  rewrite ?node_48432.
  rewrite ?node_48433.
  rewrite ?node_48447.
  rewrite ?node_48448.
  rewrite ?node_48459.
  rewrite ?node_48460.
  rewrite ?node_48471.
  rewrite ?node_48472.
  rewrite ?node_48486.
  rewrite ?node_48487.
  rewrite ?node_48498.
  rewrite ?node_48499.
  rewrite ?node_48510.
  rewrite ?node_48511.
  reflexivity.
Qed.

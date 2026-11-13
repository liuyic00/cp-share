From Stdlib Require Import ZArith List Bool Zmod.Bits.
From BitsProofs Require Import ArrayRefinementNodes017.
Import ListNotations.
Open Scope Z_scope.
Local Opaque R.v16472 N.v16472 R.v16473 N.v16473 R.v16481 N.v16481 R.v16482 N.v16482 R.v16494 N.v16494 R.v16495 N.v16495 R.v16506 N.v16506 R.v16507 N.v16507 R.v16520 N.v16520 R.v16521 N.v16521 R.v16532 N.v16532 R.v16533 N.v16533 R.v16541 N.v16541 R.v16542 N.v16542 R.v16556 N.v16556 R.v16557 N.v16557 R.v16568 N.v16568 R.v16569 N.v16569 R.v16580 N.v16580 R.v16581 N.v16581 R.v16595 N.v16595 R.v16596 N.v16596 R.v16607 N.v16607 R.v16608 N.v16608 R.v16619 N.v16619 R.v16620 N.v16620 R.v16634 N.v16634 R.v16635 N.v16635 R.v16646 N.v16646 R.v16647 N.v16647 R.v16658 N.v16658 R.v16659 N.v16659 R.v16673 N.v16673 R.v16674 N.v16674 R.v16685 N.v16685 R.v16686 N.v16686 R.v16697 N.v16697 R.v16698 N.v16698 R.v16706 N.v16706 R.v16707 N.v16707 R.v16721 N.v16721 R.v16722 N.v16722 R.v16733 N.v16733 R.v16734 N.v16734 R.v16745 N.v16745 R.v16746 N.v16746 R.v16754 N.v16754 R.v16755 N.v16755 R.v16769 N.v16769 R.v16770 N.v16770 R.v16781 N.v16781 R.v16782 N.v16782 R.v16793 N.v16793 R.v16794 N.v16794 R.v16805 N.v16805 R.v16806 N.v16806 R.v16820 N.v16820 R.v16821 N.v16821 R.v16832 N.v16832 R.v16833 N.v16833 R.v16844 N.v16844 R.v16845 N.v16845 R.v16856 N.v16856 R.v16857 N.v16857 R.v16871 N.v16871 R.v16872 N.v16872 R.v16883 N.v16883 R.v16884 N.v16884 R.v16895 N.v16895 R.v16896 N.v16896 R.v16909 N.v16909 R.v16910 N.v16910 R.v16921 N.v16921 R.v16922 N.v16922 R.v16930 N.v16930 R.v16931 N.v16931 R.v16945 N.v16945 R.v16946 N.v16946 R.v16957 N.v16957 R.v16958 N.v16958 R.v16969 N.v16969 R.v16970 N.v16970 R.v16984 N.v16984 R.v16985 N.v16985 R.v16996 N.v16996 R.v16997 N.v16997 R.v17008 N.v17008 R.v17009 N.v17009 R.v17023 N.v17023 R.v17024 N.v17024 R.v17035 N.v17035 R.v17036 N.v17036 R.v17047 N.v17047 R.v17048 N.v17048 R.v17062 N.v17062 R.v17063 N.v17063 R.v17074 N.v17074 R.v17075 N.v17075 R.v17086 N.v17086 R.v17087 N.v17087 R.v17101 N.v17101 R.v17102 N.v17102 R.v17113 N.v17113 R.v17114 N.v17114 R.v17125 N.v17125 R.v17126 N.v17126 R.v17140 N.v17140 R.v17141 N.v17141 R.v17152 N.v17152 R.v17153 N.v17153 R.v17164 N.v17164 R.v17165 N.v17165 R.v17179 N.v17179 R.v17180 N.v17180 R.v17191 N.v17191 R.v17192 N.v17192 R.v17203 N.v17203 R.v17204 N.v17204 R.v17218 N.v17218 R.v17219 N.v17219 R.v17230 N.v17230 R.v17231 N.v17231 R.v17242 N.v17242 R.v17243 N.v17243 R.v17251 N.v17251 R.v17252 N.v17252 R.v17266 N.v17266 R.v17267 N.v17267 R.v17278 N.v17278 R.v17279 N.v17279 R.v17290 N.v17290 R.v17291 N.v17291 R.v17305 N.v17305 R.v17306 N.v17306 R.v17317 N.v17317 R.v17318 N.v17318 R.v17329 N.v17329 R.v17330 N.v17330 R.v17338 N.v17338 R.v17339 N.v17339 R.v17353 N.v17353 R.v17354 N.v17354 R.v17365 N.v17365 R.v17366 N.v17366 R.v17377 N.v17377 R.v17378 N.v17378 R.v17392 N.v17392 R.v17393 N.v17393 R.v17404 N.v17404 R.v17405 N.v17405 R.v17416 N.v17416 R.v17417 N.v17417 R.v17428 N.v17428 R.v17429 N.v17429 R.v17443 N.v17443 R.v17444 N.v17444 R.v17455 N.v17455 R.v17456 N.v17456 R.v17467 N.v17467 R.v17468 N.v17468 R.v17482 N.v17482 R.v17483 N.v17483 R.v17494 N.v17494 R.v17495 N.v17495 R.v17506 N.v17506 R.v17507 N.v17507 R.v17518 N.v17518 R.v17519 N.v17519 R.v17533 N.v17533 R.v17534 N.v17534 R.v17545 N.v17545 R.v17546 N.v17546 R.v17557 N.v17557 R.v17558 N.v17558 R.v17572 N.v17572 R.v17573 N.v17573 R.v17584 N.v17584 R.v17585 N.v17585 R.v17596 N.v17596 R.v17597 N.v17597 R.v17610 N.v17610 R.v17611 N.v17611 R.v17622 N.v17622 R.v17623 N.v17623 R.v17631 N.v17631 R.v17632 N.v17632 R.v17646 N.v17646 R.v17647 N.v17647 R.v17658 N.v17658 R.v17659 N.v17659 R.v17670 N.v17670 R.v17671 N.v17671 R.v17685 N.v17685 R.v17686 N.v17686 R.v17697 N.v17697 R.v17698 N.v17698 R.v17709 N.v17709 R.v17710 N.v17710 R.v17724 N.v17724 R.v17725 N.v17725.
Definition reference_checks_0 (s : N.State) (i : N.Inputs) : list bool := [
orb (negb (Z.eqb (R.v16473 (state s) (inputs i)) 1)) (Z.eqb (R.v16472 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v16482 (state s) (inputs i)) 1)) (Z.eqb (R.v16481 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v16495 (state s) (inputs i)) 1)) (Z.eqb (R.v16494 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v16507 (state s) (inputs i)) 1)) (Z.eqb (R.v16506 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v16521 (state s) (inputs i)) 1)) (Z.eqb (R.v16520 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v16533 (state s) (inputs i)) 1)) (Z.eqb (R.v16532 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v16542 (state s) (inputs i)) 1)) (Z.eqb (R.v16541 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v16557 (state s) (inputs i)) 1)) (Z.eqb (R.v16556 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v16569 (state s) (inputs i)) 1)) (Z.eqb (R.v16568 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v16581 (state s) (inputs i)) 1)) (Z.eqb (R.v16580 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v16596 (state s) (inputs i)) 1)) (Z.eqb (R.v16595 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v16608 (state s) (inputs i)) 1)) (Z.eqb (R.v16607 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v16620 (state s) (inputs i)) 1)) (Z.eqb (R.v16619 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v16635 (state s) (inputs i)) 1)) (Z.eqb (R.v16634 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v16647 (state s) (inputs i)) 1)) (Z.eqb (R.v16646 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v16659 (state s) (inputs i)) 1)) (Z.eqb (R.v16658 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v16674 (state s) (inputs i)) 1)) (Z.eqb (R.v16673 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v16686 (state s) (inputs i)) 1)) (Z.eqb (R.v16685 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v16698 (state s) (inputs i)) 1)) (Z.eqb (R.v16697 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v16707 (state s) (inputs i)) 1)) (Z.eqb (R.v16706 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v16722 (state s) (inputs i)) 1)) (Z.eqb (R.v16721 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v16734 (state s) (inputs i)) 1)) (Z.eqb (R.v16733 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v16746 (state s) (inputs i)) 1)) (Z.eqb (R.v16745 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v16755 (state s) (inputs i)) 1)) (Z.eqb (R.v16754 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v16770 (state s) (inputs i)) 1)) (Z.eqb (R.v16769 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v16782 (state s) (inputs i)) 1)) (Z.eqb (R.v16781 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v16794 (state s) (inputs i)) 1)) (Z.eqb (R.v16793 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v16806 (state s) (inputs i)) 1)) (Z.eqb (R.v16805 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v16821 (state s) (inputs i)) 1)) (Z.eqb (R.v16820 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v16833 (state s) (inputs i)) 1)) (Z.eqb (R.v16832 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v16845 (state s) (inputs i)) 1)) (Z.eqb (R.v16844 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v16857 (state s) (inputs i)) 1)) (Z.eqb (R.v16856 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v16872 (state s) (inputs i)) 1)) (Z.eqb (R.v16871 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v16884 (state s) (inputs i)) 1)) (Z.eqb (R.v16883 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v16896 (state s) (inputs i)) 1)) (Z.eqb (R.v16895 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v16910 (state s) (inputs i)) 1)) (Z.eqb (R.v16909 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v16922 (state s) (inputs i)) 1)) (Z.eqb (R.v16921 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v16931 (state s) (inputs i)) 1)) (Z.eqb (R.v16930 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v16946 (state s) (inputs i)) 1)) (Z.eqb (R.v16945 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v16958 (state s) (inputs i)) 1)) (Z.eqb (R.v16957 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v16970 (state s) (inputs i)) 1)) (Z.eqb (R.v16969 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v16985 (state s) (inputs i)) 1)) (Z.eqb (R.v16984 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v16997 (state s) (inputs i)) 1)) (Z.eqb (R.v16996 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17009 (state s) (inputs i)) 1)) (Z.eqb (R.v17008 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17024 (state s) (inputs i)) 1)) (Z.eqb (R.v17023 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17036 (state s) (inputs i)) 1)) (Z.eqb (R.v17035 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17048 (state s) (inputs i)) 1)) (Z.eqb (R.v17047 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17063 (state s) (inputs i)) 1)) (Z.eqb (R.v17062 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17075 (state s) (inputs i)) 1)) (Z.eqb (R.v17074 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17087 (state s) (inputs i)) 1)) (Z.eqb (R.v17086 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17102 (state s) (inputs i)) 1)) (Z.eqb (R.v17101 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17114 (state s) (inputs i)) 1)) (Z.eqb (R.v17113 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17126 (state s) (inputs i)) 1)) (Z.eqb (R.v17125 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17141 (state s) (inputs i)) 1)) (Z.eqb (R.v17140 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17153 (state s) (inputs i)) 1)) (Z.eqb (R.v17152 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17165 (state s) (inputs i)) 1)) (Z.eqb (R.v17164 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17180 (state s) (inputs i)) 1)) (Z.eqb (R.v17179 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17192 (state s) (inputs i)) 1)) (Z.eqb (R.v17191 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17204 (state s) (inputs i)) 1)) (Z.eqb (R.v17203 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17219 (state s) (inputs i)) 1)) (Z.eqb (R.v17218 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17231 (state s) (inputs i)) 1)) (Z.eqb (R.v17230 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17243 (state s) (inputs i)) 1)) (Z.eqb (R.v17242 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17252 (state s) (inputs i)) 1)) (Z.eqb (R.v17251 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17267 (state s) (inputs i)) 1)) (Z.eqb (R.v17266 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17279 (state s) (inputs i)) 1)) (Z.eqb (R.v17278 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17291 (state s) (inputs i)) 1)) (Z.eqb (R.v17290 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17306 (state s) (inputs i)) 1)) (Z.eqb (R.v17305 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17318 (state s) (inputs i)) 1)) (Z.eqb (R.v17317 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17330 (state s) (inputs i)) 1)) (Z.eqb (R.v17329 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17339 (state s) (inputs i)) 1)) (Z.eqb (R.v17338 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17354 (state s) (inputs i)) 1)) (Z.eqb (R.v17353 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17366 (state s) (inputs i)) 1)) (Z.eqb (R.v17365 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17378 (state s) (inputs i)) 1)) (Z.eqb (R.v17377 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17393 (state s) (inputs i)) 1)) (Z.eqb (R.v17392 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17405 (state s) (inputs i)) 1)) (Z.eqb (R.v17404 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17417 (state s) (inputs i)) 1)) (Z.eqb (R.v17416 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17429 (state s) (inputs i)) 1)) (Z.eqb (R.v17428 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17444 (state s) (inputs i)) 1)) (Z.eqb (R.v17443 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17456 (state s) (inputs i)) 1)) (Z.eqb (R.v17455 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17468 (state s) (inputs i)) 1)) (Z.eqb (R.v17467 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17483 (state s) (inputs i)) 1)) (Z.eqb (R.v17482 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17495 (state s) (inputs i)) 1)) (Z.eqb (R.v17494 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17507 (state s) (inputs i)) 1)) (Z.eqb (R.v17506 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17519 (state s) (inputs i)) 1)) (Z.eqb (R.v17518 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17534 (state s) (inputs i)) 1)) (Z.eqb (R.v17533 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17546 (state s) (inputs i)) 1)) (Z.eqb (R.v17545 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17558 (state s) (inputs i)) 1)) (Z.eqb (R.v17557 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17573 (state s) (inputs i)) 1)) (Z.eqb (R.v17572 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17585 (state s) (inputs i)) 1)) (Z.eqb (R.v17584 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17597 (state s) (inputs i)) 1)) (Z.eqb (R.v17596 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17611 (state s) (inputs i)) 1)) (Z.eqb (R.v17610 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17623 (state s) (inputs i)) 1)) (Z.eqb (R.v17622 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17632 (state s) (inputs i)) 1)) (Z.eqb (R.v17631 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17647 (state s) (inputs i)) 1)) (Z.eqb (R.v17646 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17659 (state s) (inputs i)) 1)) (Z.eqb (R.v17658 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17671 (state s) (inputs i)) 1)) (Z.eqb (R.v17670 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17686 (state s) (inputs i)) 1)) (Z.eqb (R.v17685 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17698 (state s) (inputs i)) 1)) (Z.eqb (R.v17697 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17710 (state s) (inputs i)) 1)) (Z.eqb (R.v17709 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17725 (state s) (inputs i)) 1)) (Z.eqb (R.v17724 (state s) (inputs i)) 1)
].
Definition native_checks_0 (s : N.State) (i : N.Inputs) : list bool := [
orb (negb (Zmod.eqb (N.v16473 s i) Zmod.one)) (Zmod.eqb (N.v16472 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v16482 s i) Zmod.one)) (Zmod.eqb (N.v16481 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v16495 s i) Zmod.one)) (Zmod.eqb (N.v16494 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v16507 s i) Zmod.one)) (Zmod.eqb (N.v16506 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v16521 s i) Zmod.one)) (Zmod.eqb (N.v16520 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v16533 s i) Zmod.one)) (Zmod.eqb (N.v16532 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v16542 s i) Zmod.one)) (Zmod.eqb (N.v16541 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v16557 s i) Zmod.one)) (Zmod.eqb (N.v16556 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v16569 s i) Zmod.one)) (Zmod.eqb (N.v16568 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v16581 s i) Zmod.one)) (Zmod.eqb (N.v16580 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v16596 s i) Zmod.one)) (Zmod.eqb (N.v16595 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v16608 s i) Zmod.one)) (Zmod.eqb (N.v16607 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v16620 s i) Zmod.one)) (Zmod.eqb (N.v16619 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v16635 s i) Zmod.one)) (Zmod.eqb (N.v16634 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v16647 s i) Zmod.one)) (Zmod.eqb (N.v16646 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v16659 s i) Zmod.one)) (Zmod.eqb (N.v16658 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v16674 s i) Zmod.one)) (Zmod.eqb (N.v16673 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v16686 s i) Zmod.one)) (Zmod.eqb (N.v16685 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v16698 s i) Zmod.one)) (Zmod.eqb (N.v16697 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v16707 s i) Zmod.one)) (Zmod.eqb (N.v16706 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v16722 s i) Zmod.one)) (Zmod.eqb (N.v16721 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v16734 s i) Zmod.one)) (Zmod.eqb (N.v16733 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v16746 s i) Zmod.one)) (Zmod.eqb (N.v16745 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v16755 s i) Zmod.one)) (Zmod.eqb (N.v16754 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v16770 s i) Zmod.one)) (Zmod.eqb (N.v16769 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v16782 s i) Zmod.one)) (Zmod.eqb (N.v16781 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v16794 s i) Zmod.one)) (Zmod.eqb (N.v16793 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v16806 s i) Zmod.one)) (Zmod.eqb (N.v16805 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v16821 s i) Zmod.one)) (Zmod.eqb (N.v16820 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v16833 s i) Zmod.one)) (Zmod.eqb (N.v16832 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v16845 s i) Zmod.one)) (Zmod.eqb (N.v16844 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v16857 s i) Zmod.one)) (Zmod.eqb (N.v16856 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v16872 s i) Zmod.one)) (Zmod.eqb (N.v16871 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v16884 s i) Zmod.one)) (Zmod.eqb (N.v16883 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v16896 s i) Zmod.one)) (Zmod.eqb (N.v16895 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v16910 s i) Zmod.one)) (Zmod.eqb (N.v16909 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v16922 s i) Zmod.one)) (Zmod.eqb (N.v16921 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v16931 s i) Zmod.one)) (Zmod.eqb (N.v16930 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v16946 s i) Zmod.one)) (Zmod.eqb (N.v16945 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v16958 s i) Zmod.one)) (Zmod.eqb (N.v16957 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v16970 s i) Zmod.one)) (Zmod.eqb (N.v16969 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v16985 s i) Zmod.one)) (Zmod.eqb (N.v16984 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v16997 s i) Zmod.one)) (Zmod.eqb (N.v16996 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17009 s i) Zmod.one)) (Zmod.eqb (N.v17008 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17024 s i) Zmod.one)) (Zmod.eqb (N.v17023 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17036 s i) Zmod.one)) (Zmod.eqb (N.v17035 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17048 s i) Zmod.one)) (Zmod.eqb (N.v17047 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17063 s i) Zmod.one)) (Zmod.eqb (N.v17062 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17075 s i) Zmod.one)) (Zmod.eqb (N.v17074 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17087 s i) Zmod.one)) (Zmod.eqb (N.v17086 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17102 s i) Zmod.one)) (Zmod.eqb (N.v17101 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17114 s i) Zmod.one)) (Zmod.eqb (N.v17113 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17126 s i) Zmod.one)) (Zmod.eqb (N.v17125 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17141 s i) Zmod.one)) (Zmod.eqb (N.v17140 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17153 s i) Zmod.one)) (Zmod.eqb (N.v17152 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17165 s i) Zmod.one)) (Zmod.eqb (N.v17164 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17180 s i) Zmod.one)) (Zmod.eqb (N.v17179 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17192 s i) Zmod.one)) (Zmod.eqb (N.v17191 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17204 s i) Zmod.one)) (Zmod.eqb (N.v17203 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17219 s i) Zmod.one)) (Zmod.eqb (N.v17218 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17231 s i) Zmod.one)) (Zmod.eqb (N.v17230 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17243 s i) Zmod.one)) (Zmod.eqb (N.v17242 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17252 s i) Zmod.one)) (Zmod.eqb (N.v17251 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17267 s i) Zmod.one)) (Zmod.eqb (N.v17266 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17279 s i) Zmod.one)) (Zmod.eqb (N.v17278 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17291 s i) Zmod.one)) (Zmod.eqb (N.v17290 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17306 s i) Zmod.one)) (Zmod.eqb (N.v17305 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17318 s i) Zmod.one)) (Zmod.eqb (N.v17317 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17330 s i) Zmod.one)) (Zmod.eqb (N.v17329 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17339 s i) Zmod.one)) (Zmod.eqb (N.v17338 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17354 s i) Zmod.one)) (Zmod.eqb (N.v17353 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17366 s i) Zmod.one)) (Zmod.eqb (N.v17365 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17378 s i) Zmod.one)) (Zmod.eqb (N.v17377 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17393 s i) Zmod.one)) (Zmod.eqb (N.v17392 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17405 s i) Zmod.one)) (Zmod.eqb (N.v17404 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17417 s i) Zmod.one)) (Zmod.eqb (N.v17416 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17429 s i) Zmod.one)) (Zmod.eqb (N.v17428 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17444 s i) Zmod.one)) (Zmod.eqb (N.v17443 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17456 s i) Zmod.one)) (Zmod.eqb (N.v17455 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17468 s i) Zmod.one)) (Zmod.eqb (N.v17467 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17483 s i) Zmod.one)) (Zmod.eqb (N.v17482 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17495 s i) Zmod.one)) (Zmod.eqb (N.v17494 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17507 s i) Zmod.one)) (Zmod.eqb (N.v17506 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17519 s i) Zmod.one)) (Zmod.eqb (N.v17518 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17534 s i) Zmod.one)) (Zmod.eqb (N.v17533 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17546 s i) Zmod.one)) (Zmod.eqb (N.v17545 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17558 s i) Zmod.one)) (Zmod.eqb (N.v17557 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17573 s i) Zmod.one)) (Zmod.eqb (N.v17572 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17585 s i) Zmod.one)) (Zmod.eqb (N.v17584 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17597 s i) Zmod.one)) (Zmod.eqb (N.v17596 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17611 s i) Zmod.one)) (Zmod.eqb (N.v17610 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17623 s i) Zmod.one)) (Zmod.eqb (N.v17622 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17632 s i) Zmod.one)) (Zmod.eqb (N.v17631 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17647 s i) Zmod.one)) (Zmod.eqb (N.v17646 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17659 s i) Zmod.one)) (Zmod.eqb (N.v17658 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17671 s i) Zmod.one)) (Zmod.eqb (N.v17670 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17686 s i) Zmod.one)) (Zmod.eqb (N.v17685 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17698 s i) Zmod.one)) (Zmod.eqb (N.v17697 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17710 s i) Zmod.one)) (Zmod.eqb (N.v17709 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17725 s i) Zmod.one)) (Zmod.eqb (N.v17724 s i) Zmod.one)
].
Lemma checks_0 s i : reference_checks_0 s i = native_checks_0 s i.
Proof. unfold reference_checks_0, native_checks_0.
  rewrite ?node_16472.
  rewrite ?node_16473.
  rewrite ?node_16481.
  rewrite ?node_16482.
  rewrite ?node_16494.
  rewrite ?node_16495.
  rewrite ?node_16506.
  rewrite ?node_16507.
  rewrite ?node_16520.
  rewrite ?node_16521.
  rewrite ?node_16532.
  rewrite ?node_16533.
  rewrite ?node_16541.
  rewrite ?node_16542.
  rewrite ?node_16556.
  rewrite ?node_16557.
  rewrite ?node_16568.
  rewrite ?node_16569.
  rewrite ?node_16580.
  rewrite ?node_16581.
  rewrite ?node_16595.
  rewrite ?node_16596.
  rewrite ?node_16607.
  rewrite ?node_16608.
  rewrite ?node_16619.
  rewrite ?node_16620.
  rewrite ?node_16634.
  rewrite ?node_16635.
  rewrite ?node_16646.
  rewrite ?node_16647.
  rewrite ?node_16658.
  rewrite ?node_16659.
  rewrite ?node_16673.
  rewrite ?node_16674.
  rewrite ?node_16685.
  rewrite ?node_16686.
  rewrite ?node_16697.
  rewrite ?node_16698.
  rewrite ?node_16706.
  rewrite ?node_16707.
  rewrite ?node_16721.
  rewrite ?node_16722.
  rewrite ?node_16733.
  rewrite ?node_16734.
  rewrite ?node_16745.
  rewrite ?node_16746.
  rewrite ?node_16754.
  rewrite ?node_16755.
  rewrite ?node_16769.
  rewrite ?node_16770.
  rewrite ?node_16781.
  rewrite ?node_16782.
  rewrite ?node_16793.
  rewrite ?node_16794.
  rewrite ?node_16805.
  rewrite ?node_16806.
  rewrite ?node_16820.
  rewrite ?node_16821.
  rewrite ?node_16832.
  rewrite ?node_16833.
  rewrite ?node_16844.
  rewrite ?node_16845.
  rewrite ?node_16856.
  rewrite ?node_16857.
  rewrite ?node_16871.
  rewrite ?node_16872.
  rewrite ?node_16883.
  rewrite ?node_16884.
  rewrite ?node_16895.
  rewrite ?node_16896.
  rewrite ?node_16909.
  rewrite ?node_16910.
  rewrite ?node_16921.
  rewrite ?node_16922.
  rewrite ?node_16930.
  rewrite ?node_16931.
  rewrite ?node_16945.
  rewrite ?node_16946.
  rewrite ?node_16957.
  rewrite ?node_16958.
  rewrite ?node_16969.
  rewrite ?node_16970.
  rewrite ?node_16984.
  rewrite ?node_16985.
  rewrite ?node_16996.
  rewrite ?node_16997.
  rewrite ?node_17008.
  rewrite ?node_17009.
  rewrite ?node_17023.
  rewrite ?node_17024.
  rewrite ?node_17035.
  rewrite ?node_17036.
  rewrite ?node_17047.
  rewrite ?node_17048.
  rewrite ?node_17062.
  rewrite ?node_17063.
  rewrite ?node_17074.
  rewrite ?node_17075.
  rewrite ?node_17086.
  rewrite ?node_17087.
  rewrite ?node_17101.
  rewrite ?node_17102.
  rewrite ?node_17113.
  rewrite ?node_17114.
  rewrite ?node_17125.
  rewrite ?node_17126.
  rewrite ?node_17140.
  rewrite ?node_17141.
  rewrite ?node_17152.
  rewrite ?node_17153.
  rewrite ?node_17164.
  rewrite ?node_17165.
  rewrite ?node_17179.
  rewrite ?node_17180.
  rewrite ?node_17191.
  rewrite ?node_17192.
  rewrite ?node_17203.
  rewrite ?node_17204.
  rewrite ?node_17218.
  rewrite ?node_17219.
  rewrite ?node_17230.
  rewrite ?node_17231.
  rewrite ?node_17242.
  rewrite ?node_17243.
  rewrite ?node_17251.
  rewrite ?node_17252.
  rewrite ?node_17266.
  rewrite ?node_17267.
  rewrite ?node_17278.
  rewrite ?node_17279.
  rewrite ?node_17290.
  rewrite ?node_17291.
  rewrite ?node_17305.
  rewrite ?node_17306.
  rewrite ?node_17317.
  rewrite ?node_17318.
  rewrite ?node_17329.
  rewrite ?node_17330.
  rewrite ?node_17338.
  rewrite ?node_17339.
  rewrite ?node_17353.
  rewrite ?node_17354.
  rewrite ?node_17365.
  rewrite ?node_17366.
  rewrite ?node_17377.
  rewrite ?node_17378.
  rewrite ?node_17392.
  rewrite ?node_17393.
  rewrite ?node_17404.
  rewrite ?node_17405.
  rewrite ?node_17416.
  rewrite ?node_17417.
  rewrite ?node_17428.
  rewrite ?node_17429.
  rewrite ?node_17443.
  rewrite ?node_17444.
  rewrite ?node_17455.
  rewrite ?node_17456.
  rewrite ?node_17467.
  rewrite ?node_17468.
  rewrite ?node_17482.
  rewrite ?node_17483.
  rewrite ?node_17494.
  rewrite ?node_17495.
  rewrite ?node_17506.
  rewrite ?node_17507.
  rewrite ?node_17518.
  rewrite ?node_17519.
  rewrite ?node_17533.
  rewrite ?node_17534.
  rewrite ?node_17545.
  rewrite ?node_17546.
  rewrite ?node_17557.
  rewrite ?node_17558.
  rewrite ?node_17572.
  rewrite ?node_17573.
  rewrite ?node_17584.
  rewrite ?node_17585.
  rewrite ?node_17596.
  rewrite ?node_17597.
  rewrite ?node_17610.
  rewrite ?node_17611.
  rewrite ?node_17622.
  rewrite ?node_17623.
  rewrite ?node_17631.
  rewrite ?node_17632.
  rewrite ?node_17646.
  rewrite ?node_17647.
  rewrite ?node_17658.
  rewrite ?node_17659.
  rewrite ?node_17670.
  rewrite ?node_17671.
  rewrite ?node_17685.
  rewrite ?node_17686.
  rewrite ?node_17697.
  rewrite ?node_17698.
  rewrite ?node_17709.
  rewrite ?node_17710.
  rewrite ?node_17724.
  rewrite ?node_17725.
  reflexivity.
Qed.

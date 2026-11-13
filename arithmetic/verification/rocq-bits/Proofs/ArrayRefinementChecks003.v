From Stdlib Require Import ZArith List Bool Zmod.Bits.
From BitsProofs Require Import ArrayRefinementNodes021.
Import ListNotations.
Open Scope Z_scope.
Local Opaque R.v20308 N.v20308 R.v20309 N.v20309 R.v20320 N.v20320 R.v20321 N.v20321 R.v20335 N.v20335 R.v20336 N.v20336 R.v20347 N.v20347 R.v20348 N.v20348 R.v20359 N.v20359 R.v20360 N.v20360 R.v20374 N.v20374 R.v20375 N.v20375 R.v20386 N.v20386 R.v20387 N.v20387 R.v20398 N.v20398 R.v20399 N.v20399 R.v20413 N.v20413 R.v20414 N.v20414 R.v20425 N.v20425 R.v20426 N.v20426 R.v20437 N.v20437 R.v20438 N.v20438 R.v20452 N.v20452 R.v20453 N.v20453 R.v20464 N.v20464 R.v20465 N.v20465 R.v20476 N.v20476 R.v20477 N.v20477 R.v20491 N.v20491 R.v20492 N.v20492 R.v20503 N.v20503 R.v20504 N.v20504 R.v20515 N.v20515 R.v20516 N.v20516 R.v20530 N.v20530 R.v20531 N.v20531 R.v20542 N.v20542 R.v20543 N.v20543 R.v20554 N.v20554 R.v20555 N.v20555 R.v20569 N.v20569 R.v20570 N.v20570 R.v20581 N.v20581 R.v20582 N.v20582 R.v20593 N.v20593 R.v20594 N.v20594 R.v20608 N.v20608 R.v20609 N.v20609 R.v20620 N.v20620 R.v20621 N.v20621 R.v20632 N.v20632 R.v20633 N.v20633 R.v20647 N.v20647 R.v20648 N.v20648 R.v20659 N.v20659 R.v20660 N.v20660 R.v20671 N.v20671 R.v20672 N.v20672 R.v20686 N.v20686 R.v20687 N.v20687 R.v20698 N.v20698 R.v20699 N.v20699 R.v20710 N.v20710 R.v20711 N.v20711 R.v20725 N.v20725 R.v20726 N.v20726 R.v20737 N.v20737 R.v20738 N.v20738 R.v20749 N.v20749 R.v20750 N.v20750 R.v20758 N.v20758 R.v20759 N.v20759 R.v20773 N.v20773 R.v20774 N.v20774 R.v20785 N.v20785 R.v20786 N.v20786 R.v20797 N.v20797 R.v20798 N.v20798 R.v20812 N.v20812 R.v20813 N.v20813 R.v20824 N.v20824 R.v20825 N.v20825 R.v20836 N.v20836 R.v20837 N.v20837 R.v20851 N.v20851 R.v20852 N.v20852 R.v20863 N.v20863 R.v20864 N.v20864 R.v20875 N.v20875 R.v20876 N.v20876 R.v20890 N.v20890 R.v20891 N.v20891 R.v20902 N.v20902 R.v20903 N.v20903 R.v20914 N.v20914 R.v20915 N.v20915 R.v20929 N.v20929 R.v20930 N.v20930 R.v20941 N.v20941 R.v20942 N.v20942 R.v20953 N.v20953 R.v20954 N.v20954 R.v20962 N.v20962 R.v20963 N.v20963 R.v20977 N.v20977 R.v20978 N.v20978 R.v20989 N.v20989 R.v20990 N.v20990 R.v21001 N.v21001 R.v21002 N.v21002 R.v21016 N.v21016 R.v21017 N.v21017 R.v21028 N.v21028 R.v21029 N.v21029 R.v21040 N.v21040 R.v21041 N.v21041 R.v21055 N.v21055 R.v21056 N.v21056 R.v21067 N.v21067 R.v21068 N.v21068 R.v21079 N.v21079 R.v21080 N.v21080 R.v21094 N.v21094 R.v21095 N.v21095 R.v21106 N.v21106 R.v21107 N.v21107 R.v21118 N.v21118 R.v21119 N.v21119 R.v21133 N.v21133 R.v21134 N.v21134 R.v21145 N.v21145 R.v21146 N.v21146 R.v21157 N.v21157 R.v21158 N.v21158 R.v21169 N.v21169 R.v21170 N.v21170 R.v21184 N.v21184 R.v21185 N.v21185 R.v21196 N.v21196 R.v21197 N.v21197 R.v21208 N.v21208 R.v21209 N.v21209 R.v21223 N.v21223 R.v21224 N.v21224 R.v21235 N.v21235 R.v21236 N.v21236 R.v21247 N.v21247 R.v21248 N.v21248 R.v21262 N.v21262 R.v21263 N.v21263 R.v21274 N.v21274 R.v21275 N.v21275 R.v21286 N.v21286 R.v21287 N.v21287 R.v21301 N.v21301 R.v21302 N.v21302 R.v21313 N.v21313 R.v21314 N.v21314 R.v21325 N.v21325 R.v21326 N.v21326 R.v21340 N.v21340 R.v21341 N.v21341 R.v21352 N.v21352 R.v21353 N.v21353 R.v21364 N.v21364 R.v21365 N.v21365 R.v21376 N.v21376 R.v21377 N.v21377 R.v21391 N.v21391 R.v21392 N.v21392 R.v21403 N.v21403 R.v21404 N.v21404 R.v21415 N.v21415 R.v21416 N.v21416 R.v21430 N.v21430 R.v21431 N.v21431 R.v21442 N.v21442 R.v21443 N.v21443 R.v21454 N.v21454 R.v21455 N.v21455 R.v21469 N.v21469 R.v21470 N.v21470 R.v21481 N.v21481 R.v21482 N.v21482 R.v21493 N.v21493 R.v21494 N.v21494 R.v21508 N.v21508 R.v21509 N.v21509 R.v21520 N.v21520 R.v21521 N.v21521 R.v21532 N.v21532 R.v21533 N.v21533 R.v21547 N.v21547 R.v21548 N.v21548 R.v21559 N.v21559 R.v21560 N.v21560 R.v21571 N.v21571 R.v21572 N.v21572 R.v21585 N.v21585 R.v21586 N.v21586.
Definition reference_checks_3 (s : N.State) (i : N.Inputs) : list bool := [
orb (negb (Z.eqb (R.v20309 (state s) (inputs i)) 1)) (Z.eqb (R.v20308 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20321 (state s) (inputs i)) 1)) (Z.eqb (R.v20320 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20336 (state s) (inputs i)) 1)) (Z.eqb (R.v20335 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20348 (state s) (inputs i)) 1)) (Z.eqb (R.v20347 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20360 (state s) (inputs i)) 1)) (Z.eqb (R.v20359 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20375 (state s) (inputs i)) 1)) (Z.eqb (R.v20374 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20387 (state s) (inputs i)) 1)) (Z.eqb (R.v20386 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20399 (state s) (inputs i)) 1)) (Z.eqb (R.v20398 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20414 (state s) (inputs i)) 1)) (Z.eqb (R.v20413 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20426 (state s) (inputs i)) 1)) (Z.eqb (R.v20425 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20438 (state s) (inputs i)) 1)) (Z.eqb (R.v20437 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20453 (state s) (inputs i)) 1)) (Z.eqb (R.v20452 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20465 (state s) (inputs i)) 1)) (Z.eqb (R.v20464 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20477 (state s) (inputs i)) 1)) (Z.eqb (R.v20476 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20492 (state s) (inputs i)) 1)) (Z.eqb (R.v20491 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20504 (state s) (inputs i)) 1)) (Z.eqb (R.v20503 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20516 (state s) (inputs i)) 1)) (Z.eqb (R.v20515 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20531 (state s) (inputs i)) 1)) (Z.eqb (R.v20530 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20543 (state s) (inputs i)) 1)) (Z.eqb (R.v20542 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20555 (state s) (inputs i)) 1)) (Z.eqb (R.v20554 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20570 (state s) (inputs i)) 1)) (Z.eqb (R.v20569 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20582 (state s) (inputs i)) 1)) (Z.eqb (R.v20581 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20594 (state s) (inputs i)) 1)) (Z.eqb (R.v20593 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20609 (state s) (inputs i)) 1)) (Z.eqb (R.v20608 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20621 (state s) (inputs i)) 1)) (Z.eqb (R.v20620 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20633 (state s) (inputs i)) 1)) (Z.eqb (R.v20632 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20648 (state s) (inputs i)) 1)) (Z.eqb (R.v20647 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20660 (state s) (inputs i)) 1)) (Z.eqb (R.v20659 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20672 (state s) (inputs i)) 1)) (Z.eqb (R.v20671 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20687 (state s) (inputs i)) 1)) (Z.eqb (R.v20686 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20699 (state s) (inputs i)) 1)) (Z.eqb (R.v20698 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20711 (state s) (inputs i)) 1)) (Z.eqb (R.v20710 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20726 (state s) (inputs i)) 1)) (Z.eqb (R.v20725 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20738 (state s) (inputs i)) 1)) (Z.eqb (R.v20737 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20750 (state s) (inputs i)) 1)) (Z.eqb (R.v20749 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20759 (state s) (inputs i)) 1)) (Z.eqb (R.v20758 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20774 (state s) (inputs i)) 1)) (Z.eqb (R.v20773 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20786 (state s) (inputs i)) 1)) (Z.eqb (R.v20785 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20798 (state s) (inputs i)) 1)) (Z.eqb (R.v20797 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20813 (state s) (inputs i)) 1)) (Z.eqb (R.v20812 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20825 (state s) (inputs i)) 1)) (Z.eqb (R.v20824 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20837 (state s) (inputs i)) 1)) (Z.eqb (R.v20836 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20852 (state s) (inputs i)) 1)) (Z.eqb (R.v20851 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20864 (state s) (inputs i)) 1)) (Z.eqb (R.v20863 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20876 (state s) (inputs i)) 1)) (Z.eqb (R.v20875 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20891 (state s) (inputs i)) 1)) (Z.eqb (R.v20890 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20903 (state s) (inputs i)) 1)) (Z.eqb (R.v20902 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20915 (state s) (inputs i)) 1)) (Z.eqb (R.v20914 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20930 (state s) (inputs i)) 1)) (Z.eqb (R.v20929 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20942 (state s) (inputs i)) 1)) (Z.eqb (R.v20941 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20954 (state s) (inputs i)) 1)) (Z.eqb (R.v20953 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20963 (state s) (inputs i)) 1)) (Z.eqb (R.v20962 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20978 (state s) (inputs i)) 1)) (Z.eqb (R.v20977 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v20990 (state s) (inputs i)) 1)) (Z.eqb (R.v20989 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21002 (state s) (inputs i)) 1)) (Z.eqb (R.v21001 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21017 (state s) (inputs i)) 1)) (Z.eqb (R.v21016 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21029 (state s) (inputs i)) 1)) (Z.eqb (R.v21028 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21041 (state s) (inputs i)) 1)) (Z.eqb (R.v21040 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21056 (state s) (inputs i)) 1)) (Z.eqb (R.v21055 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21068 (state s) (inputs i)) 1)) (Z.eqb (R.v21067 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21080 (state s) (inputs i)) 1)) (Z.eqb (R.v21079 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21095 (state s) (inputs i)) 1)) (Z.eqb (R.v21094 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21107 (state s) (inputs i)) 1)) (Z.eqb (R.v21106 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21119 (state s) (inputs i)) 1)) (Z.eqb (R.v21118 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21134 (state s) (inputs i)) 1)) (Z.eqb (R.v21133 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21146 (state s) (inputs i)) 1)) (Z.eqb (R.v21145 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21158 (state s) (inputs i)) 1)) (Z.eqb (R.v21157 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21170 (state s) (inputs i)) 1)) (Z.eqb (R.v21169 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21185 (state s) (inputs i)) 1)) (Z.eqb (R.v21184 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21197 (state s) (inputs i)) 1)) (Z.eqb (R.v21196 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21209 (state s) (inputs i)) 1)) (Z.eqb (R.v21208 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21224 (state s) (inputs i)) 1)) (Z.eqb (R.v21223 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21236 (state s) (inputs i)) 1)) (Z.eqb (R.v21235 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21248 (state s) (inputs i)) 1)) (Z.eqb (R.v21247 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21263 (state s) (inputs i)) 1)) (Z.eqb (R.v21262 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21275 (state s) (inputs i)) 1)) (Z.eqb (R.v21274 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21287 (state s) (inputs i)) 1)) (Z.eqb (R.v21286 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21302 (state s) (inputs i)) 1)) (Z.eqb (R.v21301 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21314 (state s) (inputs i)) 1)) (Z.eqb (R.v21313 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21326 (state s) (inputs i)) 1)) (Z.eqb (R.v21325 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21341 (state s) (inputs i)) 1)) (Z.eqb (R.v21340 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21353 (state s) (inputs i)) 1)) (Z.eqb (R.v21352 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21365 (state s) (inputs i)) 1)) (Z.eqb (R.v21364 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21377 (state s) (inputs i)) 1)) (Z.eqb (R.v21376 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21392 (state s) (inputs i)) 1)) (Z.eqb (R.v21391 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21404 (state s) (inputs i)) 1)) (Z.eqb (R.v21403 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21416 (state s) (inputs i)) 1)) (Z.eqb (R.v21415 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21431 (state s) (inputs i)) 1)) (Z.eqb (R.v21430 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21443 (state s) (inputs i)) 1)) (Z.eqb (R.v21442 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21455 (state s) (inputs i)) 1)) (Z.eqb (R.v21454 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21470 (state s) (inputs i)) 1)) (Z.eqb (R.v21469 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21482 (state s) (inputs i)) 1)) (Z.eqb (R.v21481 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21494 (state s) (inputs i)) 1)) (Z.eqb (R.v21493 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21509 (state s) (inputs i)) 1)) (Z.eqb (R.v21508 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21521 (state s) (inputs i)) 1)) (Z.eqb (R.v21520 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21533 (state s) (inputs i)) 1)) (Z.eqb (R.v21532 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21548 (state s) (inputs i)) 1)) (Z.eqb (R.v21547 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21560 (state s) (inputs i)) 1)) (Z.eqb (R.v21559 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21572 (state s) (inputs i)) 1)) (Z.eqb (R.v21571 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21586 (state s) (inputs i)) 1)) (Z.eqb (R.v21585 (state s) (inputs i)) 1)
].
Definition native_checks_3 (s : N.State) (i : N.Inputs) : list bool := [
orb (negb (Zmod.eqb (N.v20309 s i) Zmod.one)) (Zmod.eqb (N.v20308 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20321 s i) Zmod.one)) (Zmod.eqb (N.v20320 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20336 s i) Zmod.one)) (Zmod.eqb (N.v20335 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20348 s i) Zmod.one)) (Zmod.eqb (N.v20347 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20360 s i) Zmod.one)) (Zmod.eqb (N.v20359 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20375 s i) Zmod.one)) (Zmod.eqb (N.v20374 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20387 s i) Zmod.one)) (Zmod.eqb (N.v20386 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20399 s i) Zmod.one)) (Zmod.eqb (N.v20398 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20414 s i) Zmod.one)) (Zmod.eqb (N.v20413 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20426 s i) Zmod.one)) (Zmod.eqb (N.v20425 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20438 s i) Zmod.one)) (Zmod.eqb (N.v20437 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20453 s i) Zmod.one)) (Zmod.eqb (N.v20452 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20465 s i) Zmod.one)) (Zmod.eqb (N.v20464 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20477 s i) Zmod.one)) (Zmod.eqb (N.v20476 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20492 s i) Zmod.one)) (Zmod.eqb (N.v20491 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20504 s i) Zmod.one)) (Zmod.eqb (N.v20503 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20516 s i) Zmod.one)) (Zmod.eqb (N.v20515 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20531 s i) Zmod.one)) (Zmod.eqb (N.v20530 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20543 s i) Zmod.one)) (Zmod.eqb (N.v20542 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20555 s i) Zmod.one)) (Zmod.eqb (N.v20554 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20570 s i) Zmod.one)) (Zmod.eqb (N.v20569 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20582 s i) Zmod.one)) (Zmod.eqb (N.v20581 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20594 s i) Zmod.one)) (Zmod.eqb (N.v20593 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20609 s i) Zmod.one)) (Zmod.eqb (N.v20608 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20621 s i) Zmod.one)) (Zmod.eqb (N.v20620 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20633 s i) Zmod.one)) (Zmod.eqb (N.v20632 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20648 s i) Zmod.one)) (Zmod.eqb (N.v20647 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20660 s i) Zmod.one)) (Zmod.eqb (N.v20659 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20672 s i) Zmod.one)) (Zmod.eqb (N.v20671 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20687 s i) Zmod.one)) (Zmod.eqb (N.v20686 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20699 s i) Zmod.one)) (Zmod.eqb (N.v20698 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20711 s i) Zmod.one)) (Zmod.eqb (N.v20710 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20726 s i) Zmod.one)) (Zmod.eqb (N.v20725 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20738 s i) Zmod.one)) (Zmod.eqb (N.v20737 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20750 s i) Zmod.one)) (Zmod.eqb (N.v20749 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20759 s i) Zmod.one)) (Zmod.eqb (N.v20758 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20774 s i) Zmod.one)) (Zmod.eqb (N.v20773 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20786 s i) Zmod.one)) (Zmod.eqb (N.v20785 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20798 s i) Zmod.one)) (Zmod.eqb (N.v20797 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20813 s i) Zmod.one)) (Zmod.eqb (N.v20812 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20825 s i) Zmod.one)) (Zmod.eqb (N.v20824 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20837 s i) Zmod.one)) (Zmod.eqb (N.v20836 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20852 s i) Zmod.one)) (Zmod.eqb (N.v20851 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20864 s i) Zmod.one)) (Zmod.eqb (N.v20863 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20876 s i) Zmod.one)) (Zmod.eqb (N.v20875 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20891 s i) Zmod.one)) (Zmod.eqb (N.v20890 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20903 s i) Zmod.one)) (Zmod.eqb (N.v20902 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20915 s i) Zmod.one)) (Zmod.eqb (N.v20914 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20930 s i) Zmod.one)) (Zmod.eqb (N.v20929 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20942 s i) Zmod.one)) (Zmod.eqb (N.v20941 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20954 s i) Zmod.one)) (Zmod.eqb (N.v20953 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20963 s i) Zmod.one)) (Zmod.eqb (N.v20962 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20978 s i) Zmod.one)) (Zmod.eqb (N.v20977 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v20990 s i) Zmod.one)) (Zmod.eqb (N.v20989 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21002 s i) Zmod.one)) (Zmod.eqb (N.v21001 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21017 s i) Zmod.one)) (Zmod.eqb (N.v21016 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21029 s i) Zmod.one)) (Zmod.eqb (N.v21028 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21041 s i) Zmod.one)) (Zmod.eqb (N.v21040 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21056 s i) Zmod.one)) (Zmod.eqb (N.v21055 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21068 s i) Zmod.one)) (Zmod.eqb (N.v21067 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21080 s i) Zmod.one)) (Zmod.eqb (N.v21079 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21095 s i) Zmod.one)) (Zmod.eqb (N.v21094 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21107 s i) Zmod.one)) (Zmod.eqb (N.v21106 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21119 s i) Zmod.one)) (Zmod.eqb (N.v21118 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21134 s i) Zmod.one)) (Zmod.eqb (N.v21133 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21146 s i) Zmod.one)) (Zmod.eqb (N.v21145 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21158 s i) Zmod.one)) (Zmod.eqb (N.v21157 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21170 s i) Zmod.one)) (Zmod.eqb (N.v21169 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21185 s i) Zmod.one)) (Zmod.eqb (N.v21184 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21197 s i) Zmod.one)) (Zmod.eqb (N.v21196 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21209 s i) Zmod.one)) (Zmod.eqb (N.v21208 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21224 s i) Zmod.one)) (Zmod.eqb (N.v21223 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21236 s i) Zmod.one)) (Zmod.eqb (N.v21235 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21248 s i) Zmod.one)) (Zmod.eqb (N.v21247 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21263 s i) Zmod.one)) (Zmod.eqb (N.v21262 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21275 s i) Zmod.one)) (Zmod.eqb (N.v21274 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21287 s i) Zmod.one)) (Zmod.eqb (N.v21286 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21302 s i) Zmod.one)) (Zmod.eqb (N.v21301 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21314 s i) Zmod.one)) (Zmod.eqb (N.v21313 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21326 s i) Zmod.one)) (Zmod.eqb (N.v21325 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21341 s i) Zmod.one)) (Zmod.eqb (N.v21340 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21353 s i) Zmod.one)) (Zmod.eqb (N.v21352 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21365 s i) Zmod.one)) (Zmod.eqb (N.v21364 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21377 s i) Zmod.one)) (Zmod.eqb (N.v21376 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21392 s i) Zmod.one)) (Zmod.eqb (N.v21391 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21404 s i) Zmod.one)) (Zmod.eqb (N.v21403 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21416 s i) Zmod.one)) (Zmod.eqb (N.v21415 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21431 s i) Zmod.one)) (Zmod.eqb (N.v21430 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21443 s i) Zmod.one)) (Zmod.eqb (N.v21442 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21455 s i) Zmod.one)) (Zmod.eqb (N.v21454 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21470 s i) Zmod.one)) (Zmod.eqb (N.v21469 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21482 s i) Zmod.one)) (Zmod.eqb (N.v21481 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21494 s i) Zmod.one)) (Zmod.eqb (N.v21493 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21509 s i) Zmod.one)) (Zmod.eqb (N.v21508 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21521 s i) Zmod.one)) (Zmod.eqb (N.v21520 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21533 s i) Zmod.one)) (Zmod.eqb (N.v21532 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21548 s i) Zmod.one)) (Zmod.eqb (N.v21547 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21560 s i) Zmod.one)) (Zmod.eqb (N.v21559 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21572 s i) Zmod.one)) (Zmod.eqb (N.v21571 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21586 s i) Zmod.one)) (Zmod.eqb (N.v21585 s i) Zmod.one)
].
Lemma checks_3 s i : reference_checks_3 s i = native_checks_3 s i.
Proof. unfold reference_checks_3, native_checks_3.
  rewrite ?node_20308.
  rewrite ?node_20309.
  rewrite ?node_20320.
  rewrite ?node_20321.
  rewrite ?node_20335.
  rewrite ?node_20336.
  rewrite ?node_20347.
  rewrite ?node_20348.
  rewrite ?node_20359.
  rewrite ?node_20360.
  rewrite ?node_20374.
  rewrite ?node_20375.
  rewrite ?node_20386.
  rewrite ?node_20387.
  rewrite ?node_20398.
  rewrite ?node_20399.
  rewrite ?node_20413.
  rewrite ?node_20414.
  rewrite ?node_20425.
  rewrite ?node_20426.
  rewrite ?node_20437.
  rewrite ?node_20438.
  rewrite ?node_20452.
  rewrite ?node_20453.
  rewrite ?node_20464.
  rewrite ?node_20465.
  rewrite ?node_20476.
  rewrite ?node_20477.
  rewrite ?node_20491.
  rewrite ?node_20492.
  rewrite ?node_20503.
  rewrite ?node_20504.
  rewrite ?node_20515.
  rewrite ?node_20516.
  rewrite ?node_20530.
  rewrite ?node_20531.
  rewrite ?node_20542.
  rewrite ?node_20543.
  rewrite ?node_20554.
  rewrite ?node_20555.
  rewrite ?node_20569.
  rewrite ?node_20570.
  rewrite ?node_20581.
  rewrite ?node_20582.
  rewrite ?node_20593.
  rewrite ?node_20594.
  rewrite ?node_20608.
  rewrite ?node_20609.
  rewrite ?node_20620.
  rewrite ?node_20621.
  rewrite ?node_20632.
  rewrite ?node_20633.
  rewrite ?node_20647.
  rewrite ?node_20648.
  rewrite ?node_20659.
  rewrite ?node_20660.
  rewrite ?node_20671.
  rewrite ?node_20672.
  rewrite ?node_20686.
  rewrite ?node_20687.
  rewrite ?node_20698.
  rewrite ?node_20699.
  rewrite ?node_20710.
  rewrite ?node_20711.
  rewrite ?node_20725.
  rewrite ?node_20726.
  rewrite ?node_20737.
  rewrite ?node_20738.
  rewrite ?node_20749.
  rewrite ?node_20750.
  rewrite ?node_20758.
  rewrite ?node_20759.
  rewrite ?node_20773.
  rewrite ?node_20774.
  rewrite ?node_20785.
  rewrite ?node_20786.
  rewrite ?node_20797.
  rewrite ?node_20798.
  rewrite ?node_20812.
  rewrite ?node_20813.
  rewrite ?node_20824.
  rewrite ?node_20825.
  rewrite ?node_20836.
  rewrite ?node_20837.
  rewrite ?node_20851.
  rewrite ?node_20852.
  rewrite ?node_20863.
  rewrite ?node_20864.
  rewrite ?node_20875.
  rewrite ?node_20876.
  rewrite ?node_20890.
  rewrite ?node_20891.
  rewrite ?node_20902.
  rewrite ?node_20903.
  rewrite ?node_20914.
  rewrite ?node_20915.
  rewrite ?node_20929.
  rewrite ?node_20930.
  rewrite ?node_20941.
  rewrite ?node_20942.
  rewrite ?node_20953.
  rewrite ?node_20954.
  rewrite ?node_20962.
  rewrite ?node_20963.
  rewrite ?node_20977.
  rewrite ?node_20978.
  rewrite ?node_20989.
  rewrite ?node_20990.
  rewrite ?node_21001.
  rewrite ?node_21002.
  rewrite ?node_21016.
  rewrite ?node_21017.
  rewrite ?node_21028.
  rewrite ?node_21029.
  rewrite ?node_21040.
  rewrite ?node_21041.
  rewrite ?node_21055.
  rewrite ?node_21056.
  rewrite ?node_21067.
  rewrite ?node_21068.
  rewrite ?node_21079.
  rewrite ?node_21080.
  rewrite ?node_21094.
  rewrite ?node_21095.
  rewrite ?node_21106.
  rewrite ?node_21107.
  rewrite ?node_21118.
  rewrite ?node_21119.
  rewrite ?node_21133.
  rewrite ?node_21134.
  rewrite ?node_21145.
  rewrite ?node_21146.
  rewrite ?node_21157.
  rewrite ?node_21158.
  rewrite ?node_21169.
  rewrite ?node_21170.
  rewrite ?node_21184.
  rewrite ?node_21185.
  rewrite ?node_21196.
  rewrite ?node_21197.
  rewrite ?node_21208.
  rewrite ?node_21209.
  rewrite ?node_21223.
  rewrite ?node_21224.
  rewrite ?node_21235.
  rewrite ?node_21236.
  rewrite ?node_21247.
  rewrite ?node_21248.
  rewrite ?node_21262.
  rewrite ?node_21263.
  rewrite ?node_21274.
  rewrite ?node_21275.
  rewrite ?node_21286.
  rewrite ?node_21287.
  rewrite ?node_21301.
  rewrite ?node_21302.
  rewrite ?node_21313.
  rewrite ?node_21314.
  rewrite ?node_21325.
  rewrite ?node_21326.
  rewrite ?node_21340.
  rewrite ?node_21341.
  rewrite ?node_21352.
  rewrite ?node_21353.
  rewrite ?node_21364.
  rewrite ?node_21365.
  rewrite ?node_21376.
  rewrite ?node_21377.
  rewrite ?node_21391.
  rewrite ?node_21392.
  rewrite ?node_21403.
  rewrite ?node_21404.
  rewrite ?node_21415.
  rewrite ?node_21416.
  rewrite ?node_21430.
  rewrite ?node_21431.
  rewrite ?node_21442.
  rewrite ?node_21443.
  rewrite ?node_21454.
  rewrite ?node_21455.
  rewrite ?node_21469.
  rewrite ?node_21470.
  rewrite ?node_21481.
  rewrite ?node_21482.
  rewrite ?node_21493.
  rewrite ?node_21494.
  rewrite ?node_21508.
  rewrite ?node_21509.
  rewrite ?node_21520.
  rewrite ?node_21521.
  rewrite ?node_21532.
  rewrite ?node_21533.
  rewrite ?node_21547.
  rewrite ?node_21548.
  rewrite ?node_21559.
  rewrite ?node_21560.
  rewrite ?node_21571.
  rewrite ?node_21572.
  rewrite ?node_21585.
  rewrite ?node_21586.
  reflexivity.
Qed.

From Stdlib Require Import ZArith List Bool Zmod.Bits.
From BitsProofs Require Import ArrayRefinementNodes044.
Import ListNotations.
Open Scope Z_scope.
Local Opaque R.v43401 N.v43401 R.v43402 N.v43402 R.v43416 N.v43416 R.v43417 N.v43417 R.v43428 N.v43428 R.v43429 N.v43429 R.v43440 N.v43440 R.v43441 N.v43441 R.v43455 N.v43455 R.v43456 N.v43456 R.v43467 N.v43467 R.v43468 N.v43468 R.v43479 N.v43479 R.v43480 N.v43480 R.v43494 N.v43494 R.v43495 N.v43495 R.v43506 N.v43506 R.v43507 N.v43507 R.v43518 N.v43518 R.v43519 N.v43519 R.v43533 N.v43533 R.v43534 N.v43534 R.v43545 N.v43545 R.v43546 N.v43546 R.v43557 N.v43557 R.v43558 N.v43558 R.v43572 N.v43572 R.v43573 N.v43573 R.v43584 N.v43584 R.v43585 N.v43585 R.v43596 N.v43596 R.v43597 N.v43597 R.v43611 N.v43611 R.v43612 N.v43612 R.v43623 N.v43623 R.v43624 N.v43624 R.v43635 N.v43635 R.v43636 N.v43636 R.v43650 N.v43650 R.v43651 N.v43651 R.v43662 N.v43662 R.v43663 N.v43663 R.v43674 N.v43674 R.v43675 N.v43675 R.v43689 N.v43689 R.v43690 N.v43690 R.v43701 N.v43701 R.v43702 N.v43702 R.v43713 N.v43713 R.v43714 N.v43714 R.v43728 N.v43728 R.v43729 N.v43729 R.v43740 N.v43740 R.v43741 N.v43741 R.v43752 N.v43752 R.v43753 N.v43753 R.v43767 N.v43767 R.v43768 N.v43768 R.v43779 N.v43779 R.v43780 N.v43780 R.v43791 N.v43791 R.v43792 N.v43792 R.v43806 N.v43806 R.v43807 N.v43807 R.v43818 N.v43818 R.v43819 N.v43819 R.v43830 N.v43830 R.v43831 N.v43831 R.v43845 N.v43845 R.v43846 N.v43846 R.v43857 N.v43857 R.v43858 N.v43858 R.v43869 N.v43869 R.v43870 N.v43870 R.v43884 N.v43884 R.v43885 N.v43885 R.v43896 N.v43896 R.v43897 N.v43897 R.v43908 N.v43908 R.v43909 N.v43909 R.v43923 N.v43923 R.v43924 N.v43924 R.v43935 N.v43935 R.v43936 N.v43936 R.v43947 N.v43947 R.v43948 N.v43948 R.v43962 N.v43962 R.v43963 N.v43963 R.v43974 N.v43974 R.v43975 N.v43975 R.v43986 N.v43986 R.v43987 N.v43987 R.v44001 N.v44001 R.v44002 N.v44002 R.v44013 N.v44013 R.v44014 N.v44014 R.v44025 N.v44025 R.v44026 N.v44026 R.v44040 N.v44040 R.v44041 N.v44041 R.v44052 N.v44052 R.v44053 N.v44053 R.v44064 N.v44064 R.v44065 N.v44065 R.v44079 N.v44079 R.v44080 N.v44080 R.v44091 N.v44091 R.v44092 N.v44092 R.v44103 N.v44103 R.v44104 N.v44104 R.v44118 N.v44118 R.v44119 N.v44119 R.v44130 N.v44130 R.v44131 N.v44131 R.v44142 N.v44142 R.v44143 N.v44143 R.v44157 N.v44157 R.v44158 N.v44158 R.v44169 N.v44169 R.v44170 N.v44170 R.v44181 N.v44181 R.v44182 N.v44182 R.v44196 N.v44196 R.v44197 N.v44197 R.v44208 N.v44208 R.v44209 N.v44209 R.v44220 N.v44220 R.v44221 N.v44221 R.v44235 N.v44235 R.v44236 N.v44236 R.v44247 N.v44247 R.v44248 N.v44248 R.v44259 N.v44259 R.v44260 N.v44260 R.v44274 N.v44274 R.v44275 N.v44275 R.v44286 N.v44286 R.v44287 N.v44287 R.v44298 N.v44298 R.v44299 N.v44299 R.v44313 N.v44313 R.v44314 N.v44314 R.v44325 N.v44325 R.v44326 N.v44326 R.v44337 N.v44337 R.v44338 N.v44338 R.v44352 N.v44352 R.v44353 N.v44353 R.v44364 N.v44364 R.v44365 N.v44365 R.v44376 N.v44376 R.v44377 N.v44377 R.v44391 N.v44391 R.v44392 N.v44392 R.v44403 N.v44403 R.v44404 N.v44404 R.v44415 N.v44415 R.v44416 N.v44416 R.v44430 N.v44430 R.v44431 N.v44431 R.v44442 N.v44442 R.v44443 N.v44443 R.v44454 N.v44454 R.v44455 N.v44455 R.v44469 N.v44469 R.v44470 N.v44470 R.v44481 N.v44481 R.v44482 N.v44482 R.v44493 N.v44493 R.v44494 N.v44494 R.v44508 N.v44508 R.v44509 N.v44509 R.v44520 N.v44520 R.v44521 N.v44521 R.v44532 N.v44532 R.v44533 N.v44533 R.v44547 N.v44547 R.v44548 N.v44548 R.v44559 N.v44559 R.v44560 N.v44560 R.v44571 N.v44571 R.v44572 N.v44572 R.v44586 N.v44586 R.v44587 N.v44587 R.v44598 N.v44598 R.v44599 N.v44599 R.v44610 N.v44610 R.v44611 N.v44611 R.v44625 N.v44625 R.v44626 N.v44626 R.v44637 N.v44637 R.v44638 N.v44638 R.v44649 N.v44649 R.v44650 N.v44650 R.v44661 N.v44661 R.v44662 N.v44662 R.v44676 N.v44676 R.v44677 N.v44677 R.v44688 N.v44688 R.v44689 N.v44689.
Definition reference_checks_21 (s : N.State) (i : N.Inputs) : list bool := [
orb (negb (Z.eqb (R.v43402 (state s) (inputs i)) 1)) (Z.eqb (R.v43401 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v43417 (state s) (inputs i)) 1)) (Z.eqb (R.v43416 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v43429 (state s) (inputs i)) 1)) (Z.eqb (R.v43428 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v43441 (state s) (inputs i)) 1)) (Z.eqb (R.v43440 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v43456 (state s) (inputs i)) 1)) (Z.eqb (R.v43455 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v43468 (state s) (inputs i)) 1)) (Z.eqb (R.v43467 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v43480 (state s) (inputs i)) 1)) (Z.eqb (R.v43479 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v43495 (state s) (inputs i)) 1)) (Z.eqb (R.v43494 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v43507 (state s) (inputs i)) 1)) (Z.eqb (R.v43506 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v43519 (state s) (inputs i)) 1)) (Z.eqb (R.v43518 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v43534 (state s) (inputs i)) 1)) (Z.eqb (R.v43533 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v43546 (state s) (inputs i)) 1)) (Z.eqb (R.v43545 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v43558 (state s) (inputs i)) 1)) (Z.eqb (R.v43557 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v43573 (state s) (inputs i)) 1)) (Z.eqb (R.v43572 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v43585 (state s) (inputs i)) 1)) (Z.eqb (R.v43584 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v43597 (state s) (inputs i)) 1)) (Z.eqb (R.v43596 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v43612 (state s) (inputs i)) 1)) (Z.eqb (R.v43611 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v43624 (state s) (inputs i)) 1)) (Z.eqb (R.v43623 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v43636 (state s) (inputs i)) 1)) (Z.eqb (R.v43635 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v43651 (state s) (inputs i)) 1)) (Z.eqb (R.v43650 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v43663 (state s) (inputs i)) 1)) (Z.eqb (R.v43662 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v43675 (state s) (inputs i)) 1)) (Z.eqb (R.v43674 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v43690 (state s) (inputs i)) 1)) (Z.eqb (R.v43689 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v43702 (state s) (inputs i)) 1)) (Z.eqb (R.v43701 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v43714 (state s) (inputs i)) 1)) (Z.eqb (R.v43713 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v43729 (state s) (inputs i)) 1)) (Z.eqb (R.v43728 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v43741 (state s) (inputs i)) 1)) (Z.eqb (R.v43740 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v43753 (state s) (inputs i)) 1)) (Z.eqb (R.v43752 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v43768 (state s) (inputs i)) 1)) (Z.eqb (R.v43767 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v43780 (state s) (inputs i)) 1)) (Z.eqb (R.v43779 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v43792 (state s) (inputs i)) 1)) (Z.eqb (R.v43791 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v43807 (state s) (inputs i)) 1)) (Z.eqb (R.v43806 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v43819 (state s) (inputs i)) 1)) (Z.eqb (R.v43818 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v43831 (state s) (inputs i)) 1)) (Z.eqb (R.v43830 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v43846 (state s) (inputs i)) 1)) (Z.eqb (R.v43845 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v43858 (state s) (inputs i)) 1)) (Z.eqb (R.v43857 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v43870 (state s) (inputs i)) 1)) (Z.eqb (R.v43869 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v43885 (state s) (inputs i)) 1)) (Z.eqb (R.v43884 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v43897 (state s) (inputs i)) 1)) (Z.eqb (R.v43896 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v43909 (state s) (inputs i)) 1)) (Z.eqb (R.v43908 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v43924 (state s) (inputs i)) 1)) (Z.eqb (R.v43923 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v43936 (state s) (inputs i)) 1)) (Z.eqb (R.v43935 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v43948 (state s) (inputs i)) 1)) (Z.eqb (R.v43947 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v43963 (state s) (inputs i)) 1)) (Z.eqb (R.v43962 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v43975 (state s) (inputs i)) 1)) (Z.eqb (R.v43974 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v43987 (state s) (inputs i)) 1)) (Z.eqb (R.v43986 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44002 (state s) (inputs i)) 1)) (Z.eqb (R.v44001 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44014 (state s) (inputs i)) 1)) (Z.eqb (R.v44013 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44026 (state s) (inputs i)) 1)) (Z.eqb (R.v44025 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44041 (state s) (inputs i)) 1)) (Z.eqb (R.v44040 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44053 (state s) (inputs i)) 1)) (Z.eqb (R.v44052 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44065 (state s) (inputs i)) 1)) (Z.eqb (R.v44064 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44080 (state s) (inputs i)) 1)) (Z.eqb (R.v44079 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44092 (state s) (inputs i)) 1)) (Z.eqb (R.v44091 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44104 (state s) (inputs i)) 1)) (Z.eqb (R.v44103 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44119 (state s) (inputs i)) 1)) (Z.eqb (R.v44118 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44131 (state s) (inputs i)) 1)) (Z.eqb (R.v44130 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44143 (state s) (inputs i)) 1)) (Z.eqb (R.v44142 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44158 (state s) (inputs i)) 1)) (Z.eqb (R.v44157 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44170 (state s) (inputs i)) 1)) (Z.eqb (R.v44169 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44182 (state s) (inputs i)) 1)) (Z.eqb (R.v44181 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44197 (state s) (inputs i)) 1)) (Z.eqb (R.v44196 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44209 (state s) (inputs i)) 1)) (Z.eqb (R.v44208 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44221 (state s) (inputs i)) 1)) (Z.eqb (R.v44220 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44236 (state s) (inputs i)) 1)) (Z.eqb (R.v44235 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44248 (state s) (inputs i)) 1)) (Z.eqb (R.v44247 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44260 (state s) (inputs i)) 1)) (Z.eqb (R.v44259 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44275 (state s) (inputs i)) 1)) (Z.eqb (R.v44274 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44287 (state s) (inputs i)) 1)) (Z.eqb (R.v44286 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44299 (state s) (inputs i)) 1)) (Z.eqb (R.v44298 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44314 (state s) (inputs i)) 1)) (Z.eqb (R.v44313 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44326 (state s) (inputs i)) 1)) (Z.eqb (R.v44325 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44338 (state s) (inputs i)) 1)) (Z.eqb (R.v44337 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44353 (state s) (inputs i)) 1)) (Z.eqb (R.v44352 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44365 (state s) (inputs i)) 1)) (Z.eqb (R.v44364 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44377 (state s) (inputs i)) 1)) (Z.eqb (R.v44376 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44392 (state s) (inputs i)) 1)) (Z.eqb (R.v44391 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44404 (state s) (inputs i)) 1)) (Z.eqb (R.v44403 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44416 (state s) (inputs i)) 1)) (Z.eqb (R.v44415 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44431 (state s) (inputs i)) 1)) (Z.eqb (R.v44430 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44443 (state s) (inputs i)) 1)) (Z.eqb (R.v44442 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44455 (state s) (inputs i)) 1)) (Z.eqb (R.v44454 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44470 (state s) (inputs i)) 1)) (Z.eqb (R.v44469 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44482 (state s) (inputs i)) 1)) (Z.eqb (R.v44481 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44494 (state s) (inputs i)) 1)) (Z.eqb (R.v44493 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44509 (state s) (inputs i)) 1)) (Z.eqb (R.v44508 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44521 (state s) (inputs i)) 1)) (Z.eqb (R.v44520 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44533 (state s) (inputs i)) 1)) (Z.eqb (R.v44532 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44548 (state s) (inputs i)) 1)) (Z.eqb (R.v44547 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44560 (state s) (inputs i)) 1)) (Z.eqb (R.v44559 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44572 (state s) (inputs i)) 1)) (Z.eqb (R.v44571 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44587 (state s) (inputs i)) 1)) (Z.eqb (R.v44586 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44599 (state s) (inputs i)) 1)) (Z.eqb (R.v44598 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44611 (state s) (inputs i)) 1)) (Z.eqb (R.v44610 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44626 (state s) (inputs i)) 1)) (Z.eqb (R.v44625 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44638 (state s) (inputs i)) 1)) (Z.eqb (R.v44637 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44650 (state s) (inputs i)) 1)) (Z.eqb (R.v44649 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44662 (state s) (inputs i)) 1)) (Z.eqb (R.v44661 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44677 (state s) (inputs i)) 1)) (Z.eqb (R.v44676 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v44689 (state s) (inputs i)) 1)) (Z.eqb (R.v44688 (state s) (inputs i)) 1)
].
Definition native_checks_21 (s : N.State) (i : N.Inputs) : list bool := [
orb (negb (Zmod.eqb (N.v43402 s i) Zmod.one)) (Zmod.eqb (N.v43401 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v43417 s i) Zmod.one)) (Zmod.eqb (N.v43416 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v43429 s i) Zmod.one)) (Zmod.eqb (N.v43428 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v43441 s i) Zmod.one)) (Zmod.eqb (N.v43440 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v43456 s i) Zmod.one)) (Zmod.eqb (N.v43455 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v43468 s i) Zmod.one)) (Zmod.eqb (N.v43467 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v43480 s i) Zmod.one)) (Zmod.eqb (N.v43479 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v43495 s i) Zmod.one)) (Zmod.eqb (N.v43494 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v43507 s i) Zmod.one)) (Zmod.eqb (N.v43506 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v43519 s i) Zmod.one)) (Zmod.eqb (N.v43518 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v43534 s i) Zmod.one)) (Zmod.eqb (N.v43533 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v43546 s i) Zmod.one)) (Zmod.eqb (N.v43545 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v43558 s i) Zmod.one)) (Zmod.eqb (N.v43557 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v43573 s i) Zmod.one)) (Zmod.eqb (N.v43572 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v43585 s i) Zmod.one)) (Zmod.eqb (N.v43584 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v43597 s i) Zmod.one)) (Zmod.eqb (N.v43596 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v43612 s i) Zmod.one)) (Zmod.eqb (N.v43611 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v43624 s i) Zmod.one)) (Zmod.eqb (N.v43623 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v43636 s i) Zmod.one)) (Zmod.eqb (N.v43635 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v43651 s i) Zmod.one)) (Zmod.eqb (N.v43650 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v43663 s i) Zmod.one)) (Zmod.eqb (N.v43662 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v43675 s i) Zmod.one)) (Zmod.eqb (N.v43674 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v43690 s i) Zmod.one)) (Zmod.eqb (N.v43689 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v43702 s i) Zmod.one)) (Zmod.eqb (N.v43701 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v43714 s i) Zmod.one)) (Zmod.eqb (N.v43713 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v43729 s i) Zmod.one)) (Zmod.eqb (N.v43728 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v43741 s i) Zmod.one)) (Zmod.eqb (N.v43740 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v43753 s i) Zmod.one)) (Zmod.eqb (N.v43752 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v43768 s i) Zmod.one)) (Zmod.eqb (N.v43767 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v43780 s i) Zmod.one)) (Zmod.eqb (N.v43779 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v43792 s i) Zmod.one)) (Zmod.eqb (N.v43791 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v43807 s i) Zmod.one)) (Zmod.eqb (N.v43806 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v43819 s i) Zmod.one)) (Zmod.eqb (N.v43818 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v43831 s i) Zmod.one)) (Zmod.eqb (N.v43830 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v43846 s i) Zmod.one)) (Zmod.eqb (N.v43845 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v43858 s i) Zmod.one)) (Zmod.eqb (N.v43857 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v43870 s i) Zmod.one)) (Zmod.eqb (N.v43869 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v43885 s i) Zmod.one)) (Zmod.eqb (N.v43884 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v43897 s i) Zmod.one)) (Zmod.eqb (N.v43896 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v43909 s i) Zmod.one)) (Zmod.eqb (N.v43908 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v43924 s i) Zmod.one)) (Zmod.eqb (N.v43923 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v43936 s i) Zmod.one)) (Zmod.eqb (N.v43935 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v43948 s i) Zmod.one)) (Zmod.eqb (N.v43947 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v43963 s i) Zmod.one)) (Zmod.eqb (N.v43962 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v43975 s i) Zmod.one)) (Zmod.eqb (N.v43974 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v43987 s i) Zmod.one)) (Zmod.eqb (N.v43986 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44002 s i) Zmod.one)) (Zmod.eqb (N.v44001 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44014 s i) Zmod.one)) (Zmod.eqb (N.v44013 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44026 s i) Zmod.one)) (Zmod.eqb (N.v44025 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44041 s i) Zmod.one)) (Zmod.eqb (N.v44040 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44053 s i) Zmod.one)) (Zmod.eqb (N.v44052 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44065 s i) Zmod.one)) (Zmod.eqb (N.v44064 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44080 s i) Zmod.one)) (Zmod.eqb (N.v44079 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44092 s i) Zmod.one)) (Zmod.eqb (N.v44091 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44104 s i) Zmod.one)) (Zmod.eqb (N.v44103 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44119 s i) Zmod.one)) (Zmod.eqb (N.v44118 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44131 s i) Zmod.one)) (Zmod.eqb (N.v44130 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44143 s i) Zmod.one)) (Zmod.eqb (N.v44142 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44158 s i) Zmod.one)) (Zmod.eqb (N.v44157 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44170 s i) Zmod.one)) (Zmod.eqb (N.v44169 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44182 s i) Zmod.one)) (Zmod.eqb (N.v44181 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44197 s i) Zmod.one)) (Zmod.eqb (N.v44196 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44209 s i) Zmod.one)) (Zmod.eqb (N.v44208 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44221 s i) Zmod.one)) (Zmod.eqb (N.v44220 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44236 s i) Zmod.one)) (Zmod.eqb (N.v44235 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44248 s i) Zmod.one)) (Zmod.eqb (N.v44247 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44260 s i) Zmod.one)) (Zmod.eqb (N.v44259 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44275 s i) Zmod.one)) (Zmod.eqb (N.v44274 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44287 s i) Zmod.one)) (Zmod.eqb (N.v44286 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44299 s i) Zmod.one)) (Zmod.eqb (N.v44298 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44314 s i) Zmod.one)) (Zmod.eqb (N.v44313 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44326 s i) Zmod.one)) (Zmod.eqb (N.v44325 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44338 s i) Zmod.one)) (Zmod.eqb (N.v44337 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44353 s i) Zmod.one)) (Zmod.eqb (N.v44352 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44365 s i) Zmod.one)) (Zmod.eqb (N.v44364 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44377 s i) Zmod.one)) (Zmod.eqb (N.v44376 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44392 s i) Zmod.one)) (Zmod.eqb (N.v44391 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44404 s i) Zmod.one)) (Zmod.eqb (N.v44403 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44416 s i) Zmod.one)) (Zmod.eqb (N.v44415 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44431 s i) Zmod.one)) (Zmod.eqb (N.v44430 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44443 s i) Zmod.one)) (Zmod.eqb (N.v44442 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44455 s i) Zmod.one)) (Zmod.eqb (N.v44454 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44470 s i) Zmod.one)) (Zmod.eqb (N.v44469 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44482 s i) Zmod.one)) (Zmod.eqb (N.v44481 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44494 s i) Zmod.one)) (Zmod.eqb (N.v44493 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44509 s i) Zmod.one)) (Zmod.eqb (N.v44508 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44521 s i) Zmod.one)) (Zmod.eqb (N.v44520 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44533 s i) Zmod.one)) (Zmod.eqb (N.v44532 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44548 s i) Zmod.one)) (Zmod.eqb (N.v44547 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44560 s i) Zmod.one)) (Zmod.eqb (N.v44559 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44572 s i) Zmod.one)) (Zmod.eqb (N.v44571 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44587 s i) Zmod.one)) (Zmod.eqb (N.v44586 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44599 s i) Zmod.one)) (Zmod.eqb (N.v44598 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44611 s i) Zmod.one)) (Zmod.eqb (N.v44610 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44626 s i) Zmod.one)) (Zmod.eqb (N.v44625 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44638 s i) Zmod.one)) (Zmod.eqb (N.v44637 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44650 s i) Zmod.one)) (Zmod.eqb (N.v44649 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44662 s i) Zmod.one)) (Zmod.eqb (N.v44661 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44677 s i) Zmod.one)) (Zmod.eqb (N.v44676 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v44689 s i) Zmod.one)) (Zmod.eqb (N.v44688 s i) Zmod.one)
].
Lemma checks_21 s i : reference_checks_21 s i = native_checks_21 s i.
Proof. unfold reference_checks_21, native_checks_21.
  rewrite ?node_43401.
  rewrite ?node_43402.
  rewrite ?node_43416.
  rewrite ?node_43417.
  rewrite ?node_43428.
  rewrite ?node_43429.
  rewrite ?node_43440.
  rewrite ?node_43441.
  rewrite ?node_43455.
  rewrite ?node_43456.
  rewrite ?node_43467.
  rewrite ?node_43468.
  rewrite ?node_43479.
  rewrite ?node_43480.
  rewrite ?node_43494.
  rewrite ?node_43495.
  rewrite ?node_43506.
  rewrite ?node_43507.
  rewrite ?node_43518.
  rewrite ?node_43519.
  rewrite ?node_43533.
  rewrite ?node_43534.
  rewrite ?node_43545.
  rewrite ?node_43546.
  rewrite ?node_43557.
  rewrite ?node_43558.
  rewrite ?node_43572.
  rewrite ?node_43573.
  rewrite ?node_43584.
  rewrite ?node_43585.
  rewrite ?node_43596.
  rewrite ?node_43597.
  rewrite ?node_43611.
  rewrite ?node_43612.
  rewrite ?node_43623.
  rewrite ?node_43624.
  rewrite ?node_43635.
  rewrite ?node_43636.
  rewrite ?node_43650.
  rewrite ?node_43651.
  rewrite ?node_43662.
  rewrite ?node_43663.
  rewrite ?node_43674.
  rewrite ?node_43675.
  rewrite ?node_43689.
  rewrite ?node_43690.
  rewrite ?node_43701.
  rewrite ?node_43702.
  rewrite ?node_43713.
  rewrite ?node_43714.
  rewrite ?node_43728.
  rewrite ?node_43729.
  rewrite ?node_43740.
  rewrite ?node_43741.
  rewrite ?node_43752.
  rewrite ?node_43753.
  rewrite ?node_43767.
  rewrite ?node_43768.
  rewrite ?node_43779.
  rewrite ?node_43780.
  rewrite ?node_43791.
  rewrite ?node_43792.
  rewrite ?node_43806.
  rewrite ?node_43807.
  rewrite ?node_43818.
  rewrite ?node_43819.
  rewrite ?node_43830.
  rewrite ?node_43831.
  rewrite ?node_43845.
  rewrite ?node_43846.
  rewrite ?node_43857.
  rewrite ?node_43858.
  rewrite ?node_43869.
  rewrite ?node_43870.
  rewrite ?node_43884.
  rewrite ?node_43885.
  rewrite ?node_43896.
  rewrite ?node_43897.
  rewrite ?node_43908.
  rewrite ?node_43909.
  rewrite ?node_43923.
  rewrite ?node_43924.
  rewrite ?node_43935.
  rewrite ?node_43936.
  rewrite ?node_43947.
  rewrite ?node_43948.
  rewrite ?node_43962.
  rewrite ?node_43963.
  rewrite ?node_43974.
  rewrite ?node_43975.
  rewrite ?node_43986.
  rewrite ?node_43987.
  rewrite ?node_44001.
  rewrite ?node_44002.
  rewrite ?node_44013.
  rewrite ?node_44014.
  rewrite ?node_44025.
  rewrite ?node_44026.
  rewrite ?node_44040.
  rewrite ?node_44041.
  rewrite ?node_44052.
  rewrite ?node_44053.
  rewrite ?node_44064.
  rewrite ?node_44065.
  rewrite ?node_44079.
  rewrite ?node_44080.
  rewrite ?node_44091.
  rewrite ?node_44092.
  rewrite ?node_44103.
  rewrite ?node_44104.
  rewrite ?node_44118.
  rewrite ?node_44119.
  rewrite ?node_44130.
  rewrite ?node_44131.
  rewrite ?node_44142.
  rewrite ?node_44143.
  rewrite ?node_44157.
  rewrite ?node_44158.
  rewrite ?node_44169.
  rewrite ?node_44170.
  rewrite ?node_44181.
  rewrite ?node_44182.
  rewrite ?node_44196.
  rewrite ?node_44197.
  rewrite ?node_44208.
  rewrite ?node_44209.
  rewrite ?node_44220.
  rewrite ?node_44221.
  rewrite ?node_44235.
  rewrite ?node_44236.
  rewrite ?node_44247.
  rewrite ?node_44248.
  rewrite ?node_44259.
  rewrite ?node_44260.
  rewrite ?node_44274.
  rewrite ?node_44275.
  rewrite ?node_44286.
  rewrite ?node_44287.
  rewrite ?node_44298.
  rewrite ?node_44299.
  rewrite ?node_44313.
  rewrite ?node_44314.
  rewrite ?node_44325.
  rewrite ?node_44326.
  rewrite ?node_44337.
  rewrite ?node_44338.
  rewrite ?node_44352.
  rewrite ?node_44353.
  rewrite ?node_44364.
  rewrite ?node_44365.
  rewrite ?node_44376.
  rewrite ?node_44377.
  rewrite ?node_44391.
  rewrite ?node_44392.
  rewrite ?node_44403.
  rewrite ?node_44404.
  rewrite ?node_44415.
  rewrite ?node_44416.
  rewrite ?node_44430.
  rewrite ?node_44431.
  rewrite ?node_44442.
  rewrite ?node_44443.
  rewrite ?node_44454.
  rewrite ?node_44455.
  rewrite ?node_44469.
  rewrite ?node_44470.
  rewrite ?node_44481.
  rewrite ?node_44482.
  rewrite ?node_44493.
  rewrite ?node_44494.
  rewrite ?node_44508.
  rewrite ?node_44509.
  rewrite ?node_44520.
  rewrite ?node_44521.
  rewrite ?node_44532.
  rewrite ?node_44533.
  rewrite ?node_44547.
  rewrite ?node_44548.
  rewrite ?node_44559.
  rewrite ?node_44560.
  rewrite ?node_44571.
  rewrite ?node_44572.
  rewrite ?node_44586.
  rewrite ?node_44587.
  rewrite ?node_44598.
  rewrite ?node_44599.
  rewrite ?node_44610.
  rewrite ?node_44611.
  rewrite ?node_44625.
  rewrite ?node_44626.
  rewrite ?node_44637.
  rewrite ?node_44638.
  rewrite ?node_44649.
  rewrite ?node_44650.
  rewrite ?node_44661.
  rewrite ?node_44662.
  rewrite ?node_44676.
  rewrite ?node_44677.
  rewrite ?node_44688.
  rewrite ?node_44689.
  reflexivity.
Qed.

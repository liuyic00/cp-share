From Stdlib Require Import ZArith List Bool Zmod.Bits.
From BitsProofs Require Import ArrayRefinementNodes052.
Import ListNotations.
Open Scope Z_scope.
Local Opaque R.v50990 N.v50990 R.v50991 N.v50991 R.v51005 N.v51005 R.v51006 N.v51006 R.v51017 N.v51017 R.v51018 N.v51018 R.v51029 N.v51029 R.v51030 N.v51030 R.v51044 N.v51044 R.v51045 N.v51045 R.v51056 N.v51056 R.v51057 N.v51057 R.v51068 N.v51068 R.v51069 N.v51069 R.v51083 N.v51083 R.v51084 N.v51084 R.v51095 N.v51095 R.v51096 N.v51096 R.v51107 N.v51107 R.v51108 N.v51108 R.v51122 N.v51122 R.v51123 N.v51123 R.v51134 N.v51134 R.v51135 N.v51135 R.v51146 N.v51146 R.v51147 N.v51147 R.v51161 N.v51161 R.v51162 N.v51162 R.v51173 N.v51173 R.v51174 N.v51174 R.v51185 N.v51185 R.v51186 N.v51186 R.v51200 N.v51200 R.v51201 N.v51201 R.v51212 N.v51212 R.v51213 N.v51213 R.v51224 N.v51224 R.v51225 N.v51225 R.v51239 N.v51239 R.v51240 N.v51240 R.v51251 N.v51251 R.v51252 N.v51252 R.v51263 N.v51263 R.v51264 N.v51264 R.v51278 N.v51278 R.v51279 N.v51279 R.v51290 N.v51290 R.v51291 N.v51291 R.v51302 N.v51302 R.v51303 N.v51303 R.v51317 N.v51317 R.v51318 N.v51318 R.v51329 N.v51329 R.v51330 N.v51330 R.v51341 N.v51341 R.v51342 N.v51342 R.v51356 N.v51356 R.v51357 N.v51357 R.v51368 N.v51368 R.v51369 N.v51369 R.v51380 N.v51380 R.v51381 N.v51381 R.v51395 N.v51395 R.v51396 N.v51396 R.v51407 N.v51407 R.v51408 N.v51408 R.v51419 N.v51419 R.v51420 N.v51420 R.v51434 N.v51434 R.v51435 N.v51435 R.v51446 N.v51446 R.v51447 N.v51447 R.v51458 N.v51458 R.v51459 N.v51459 R.v51467 N.v51467 R.v51468 N.v51468 R.v51482 N.v51482 R.v51483 N.v51483 R.v51494 N.v51494 R.v51495 N.v51495 R.v51506 N.v51506 R.v51507 N.v51507 R.v51521 N.v51521 R.v51522 N.v51522 R.v51533 N.v51533 R.v51534 N.v51534 R.v51545 N.v51545 R.v51546 N.v51546 R.v51554 N.v51554 R.v51555 N.v51555 R.v51569 N.v51569 R.v51570 N.v51570 R.v51581 N.v51581 R.v51582 N.v51582 R.v51593 N.v51593 R.v51594 N.v51594 R.v51608 N.v51608 R.v51609 N.v51609 R.v51620 N.v51620 R.v51621 N.v51621 R.v51632 N.v51632 R.v51633 N.v51633 R.v51647 N.v51647 R.v51648 N.v51648 R.v51659 N.v51659 R.v51660 N.v51660 R.v51671 N.v51671 R.v51672 N.v51672 R.v51686 N.v51686 R.v51687 N.v51687 R.v51698 N.v51698 R.v51699 N.v51699 R.v51710 N.v51710 R.v51711 N.v51711 R.v51725 N.v51725 R.v51726 N.v51726 R.v51737 N.v51737 R.v51738 N.v51738 R.v51749 N.v51749 R.v51750 N.v51750 R.v51764 N.v51764 R.v51765 N.v51765 R.v51776 N.v51776 R.v51777 N.v51777 R.v51788 N.v51788 R.v51789 N.v51789 R.v51803 N.v51803 R.v51804 N.v51804 R.v51815 N.v51815 R.v51816 N.v51816 R.v51827 N.v51827 R.v51828 N.v51828 R.v51842 N.v51842 R.v51843 N.v51843 R.v51854 N.v51854 R.v51855 N.v51855 R.v51866 N.v51866 R.v51867 N.v51867 R.v51881 N.v51881 R.v51882 N.v51882 R.v51893 N.v51893 R.v51894 N.v51894 R.v51905 N.v51905 R.v51906 N.v51906 R.v51920 N.v51920 R.v51921 N.v51921 R.v51932 N.v51932 R.v51933 N.v51933 R.v51944 N.v51944 R.v51945 N.v51945 R.v51959 N.v51959 R.v51960 N.v51960 R.v51971 N.v51971 R.v51972 N.v51972 R.v51983 N.v51983 R.v51984 N.v51984 R.v51998 N.v51998 R.v51999 N.v51999 R.v52010 N.v52010 R.v52011 N.v52011 R.v52022 N.v52022 R.v52023 N.v52023 R.v52037 N.v52037 R.v52038 N.v52038 R.v52049 N.v52049 R.v52050 N.v52050 R.v52061 N.v52061 R.v52062 N.v52062 R.v52076 N.v52076 R.v52077 N.v52077 R.v52088 N.v52088 R.v52089 N.v52089 R.v52100 N.v52100 R.v52101 N.v52101 R.v52115 N.v52115 R.v52116 N.v52116 R.v52127 N.v52127 R.v52128 N.v52128 R.v52139 N.v52139 R.v52140 N.v52140 R.v52154 N.v52154 R.v52155 N.v52155 R.v52166 N.v52166 R.v52167 N.v52167 R.v52178 N.v52178 R.v52179 N.v52179 R.v52193 N.v52193 R.v52194 N.v52194 R.v52205 N.v52205 R.v52206 N.v52206 R.v52217 N.v52217 R.v52218 N.v52218 R.v52232 N.v52232 R.v52233 N.v52233 R.v52244 N.v52244 R.v52245 N.v52245 R.v52256 N.v52256 R.v52257 N.v52257 R.v52271 N.v52271 R.v52272 N.v52272.
Definition reference_checks_27 (s : N.State) (i : N.Inputs) : list bool := [
orb (negb (Z.eqb (R.v50991 (state s) (inputs i)) 1)) (Z.eqb (R.v50990 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51006 (state s) (inputs i)) 1)) (Z.eqb (R.v51005 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51018 (state s) (inputs i)) 1)) (Z.eqb (R.v51017 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51030 (state s) (inputs i)) 1)) (Z.eqb (R.v51029 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51045 (state s) (inputs i)) 1)) (Z.eqb (R.v51044 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51057 (state s) (inputs i)) 1)) (Z.eqb (R.v51056 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51069 (state s) (inputs i)) 1)) (Z.eqb (R.v51068 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51084 (state s) (inputs i)) 1)) (Z.eqb (R.v51083 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51096 (state s) (inputs i)) 1)) (Z.eqb (R.v51095 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51108 (state s) (inputs i)) 1)) (Z.eqb (R.v51107 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51123 (state s) (inputs i)) 1)) (Z.eqb (R.v51122 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51135 (state s) (inputs i)) 1)) (Z.eqb (R.v51134 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51147 (state s) (inputs i)) 1)) (Z.eqb (R.v51146 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51162 (state s) (inputs i)) 1)) (Z.eqb (R.v51161 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51174 (state s) (inputs i)) 1)) (Z.eqb (R.v51173 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51186 (state s) (inputs i)) 1)) (Z.eqb (R.v51185 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51201 (state s) (inputs i)) 1)) (Z.eqb (R.v51200 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51213 (state s) (inputs i)) 1)) (Z.eqb (R.v51212 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51225 (state s) (inputs i)) 1)) (Z.eqb (R.v51224 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51240 (state s) (inputs i)) 1)) (Z.eqb (R.v51239 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51252 (state s) (inputs i)) 1)) (Z.eqb (R.v51251 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51264 (state s) (inputs i)) 1)) (Z.eqb (R.v51263 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51279 (state s) (inputs i)) 1)) (Z.eqb (R.v51278 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51291 (state s) (inputs i)) 1)) (Z.eqb (R.v51290 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51303 (state s) (inputs i)) 1)) (Z.eqb (R.v51302 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51318 (state s) (inputs i)) 1)) (Z.eqb (R.v51317 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51330 (state s) (inputs i)) 1)) (Z.eqb (R.v51329 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51342 (state s) (inputs i)) 1)) (Z.eqb (R.v51341 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51357 (state s) (inputs i)) 1)) (Z.eqb (R.v51356 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51369 (state s) (inputs i)) 1)) (Z.eqb (R.v51368 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51381 (state s) (inputs i)) 1)) (Z.eqb (R.v51380 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51396 (state s) (inputs i)) 1)) (Z.eqb (R.v51395 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51408 (state s) (inputs i)) 1)) (Z.eqb (R.v51407 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51420 (state s) (inputs i)) 1)) (Z.eqb (R.v51419 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51435 (state s) (inputs i)) 1)) (Z.eqb (R.v51434 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51447 (state s) (inputs i)) 1)) (Z.eqb (R.v51446 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51459 (state s) (inputs i)) 1)) (Z.eqb (R.v51458 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51468 (state s) (inputs i)) 1)) (Z.eqb (R.v51467 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51483 (state s) (inputs i)) 1)) (Z.eqb (R.v51482 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51495 (state s) (inputs i)) 1)) (Z.eqb (R.v51494 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51507 (state s) (inputs i)) 1)) (Z.eqb (R.v51506 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51522 (state s) (inputs i)) 1)) (Z.eqb (R.v51521 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51534 (state s) (inputs i)) 1)) (Z.eqb (R.v51533 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51546 (state s) (inputs i)) 1)) (Z.eqb (R.v51545 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51555 (state s) (inputs i)) 1)) (Z.eqb (R.v51554 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51570 (state s) (inputs i)) 1)) (Z.eqb (R.v51569 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51582 (state s) (inputs i)) 1)) (Z.eqb (R.v51581 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51594 (state s) (inputs i)) 1)) (Z.eqb (R.v51593 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51609 (state s) (inputs i)) 1)) (Z.eqb (R.v51608 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51621 (state s) (inputs i)) 1)) (Z.eqb (R.v51620 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51633 (state s) (inputs i)) 1)) (Z.eqb (R.v51632 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51648 (state s) (inputs i)) 1)) (Z.eqb (R.v51647 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51660 (state s) (inputs i)) 1)) (Z.eqb (R.v51659 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51672 (state s) (inputs i)) 1)) (Z.eqb (R.v51671 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51687 (state s) (inputs i)) 1)) (Z.eqb (R.v51686 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51699 (state s) (inputs i)) 1)) (Z.eqb (R.v51698 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51711 (state s) (inputs i)) 1)) (Z.eqb (R.v51710 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51726 (state s) (inputs i)) 1)) (Z.eqb (R.v51725 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51738 (state s) (inputs i)) 1)) (Z.eqb (R.v51737 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51750 (state s) (inputs i)) 1)) (Z.eqb (R.v51749 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51765 (state s) (inputs i)) 1)) (Z.eqb (R.v51764 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51777 (state s) (inputs i)) 1)) (Z.eqb (R.v51776 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51789 (state s) (inputs i)) 1)) (Z.eqb (R.v51788 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51804 (state s) (inputs i)) 1)) (Z.eqb (R.v51803 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51816 (state s) (inputs i)) 1)) (Z.eqb (R.v51815 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51828 (state s) (inputs i)) 1)) (Z.eqb (R.v51827 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51843 (state s) (inputs i)) 1)) (Z.eqb (R.v51842 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51855 (state s) (inputs i)) 1)) (Z.eqb (R.v51854 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51867 (state s) (inputs i)) 1)) (Z.eqb (R.v51866 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51882 (state s) (inputs i)) 1)) (Z.eqb (R.v51881 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51894 (state s) (inputs i)) 1)) (Z.eqb (R.v51893 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51906 (state s) (inputs i)) 1)) (Z.eqb (R.v51905 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51921 (state s) (inputs i)) 1)) (Z.eqb (R.v51920 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51933 (state s) (inputs i)) 1)) (Z.eqb (R.v51932 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51945 (state s) (inputs i)) 1)) (Z.eqb (R.v51944 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51960 (state s) (inputs i)) 1)) (Z.eqb (R.v51959 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51972 (state s) (inputs i)) 1)) (Z.eqb (R.v51971 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51984 (state s) (inputs i)) 1)) (Z.eqb (R.v51983 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v51999 (state s) (inputs i)) 1)) (Z.eqb (R.v51998 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52011 (state s) (inputs i)) 1)) (Z.eqb (R.v52010 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52023 (state s) (inputs i)) 1)) (Z.eqb (R.v52022 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52038 (state s) (inputs i)) 1)) (Z.eqb (R.v52037 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52050 (state s) (inputs i)) 1)) (Z.eqb (R.v52049 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52062 (state s) (inputs i)) 1)) (Z.eqb (R.v52061 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52077 (state s) (inputs i)) 1)) (Z.eqb (R.v52076 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52089 (state s) (inputs i)) 1)) (Z.eqb (R.v52088 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52101 (state s) (inputs i)) 1)) (Z.eqb (R.v52100 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52116 (state s) (inputs i)) 1)) (Z.eqb (R.v52115 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52128 (state s) (inputs i)) 1)) (Z.eqb (R.v52127 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52140 (state s) (inputs i)) 1)) (Z.eqb (R.v52139 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52155 (state s) (inputs i)) 1)) (Z.eqb (R.v52154 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52167 (state s) (inputs i)) 1)) (Z.eqb (R.v52166 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52179 (state s) (inputs i)) 1)) (Z.eqb (R.v52178 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52194 (state s) (inputs i)) 1)) (Z.eqb (R.v52193 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52206 (state s) (inputs i)) 1)) (Z.eqb (R.v52205 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52218 (state s) (inputs i)) 1)) (Z.eqb (R.v52217 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52233 (state s) (inputs i)) 1)) (Z.eqb (R.v52232 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52245 (state s) (inputs i)) 1)) (Z.eqb (R.v52244 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52257 (state s) (inputs i)) 1)) (Z.eqb (R.v52256 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v52272 (state s) (inputs i)) 1)) (Z.eqb (R.v52271 (state s) (inputs i)) 1)
].
Definition native_checks_27 (s : N.State) (i : N.Inputs) : list bool := [
orb (negb (Zmod.eqb (N.v50991 s i) Zmod.one)) (Zmod.eqb (N.v50990 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51006 s i) Zmod.one)) (Zmod.eqb (N.v51005 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51018 s i) Zmod.one)) (Zmod.eqb (N.v51017 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51030 s i) Zmod.one)) (Zmod.eqb (N.v51029 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51045 s i) Zmod.one)) (Zmod.eqb (N.v51044 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51057 s i) Zmod.one)) (Zmod.eqb (N.v51056 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51069 s i) Zmod.one)) (Zmod.eqb (N.v51068 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51084 s i) Zmod.one)) (Zmod.eqb (N.v51083 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51096 s i) Zmod.one)) (Zmod.eqb (N.v51095 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51108 s i) Zmod.one)) (Zmod.eqb (N.v51107 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51123 s i) Zmod.one)) (Zmod.eqb (N.v51122 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51135 s i) Zmod.one)) (Zmod.eqb (N.v51134 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51147 s i) Zmod.one)) (Zmod.eqb (N.v51146 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51162 s i) Zmod.one)) (Zmod.eqb (N.v51161 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51174 s i) Zmod.one)) (Zmod.eqb (N.v51173 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51186 s i) Zmod.one)) (Zmod.eqb (N.v51185 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51201 s i) Zmod.one)) (Zmod.eqb (N.v51200 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51213 s i) Zmod.one)) (Zmod.eqb (N.v51212 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51225 s i) Zmod.one)) (Zmod.eqb (N.v51224 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51240 s i) Zmod.one)) (Zmod.eqb (N.v51239 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51252 s i) Zmod.one)) (Zmod.eqb (N.v51251 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51264 s i) Zmod.one)) (Zmod.eqb (N.v51263 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51279 s i) Zmod.one)) (Zmod.eqb (N.v51278 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51291 s i) Zmod.one)) (Zmod.eqb (N.v51290 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51303 s i) Zmod.one)) (Zmod.eqb (N.v51302 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51318 s i) Zmod.one)) (Zmod.eqb (N.v51317 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51330 s i) Zmod.one)) (Zmod.eqb (N.v51329 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51342 s i) Zmod.one)) (Zmod.eqb (N.v51341 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51357 s i) Zmod.one)) (Zmod.eqb (N.v51356 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51369 s i) Zmod.one)) (Zmod.eqb (N.v51368 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51381 s i) Zmod.one)) (Zmod.eqb (N.v51380 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51396 s i) Zmod.one)) (Zmod.eqb (N.v51395 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51408 s i) Zmod.one)) (Zmod.eqb (N.v51407 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51420 s i) Zmod.one)) (Zmod.eqb (N.v51419 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51435 s i) Zmod.one)) (Zmod.eqb (N.v51434 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51447 s i) Zmod.one)) (Zmod.eqb (N.v51446 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51459 s i) Zmod.one)) (Zmod.eqb (N.v51458 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51468 s i) Zmod.one)) (Zmod.eqb (N.v51467 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51483 s i) Zmod.one)) (Zmod.eqb (N.v51482 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51495 s i) Zmod.one)) (Zmod.eqb (N.v51494 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51507 s i) Zmod.one)) (Zmod.eqb (N.v51506 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51522 s i) Zmod.one)) (Zmod.eqb (N.v51521 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51534 s i) Zmod.one)) (Zmod.eqb (N.v51533 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51546 s i) Zmod.one)) (Zmod.eqb (N.v51545 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51555 s i) Zmod.one)) (Zmod.eqb (N.v51554 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51570 s i) Zmod.one)) (Zmod.eqb (N.v51569 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51582 s i) Zmod.one)) (Zmod.eqb (N.v51581 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51594 s i) Zmod.one)) (Zmod.eqb (N.v51593 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51609 s i) Zmod.one)) (Zmod.eqb (N.v51608 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51621 s i) Zmod.one)) (Zmod.eqb (N.v51620 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51633 s i) Zmod.one)) (Zmod.eqb (N.v51632 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51648 s i) Zmod.one)) (Zmod.eqb (N.v51647 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51660 s i) Zmod.one)) (Zmod.eqb (N.v51659 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51672 s i) Zmod.one)) (Zmod.eqb (N.v51671 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51687 s i) Zmod.one)) (Zmod.eqb (N.v51686 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51699 s i) Zmod.one)) (Zmod.eqb (N.v51698 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51711 s i) Zmod.one)) (Zmod.eqb (N.v51710 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51726 s i) Zmod.one)) (Zmod.eqb (N.v51725 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51738 s i) Zmod.one)) (Zmod.eqb (N.v51737 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51750 s i) Zmod.one)) (Zmod.eqb (N.v51749 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51765 s i) Zmod.one)) (Zmod.eqb (N.v51764 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51777 s i) Zmod.one)) (Zmod.eqb (N.v51776 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51789 s i) Zmod.one)) (Zmod.eqb (N.v51788 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51804 s i) Zmod.one)) (Zmod.eqb (N.v51803 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51816 s i) Zmod.one)) (Zmod.eqb (N.v51815 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51828 s i) Zmod.one)) (Zmod.eqb (N.v51827 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51843 s i) Zmod.one)) (Zmod.eqb (N.v51842 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51855 s i) Zmod.one)) (Zmod.eqb (N.v51854 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51867 s i) Zmod.one)) (Zmod.eqb (N.v51866 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51882 s i) Zmod.one)) (Zmod.eqb (N.v51881 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51894 s i) Zmod.one)) (Zmod.eqb (N.v51893 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51906 s i) Zmod.one)) (Zmod.eqb (N.v51905 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51921 s i) Zmod.one)) (Zmod.eqb (N.v51920 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51933 s i) Zmod.one)) (Zmod.eqb (N.v51932 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51945 s i) Zmod.one)) (Zmod.eqb (N.v51944 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51960 s i) Zmod.one)) (Zmod.eqb (N.v51959 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51972 s i) Zmod.one)) (Zmod.eqb (N.v51971 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51984 s i) Zmod.one)) (Zmod.eqb (N.v51983 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v51999 s i) Zmod.one)) (Zmod.eqb (N.v51998 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52011 s i) Zmod.one)) (Zmod.eqb (N.v52010 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52023 s i) Zmod.one)) (Zmod.eqb (N.v52022 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52038 s i) Zmod.one)) (Zmod.eqb (N.v52037 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52050 s i) Zmod.one)) (Zmod.eqb (N.v52049 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52062 s i) Zmod.one)) (Zmod.eqb (N.v52061 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52077 s i) Zmod.one)) (Zmod.eqb (N.v52076 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52089 s i) Zmod.one)) (Zmod.eqb (N.v52088 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52101 s i) Zmod.one)) (Zmod.eqb (N.v52100 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52116 s i) Zmod.one)) (Zmod.eqb (N.v52115 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52128 s i) Zmod.one)) (Zmod.eqb (N.v52127 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52140 s i) Zmod.one)) (Zmod.eqb (N.v52139 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52155 s i) Zmod.one)) (Zmod.eqb (N.v52154 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52167 s i) Zmod.one)) (Zmod.eqb (N.v52166 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52179 s i) Zmod.one)) (Zmod.eqb (N.v52178 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52194 s i) Zmod.one)) (Zmod.eqb (N.v52193 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52206 s i) Zmod.one)) (Zmod.eqb (N.v52205 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52218 s i) Zmod.one)) (Zmod.eqb (N.v52217 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52233 s i) Zmod.one)) (Zmod.eqb (N.v52232 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52245 s i) Zmod.one)) (Zmod.eqb (N.v52244 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52257 s i) Zmod.one)) (Zmod.eqb (N.v52256 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v52272 s i) Zmod.one)) (Zmod.eqb (N.v52271 s i) Zmod.one)
].
Lemma checks_27 s i : reference_checks_27 s i = native_checks_27 s i.
Proof. unfold reference_checks_27, native_checks_27.
  rewrite ?node_50990.
  rewrite ?node_50991.
  rewrite ?node_51005.
  rewrite ?node_51006.
  rewrite ?node_51017.
  rewrite ?node_51018.
  rewrite ?node_51029.
  rewrite ?node_51030.
  rewrite ?node_51044.
  rewrite ?node_51045.
  rewrite ?node_51056.
  rewrite ?node_51057.
  rewrite ?node_51068.
  rewrite ?node_51069.
  rewrite ?node_51083.
  rewrite ?node_51084.
  rewrite ?node_51095.
  rewrite ?node_51096.
  rewrite ?node_51107.
  rewrite ?node_51108.
  rewrite ?node_51122.
  rewrite ?node_51123.
  rewrite ?node_51134.
  rewrite ?node_51135.
  rewrite ?node_51146.
  rewrite ?node_51147.
  rewrite ?node_51161.
  rewrite ?node_51162.
  rewrite ?node_51173.
  rewrite ?node_51174.
  rewrite ?node_51185.
  rewrite ?node_51186.
  rewrite ?node_51200.
  rewrite ?node_51201.
  rewrite ?node_51212.
  rewrite ?node_51213.
  rewrite ?node_51224.
  rewrite ?node_51225.
  rewrite ?node_51239.
  rewrite ?node_51240.
  rewrite ?node_51251.
  rewrite ?node_51252.
  rewrite ?node_51263.
  rewrite ?node_51264.
  rewrite ?node_51278.
  rewrite ?node_51279.
  rewrite ?node_51290.
  rewrite ?node_51291.
  rewrite ?node_51302.
  rewrite ?node_51303.
  rewrite ?node_51317.
  rewrite ?node_51318.
  rewrite ?node_51329.
  rewrite ?node_51330.
  rewrite ?node_51341.
  rewrite ?node_51342.
  rewrite ?node_51356.
  rewrite ?node_51357.
  rewrite ?node_51368.
  rewrite ?node_51369.
  rewrite ?node_51380.
  rewrite ?node_51381.
  rewrite ?node_51395.
  rewrite ?node_51396.
  rewrite ?node_51407.
  rewrite ?node_51408.
  rewrite ?node_51419.
  rewrite ?node_51420.
  rewrite ?node_51434.
  rewrite ?node_51435.
  rewrite ?node_51446.
  rewrite ?node_51447.
  rewrite ?node_51458.
  rewrite ?node_51459.
  rewrite ?node_51467.
  rewrite ?node_51468.
  rewrite ?node_51482.
  rewrite ?node_51483.
  rewrite ?node_51494.
  rewrite ?node_51495.
  rewrite ?node_51506.
  rewrite ?node_51507.
  rewrite ?node_51521.
  rewrite ?node_51522.
  rewrite ?node_51533.
  rewrite ?node_51534.
  rewrite ?node_51545.
  rewrite ?node_51546.
  rewrite ?node_51554.
  rewrite ?node_51555.
  rewrite ?node_51569.
  rewrite ?node_51570.
  rewrite ?node_51581.
  rewrite ?node_51582.
  rewrite ?node_51593.
  rewrite ?node_51594.
  rewrite ?node_51608.
  rewrite ?node_51609.
  rewrite ?node_51620.
  rewrite ?node_51621.
  rewrite ?node_51632.
  rewrite ?node_51633.
  rewrite ?node_51647.
  rewrite ?node_51648.
  rewrite ?node_51659.
  rewrite ?node_51660.
  rewrite ?node_51671.
  rewrite ?node_51672.
  rewrite ?node_51686.
  rewrite ?node_51687.
  rewrite ?node_51698.
  rewrite ?node_51699.
  rewrite ?node_51710.
  rewrite ?node_51711.
  rewrite ?node_51725.
  rewrite ?node_51726.
  rewrite ?node_51737.
  rewrite ?node_51738.
  rewrite ?node_51749.
  rewrite ?node_51750.
  rewrite ?node_51764.
  rewrite ?node_51765.
  rewrite ?node_51776.
  rewrite ?node_51777.
  rewrite ?node_51788.
  rewrite ?node_51789.
  rewrite ?node_51803.
  rewrite ?node_51804.
  rewrite ?node_51815.
  rewrite ?node_51816.
  rewrite ?node_51827.
  rewrite ?node_51828.
  rewrite ?node_51842.
  rewrite ?node_51843.
  rewrite ?node_51854.
  rewrite ?node_51855.
  rewrite ?node_51866.
  rewrite ?node_51867.
  rewrite ?node_51881.
  rewrite ?node_51882.
  rewrite ?node_51893.
  rewrite ?node_51894.
  rewrite ?node_51905.
  rewrite ?node_51906.
  rewrite ?node_51920.
  rewrite ?node_51921.
  rewrite ?node_51932.
  rewrite ?node_51933.
  rewrite ?node_51944.
  rewrite ?node_51945.
  rewrite ?node_51959.
  rewrite ?node_51960.
  rewrite ?node_51971.
  rewrite ?node_51972.
  rewrite ?node_51983.
  rewrite ?node_51984.
  rewrite ?node_51998.
  rewrite ?node_51999.
  rewrite ?node_52010.
  rewrite ?node_52011.
  rewrite ?node_52022.
  rewrite ?node_52023.
  rewrite ?node_52037.
  rewrite ?node_52038.
  rewrite ?node_52049.
  rewrite ?node_52050.
  rewrite ?node_52061.
  rewrite ?node_52062.
  rewrite ?node_52076.
  rewrite ?node_52077.
  rewrite ?node_52088.
  rewrite ?node_52089.
  rewrite ?node_52100.
  rewrite ?node_52101.
  rewrite ?node_52115.
  rewrite ?node_52116.
  rewrite ?node_52127.
  rewrite ?node_52128.
  rewrite ?node_52139.
  rewrite ?node_52140.
  rewrite ?node_52154.
  rewrite ?node_52155.
  rewrite ?node_52166.
  rewrite ?node_52167.
  rewrite ?node_52178.
  rewrite ?node_52179.
  rewrite ?node_52193.
  rewrite ?node_52194.
  rewrite ?node_52205.
  rewrite ?node_52206.
  rewrite ?node_52217.
  rewrite ?node_52218.
  rewrite ?node_52232.
  rewrite ?node_52233.
  rewrite ?node_52244.
  rewrite ?node_52245.
  rewrite ?node_52256.
  rewrite ?node_52257.
  rewrite ?node_52271.
  rewrite ?node_52272.
  reflexivity.
Qed.

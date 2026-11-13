From Stdlib Require Import ZArith List Bool Zmod.Bits.
From BitsProofs Require Import ArrayRefinementNodes022.
Import ListNotations.
Open Scope Z_scope.
Local Opaque R.v21597 N.v21597 R.v21598 N.v21598 R.v21606 N.v21606 R.v21607 N.v21607 R.v21621 N.v21621 R.v21622 N.v21622 R.v21633 N.v21633 R.v21634 N.v21634 R.v21645 N.v21645 R.v21646 N.v21646 R.v21660 N.v21660 R.v21661 N.v21661 R.v21672 N.v21672 R.v21673 N.v21673 R.v21684 N.v21684 R.v21685 N.v21685 R.v21699 N.v21699 R.v21700 N.v21700 R.v21711 N.v21711 R.v21712 N.v21712 R.v21723 N.v21723 R.v21724 N.v21724 R.v21738 N.v21738 R.v21739 N.v21739 R.v21750 N.v21750 R.v21751 N.v21751 R.v21762 N.v21762 R.v21763 N.v21763 R.v21777 N.v21777 R.v21778 N.v21778 R.v21789 N.v21789 R.v21790 N.v21790 R.v21801 N.v21801 R.v21802 N.v21802 R.v21816 N.v21816 R.v21817 N.v21817 R.v21828 N.v21828 R.v21829 N.v21829 R.v21840 N.v21840 R.v21841 N.v21841 R.v21855 N.v21855 R.v21856 N.v21856 R.v21867 N.v21867 R.v21868 N.v21868 R.v21879 N.v21879 R.v21880 N.v21880 R.v21894 N.v21894 R.v21895 N.v21895 R.v21906 N.v21906 R.v21907 N.v21907 R.v21918 N.v21918 R.v21919 N.v21919 R.v21933 N.v21933 R.v21934 N.v21934 R.v21945 N.v21945 R.v21946 N.v21946 R.v21957 N.v21957 R.v21958 N.v21958 R.v21972 N.v21972 R.v21973 N.v21973 R.v21984 N.v21984 R.v21985 N.v21985 R.v21996 N.v21996 R.v21997 N.v21997 R.v22011 N.v22011 R.v22012 N.v22012 R.v22023 N.v22023 R.v22024 N.v22024 R.v22035 N.v22035 R.v22036 N.v22036 R.v22050 N.v22050 R.v22051 N.v22051 R.v22062 N.v22062 R.v22063 N.v22063 R.v22074 N.v22074 R.v22075 N.v22075 R.v22089 N.v22089 R.v22090 N.v22090 R.v22101 N.v22101 R.v22102 N.v22102 R.v22113 N.v22113 R.v22114 N.v22114 R.v22128 N.v22128 R.v22129 N.v22129 R.v22140 N.v22140 R.v22141 N.v22141 R.v22152 N.v22152 R.v22153 N.v22153 R.v22167 N.v22167 R.v22168 N.v22168 R.v22179 N.v22179 R.v22180 N.v22180 R.v22191 N.v22191 R.v22192 N.v22192 R.v22206 N.v22206 R.v22207 N.v22207 R.v22218 N.v22218 R.v22219 N.v22219 R.v22230 N.v22230 R.v22231 N.v22231 R.v22245 N.v22245 R.v22246 N.v22246 R.v22257 N.v22257 R.v22258 N.v22258 R.v22269 N.v22269 R.v22270 N.v22270 R.v22284 N.v22284 R.v22285 N.v22285 R.v22296 N.v22296 R.v22297 N.v22297 R.v22308 N.v22308 R.v22309 N.v22309 R.v22323 N.v22323 R.v22324 N.v22324 R.v22335 N.v22335 R.v22336 N.v22336 R.v22347 N.v22347 R.v22348 N.v22348 R.v22362 N.v22362 R.v22363 N.v22363 R.v22374 N.v22374 R.v22375 N.v22375 R.v22386 N.v22386 R.v22387 N.v22387 R.v22401 N.v22401 R.v22402 N.v22402 R.v22413 N.v22413 R.v22414 N.v22414 R.v22425 N.v22425 R.v22426 N.v22426 R.v22440 N.v22440 R.v22441 N.v22441 R.v22452 N.v22452 R.v22453 N.v22453 R.v22464 N.v22464 R.v22465 N.v22465 R.v22479 N.v22479 R.v22480 N.v22480 R.v22491 N.v22491 R.v22492 N.v22492 R.v22503 N.v22503 R.v22504 N.v22504 R.v22518 N.v22518 R.v22519 N.v22519 R.v22530 N.v22530 R.v22531 N.v22531 R.v22542 N.v22542 R.v22543 N.v22543 R.v22551 N.v22551 R.v22552 N.v22552 R.v22566 N.v22566 R.v22567 N.v22567 R.v22578 N.v22578 R.v22579 N.v22579 R.v22590 N.v22590 R.v22591 N.v22591 R.v22605 N.v22605 R.v22606 N.v22606 R.v22617 N.v22617 R.v22618 N.v22618 R.v22629 N.v22629 R.v22630 N.v22630 R.v22644 N.v22644 R.v22645 N.v22645 R.v22656 N.v22656 R.v22657 N.v22657 R.v22668 N.v22668 R.v22669 N.v22669 R.v22683 N.v22683 R.v22684 N.v22684 R.v22695 N.v22695 R.v22696 N.v22696 R.v22707 N.v22707 R.v22708 N.v22708 R.v22722 N.v22722 R.v22723 N.v22723 R.v22734 N.v22734 R.v22735 N.v22735 R.v22746 N.v22746 R.v22747 N.v22747 R.v22761 N.v22761 R.v22762 N.v22762 R.v22773 N.v22773 R.v22774 N.v22774 R.v22785 N.v22785 R.v22786 N.v22786 R.v22794 N.v22794 R.v22795 N.v22795 R.v22809 N.v22809 R.v22810 N.v22810 R.v22821 N.v22821 R.v22822 N.v22822 R.v22833 N.v22833 R.v22834 N.v22834 R.v22848 N.v22848 R.v22849 N.v22849 R.v22860 N.v22860 R.v22861 N.v22861 R.v22872 N.v22872 R.v22873 N.v22873.
Definition reference_checks_4 (s : N.State) (i : N.Inputs) : list bool := [
orb (negb (Z.eqb (R.v21598 (state s) (inputs i)) 1)) (Z.eqb (R.v21597 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21607 (state s) (inputs i)) 1)) (Z.eqb (R.v21606 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21622 (state s) (inputs i)) 1)) (Z.eqb (R.v21621 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21634 (state s) (inputs i)) 1)) (Z.eqb (R.v21633 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21646 (state s) (inputs i)) 1)) (Z.eqb (R.v21645 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21661 (state s) (inputs i)) 1)) (Z.eqb (R.v21660 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21673 (state s) (inputs i)) 1)) (Z.eqb (R.v21672 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21685 (state s) (inputs i)) 1)) (Z.eqb (R.v21684 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21700 (state s) (inputs i)) 1)) (Z.eqb (R.v21699 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21712 (state s) (inputs i)) 1)) (Z.eqb (R.v21711 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21724 (state s) (inputs i)) 1)) (Z.eqb (R.v21723 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21739 (state s) (inputs i)) 1)) (Z.eqb (R.v21738 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21751 (state s) (inputs i)) 1)) (Z.eqb (R.v21750 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21763 (state s) (inputs i)) 1)) (Z.eqb (R.v21762 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21778 (state s) (inputs i)) 1)) (Z.eqb (R.v21777 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21790 (state s) (inputs i)) 1)) (Z.eqb (R.v21789 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21802 (state s) (inputs i)) 1)) (Z.eqb (R.v21801 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21817 (state s) (inputs i)) 1)) (Z.eqb (R.v21816 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21829 (state s) (inputs i)) 1)) (Z.eqb (R.v21828 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21841 (state s) (inputs i)) 1)) (Z.eqb (R.v21840 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21856 (state s) (inputs i)) 1)) (Z.eqb (R.v21855 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21868 (state s) (inputs i)) 1)) (Z.eqb (R.v21867 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21880 (state s) (inputs i)) 1)) (Z.eqb (R.v21879 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21895 (state s) (inputs i)) 1)) (Z.eqb (R.v21894 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21907 (state s) (inputs i)) 1)) (Z.eqb (R.v21906 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21919 (state s) (inputs i)) 1)) (Z.eqb (R.v21918 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21934 (state s) (inputs i)) 1)) (Z.eqb (R.v21933 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21946 (state s) (inputs i)) 1)) (Z.eqb (R.v21945 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21958 (state s) (inputs i)) 1)) (Z.eqb (R.v21957 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21973 (state s) (inputs i)) 1)) (Z.eqb (R.v21972 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21985 (state s) (inputs i)) 1)) (Z.eqb (R.v21984 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v21997 (state s) (inputs i)) 1)) (Z.eqb (R.v21996 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22012 (state s) (inputs i)) 1)) (Z.eqb (R.v22011 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22024 (state s) (inputs i)) 1)) (Z.eqb (R.v22023 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22036 (state s) (inputs i)) 1)) (Z.eqb (R.v22035 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22051 (state s) (inputs i)) 1)) (Z.eqb (R.v22050 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22063 (state s) (inputs i)) 1)) (Z.eqb (R.v22062 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22075 (state s) (inputs i)) 1)) (Z.eqb (R.v22074 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22090 (state s) (inputs i)) 1)) (Z.eqb (R.v22089 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22102 (state s) (inputs i)) 1)) (Z.eqb (R.v22101 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22114 (state s) (inputs i)) 1)) (Z.eqb (R.v22113 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22129 (state s) (inputs i)) 1)) (Z.eqb (R.v22128 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22141 (state s) (inputs i)) 1)) (Z.eqb (R.v22140 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22153 (state s) (inputs i)) 1)) (Z.eqb (R.v22152 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22168 (state s) (inputs i)) 1)) (Z.eqb (R.v22167 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22180 (state s) (inputs i)) 1)) (Z.eqb (R.v22179 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22192 (state s) (inputs i)) 1)) (Z.eqb (R.v22191 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22207 (state s) (inputs i)) 1)) (Z.eqb (R.v22206 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22219 (state s) (inputs i)) 1)) (Z.eqb (R.v22218 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22231 (state s) (inputs i)) 1)) (Z.eqb (R.v22230 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22246 (state s) (inputs i)) 1)) (Z.eqb (R.v22245 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22258 (state s) (inputs i)) 1)) (Z.eqb (R.v22257 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22270 (state s) (inputs i)) 1)) (Z.eqb (R.v22269 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22285 (state s) (inputs i)) 1)) (Z.eqb (R.v22284 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22297 (state s) (inputs i)) 1)) (Z.eqb (R.v22296 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22309 (state s) (inputs i)) 1)) (Z.eqb (R.v22308 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22324 (state s) (inputs i)) 1)) (Z.eqb (R.v22323 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22336 (state s) (inputs i)) 1)) (Z.eqb (R.v22335 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22348 (state s) (inputs i)) 1)) (Z.eqb (R.v22347 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22363 (state s) (inputs i)) 1)) (Z.eqb (R.v22362 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22375 (state s) (inputs i)) 1)) (Z.eqb (R.v22374 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22387 (state s) (inputs i)) 1)) (Z.eqb (R.v22386 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22402 (state s) (inputs i)) 1)) (Z.eqb (R.v22401 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22414 (state s) (inputs i)) 1)) (Z.eqb (R.v22413 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22426 (state s) (inputs i)) 1)) (Z.eqb (R.v22425 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22441 (state s) (inputs i)) 1)) (Z.eqb (R.v22440 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22453 (state s) (inputs i)) 1)) (Z.eqb (R.v22452 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22465 (state s) (inputs i)) 1)) (Z.eqb (R.v22464 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22480 (state s) (inputs i)) 1)) (Z.eqb (R.v22479 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22492 (state s) (inputs i)) 1)) (Z.eqb (R.v22491 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22504 (state s) (inputs i)) 1)) (Z.eqb (R.v22503 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22519 (state s) (inputs i)) 1)) (Z.eqb (R.v22518 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22531 (state s) (inputs i)) 1)) (Z.eqb (R.v22530 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22543 (state s) (inputs i)) 1)) (Z.eqb (R.v22542 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22552 (state s) (inputs i)) 1)) (Z.eqb (R.v22551 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22567 (state s) (inputs i)) 1)) (Z.eqb (R.v22566 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22579 (state s) (inputs i)) 1)) (Z.eqb (R.v22578 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22591 (state s) (inputs i)) 1)) (Z.eqb (R.v22590 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22606 (state s) (inputs i)) 1)) (Z.eqb (R.v22605 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22618 (state s) (inputs i)) 1)) (Z.eqb (R.v22617 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22630 (state s) (inputs i)) 1)) (Z.eqb (R.v22629 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22645 (state s) (inputs i)) 1)) (Z.eqb (R.v22644 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22657 (state s) (inputs i)) 1)) (Z.eqb (R.v22656 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22669 (state s) (inputs i)) 1)) (Z.eqb (R.v22668 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22684 (state s) (inputs i)) 1)) (Z.eqb (R.v22683 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22696 (state s) (inputs i)) 1)) (Z.eqb (R.v22695 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22708 (state s) (inputs i)) 1)) (Z.eqb (R.v22707 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22723 (state s) (inputs i)) 1)) (Z.eqb (R.v22722 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22735 (state s) (inputs i)) 1)) (Z.eqb (R.v22734 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22747 (state s) (inputs i)) 1)) (Z.eqb (R.v22746 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22762 (state s) (inputs i)) 1)) (Z.eqb (R.v22761 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22774 (state s) (inputs i)) 1)) (Z.eqb (R.v22773 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22786 (state s) (inputs i)) 1)) (Z.eqb (R.v22785 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22795 (state s) (inputs i)) 1)) (Z.eqb (R.v22794 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22810 (state s) (inputs i)) 1)) (Z.eqb (R.v22809 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22822 (state s) (inputs i)) 1)) (Z.eqb (R.v22821 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22834 (state s) (inputs i)) 1)) (Z.eqb (R.v22833 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22849 (state s) (inputs i)) 1)) (Z.eqb (R.v22848 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22861 (state s) (inputs i)) 1)) (Z.eqb (R.v22860 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v22873 (state s) (inputs i)) 1)) (Z.eqb (R.v22872 (state s) (inputs i)) 1)
].
Definition native_checks_4 (s : N.State) (i : N.Inputs) : list bool := [
orb (negb (Zmod.eqb (N.v21598 s i) Zmod.one)) (Zmod.eqb (N.v21597 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21607 s i) Zmod.one)) (Zmod.eqb (N.v21606 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21622 s i) Zmod.one)) (Zmod.eqb (N.v21621 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21634 s i) Zmod.one)) (Zmod.eqb (N.v21633 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21646 s i) Zmod.one)) (Zmod.eqb (N.v21645 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21661 s i) Zmod.one)) (Zmod.eqb (N.v21660 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21673 s i) Zmod.one)) (Zmod.eqb (N.v21672 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21685 s i) Zmod.one)) (Zmod.eqb (N.v21684 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21700 s i) Zmod.one)) (Zmod.eqb (N.v21699 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21712 s i) Zmod.one)) (Zmod.eqb (N.v21711 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21724 s i) Zmod.one)) (Zmod.eqb (N.v21723 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21739 s i) Zmod.one)) (Zmod.eqb (N.v21738 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21751 s i) Zmod.one)) (Zmod.eqb (N.v21750 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21763 s i) Zmod.one)) (Zmod.eqb (N.v21762 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21778 s i) Zmod.one)) (Zmod.eqb (N.v21777 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21790 s i) Zmod.one)) (Zmod.eqb (N.v21789 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21802 s i) Zmod.one)) (Zmod.eqb (N.v21801 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21817 s i) Zmod.one)) (Zmod.eqb (N.v21816 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21829 s i) Zmod.one)) (Zmod.eqb (N.v21828 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21841 s i) Zmod.one)) (Zmod.eqb (N.v21840 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21856 s i) Zmod.one)) (Zmod.eqb (N.v21855 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21868 s i) Zmod.one)) (Zmod.eqb (N.v21867 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21880 s i) Zmod.one)) (Zmod.eqb (N.v21879 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21895 s i) Zmod.one)) (Zmod.eqb (N.v21894 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21907 s i) Zmod.one)) (Zmod.eqb (N.v21906 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21919 s i) Zmod.one)) (Zmod.eqb (N.v21918 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21934 s i) Zmod.one)) (Zmod.eqb (N.v21933 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21946 s i) Zmod.one)) (Zmod.eqb (N.v21945 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21958 s i) Zmod.one)) (Zmod.eqb (N.v21957 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21973 s i) Zmod.one)) (Zmod.eqb (N.v21972 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21985 s i) Zmod.one)) (Zmod.eqb (N.v21984 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v21997 s i) Zmod.one)) (Zmod.eqb (N.v21996 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22012 s i) Zmod.one)) (Zmod.eqb (N.v22011 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22024 s i) Zmod.one)) (Zmod.eqb (N.v22023 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22036 s i) Zmod.one)) (Zmod.eqb (N.v22035 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22051 s i) Zmod.one)) (Zmod.eqb (N.v22050 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22063 s i) Zmod.one)) (Zmod.eqb (N.v22062 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22075 s i) Zmod.one)) (Zmod.eqb (N.v22074 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22090 s i) Zmod.one)) (Zmod.eqb (N.v22089 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22102 s i) Zmod.one)) (Zmod.eqb (N.v22101 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22114 s i) Zmod.one)) (Zmod.eqb (N.v22113 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22129 s i) Zmod.one)) (Zmod.eqb (N.v22128 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22141 s i) Zmod.one)) (Zmod.eqb (N.v22140 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22153 s i) Zmod.one)) (Zmod.eqb (N.v22152 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22168 s i) Zmod.one)) (Zmod.eqb (N.v22167 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22180 s i) Zmod.one)) (Zmod.eqb (N.v22179 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22192 s i) Zmod.one)) (Zmod.eqb (N.v22191 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22207 s i) Zmod.one)) (Zmod.eqb (N.v22206 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22219 s i) Zmod.one)) (Zmod.eqb (N.v22218 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22231 s i) Zmod.one)) (Zmod.eqb (N.v22230 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22246 s i) Zmod.one)) (Zmod.eqb (N.v22245 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22258 s i) Zmod.one)) (Zmod.eqb (N.v22257 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22270 s i) Zmod.one)) (Zmod.eqb (N.v22269 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22285 s i) Zmod.one)) (Zmod.eqb (N.v22284 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22297 s i) Zmod.one)) (Zmod.eqb (N.v22296 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22309 s i) Zmod.one)) (Zmod.eqb (N.v22308 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22324 s i) Zmod.one)) (Zmod.eqb (N.v22323 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22336 s i) Zmod.one)) (Zmod.eqb (N.v22335 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22348 s i) Zmod.one)) (Zmod.eqb (N.v22347 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22363 s i) Zmod.one)) (Zmod.eqb (N.v22362 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22375 s i) Zmod.one)) (Zmod.eqb (N.v22374 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22387 s i) Zmod.one)) (Zmod.eqb (N.v22386 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22402 s i) Zmod.one)) (Zmod.eqb (N.v22401 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22414 s i) Zmod.one)) (Zmod.eqb (N.v22413 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22426 s i) Zmod.one)) (Zmod.eqb (N.v22425 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22441 s i) Zmod.one)) (Zmod.eqb (N.v22440 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22453 s i) Zmod.one)) (Zmod.eqb (N.v22452 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22465 s i) Zmod.one)) (Zmod.eqb (N.v22464 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22480 s i) Zmod.one)) (Zmod.eqb (N.v22479 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22492 s i) Zmod.one)) (Zmod.eqb (N.v22491 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22504 s i) Zmod.one)) (Zmod.eqb (N.v22503 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22519 s i) Zmod.one)) (Zmod.eqb (N.v22518 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22531 s i) Zmod.one)) (Zmod.eqb (N.v22530 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22543 s i) Zmod.one)) (Zmod.eqb (N.v22542 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22552 s i) Zmod.one)) (Zmod.eqb (N.v22551 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22567 s i) Zmod.one)) (Zmod.eqb (N.v22566 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22579 s i) Zmod.one)) (Zmod.eqb (N.v22578 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22591 s i) Zmod.one)) (Zmod.eqb (N.v22590 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22606 s i) Zmod.one)) (Zmod.eqb (N.v22605 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22618 s i) Zmod.one)) (Zmod.eqb (N.v22617 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22630 s i) Zmod.one)) (Zmod.eqb (N.v22629 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22645 s i) Zmod.one)) (Zmod.eqb (N.v22644 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22657 s i) Zmod.one)) (Zmod.eqb (N.v22656 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22669 s i) Zmod.one)) (Zmod.eqb (N.v22668 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22684 s i) Zmod.one)) (Zmod.eqb (N.v22683 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22696 s i) Zmod.one)) (Zmod.eqb (N.v22695 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22708 s i) Zmod.one)) (Zmod.eqb (N.v22707 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22723 s i) Zmod.one)) (Zmod.eqb (N.v22722 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22735 s i) Zmod.one)) (Zmod.eqb (N.v22734 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22747 s i) Zmod.one)) (Zmod.eqb (N.v22746 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22762 s i) Zmod.one)) (Zmod.eqb (N.v22761 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22774 s i) Zmod.one)) (Zmod.eqb (N.v22773 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22786 s i) Zmod.one)) (Zmod.eqb (N.v22785 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22795 s i) Zmod.one)) (Zmod.eqb (N.v22794 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22810 s i) Zmod.one)) (Zmod.eqb (N.v22809 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22822 s i) Zmod.one)) (Zmod.eqb (N.v22821 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22834 s i) Zmod.one)) (Zmod.eqb (N.v22833 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22849 s i) Zmod.one)) (Zmod.eqb (N.v22848 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22861 s i) Zmod.one)) (Zmod.eqb (N.v22860 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v22873 s i) Zmod.one)) (Zmod.eqb (N.v22872 s i) Zmod.one)
].
Lemma checks_4 s i : reference_checks_4 s i = native_checks_4 s i.
Proof. unfold reference_checks_4, native_checks_4.
  rewrite ?node_21597.
  rewrite ?node_21598.
  rewrite ?node_21606.
  rewrite ?node_21607.
  rewrite ?node_21621.
  rewrite ?node_21622.
  rewrite ?node_21633.
  rewrite ?node_21634.
  rewrite ?node_21645.
  rewrite ?node_21646.
  rewrite ?node_21660.
  rewrite ?node_21661.
  rewrite ?node_21672.
  rewrite ?node_21673.
  rewrite ?node_21684.
  rewrite ?node_21685.
  rewrite ?node_21699.
  rewrite ?node_21700.
  rewrite ?node_21711.
  rewrite ?node_21712.
  rewrite ?node_21723.
  rewrite ?node_21724.
  rewrite ?node_21738.
  rewrite ?node_21739.
  rewrite ?node_21750.
  rewrite ?node_21751.
  rewrite ?node_21762.
  rewrite ?node_21763.
  rewrite ?node_21777.
  rewrite ?node_21778.
  rewrite ?node_21789.
  rewrite ?node_21790.
  rewrite ?node_21801.
  rewrite ?node_21802.
  rewrite ?node_21816.
  rewrite ?node_21817.
  rewrite ?node_21828.
  rewrite ?node_21829.
  rewrite ?node_21840.
  rewrite ?node_21841.
  rewrite ?node_21855.
  rewrite ?node_21856.
  rewrite ?node_21867.
  rewrite ?node_21868.
  rewrite ?node_21879.
  rewrite ?node_21880.
  rewrite ?node_21894.
  rewrite ?node_21895.
  rewrite ?node_21906.
  rewrite ?node_21907.
  rewrite ?node_21918.
  rewrite ?node_21919.
  rewrite ?node_21933.
  rewrite ?node_21934.
  rewrite ?node_21945.
  rewrite ?node_21946.
  rewrite ?node_21957.
  rewrite ?node_21958.
  rewrite ?node_21972.
  rewrite ?node_21973.
  rewrite ?node_21984.
  rewrite ?node_21985.
  rewrite ?node_21996.
  rewrite ?node_21997.
  rewrite ?node_22011.
  rewrite ?node_22012.
  rewrite ?node_22023.
  rewrite ?node_22024.
  rewrite ?node_22035.
  rewrite ?node_22036.
  rewrite ?node_22050.
  rewrite ?node_22051.
  rewrite ?node_22062.
  rewrite ?node_22063.
  rewrite ?node_22074.
  rewrite ?node_22075.
  rewrite ?node_22089.
  rewrite ?node_22090.
  rewrite ?node_22101.
  rewrite ?node_22102.
  rewrite ?node_22113.
  rewrite ?node_22114.
  rewrite ?node_22128.
  rewrite ?node_22129.
  rewrite ?node_22140.
  rewrite ?node_22141.
  rewrite ?node_22152.
  rewrite ?node_22153.
  rewrite ?node_22167.
  rewrite ?node_22168.
  rewrite ?node_22179.
  rewrite ?node_22180.
  rewrite ?node_22191.
  rewrite ?node_22192.
  rewrite ?node_22206.
  rewrite ?node_22207.
  rewrite ?node_22218.
  rewrite ?node_22219.
  rewrite ?node_22230.
  rewrite ?node_22231.
  rewrite ?node_22245.
  rewrite ?node_22246.
  rewrite ?node_22257.
  rewrite ?node_22258.
  rewrite ?node_22269.
  rewrite ?node_22270.
  rewrite ?node_22284.
  rewrite ?node_22285.
  rewrite ?node_22296.
  rewrite ?node_22297.
  rewrite ?node_22308.
  rewrite ?node_22309.
  rewrite ?node_22323.
  rewrite ?node_22324.
  rewrite ?node_22335.
  rewrite ?node_22336.
  rewrite ?node_22347.
  rewrite ?node_22348.
  rewrite ?node_22362.
  rewrite ?node_22363.
  rewrite ?node_22374.
  rewrite ?node_22375.
  rewrite ?node_22386.
  rewrite ?node_22387.
  rewrite ?node_22401.
  rewrite ?node_22402.
  rewrite ?node_22413.
  rewrite ?node_22414.
  rewrite ?node_22425.
  rewrite ?node_22426.
  rewrite ?node_22440.
  rewrite ?node_22441.
  rewrite ?node_22452.
  rewrite ?node_22453.
  rewrite ?node_22464.
  rewrite ?node_22465.
  rewrite ?node_22479.
  rewrite ?node_22480.
  rewrite ?node_22491.
  rewrite ?node_22492.
  rewrite ?node_22503.
  rewrite ?node_22504.
  rewrite ?node_22518.
  rewrite ?node_22519.
  rewrite ?node_22530.
  rewrite ?node_22531.
  rewrite ?node_22542.
  rewrite ?node_22543.
  rewrite ?node_22551.
  rewrite ?node_22552.
  rewrite ?node_22566.
  rewrite ?node_22567.
  rewrite ?node_22578.
  rewrite ?node_22579.
  rewrite ?node_22590.
  rewrite ?node_22591.
  rewrite ?node_22605.
  rewrite ?node_22606.
  rewrite ?node_22617.
  rewrite ?node_22618.
  rewrite ?node_22629.
  rewrite ?node_22630.
  rewrite ?node_22644.
  rewrite ?node_22645.
  rewrite ?node_22656.
  rewrite ?node_22657.
  rewrite ?node_22668.
  rewrite ?node_22669.
  rewrite ?node_22683.
  rewrite ?node_22684.
  rewrite ?node_22695.
  rewrite ?node_22696.
  rewrite ?node_22707.
  rewrite ?node_22708.
  rewrite ?node_22722.
  rewrite ?node_22723.
  rewrite ?node_22734.
  rewrite ?node_22735.
  rewrite ?node_22746.
  rewrite ?node_22747.
  rewrite ?node_22761.
  rewrite ?node_22762.
  rewrite ?node_22773.
  rewrite ?node_22774.
  rewrite ?node_22785.
  rewrite ?node_22786.
  rewrite ?node_22794.
  rewrite ?node_22795.
  rewrite ?node_22809.
  rewrite ?node_22810.
  rewrite ?node_22821.
  rewrite ?node_22822.
  rewrite ?node_22833.
  rewrite ?node_22834.
  rewrite ?node_22848.
  rewrite ?node_22849.
  rewrite ?node_22860.
  rewrite ?node_22861.
  rewrite ?node_22872.
  rewrite ?node_22873.
  reflexivity.
Qed.

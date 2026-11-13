From Stdlib Require Import ZArith List Bool Zmod.Bits.
From BitsProofs Require Import ArrayRefinementNodes019.
Import ListNotations.
Open Scope Z_scope.
Local Opaque R.v17736 N.v17736 R.v17737 N.v17737 R.v17748 N.v17748 R.v17749 N.v17749 R.v17763 N.v17763 R.v17764 N.v17764 R.v17775 N.v17775 R.v17776 N.v17776 R.v17787 N.v17787 R.v17788 N.v17788 R.v17802 N.v17802 R.v17803 N.v17803 R.v17814 N.v17814 R.v17815 N.v17815 R.v17826 N.v17826 R.v17827 N.v17827 R.v17841 N.v17841 R.v17842 N.v17842 R.v17853 N.v17853 R.v17854 N.v17854 R.v17865 N.v17865 R.v17866 N.v17866 R.v17880 N.v17880 R.v17881 N.v17881 R.v17892 N.v17892 R.v17893 N.v17893 R.v17904 N.v17904 R.v17905 N.v17905 R.v17919 N.v17919 R.v17920 N.v17920 R.v17931 N.v17931 R.v17932 N.v17932 R.v17943 N.v17943 R.v17944 N.v17944 R.v17958 N.v17958 R.v17959 N.v17959 R.v17970 N.v17970 R.v17971 N.v17971 R.v17982 N.v17982 R.v17983 N.v17983 R.v17997 N.v17997 R.v17998 N.v17998 R.v18009 N.v18009 R.v18010 N.v18010 R.v18021 N.v18021 R.v18022 N.v18022 R.v18036 N.v18036 R.v18037 N.v18037 R.v18048 N.v18048 R.v18049 N.v18049 R.v18060 N.v18060 R.v18061 N.v18061 R.v18075 N.v18075 R.v18076 N.v18076 R.v18087 N.v18087 R.v18088 N.v18088 R.v18099 N.v18099 R.v18100 N.v18100 R.v18108 N.v18108 R.v18109 N.v18109 R.v18123 N.v18123 R.v18124 N.v18124 R.v18135 N.v18135 R.v18136 N.v18136 R.v18147 N.v18147 R.v18148 N.v18148 R.v18162 N.v18162 R.v18163 N.v18163 R.v18174 N.v18174 R.v18175 N.v18175 R.v18186 N.v18186 R.v18187 N.v18187 R.v18201 N.v18201 R.v18202 N.v18202 R.v18213 N.v18213 R.v18214 N.v18214 R.v18225 N.v18225 R.v18226 N.v18226 R.v18234 N.v18234 R.v18235 N.v18235 R.v18249 N.v18249 R.v18250 N.v18250 R.v18261 N.v18261 R.v18262 N.v18262 R.v18273 N.v18273 R.v18274 N.v18274 R.v18288 N.v18288 R.v18289 N.v18289 R.v18300 N.v18300 R.v18301 N.v18301 R.v18312 N.v18312 R.v18313 N.v18313 R.v18327 N.v18327 R.v18328 N.v18328 R.v18339 N.v18339 R.v18340 N.v18340 R.v18351 N.v18351 R.v18352 N.v18352 R.v18363 N.v18363 R.v18364 N.v18364 R.v18378 N.v18378 R.v18379 N.v18379 R.v18390 N.v18390 R.v18391 N.v18391 R.v18402 N.v18402 R.v18403 N.v18403 R.v18417 N.v18417 R.v18418 N.v18418 R.v18429 N.v18429 R.v18430 N.v18430 R.v18441 N.v18441 R.v18442 N.v18442 R.v18456 N.v18456 R.v18457 N.v18457 R.v18468 N.v18468 R.v18469 N.v18469 R.v18480 N.v18480 R.v18481 N.v18481 R.v18492 N.v18492 R.v18493 N.v18493 R.v18507 N.v18507 R.v18508 N.v18508 R.v18519 N.v18519 R.v18520 N.v18520 R.v18531 N.v18531 R.v18532 N.v18532 R.v18546 N.v18546 R.v18547 N.v18547 R.v18558 N.v18558 R.v18559 N.v18559 R.v18570 N.v18570 R.v18571 N.v18571 R.v18585 N.v18585 R.v18586 N.v18586 R.v18597 N.v18597 R.v18598 N.v18598 R.v18609 N.v18609 R.v18610 N.v18610 R.v18623 N.v18623 R.v18624 N.v18624 R.v18635 N.v18635 R.v18636 N.v18636 R.v18644 N.v18644 R.v18645 N.v18645 R.v18659 N.v18659 R.v18660 N.v18660 R.v18671 N.v18671 R.v18672 N.v18672 R.v18683 N.v18683 R.v18684 N.v18684 R.v18698 N.v18698 R.v18699 N.v18699 R.v18710 N.v18710 R.v18711 N.v18711 R.v18722 N.v18722 R.v18723 N.v18723 R.v18737 N.v18737 R.v18738 N.v18738 R.v18749 N.v18749 R.v18750 N.v18750 R.v18761 N.v18761 R.v18762 N.v18762 R.v18776 N.v18776 R.v18777 N.v18777 R.v18788 N.v18788 R.v18789 N.v18789 R.v18800 N.v18800 R.v18801 N.v18801 R.v18815 N.v18815 R.v18816 N.v18816 R.v18827 N.v18827 R.v18828 N.v18828 R.v18839 N.v18839 R.v18840 N.v18840 R.v18854 N.v18854 R.v18855 N.v18855 R.v18866 N.v18866 R.v18867 N.v18867 R.v18878 N.v18878 R.v18879 N.v18879 R.v18893 N.v18893 R.v18894 N.v18894 R.v18905 N.v18905 R.v18906 N.v18906 R.v18917 N.v18917 R.v18918 N.v18918 R.v18932 N.v18932 R.v18933 N.v18933 R.v18944 N.v18944 R.v18945 N.v18945 R.v18956 N.v18956 R.v18957 N.v18957 R.v18971 N.v18971 R.v18972 N.v18972 R.v18983 N.v18983 R.v18984 N.v18984 R.v18995 N.v18995 R.v18996 N.v18996 R.v19010 N.v19010 R.v19011 N.v19011.
Definition reference_checks_1 (s : N.State) (i : N.Inputs) : list bool := [
orb (negb (Z.eqb (R.v17737 (state s) (inputs i)) 1)) (Z.eqb (R.v17736 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17749 (state s) (inputs i)) 1)) (Z.eqb (R.v17748 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17764 (state s) (inputs i)) 1)) (Z.eqb (R.v17763 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17776 (state s) (inputs i)) 1)) (Z.eqb (R.v17775 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17788 (state s) (inputs i)) 1)) (Z.eqb (R.v17787 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17803 (state s) (inputs i)) 1)) (Z.eqb (R.v17802 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17815 (state s) (inputs i)) 1)) (Z.eqb (R.v17814 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17827 (state s) (inputs i)) 1)) (Z.eqb (R.v17826 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17842 (state s) (inputs i)) 1)) (Z.eqb (R.v17841 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17854 (state s) (inputs i)) 1)) (Z.eqb (R.v17853 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17866 (state s) (inputs i)) 1)) (Z.eqb (R.v17865 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17881 (state s) (inputs i)) 1)) (Z.eqb (R.v17880 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17893 (state s) (inputs i)) 1)) (Z.eqb (R.v17892 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17905 (state s) (inputs i)) 1)) (Z.eqb (R.v17904 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17920 (state s) (inputs i)) 1)) (Z.eqb (R.v17919 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17932 (state s) (inputs i)) 1)) (Z.eqb (R.v17931 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17944 (state s) (inputs i)) 1)) (Z.eqb (R.v17943 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17959 (state s) (inputs i)) 1)) (Z.eqb (R.v17958 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17971 (state s) (inputs i)) 1)) (Z.eqb (R.v17970 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17983 (state s) (inputs i)) 1)) (Z.eqb (R.v17982 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v17998 (state s) (inputs i)) 1)) (Z.eqb (R.v17997 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18010 (state s) (inputs i)) 1)) (Z.eqb (R.v18009 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18022 (state s) (inputs i)) 1)) (Z.eqb (R.v18021 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18037 (state s) (inputs i)) 1)) (Z.eqb (R.v18036 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18049 (state s) (inputs i)) 1)) (Z.eqb (R.v18048 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18061 (state s) (inputs i)) 1)) (Z.eqb (R.v18060 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18076 (state s) (inputs i)) 1)) (Z.eqb (R.v18075 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18088 (state s) (inputs i)) 1)) (Z.eqb (R.v18087 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18100 (state s) (inputs i)) 1)) (Z.eqb (R.v18099 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18109 (state s) (inputs i)) 1)) (Z.eqb (R.v18108 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18124 (state s) (inputs i)) 1)) (Z.eqb (R.v18123 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18136 (state s) (inputs i)) 1)) (Z.eqb (R.v18135 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18148 (state s) (inputs i)) 1)) (Z.eqb (R.v18147 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18163 (state s) (inputs i)) 1)) (Z.eqb (R.v18162 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18175 (state s) (inputs i)) 1)) (Z.eqb (R.v18174 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18187 (state s) (inputs i)) 1)) (Z.eqb (R.v18186 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18202 (state s) (inputs i)) 1)) (Z.eqb (R.v18201 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18214 (state s) (inputs i)) 1)) (Z.eqb (R.v18213 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18226 (state s) (inputs i)) 1)) (Z.eqb (R.v18225 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18235 (state s) (inputs i)) 1)) (Z.eqb (R.v18234 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18250 (state s) (inputs i)) 1)) (Z.eqb (R.v18249 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18262 (state s) (inputs i)) 1)) (Z.eqb (R.v18261 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18274 (state s) (inputs i)) 1)) (Z.eqb (R.v18273 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18289 (state s) (inputs i)) 1)) (Z.eqb (R.v18288 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18301 (state s) (inputs i)) 1)) (Z.eqb (R.v18300 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18313 (state s) (inputs i)) 1)) (Z.eqb (R.v18312 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18328 (state s) (inputs i)) 1)) (Z.eqb (R.v18327 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18340 (state s) (inputs i)) 1)) (Z.eqb (R.v18339 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18352 (state s) (inputs i)) 1)) (Z.eqb (R.v18351 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18364 (state s) (inputs i)) 1)) (Z.eqb (R.v18363 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18379 (state s) (inputs i)) 1)) (Z.eqb (R.v18378 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18391 (state s) (inputs i)) 1)) (Z.eqb (R.v18390 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18403 (state s) (inputs i)) 1)) (Z.eqb (R.v18402 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18418 (state s) (inputs i)) 1)) (Z.eqb (R.v18417 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18430 (state s) (inputs i)) 1)) (Z.eqb (R.v18429 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18442 (state s) (inputs i)) 1)) (Z.eqb (R.v18441 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18457 (state s) (inputs i)) 1)) (Z.eqb (R.v18456 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18469 (state s) (inputs i)) 1)) (Z.eqb (R.v18468 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18481 (state s) (inputs i)) 1)) (Z.eqb (R.v18480 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18493 (state s) (inputs i)) 1)) (Z.eqb (R.v18492 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18508 (state s) (inputs i)) 1)) (Z.eqb (R.v18507 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18520 (state s) (inputs i)) 1)) (Z.eqb (R.v18519 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18532 (state s) (inputs i)) 1)) (Z.eqb (R.v18531 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18547 (state s) (inputs i)) 1)) (Z.eqb (R.v18546 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18559 (state s) (inputs i)) 1)) (Z.eqb (R.v18558 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18571 (state s) (inputs i)) 1)) (Z.eqb (R.v18570 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18586 (state s) (inputs i)) 1)) (Z.eqb (R.v18585 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18598 (state s) (inputs i)) 1)) (Z.eqb (R.v18597 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18610 (state s) (inputs i)) 1)) (Z.eqb (R.v18609 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18624 (state s) (inputs i)) 1)) (Z.eqb (R.v18623 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18636 (state s) (inputs i)) 1)) (Z.eqb (R.v18635 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18645 (state s) (inputs i)) 1)) (Z.eqb (R.v18644 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18660 (state s) (inputs i)) 1)) (Z.eqb (R.v18659 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18672 (state s) (inputs i)) 1)) (Z.eqb (R.v18671 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18684 (state s) (inputs i)) 1)) (Z.eqb (R.v18683 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18699 (state s) (inputs i)) 1)) (Z.eqb (R.v18698 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18711 (state s) (inputs i)) 1)) (Z.eqb (R.v18710 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18723 (state s) (inputs i)) 1)) (Z.eqb (R.v18722 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18738 (state s) (inputs i)) 1)) (Z.eqb (R.v18737 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18750 (state s) (inputs i)) 1)) (Z.eqb (R.v18749 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18762 (state s) (inputs i)) 1)) (Z.eqb (R.v18761 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18777 (state s) (inputs i)) 1)) (Z.eqb (R.v18776 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18789 (state s) (inputs i)) 1)) (Z.eqb (R.v18788 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18801 (state s) (inputs i)) 1)) (Z.eqb (R.v18800 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18816 (state s) (inputs i)) 1)) (Z.eqb (R.v18815 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18828 (state s) (inputs i)) 1)) (Z.eqb (R.v18827 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18840 (state s) (inputs i)) 1)) (Z.eqb (R.v18839 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18855 (state s) (inputs i)) 1)) (Z.eqb (R.v18854 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18867 (state s) (inputs i)) 1)) (Z.eqb (R.v18866 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18879 (state s) (inputs i)) 1)) (Z.eqb (R.v18878 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18894 (state s) (inputs i)) 1)) (Z.eqb (R.v18893 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18906 (state s) (inputs i)) 1)) (Z.eqb (R.v18905 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18918 (state s) (inputs i)) 1)) (Z.eqb (R.v18917 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18933 (state s) (inputs i)) 1)) (Z.eqb (R.v18932 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18945 (state s) (inputs i)) 1)) (Z.eqb (R.v18944 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18957 (state s) (inputs i)) 1)) (Z.eqb (R.v18956 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18972 (state s) (inputs i)) 1)) (Z.eqb (R.v18971 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18984 (state s) (inputs i)) 1)) (Z.eqb (R.v18983 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v18996 (state s) (inputs i)) 1)) (Z.eqb (R.v18995 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v19011 (state s) (inputs i)) 1)) (Z.eqb (R.v19010 (state s) (inputs i)) 1)
].
Definition native_checks_1 (s : N.State) (i : N.Inputs) : list bool := [
orb (negb (Zmod.eqb (N.v17737 s i) Zmod.one)) (Zmod.eqb (N.v17736 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17749 s i) Zmod.one)) (Zmod.eqb (N.v17748 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17764 s i) Zmod.one)) (Zmod.eqb (N.v17763 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17776 s i) Zmod.one)) (Zmod.eqb (N.v17775 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17788 s i) Zmod.one)) (Zmod.eqb (N.v17787 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17803 s i) Zmod.one)) (Zmod.eqb (N.v17802 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17815 s i) Zmod.one)) (Zmod.eqb (N.v17814 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17827 s i) Zmod.one)) (Zmod.eqb (N.v17826 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17842 s i) Zmod.one)) (Zmod.eqb (N.v17841 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17854 s i) Zmod.one)) (Zmod.eqb (N.v17853 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17866 s i) Zmod.one)) (Zmod.eqb (N.v17865 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17881 s i) Zmod.one)) (Zmod.eqb (N.v17880 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17893 s i) Zmod.one)) (Zmod.eqb (N.v17892 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17905 s i) Zmod.one)) (Zmod.eqb (N.v17904 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17920 s i) Zmod.one)) (Zmod.eqb (N.v17919 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17932 s i) Zmod.one)) (Zmod.eqb (N.v17931 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17944 s i) Zmod.one)) (Zmod.eqb (N.v17943 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17959 s i) Zmod.one)) (Zmod.eqb (N.v17958 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17971 s i) Zmod.one)) (Zmod.eqb (N.v17970 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17983 s i) Zmod.one)) (Zmod.eqb (N.v17982 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v17998 s i) Zmod.one)) (Zmod.eqb (N.v17997 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18010 s i) Zmod.one)) (Zmod.eqb (N.v18009 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18022 s i) Zmod.one)) (Zmod.eqb (N.v18021 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18037 s i) Zmod.one)) (Zmod.eqb (N.v18036 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18049 s i) Zmod.one)) (Zmod.eqb (N.v18048 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18061 s i) Zmod.one)) (Zmod.eqb (N.v18060 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18076 s i) Zmod.one)) (Zmod.eqb (N.v18075 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18088 s i) Zmod.one)) (Zmod.eqb (N.v18087 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18100 s i) Zmod.one)) (Zmod.eqb (N.v18099 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18109 s i) Zmod.one)) (Zmod.eqb (N.v18108 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18124 s i) Zmod.one)) (Zmod.eqb (N.v18123 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18136 s i) Zmod.one)) (Zmod.eqb (N.v18135 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18148 s i) Zmod.one)) (Zmod.eqb (N.v18147 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18163 s i) Zmod.one)) (Zmod.eqb (N.v18162 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18175 s i) Zmod.one)) (Zmod.eqb (N.v18174 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18187 s i) Zmod.one)) (Zmod.eqb (N.v18186 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18202 s i) Zmod.one)) (Zmod.eqb (N.v18201 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18214 s i) Zmod.one)) (Zmod.eqb (N.v18213 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18226 s i) Zmod.one)) (Zmod.eqb (N.v18225 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18235 s i) Zmod.one)) (Zmod.eqb (N.v18234 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18250 s i) Zmod.one)) (Zmod.eqb (N.v18249 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18262 s i) Zmod.one)) (Zmod.eqb (N.v18261 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18274 s i) Zmod.one)) (Zmod.eqb (N.v18273 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18289 s i) Zmod.one)) (Zmod.eqb (N.v18288 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18301 s i) Zmod.one)) (Zmod.eqb (N.v18300 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18313 s i) Zmod.one)) (Zmod.eqb (N.v18312 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18328 s i) Zmod.one)) (Zmod.eqb (N.v18327 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18340 s i) Zmod.one)) (Zmod.eqb (N.v18339 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18352 s i) Zmod.one)) (Zmod.eqb (N.v18351 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18364 s i) Zmod.one)) (Zmod.eqb (N.v18363 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18379 s i) Zmod.one)) (Zmod.eqb (N.v18378 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18391 s i) Zmod.one)) (Zmod.eqb (N.v18390 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18403 s i) Zmod.one)) (Zmod.eqb (N.v18402 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18418 s i) Zmod.one)) (Zmod.eqb (N.v18417 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18430 s i) Zmod.one)) (Zmod.eqb (N.v18429 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18442 s i) Zmod.one)) (Zmod.eqb (N.v18441 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18457 s i) Zmod.one)) (Zmod.eqb (N.v18456 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18469 s i) Zmod.one)) (Zmod.eqb (N.v18468 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18481 s i) Zmod.one)) (Zmod.eqb (N.v18480 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18493 s i) Zmod.one)) (Zmod.eqb (N.v18492 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18508 s i) Zmod.one)) (Zmod.eqb (N.v18507 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18520 s i) Zmod.one)) (Zmod.eqb (N.v18519 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18532 s i) Zmod.one)) (Zmod.eqb (N.v18531 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18547 s i) Zmod.one)) (Zmod.eqb (N.v18546 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18559 s i) Zmod.one)) (Zmod.eqb (N.v18558 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18571 s i) Zmod.one)) (Zmod.eqb (N.v18570 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18586 s i) Zmod.one)) (Zmod.eqb (N.v18585 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18598 s i) Zmod.one)) (Zmod.eqb (N.v18597 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18610 s i) Zmod.one)) (Zmod.eqb (N.v18609 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18624 s i) Zmod.one)) (Zmod.eqb (N.v18623 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18636 s i) Zmod.one)) (Zmod.eqb (N.v18635 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18645 s i) Zmod.one)) (Zmod.eqb (N.v18644 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18660 s i) Zmod.one)) (Zmod.eqb (N.v18659 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18672 s i) Zmod.one)) (Zmod.eqb (N.v18671 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18684 s i) Zmod.one)) (Zmod.eqb (N.v18683 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18699 s i) Zmod.one)) (Zmod.eqb (N.v18698 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18711 s i) Zmod.one)) (Zmod.eqb (N.v18710 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18723 s i) Zmod.one)) (Zmod.eqb (N.v18722 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18738 s i) Zmod.one)) (Zmod.eqb (N.v18737 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18750 s i) Zmod.one)) (Zmod.eqb (N.v18749 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18762 s i) Zmod.one)) (Zmod.eqb (N.v18761 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18777 s i) Zmod.one)) (Zmod.eqb (N.v18776 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18789 s i) Zmod.one)) (Zmod.eqb (N.v18788 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18801 s i) Zmod.one)) (Zmod.eqb (N.v18800 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18816 s i) Zmod.one)) (Zmod.eqb (N.v18815 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18828 s i) Zmod.one)) (Zmod.eqb (N.v18827 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18840 s i) Zmod.one)) (Zmod.eqb (N.v18839 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18855 s i) Zmod.one)) (Zmod.eqb (N.v18854 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18867 s i) Zmod.one)) (Zmod.eqb (N.v18866 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18879 s i) Zmod.one)) (Zmod.eqb (N.v18878 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18894 s i) Zmod.one)) (Zmod.eqb (N.v18893 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18906 s i) Zmod.one)) (Zmod.eqb (N.v18905 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18918 s i) Zmod.one)) (Zmod.eqb (N.v18917 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18933 s i) Zmod.one)) (Zmod.eqb (N.v18932 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18945 s i) Zmod.one)) (Zmod.eqb (N.v18944 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18957 s i) Zmod.one)) (Zmod.eqb (N.v18956 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18972 s i) Zmod.one)) (Zmod.eqb (N.v18971 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18984 s i) Zmod.one)) (Zmod.eqb (N.v18983 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v18996 s i) Zmod.one)) (Zmod.eqb (N.v18995 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v19011 s i) Zmod.one)) (Zmod.eqb (N.v19010 s i) Zmod.one)
].
Lemma checks_1 s i : reference_checks_1 s i = native_checks_1 s i.
Proof. unfold reference_checks_1, native_checks_1.
  rewrite ?node_17736.
  rewrite ?node_17737.
  rewrite ?node_17748.
  rewrite ?node_17749.
  rewrite ?node_17763.
  rewrite ?node_17764.
  rewrite ?node_17775.
  rewrite ?node_17776.
  rewrite ?node_17787.
  rewrite ?node_17788.
  rewrite ?node_17802.
  rewrite ?node_17803.
  rewrite ?node_17814.
  rewrite ?node_17815.
  rewrite ?node_17826.
  rewrite ?node_17827.
  rewrite ?node_17841.
  rewrite ?node_17842.
  rewrite ?node_17853.
  rewrite ?node_17854.
  rewrite ?node_17865.
  rewrite ?node_17866.
  rewrite ?node_17880.
  rewrite ?node_17881.
  rewrite ?node_17892.
  rewrite ?node_17893.
  rewrite ?node_17904.
  rewrite ?node_17905.
  rewrite ?node_17919.
  rewrite ?node_17920.
  rewrite ?node_17931.
  rewrite ?node_17932.
  rewrite ?node_17943.
  rewrite ?node_17944.
  rewrite ?node_17958.
  rewrite ?node_17959.
  rewrite ?node_17970.
  rewrite ?node_17971.
  rewrite ?node_17982.
  rewrite ?node_17983.
  rewrite ?node_17997.
  rewrite ?node_17998.
  rewrite ?node_18009.
  rewrite ?node_18010.
  rewrite ?node_18021.
  rewrite ?node_18022.
  rewrite ?node_18036.
  rewrite ?node_18037.
  rewrite ?node_18048.
  rewrite ?node_18049.
  rewrite ?node_18060.
  rewrite ?node_18061.
  rewrite ?node_18075.
  rewrite ?node_18076.
  rewrite ?node_18087.
  rewrite ?node_18088.
  rewrite ?node_18099.
  rewrite ?node_18100.
  rewrite ?node_18108.
  rewrite ?node_18109.
  rewrite ?node_18123.
  rewrite ?node_18124.
  rewrite ?node_18135.
  rewrite ?node_18136.
  rewrite ?node_18147.
  rewrite ?node_18148.
  rewrite ?node_18162.
  rewrite ?node_18163.
  rewrite ?node_18174.
  rewrite ?node_18175.
  rewrite ?node_18186.
  rewrite ?node_18187.
  rewrite ?node_18201.
  rewrite ?node_18202.
  rewrite ?node_18213.
  rewrite ?node_18214.
  rewrite ?node_18225.
  rewrite ?node_18226.
  rewrite ?node_18234.
  rewrite ?node_18235.
  rewrite ?node_18249.
  rewrite ?node_18250.
  rewrite ?node_18261.
  rewrite ?node_18262.
  rewrite ?node_18273.
  rewrite ?node_18274.
  rewrite ?node_18288.
  rewrite ?node_18289.
  rewrite ?node_18300.
  rewrite ?node_18301.
  rewrite ?node_18312.
  rewrite ?node_18313.
  rewrite ?node_18327.
  rewrite ?node_18328.
  rewrite ?node_18339.
  rewrite ?node_18340.
  rewrite ?node_18351.
  rewrite ?node_18352.
  rewrite ?node_18363.
  rewrite ?node_18364.
  rewrite ?node_18378.
  rewrite ?node_18379.
  rewrite ?node_18390.
  rewrite ?node_18391.
  rewrite ?node_18402.
  rewrite ?node_18403.
  rewrite ?node_18417.
  rewrite ?node_18418.
  rewrite ?node_18429.
  rewrite ?node_18430.
  rewrite ?node_18441.
  rewrite ?node_18442.
  rewrite ?node_18456.
  rewrite ?node_18457.
  rewrite ?node_18468.
  rewrite ?node_18469.
  rewrite ?node_18480.
  rewrite ?node_18481.
  rewrite ?node_18492.
  rewrite ?node_18493.
  rewrite ?node_18507.
  rewrite ?node_18508.
  rewrite ?node_18519.
  rewrite ?node_18520.
  rewrite ?node_18531.
  rewrite ?node_18532.
  rewrite ?node_18546.
  rewrite ?node_18547.
  rewrite ?node_18558.
  rewrite ?node_18559.
  rewrite ?node_18570.
  rewrite ?node_18571.
  rewrite ?node_18585.
  rewrite ?node_18586.
  rewrite ?node_18597.
  rewrite ?node_18598.
  rewrite ?node_18609.
  rewrite ?node_18610.
  rewrite ?node_18623.
  rewrite ?node_18624.
  rewrite ?node_18635.
  rewrite ?node_18636.
  rewrite ?node_18644.
  rewrite ?node_18645.
  rewrite ?node_18659.
  rewrite ?node_18660.
  rewrite ?node_18671.
  rewrite ?node_18672.
  rewrite ?node_18683.
  rewrite ?node_18684.
  rewrite ?node_18698.
  rewrite ?node_18699.
  rewrite ?node_18710.
  rewrite ?node_18711.
  rewrite ?node_18722.
  rewrite ?node_18723.
  rewrite ?node_18737.
  rewrite ?node_18738.
  rewrite ?node_18749.
  rewrite ?node_18750.
  rewrite ?node_18761.
  rewrite ?node_18762.
  rewrite ?node_18776.
  rewrite ?node_18777.
  rewrite ?node_18788.
  rewrite ?node_18789.
  rewrite ?node_18800.
  rewrite ?node_18801.
  rewrite ?node_18815.
  rewrite ?node_18816.
  rewrite ?node_18827.
  rewrite ?node_18828.
  rewrite ?node_18839.
  rewrite ?node_18840.
  rewrite ?node_18854.
  rewrite ?node_18855.
  rewrite ?node_18866.
  rewrite ?node_18867.
  rewrite ?node_18878.
  rewrite ?node_18879.
  rewrite ?node_18893.
  rewrite ?node_18894.
  rewrite ?node_18905.
  rewrite ?node_18906.
  rewrite ?node_18917.
  rewrite ?node_18918.
  rewrite ?node_18932.
  rewrite ?node_18933.
  rewrite ?node_18944.
  rewrite ?node_18945.
  rewrite ?node_18956.
  rewrite ?node_18957.
  rewrite ?node_18971.
  rewrite ?node_18972.
  rewrite ?node_18983.
  rewrite ?node_18984.
  rewrite ?node_18995.
  rewrite ?node_18996.
  rewrite ?node_19010.
  rewrite ?node_19011.
  reflexivity.
Qed.

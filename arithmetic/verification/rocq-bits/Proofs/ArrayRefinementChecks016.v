From Stdlib Require Import ZArith List Bool Zmod.Bits.
From BitsProofs Require Import ArrayRefinementNodes038.
Import ListNotations.
Open Scope Z_scope.
Local Opaque R.v37052 N.v37052 R.v37053 N.v37053 R.v37063 N.v37063 R.v37064 N.v37064 R.v37075 N.v37075 R.v37076 N.v37076 R.v37090 N.v37090 R.v37091 N.v37091 R.v37102 N.v37102 R.v37103 N.v37103 R.v37114 N.v37114 R.v37115 N.v37115 R.v37129 N.v37129 R.v37130 N.v37130 R.v37141 N.v37141 R.v37142 N.v37142 R.v37153 N.v37153 R.v37154 N.v37154 R.v37168 N.v37168 R.v37169 N.v37169 R.v37180 N.v37180 R.v37181 N.v37181 R.v37192 N.v37192 R.v37193 N.v37193 R.v37206 N.v37206 R.v37207 N.v37207 R.v37217 N.v37217 R.v37218 N.v37218 R.v37229 N.v37229 R.v37230 N.v37230 R.v37244 N.v37244 R.v37245 N.v37245 R.v37256 N.v37256 R.v37257 N.v37257 R.v37268 N.v37268 R.v37269 N.v37269 R.v37283 N.v37283 R.v37284 N.v37284 R.v37295 N.v37295 R.v37296 N.v37296 R.v37307 N.v37307 R.v37308 N.v37308 R.v37319 N.v37319 R.v37320 N.v37320 R.v37333 N.v37333 R.v37334 N.v37334 R.v37344 N.v37344 R.v37345 N.v37345 R.v37356 N.v37356 R.v37357 N.v37357 R.v37368 N.v37368 R.v37369 N.v37369 R.v37383 N.v37383 R.v37384 N.v37384 R.v37395 N.v37395 R.v37396 N.v37396 R.v37407 N.v37407 R.v37408 N.v37408 R.v37416 N.v37416 R.v37417 N.v37417 R.v37430 N.v37430 R.v37431 N.v37431 R.v37441 N.v37441 R.v37442 N.v37442 R.v37453 N.v37453 R.v37454 N.v37454 R.v37462 N.v37462 R.v37463 N.v37463 R.v37477 N.v37477 R.v37478 N.v37478 R.v37489 N.v37489 R.v37490 N.v37490 R.v37501 N.v37501 R.v37502 N.v37502 R.v37515 N.v37515 R.v37516 N.v37516 R.v37526 N.v37526 R.v37527 N.v37527 R.v37538 N.v37538 R.v37539 N.v37539 R.v37553 N.v37553 R.v37554 N.v37554 R.v37565 N.v37565 R.v37566 N.v37566 R.v37577 N.v37577 R.v37578 N.v37578 R.v37591 N.v37591 R.v37592 N.v37592 R.v37602 N.v37602 R.v37603 N.v37603 R.v37614 N.v37614 R.v37615 N.v37615 R.v37626 N.v37626 R.v37627 N.v37627 R.v37637 N.v37637 R.v37638 N.v37638 R.v37646 N.v37646 R.v37647 N.v37647 R.v37654 N.v37654 R.v37655 N.v37655 R.v37663 N.v37663 R.v37664 N.v37664 R.v37672 N.v37672 R.v37673 N.v37673 R.v37681 N.v37681 R.v37682 N.v37682 R.v37690 N.v37690 R.v37691 N.v37691 R.v37699 N.v37699 R.v37700 N.v37700 R.v37711 N.v37711 R.v37712 N.v37712 R.v37723 N.v37723 R.v37724 N.v37724 R.v37735 N.v37735 R.v37736 N.v37736 R.v37749 N.v37749 R.v37750 N.v37750 R.v37761 N.v37761 R.v37762 N.v37762 R.v37770 N.v37770 R.v37771 N.v37771 R.v37785 N.v37785 R.v37786 N.v37786 R.v37797 N.v37797 R.v37798 N.v37798 R.v37809 N.v37809 R.v37810 N.v37810 R.v37824 N.v37824 R.v37825 N.v37825 R.v37836 N.v37836 R.v37837 N.v37837 R.v37848 N.v37848 R.v37849 N.v37849 R.v37863 N.v37863 R.v37864 N.v37864 R.v37875 N.v37875 R.v37876 N.v37876 R.v37887 N.v37887 R.v37888 N.v37888 R.v37902 N.v37902 R.v37903 N.v37903 R.v37914 N.v37914 R.v37915 N.v37915 R.v37926 N.v37926 R.v37927 N.v37927 R.v37941 N.v37941 R.v37942 N.v37942 R.v37953 N.v37953 R.v37954 N.v37954 R.v37965 N.v37965 R.v37966 N.v37966 R.v37980 N.v37980 R.v37981 N.v37981 R.v37992 N.v37992 R.v37993 N.v37993 R.v38004 N.v38004 R.v38005 N.v38005 R.v38019 N.v38019 R.v38020 N.v38020 R.v38031 N.v38031 R.v38032 N.v38032 R.v38043 N.v38043 R.v38044 N.v38044 R.v38058 N.v38058 R.v38059 N.v38059 R.v38070 N.v38070 R.v38071 N.v38071 R.v38082 N.v38082 R.v38083 N.v38083 R.v38091 N.v38091 R.v38092 N.v38092 R.v38106 N.v38106 R.v38107 N.v38107 R.v38118 N.v38118 R.v38119 N.v38119 R.v38130 N.v38130 R.v38131 N.v38131 R.v38139 N.v38139 R.v38140 N.v38140 R.v38154 N.v38154 R.v38155 N.v38155 R.v38166 N.v38166 R.v38167 N.v38167 R.v38178 N.v38178 R.v38179 N.v38179 R.v38187 N.v38187 R.v38188 N.v38188 R.v38202 N.v38202 R.v38203 N.v38203 R.v38214 N.v38214 R.v38215 N.v38215 R.v38226 N.v38226 R.v38227 N.v38227 R.v38235 N.v38235 R.v38236 N.v38236 R.v38250 N.v38250 R.v38251 N.v38251 R.v38262 N.v38262 R.v38263 N.v38263.
Definition reference_checks_16 (s : N.State) (i : N.Inputs) : list bool := [
orb (negb (Z.eqb (R.v37053 (state s) (inputs i)) 1)) (Z.eqb (R.v37052 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37064 (state s) (inputs i)) 1)) (Z.eqb (R.v37063 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37076 (state s) (inputs i)) 1)) (Z.eqb (R.v37075 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37091 (state s) (inputs i)) 1)) (Z.eqb (R.v37090 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37103 (state s) (inputs i)) 1)) (Z.eqb (R.v37102 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37115 (state s) (inputs i)) 1)) (Z.eqb (R.v37114 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37130 (state s) (inputs i)) 1)) (Z.eqb (R.v37129 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37142 (state s) (inputs i)) 1)) (Z.eqb (R.v37141 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37154 (state s) (inputs i)) 1)) (Z.eqb (R.v37153 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37169 (state s) (inputs i)) 1)) (Z.eqb (R.v37168 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37181 (state s) (inputs i)) 1)) (Z.eqb (R.v37180 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37193 (state s) (inputs i)) 1)) (Z.eqb (R.v37192 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37207 (state s) (inputs i)) 1)) (Z.eqb (R.v37206 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37218 (state s) (inputs i)) 1)) (Z.eqb (R.v37217 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37230 (state s) (inputs i)) 1)) (Z.eqb (R.v37229 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37245 (state s) (inputs i)) 1)) (Z.eqb (R.v37244 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37257 (state s) (inputs i)) 1)) (Z.eqb (R.v37256 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37269 (state s) (inputs i)) 1)) (Z.eqb (R.v37268 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37284 (state s) (inputs i)) 1)) (Z.eqb (R.v37283 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37296 (state s) (inputs i)) 1)) (Z.eqb (R.v37295 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37308 (state s) (inputs i)) 1)) (Z.eqb (R.v37307 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37320 (state s) (inputs i)) 1)) (Z.eqb (R.v37319 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37334 (state s) (inputs i)) 1)) (Z.eqb (R.v37333 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37345 (state s) (inputs i)) 1)) (Z.eqb (R.v37344 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37357 (state s) (inputs i)) 1)) (Z.eqb (R.v37356 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37369 (state s) (inputs i)) 1)) (Z.eqb (R.v37368 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37384 (state s) (inputs i)) 1)) (Z.eqb (R.v37383 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37396 (state s) (inputs i)) 1)) (Z.eqb (R.v37395 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37408 (state s) (inputs i)) 1)) (Z.eqb (R.v37407 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37417 (state s) (inputs i)) 1)) (Z.eqb (R.v37416 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37431 (state s) (inputs i)) 1)) (Z.eqb (R.v37430 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37442 (state s) (inputs i)) 1)) (Z.eqb (R.v37441 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37454 (state s) (inputs i)) 1)) (Z.eqb (R.v37453 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37463 (state s) (inputs i)) 1)) (Z.eqb (R.v37462 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37478 (state s) (inputs i)) 1)) (Z.eqb (R.v37477 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37490 (state s) (inputs i)) 1)) (Z.eqb (R.v37489 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37502 (state s) (inputs i)) 1)) (Z.eqb (R.v37501 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37516 (state s) (inputs i)) 1)) (Z.eqb (R.v37515 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37527 (state s) (inputs i)) 1)) (Z.eqb (R.v37526 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37539 (state s) (inputs i)) 1)) (Z.eqb (R.v37538 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37554 (state s) (inputs i)) 1)) (Z.eqb (R.v37553 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37566 (state s) (inputs i)) 1)) (Z.eqb (R.v37565 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37578 (state s) (inputs i)) 1)) (Z.eqb (R.v37577 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37592 (state s) (inputs i)) 1)) (Z.eqb (R.v37591 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37603 (state s) (inputs i)) 1)) (Z.eqb (R.v37602 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37615 (state s) (inputs i)) 1)) (Z.eqb (R.v37614 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37627 (state s) (inputs i)) 1)) (Z.eqb (R.v37626 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37638 (state s) (inputs i)) 1)) (Z.eqb (R.v37637 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37647 (state s) (inputs i)) 1)) (Z.eqb (R.v37646 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37655 (state s) (inputs i)) 1)) (Z.eqb (R.v37654 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37664 (state s) (inputs i)) 1)) (Z.eqb (R.v37663 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37673 (state s) (inputs i)) 1)) (Z.eqb (R.v37672 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37682 (state s) (inputs i)) 1)) (Z.eqb (R.v37681 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37691 (state s) (inputs i)) 1)) (Z.eqb (R.v37690 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37700 (state s) (inputs i)) 1)) (Z.eqb (R.v37699 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37712 (state s) (inputs i)) 1)) (Z.eqb (R.v37711 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37724 (state s) (inputs i)) 1)) (Z.eqb (R.v37723 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37736 (state s) (inputs i)) 1)) (Z.eqb (R.v37735 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37750 (state s) (inputs i)) 1)) (Z.eqb (R.v37749 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37762 (state s) (inputs i)) 1)) (Z.eqb (R.v37761 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37771 (state s) (inputs i)) 1)) (Z.eqb (R.v37770 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37786 (state s) (inputs i)) 1)) (Z.eqb (R.v37785 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37798 (state s) (inputs i)) 1)) (Z.eqb (R.v37797 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37810 (state s) (inputs i)) 1)) (Z.eqb (R.v37809 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37825 (state s) (inputs i)) 1)) (Z.eqb (R.v37824 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37837 (state s) (inputs i)) 1)) (Z.eqb (R.v37836 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37849 (state s) (inputs i)) 1)) (Z.eqb (R.v37848 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37864 (state s) (inputs i)) 1)) (Z.eqb (R.v37863 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37876 (state s) (inputs i)) 1)) (Z.eqb (R.v37875 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37888 (state s) (inputs i)) 1)) (Z.eqb (R.v37887 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37903 (state s) (inputs i)) 1)) (Z.eqb (R.v37902 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37915 (state s) (inputs i)) 1)) (Z.eqb (R.v37914 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37927 (state s) (inputs i)) 1)) (Z.eqb (R.v37926 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37942 (state s) (inputs i)) 1)) (Z.eqb (R.v37941 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37954 (state s) (inputs i)) 1)) (Z.eqb (R.v37953 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37966 (state s) (inputs i)) 1)) (Z.eqb (R.v37965 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37981 (state s) (inputs i)) 1)) (Z.eqb (R.v37980 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v37993 (state s) (inputs i)) 1)) (Z.eqb (R.v37992 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v38005 (state s) (inputs i)) 1)) (Z.eqb (R.v38004 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v38020 (state s) (inputs i)) 1)) (Z.eqb (R.v38019 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v38032 (state s) (inputs i)) 1)) (Z.eqb (R.v38031 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v38044 (state s) (inputs i)) 1)) (Z.eqb (R.v38043 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v38059 (state s) (inputs i)) 1)) (Z.eqb (R.v38058 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v38071 (state s) (inputs i)) 1)) (Z.eqb (R.v38070 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v38083 (state s) (inputs i)) 1)) (Z.eqb (R.v38082 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v38092 (state s) (inputs i)) 1)) (Z.eqb (R.v38091 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v38107 (state s) (inputs i)) 1)) (Z.eqb (R.v38106 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v38119 (state s) (inputs i)) 1)) (Z.eqb (R.v38118 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v38131 (state s) (inputs i)) 1)) (Z.eqb (R.v38130 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v38140 (state s) (inputs i)) 1)) (Z.eqb (R.v38139 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v38155 (state s) (inputs i)) 1)) (Z.eqb (R.v38154 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v38167 (state s) (inputs i)) 1)) (Z.eqb (R.v38166 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v38179 (state s) (inputs i)) 1)) (Z.eqb (R.v38178 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v38188 (state s) (inputs i)) 1)) (Z.eqb (R.v38187 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v38203 (state s) (inputs i)) 1)) (Z.eqb (R.v38202 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v38215 (state s) (inputs i)) 1)) (Z.eqb (R.v38214 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v38227 (state s) (inputs i)) 1)) (Z.eqb (R.v38226 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v38236 (state s) (inputs i)) 1)) (Z.eqb (R.v38235 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v38251 (state s) (inputs i)) 1)) (Z.eqb (R.v38250 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v38263 (state s) (inputs i)) 1)) (Z.eqb (R.v38262 (state s) (inputs i)) 1)
].
Definition native_checks_16 (s : N.State) (i : N.Inputs) : list bool := [
orb (negb (Zmod.eqb (N.v37053 s i) Zmod.one)) (Zmod.eqb (N.v37052 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37064 s i) Zmod.one)) (Zmod.eqb (N.v37063 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37076 s i) Zmod.one)) (Zmod.eqb (N.v37075 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37091 s i) Zmod.one)) (Zmod.eqb (N.v37090 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37103 s i) Zmod.one)) (Zmod.eqb (N.v37102 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37115 s i) Zmod.one)) (Zmod.eqb (N.v37114 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37130 s i) Zmod.one)) (Zmod.eqb (N.v37129 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37142 s i) Zmod.one)) (Zmod.eqb (N.v37141 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37154 s i) Zmod.one)) (Zmod.eqb (N.v37153 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37169 s i) Zmod.one)) (Zmod.eqb (N.v37168 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37181 s i) Zmod.one)) (Zmod.eqb (N.v37180 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37193 s i) Zmod.one)) (Zmod.eqb (N.v37192 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37207 s i) Zmod.one)) (Zmod.eqb (N.v37206 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37218 s i) Zmod.one)) (Zmod.eqb (N.v37217 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37230 s i) Zmod.one)) (Zmod.eqb (N.v37229 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37245 s i) Zmod.one)) (Zmod.eqb (N.v37244 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37257 s i) Zmod.one)) (Zmod.eqb (N.v37256 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37269 s i) Zmod.one)) (Zmod.eqb (N.v37268 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37284 s i) Zmod.one)) (Zmod.eqb (N.v37283 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37296 s i) Zmod.one)) (Zmod.eqb (N.v37295 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37308 s i) Zmod.one)) (Zmod.eqb (N.v37307 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37320 s i) Zmod.one)) (Zmod.eqb (N.v37319 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37334 s i) Zmod.one)) (Zmod.eqb (N.v37333 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37345 s i) Zmod.one)) (Zmod.eqb (N.v37344 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37357 s i) Zmod.one)) (Zmod.eqb (N.v37356 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37369 s i) Zmod.one)) (Zmod.eqb (N.v37368 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37384 s i) Zmod.one)) (Zmod.eqb (N.v37383 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37396 s i) Zmod.one)) (Zmod.eqb (N.v37395 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37408 s i) Zmod.one)) (Zmod.eqb (N.v37407 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37417 s i) Zmod.one)) (Zmod.eqb (N.v37416 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37431 s i) Zmod.one)) (Zmod.eqb (N.v37430 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37442 s i) Zmod.one)) (Zmod.eqb (N.v37441 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37454 s i) Zmod.one)) (Zmod.eqb (N.v37453 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37463 s i) Zmod.one)) (Zmod.eqb (N.v37462 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37478 s i) Zmod.one)) (Zmod.eqb (N.v37477 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37490 s i) Zmod.one)) (Zmod.eqb (N.v37489 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37502 s i) Zmod.one)) (Zmod.eqb (N.v37501 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37516 s i) Zmod.one)) (Zmod.eqb (N.v37515 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37527 s i) Zmod.one)) (Zmod.eqb (N.v37526 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37539 s i) Zmod.one)) (Zmod.eqb (N.v37538 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37554 s i) Zmod.one)) (Zmod.eqb (N.v37553 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37566 s i) Zmod.one)) (Zmod.eqb (N.v37565 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37578 s i) Zmod.one)) (Zmod.eqb (N.v37577 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37592 s i) Zmod.one)) (Zmod.eqb (N.v37591 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37603 s i) Zmod.one)) (Zmod.eqb (N.v37602 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37615 s i) Zmod.one)) (Zmod.eqb (N.v37614 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37627 s i) Zmod.one)) (Zmod.eqb (N.v37626 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37638 s i) Zmod.one)) (Zmod.eqb (N.v37637 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37647 s i) Zmod.one)) (Zmod.eqb (N.v37646 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37655 s i) Zmod.one)) (Zmod.eqb (N.v37654 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37664 s i) Zmod.one)) (Zmod.eqb (N.v37663 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37673 s i) Zmod.one)) (Zmod.eqb (N.v37672 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37682 s i) Zmod.one)) (Zmod.eqb (N.v37681 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37691 s i) Zmod.one)) (Zmod.eqb (N.v37690 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37700 s i) Zmod.one)) (Zmod.eqb (N.v37699 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37712 s i) Zmod.one)) (Zmod.eqb (N.v37711 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37724 s i) Zmod.one)) (Zmod.eqb (N.v37723 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37736 s i) Zmod.one)) (Zmod.eqb (N.v37735 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37750 s i) Zmod.one)) (Zmod.eqb (N.v37749 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37762 s i) Zmod.one)) (Zmod.eqb (N.v37761 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37771 s i) Zmod.one)) (Zmod.eqb (N.v37770 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37786 s i) Zmod.one)) (Zmod.eqb (N.v37785 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37798 s i) Zmod.one)) (Zmod.eqb (N.v37797 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37810 s i) Zmod.one)) (Zmod.eqb (N.v37809 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37825 s i) Zmod.one)) (Zmod.eqb (N.v37824 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37837 s i) Zmod.one)) (Zmod.eqb (N.v37836 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37849 s i) Zmod.one)) (Zmod.eqb (N.v37848 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37864 s i) Zmod.one)) (Zmod.eqb (N.v37863 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37876 s i) Zmod.one)) (Zmod.eqb (N.v37875 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37888 s i) Zmod.one)) (Zmod.eqb (N.v37887 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37903 s i) Zmod.one)) (Zmod.eqb (N.v37902 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37915 s i) Zmod.one)) (Zmod.eqb (N.v37914 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37927 s i) Zmod.one)) (Zmod.eqb (N.v37926 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37942 s i) Zmod.one)) (Zmod.eqb (N.v37941 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37954 s i) Zmod.one)) (Zmod.eqb (N.v37953 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37966 s i) Zmod.one)) (Zmod.eqb (N.v37965 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37981 s i) Zmod.one)) (Zmod.eqb (N.v37980 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v37993 s i) Zmod.one)) (Zmod.eqb (N.v37992 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v38005 s i) Zmod.one)) (Zmod.eqb (N.v38004 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v38020 s i) Zmod.one)) (Zmod.eqb (N.v38019 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v38032 s i) Zmod.one)) (Zmod.eqb (N.v38031 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v38044 s i) Zmod.one)) (Zmod.eqb (N.v38043 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v38059 s i) Zmod.one)) (Zmod.eqb (N.v38058 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v38071 s i) Zmod.one)) (Zmod.eqb (N.v38070 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v38083 s i) Zmod.one)) (Zmod.eqb (N.v38082 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v38092 s i) Zmod.one)) (Zmod.eqb (N.v38091 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v38107 s i) Zmod.one)) (Zmod.eqb (N.v38106 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v38119 s i) Zmod.one)) (Zmod.eqb (N.v38118 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v38131 s i) Zmod.one)) (Zmod.eqb (N.v38130 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v38140 s i) Zmod.one)) (Zmod.eqb (N.v38139 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v38155 s i) Zmod.one)) (Zmod.eqb (N.v38154 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v38167 s i) Zmod.one)) (Zmod.eqb (N.v38166 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v38179 s i) Zmod.one)) (Zmod.eqb (N.v38178 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v38188 s i) Zmod.one)) (Zmod.eqb (N.v38187 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v38203 s i) Zmod.one)) (Zmod.eqb (N.v38202 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v38215 s i) Zmod.one)) (Zmod.eqb (N.v38214 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v38227 s i) Zmod.one)) (Zmod.eqb (N.v38226 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v38236 s i) Zmod.one)) (Zmod.eqb (N.v38235 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v38251 s i) Zmod.one)) (Zmod.eqb (N.v38250 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v38263 s i) Zmod.one)) (Zmod.eqb (N.v38262 s i) Zmod.one)
].
Lemma checks_16 s i : reference_checks_16 s i = native_checks_16 s i.
Proof. unfold reference_checks_16, native_checks_16.
  rewrite ?node_37052.
  rewrite ?node_37053.
  rewrite ?node_37063.
  rewrite ?node_37064.
  rewrite ?node_37075.
  rewrite ?node_37076.
  rewrite ?node_37090.
  rewrite ?node_37091.
  rewrite ?node_37102.
  rewrite ?node_37103.
  rewrite ?node_37114.
  rewrite ?node_37115.
  rewrite ?node_37129.
  rewrite ?node_37130.
  rewrite ?node_37141.
  rewrite ?node_37142.
  rewrite ?node_37153.
  rewrite ?node_37154.
  rewrite ?node_37168.
  rewrite ?node_37169.
  rewrite ?node_37180.
  rewrite ?node_37181.
  rewrite ?node_37192.
  rewrite ?node_37193.
  rewrite ?node_37206.
  rewrite ?node_37207.
  rewrite ?node_37217.
  rewrite ?node_37218.
  rewrite ?node_37229.
  rewrite ?node_37230.
  rewrite ?node_37244.
  rewrite ?node_37245.
  rewrite ?node_37256.
  rewrite ?node_37257.
  rewrite ?node_37268.
  rewrite ?node_37269.
  rewrite ?node_37283.
  rewrite ?node_37284.
  rewrite ?node_37295.
  rewrite ?node_37296.
  rewrite ?node_37307.
  rewrite ?node_37308.
  rewrite ?node_37319.
  rewrite ?node_37320.
  rewrite ?node_37333.
  rewrite ?node_37334.
  rewrite ?node_37344.
  rewrite ?node_37345.
  rewrite ?node_37356.
  rewrite ?node_37357.
  rewrite ?node_37368.
  rewrite ?node_37369.
  rewrite ?node_37383.
  rewrite ?node_37384.
  rewrite ?node_37395.
  rewrite ?node_37396.
  rewrite ?node_37407.
  rewrite ?node_37408.
  rewrite ?node_37416.
  rewrite ?node_37417.
  rewrite ?node_37430.
  rewrite ?node_37431.
  rewrite ?node_37441.
  rewrite ?node_37442.
  rewrite ?node_37453.
  rewrite ?node_37454.
  rewrite ?node_37462.
  rewrite ?node_37463.
  rewrite ?node_37477.
  rewrite ?node_37478.
  rewrite ?node_37489.
  rewrite ?node_37490.
  rewrite ?node_37501.
  rewrite ?node_37502.
  rewrite ?node_37515.
  rewrite ?node_37516.
  rewrite ?node_37526.
  rewrite ?node_37527.
  rewrite ?node_37538.
  rewrite ?node_37539.
  rewrite ?node_37553.
  rewrite ?node_37554.
  rewrite ?node_37565.
  rewrite ?node_37566.
  rewrite ?node_37577.
  rewrite ?node_37578.
  rewrite ?node_37591.
  rewrite ?node_37592.
  rewrite ?node_37602.
  rewrite ?node_37603.
  rewrite ?node_37614.
  rewrite ?node_37615.
  rewrite ?node_37626.
  rewrite ?node_37627.
  rewrite ?node_37637.
  rewrite ?node_37638.
  rewrite ?node_37646.
  rewrite ?node_37647.
  rewrite ?node_37654.
  rewrite ?node_37655.
  rewrite ?node_37663.
  rewrite ?node_37664.
  rewrite ?node_37672.
  rewrite ?node_37673.
  rewrite ?node_37681.
  rewrite ?node_37682.
  rewrite ?node_37690.
  rewrite ?node_37691.
  rewrite ?node_37699.
  rewrite ?node_37700.
  rewrite ?node_37711.
  rewrite ?node_37712.
  rewrite ?node_37723.
  rewrite ?node_37724.
  rewrite ?node_37735.
  rewrite ?node_37736.
  rewrite ?node_37749.
  rewrite ?node_37750.
  rewrite ?node_37761.
  rewrite ?node_37762.
  rewrite ?node_37770.
  rewrite ?node_37771.
  rewrite ?node_37785.
  rewrite ?node_37786.
  rewrite ?node_37797.
  rewrite ?node_37798.
  rewrite ?node_37809.
  rewrite ?node_37810.
  rewrite ?node_37824.
  rewrite ?node_37825.
  rewrite ?node_37836.
  rewrite ?node_37837.
  rewrite ?node_37848.
  rewrite ?node_37849.
  rewrite ?node_37863.
  rewrite ?node_37864.
  rewrite ?node_37875.
  rewrite ?node_37876.
  rewrite ?node_37887.
  rewrite ?node_37888.
  rewrite ?node_37902.
  rewrite ?node_37903.
  rewrite ?node_37914.
  rewrite ?node_37915.
  rewrite ?node_37926.
  rewrite ?node_37927.
  rewrite ?node_37941.
  rewrite ?node_37942.
  rewrite ?node_37953.
  rewrite ?node_37954.
  rewrite ?node_37965.
  rewrite ?node_37966.
  rewrite ?node_37980.
  rewrite ?node_37981.
  rewrite ?node_37992.
  rewrite ?node_37993.
  rewrite ?node_38004.
  rewrite ?node_38005.
  rewrite ?node_38019.
  rewrite ?node_38020.
  rewrite ?node_38031.
  rewrite ?node_38032.
  rewrite ?node_38043.
  rewrite ?node_38044.
  rewrite ?node_38058.
  rewrite ?node_38059.
  rewrite ?node_38070.
  rewrite ?node_38071.
  rewrite ?node_38082.
  rewrite ?node_38083.
  rewrite ?node_38091.
  rewrite ?node_38092.
  rewrite ?node_38106.
  rewrite ?node_38107.
  rewrite ?node_38118.
  rewrite ?node_38119.
  rewrite ?node_38130.
  rewrite ?node_38131.
  rewrite ?node_38139.
  rewrite ?node_38140.
  rewrite ?node_38154.
  rewrite ?node_38155.
  rewrite ?node_38166.
  rewrite ?node_38167.
  rewrite ?node_38178.
  rewrite ?node_38179.
  rewrite ?node_38187.
  rewrite ?node_38188.
  rewrite ?node_38202.
  rewrite ?node_38203.
  rewrite ?node_38214.
  rewrite ?node_38215.
  rewrite ?node_38226.
  rewrite ?node_38227.
  rewrite ?node_38235.
  rewrite ?node_38236.
  rewrite ?node_38250.
  rewrite ?node_38251.
  rewrite ?node_38262.
  rewrite ?node_38263.
  reflexivity.
Qed.

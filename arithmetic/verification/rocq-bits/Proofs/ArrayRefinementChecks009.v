From Stdlib Require Import ZArith List Bool Zmod.Bits.
From BitsProofs Require Import ArrayRefinementNodes029.
Import ListNotations.
Open Scope Z_scope.
Local Opaque R.v28057 N.v28057 R.v28058 N.v28058 R.v28072 N.v28072 R.v28073 N.v28073 R.v28084 N.v28084 R.v28085 N.v28085 R.v28096 N.v28096 R.v28097 N.v28097 R.v28111 N.v28111 R.v28112 N.v28112 R.v28123 N.v28123 R.v28124 N.v28124 R.v28135 N.v28135 R.v28136 N.v28136 R.v28150 N.v28150 R.v28151 N.v28151 R.v28162 N.v28162 R.v28163 N.v28163 R.v28174 N.v28174 R.v28175 N.v28175 R.v28189 N.v28189 R.v28190 N.v28190 R.v28201 N.v28201 R.v28202 N.v28202 R.v28213 N.v28213 R.v28214 N.v28214 R.v28228 N.v28228 R.v28229 N.v28229 R.v28240 N.v28240 R.v28241 N.v28241 R.v28252 N.v28252 R.v28253 N.v28253 R.v28267 N.v28267 R.v28268 N.v28268 R.v28279 N.v28279 R.v28280 N.v28280 R.v28291 N.v28291 R.v28292 N.v28292 R.v28306 N.v28306 R.v28307 N.v28307 R.v28318 N.v28318 R.v28319 N.v28319 R.v28330 N.v28330 R.v28331 N.v28331 R.v28344 N.v28344 R.v28345 N.v28345 R.v28355 N.v28355 R.v28356 N.v28356 R.v28367 N.v28367 R.v28368 N.v28368 R.v28382 N.v28382 R.v28383 N.v28383 R.v28394 N.v28394 R.v28395 N.v28395 R.v28406 N.v28406 R.v28407 N.v28407 R.v28421 N.v28421 R.v28422 N.v28422 R.v28433 N.v28433 R.v28434 N.v28434 R.v28445 N.v28445 R.v28446 N.v28446 R.v28460 N.v28460 R.v28461 N.v28461 R.v28472 N.v28472 R.v28473 N.v28473 R.v28484 N.v28484 R.v28485 N.v28485 R.v28499 N.v28499 R.v28500 N.v28500 R.v28511 N.v28511 R.v28512 N.v28512 R.v28523 N.v28523 R.v28524 N.v28524 R.v28538 N.v28538 R.v28539 N.v28539 R.v28550 N.v28550 R.v28551 N.v28551 R.v28562 N.v28562 R.v28563 N.v28563 R.v28577 N.v28577 R.v28578 N.v28578 R.v28589 N.v28589 R.v28590 N.v28590 R.v28601 N.v28601 R.v28602 N.v28602 R.v28616 N.v28616 R.v28617 N.v28617 R.v28628 N.v28628 R.v28629 N.v28629 R.v28640 N.v28640 R.v28641 N.v28641 R.v28655 N.v28655 R.v28656 N.v28656 R.v28667 N.v28667 R.v28668 N.v28668 R.v28679 N.v28679 R.v28680 N.v28680 R.v28694 N.v28694 R.v28695 N.v28695 R.v28706 N.v28706 R.v28707 N.v28707 R.v28718 N.v28718 R.v28719 N.v28719 R.v28733 N.v28733 R.v28734 N.v28734 R.v28745 N.v28745 R.v28746 N.v28746 R.v28757 N.v28757 R.v28758 N.v28758 R.v28772 N.v28772 R.v28773 N.v28773 R.v28784 N.v28784 R.v28785 N.v28785 R.v28796 N.v28796 R.v28797 N.v28797 R.v28811 N.v28811 R.v28812 N.v28812 R.v28823 N.v28823 R.v28824 N.v28824 R.v28835 N.v28835 R.v28836 N.v28836 R.v28850 N.v28850 R.v28851 N.v28851 R.v28862 N.v28862 R.v28863 N.v28863 R.v28874 N.v28874 R.v28875 N.v28875 R.v28889 N.v28889 R.v28890 N.v28890 R.v28901 N.v28901 R.v28902 N.v28902 R.v28913 N.v28913 R.v28914 N.v28914 R.v28925 N.v28925 R.v28926 N.v28926 R.v28939 N.v28939 R.v28940 N.v28940 R.v28950 N.v28950 R.v28951 N.v28951 R.v28962 N.v28962 R.v28963 N.v28963 R.v28977 N.v28977 R.v28978 N.v28978 R.v28989 N.v28989 R.v28990 N.v28990 R.v29001 N.v29001 R.v29002 N.v29002 R.v29016 N.v29016 R.v29017 N.v29017 R.v29028 N.v29028 R.v29029 N.v29029 R.v29040 N.v29040 R.v29041 N.v29041 R.v29055 N.v29055 R.v29056 N.v29056 R.v29067 N.v29067 R.v29068 N.v29068 R.v29079 N.v29079 R.v29080 N.v29080 R.v29094 N.v29094 R.v29095 N.v29095 R.v29106 N.v29106 R.v29107 N.v29107 R.v29118 N.v29118 R.v29119 N.v29119 R.v29133 N.v29133 R.v29134 N.v29134 R.v29145 N.v29145 R.v29146 N.v29146 R.v29157 N.v29157 R.v29158 N.v29158 R.v29172 N.v29172 R.v29173 N.v29173 R.v29184 N.v29184 R.v29185 N.v29185 R.v29196 N.v29196 R.v29197 N.v29197 R.v29208 N.v29208 R.v29209 N.v29209 R.v29223 N.v29223 R.v29224 N.v29224 R.v29235 N.v29235 R.v29236 N.v29236 R.v29247 N.v29247 R.v29248 N.v29248 R.v29262 N.v29262 R.v29263 N.v29263 R.v29274 N.v29274 R.v29275 N.v29275 R.v29286 N.v29286 R.v29287 N.v29287 R.v29301 N.v29301 R.v29302 N.v29302 R.v29313 N.v29313 R.v29314 N.v29314 R.v29325 N.v29325 R.v29326 N.v29326 R.v29340 N.v29340 R.v29341 N.v29341.
Definition reference_checks_9 (s : N.State) (i : N.Inputs) : list bool := [
orb (negb (Z.eqb (R.v28058 (state s) (inputs i)) 1)) (Z.eqb (R.v28057 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28073 (state s) (inputs i)) 1)) (Z.eqb (R.v28072 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28085 (state s) (inputs i)) 1)) (Z.eqb (R.v28084 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28097 (state s) (inputs i)) 1)) (Z.eqb (R.v28096 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28112 (state s) (inputs i)) 1)) (Z.eqb (R.v28111 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28124 (state s) (inputs i)) 1)) (Z.eqb (R.v28123 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28136 (state s) (inputs i)) 1)) (Z.eqb (R.v28135 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28151 (state s) (inputs i)) 1)) (Z.eqb (R.v28150 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28163 (state s) (inputs i)) 1)) (Z.eqb (R.v28162 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28175 (state s) (inputs i)) 1)) (Z.eqb (R.v28174 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28190 (state s) (inputs i)) 1)) (Z.eqb (R.v28189 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28202 (state s) (inputs i)) 1)) (Z.eqb (R.v28201 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28214 (state s) (inputs i)) 1)) (Z.eqb (R.v28213 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28229 (state s) (inputs i)) 1)) (Z.eqb (R.v28228 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28241 (state s) (inputs i)) 1)) (Z.eqb (R.v28240 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28253 (state s) (inputs i)) 1)) (Z.eqb (R.v28252 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28268 (state s) (inputs i)) 1)) (Z.eqb (R.v28267 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28280 (state s) (inputs i)) 1)) (Z.eqb (R.v28279 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28292 (state s) (inputs i)) 1)) (Z.eqb (R.v28291 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28307 (state s) (inputs i)) 1)) (Z.eqb (R.v28306 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28319 (state s) (inputs i)) 1)) (Z.eqb (R.v28318 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28331 (state s) (inputs i)) 1)) (Z.eqb (R.v28330 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28345 (state s) (inputs i)) 1)) (Z.eqb (R.v28344 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28356 (state s) (inputs i)) 1)) (Z.eqb (R.v28355 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28368 (state s) (inputs i)) 1)) (Z.eqb (R.v28367 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28383 (state s) (inputs i)) 1)) (Z.eqb (R.v28382 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28395 (state s) (inputs i)) 1)) (Z.eqb (R.v28394 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28407 (state s) (inputs i)) 1)) (Z.eqb (R.v28406 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28422 (state s) (inputs i)) 1)) (Z.eqb (R.v28421 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28434 (state s) (inputs i)) 1)) (Z.eqb (R.v28433 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28446 (state s) (inputs i)) 1)) (Z.eqb (R.v28445 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28461 (state s) (inputs i)) 1)) (Z.eqb (R.v28460 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28473 (state s) (inputs i)) 1)) (Z.eqb (R.v28472 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28485 (state s) (inputs i)) 1)) (Z.eqb (R.v28484 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28500 (state s) (inputs i)) 1)) (Z.eqb (R.v28499 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28512 (state s) (inputs i)) 1)) (Z.eqb (R.v28511 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28524 (state s) (inputs i)) 1)) (Z.eqb (R.v28523 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28539 (state s) (inputs i)) 1)) (Z.eqb (R.v28538 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28551 (state s) (inputs i)) 1)) (Z.eqb (R.v28550 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28563 (state s) (inputs i)) 1)) (Z.eqb (R.v28562 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28578 (state s) (inputs i)) 1)) (Z.eqb (R.v28577 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28590 (state s) (inputs i)) 1)) (Z.eqb (R.v28589 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28602 (state s) (inputs i)) 1)) (Z.eqb (R.v28601 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28617 (state s) (inputs i)) 1)) (Z.eqb (R.v28616 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28629 (state s) (inputs i)) 1)) (Z.eqb (R.v28628 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28641 (state s) (inputs i)) 1)) (Z.eqb (R.v28640 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28656 (state s) (inputs i)) 1)) (Z.eqb (R.v28655 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28668 (state s) (inputs i)) 1)) (Z.eqb (R.v28667 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28680 (state s) (inputs i)) 1)) (Z.eqb (R.v28679 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28695 (state s) (inputs i)) 1)) (Z.eqb (R.v28694 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28707 (state s) (inputs i)) 1)) (Z.eqb (R.v28706 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28719 (state s) (inputs i)) 1)) (Z.eqb (R.v28718 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28734 (state s) (inputs i)) 1)) (Z.eqb (R.v28733 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28746 (state s) (inputs i)) 1)) (Z.eqb (R.v28745 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28758 (state s) (inputs i)) 1)) (Z.eqb (R.v28757 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28773 (state s) (inputs i)) 1)) (Z.eqb (R.v28772 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28785 (state s) (inputs i)) 1)) (Z.eqb (R.v28784 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28797 (state s) (inputs i)) 1)) (Z.eqb (R.v28796 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28812 (state s) (inputs i)) 1)) (Z.eqb (R.v28811 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28824 (state s) (inputs i)) 1)) (Z.eqb (R.v28823 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28836 (state s) (inputs i)) 1)) (Z.eqb (R.v28835 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28851 (state s) (inputs i)) 1)) (Z.eqb (R.v28850 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28863 (state s) (inputs i)) 1)) (Z.eqb (R.v28862 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28875 (state s) (inputs i)) 1)) (Z.eqb (R.v28874 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28890 (state s) (inputs i)) 1)) (Z.eqb (R.v28889 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28902 (state s) (inputs i)) 1)) (Z.eqb (R.v28901 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28914 (state s) (inputs i)) 1)) (Z.eqb (R.v28913 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28926 (state s) (inputs i)) 1)) (Z.eqb (R.v28925 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28940 (state s) (inputs i)) 1)) (Z.eqb (R.v28939 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28951 (state s) (inputs i)) 1)) (Z.eqb (R.v28950 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28963 (state s) (inputs i)) 1)) (Z.eqb (R.v28962 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28978 (state s) (inputs i)) 1)) (Z.eqb (R.v28977 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v28990 (state s) (inputs i)) 1)) (Z.eqb (R.v28989 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v29002 (state s) (inputs i)) 1)) (Z.eqb (R.v29001 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v29017 (state s) (inputs i)) 1)) (Z.eqb (R.v29016 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v29029 (state s) (inputs i)) 1)) (Z.eqb (R.v29028 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v29041 (state s) (inputs i)) 1)) (Z.eqb (R.v29040 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v29056 (state s) (inputs i)) 1)) (Z.eqb (R.v29055 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v29068 (state s) (inputs i)) 1)) (Z.eqb (R.v29067 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v29080 (state s) (inputs i)) 1)) (Z.eqb (R.v29079 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v29095 (state s) (inputs i)) 1)) (Z.eqb (R.v29094 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v29107 (state s) (inputs i)) 1)) (Z.eqb (R.v29106 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v29119 (state s) (inputs i)) 1)) (Z.eqb (R.v29118 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v29134 (state s) (inputs i)) 1)) (Z.eqb (R.v29133 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v29146 (state s) (inputs i)) 1)) (Z.eqb (R.v29145 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v29158 (state s) (inputs i)) 1)) (Z.eqb (R.v29157 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v29173 (state s) (inputs i)) 1)) (Z.eqb (R.v29172 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v29185 (state s) (inputs i)) 1)) (Z.eqb (R.v29184 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v29197 (state s) (inputs i)) 1)) (Z.eqb (R.v29196 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v29209 (state s) (inputs i)) 1)) (Z.eqb (R.v29208 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v29224 (state s) (inputs i)) 1)) (Z.eqb (R.v29223 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v29236 (state s) (inputs i)) 1)) (Z.eqb (R.v29235 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v29248 (state s) (inputs i)) 1)) (Z.eqb (R.v29247 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v29263 (state s) (inputs i)) 1)) (Z.eqb (R.v29262 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v29275 (state s) (inputs i)) 1)) (Z.eqb (R.v29274 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v29287 (state s) (inputs i)) 1)) (Z.eqb (R.v29286 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v29302 (state s) (inputs i)) 1)) (Z.eqb (R.v29301 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v29314 (state s) (inputs i)) 1)) (Z.eqb (R.v29313 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v29326 (state s) (inputs i)) 1)) (Z.eqb (R.v29325 (state s) (inputs i)) 1)
; orb (negb (Z.eqb (R.v29341 (state s) (inputs i)) 1)) (Z.eqb (R.v29340 (state s) (inputs i)) 1)
].
Definition native_checks_9 (s : N.State) (i : N.Inputs) : list bool := [
orb (negb (Zmod.eqb (N.v28058 s i) Zmod.one)) (Zmod.eqb (N.v28057 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28073 s i) Zmod.one)) (Zmod.eqb (N.v28072 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28085 s i) Zmod.one)) (Zmod.eqb (N.v28084 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28097 s i) Zmod.one)) (Zmod.eqb (N.v28096 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28112 s i) Zmod.one)) (Zmod.eqb (N.v28111 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28124 s i) Zmod.one)) (Zmod.eqb (N.v28123 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28136 s i) Zmod.one)) (Zmod.eqb (N.v28135 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28151 s i) Zmod.one)) (Zmod.eqb (N.v28150 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28163 s i) Zmod.one)) (Zmod.eqb (N.v28162 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28175 s i) Zmod.one)) (Zmod.eqb (N.v28174 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28190 s i) Zmod.one)) (Zmod.eqb (N.v28189 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28202 s i) Zmod.one)) (Zmod.eqb (N.v28201 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28214 s i) Zmod.one)) (Zmod.eqb (N.v28213 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28229 s i) Zmod.one)) (Zmod.eqb (N.v28228 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28241 s i) Zmod.one)) (Zmod.eqb (N.v28240 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28253 s i) Zmod.one)) (Zmod.eqb (N.v28252 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28268 s i) Zmod.one)) (Zmod.eqb (N.v28267 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28280 s i) Zmod.one)) (Zmod.eqb (N.v28279 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28292 s i) Zmod.one)) (Zmod.eqb (N.v28291 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28307 s i) Zmod.one)) (Zmod.eqb (N.v28306 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28319 s i) Zmod.one)) (Zmod.eqb (N.v28318 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28331 s i) Zmod.one)) (Zmod.eqb (N.v28330 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28345 s i) Zmod.one)) (Zmod.eqb (N.v28344 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28356 s i) Zmod.one)) (Zmod.eqb (N.v28355 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28368 s i) Zmod.one)) (Zmod.eqb (N.v28367 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28383 s i) Zmod.one)) (Zmod.eqb (N.v28382 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28395 s i) Zmod.one)) (Zmod.eqb (N.v28394 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28407 s i) Zmod.one)) (Zmod.eqb (N.v28406 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28422 s i) Zmod.one)) (Zmod.eqb (N.v28421 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28434 s i) Zmod.one)) (Zmod.eqb (N.v28433 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28446 s i) Zmod.one)) (Zmod.eqb (N.v28445 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28461 s i) Zmod.one)) (Zmod.eqb (N.v28460 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28473 s i) Zmod.one)) (Zmod.eqb (N.v28472 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28485 s i) Zmod.one)) (Zmod.eqb (N.v28484 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28500 s i) Zmod.one)) (Zmod.eqb (N.v28499 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28512 s i) Zmod.one)) (Zmod.eqb (N.v28511 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28524 s i) Zmod.one)) (Zmod.eqb (N.v28523 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28539 s i) Zmod.one)) (Zmod.eqb (N.v28538 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28551 s i) Zmod.one)) (Zmod.eqb (N.v28550 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28563 s i) Zmod.one)) (Zmod.eqb (N.v28562 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28578 s i) Zmod.one)) (Zmod.eqb (N.v28577 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28590 s i) Zmod.one)) (Zmod.eqb (N.v28589 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28602 s i) Zmod.one)) (Zmod.eqb (N.v28601 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28617 s i) Zmod.one)) (Zmod.eqb (N.v28616 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28629 s i) Zmod.one)) (Zmod.eqb (N.v28628 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28641 s i) Zmod.one)) (Zmod.eqb (N.v28640 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28656 s i) Zmod.one)) (Zmod.eqb (N.v28655 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28668 s i) Zmod.one)) (Zmod.eqb (N.v28667 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28680 s i) Zmod.one)) (Zmod.eqb (N.v28679 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28695 s i) Zmod.one)) (Zmod.eqb (N.v28694 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28707 s i) Zmod.one)) (Zmod.eqb (N.v28706 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28719 s i) Zmod.one)) (Zmod.eqb (N.v28718 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28734 s i) Zmod.one)) (Zmod.eqb (N.v28733 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28746 s i) Zmod.one)) (Zmod.eqb (N.v28745 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28758 s i) Zmod.one)) (Zmod.eqb (N.v28757 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28773 s i) Zmod.one)) (Zmod.eqb (N.v28772 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28785 s i) Zmod.one)) (Zmod.eqb (N.v28784 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28797 s i) Zmod.one)) (Zmod.eqb (N.v28796 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28812 s i) Zmod.one)) (Zmod.eqb (N.v28811 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28824 s i) Zmod.one)) (Zmod.eqb (N.v28823 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28836 s i) Zmod.one)) (Zmod.eqb (N.v28835 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28851 s i) Zmod.one)) (Zmod.eqb (N.v28850 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28863 s i) Zmod.one)) (Zmod.eqb (N.v28862 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28875 s i) Zmod.one)) (Zmod.eqb (N.v28874 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28890 s i) Zmod.one)) (Zmod.eqb (N.v28889 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28902 s i) Zmod.one)) (Zmod.eqb (N.v28901 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28914 s i) Zmod.one)) (Zmod.eqb (N.v28913 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28926 s i) Zmod.one)) (Zmod.eqb (N.v28925 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28940 s i) Zmod.one)) (Zmod.eqb (N.v28939 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28951 s i) Zmod.one)) (Zmod.eqb (N.v28950 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28963 s i) Zmod.one)) (Zmod.eqb (N.v28962 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28978 s i) Zmod.one)) (Zmod.eqb (N.v28977 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v28990 s i) Zmod.one)) (Zmod.eqb (N.v28989 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v29002 s i) Zmod.one)) (Zmod.eqb (N.v29001 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v29017 s i) Zmod.one)) (Zmod.eqb (N.v29016 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v29029 s i) Zmod.one)) (Zmod.eqb (N.v29028 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v29041 s i) Zmod.one)) (Zmod.eqb (N.v29040 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v29056 s i) Zmod.one)) (Zmod.eqb (N.v29055 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v29068 s i) Zmod.one)) (Zmod.eqb (N.v29067 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v29080 s i) Zmod.one)) (Zmod.eqb (N.v29079 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v29095 s i) Zmod.one)) (Zmod.eqb (N.v29094 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v29107 s i) Zmod.one)) (Zmod.eqb (N.v29106 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v29119 s i) Zmod.one)) (Zmod.eqb (N.v29118 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v29134 s i) Zmod.one)) (Zmod.eqb (N.v29133 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v29146 s i) Zmod.one)) (Zmod.eqb (N.v29145 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v29158 s i) Zmod.one)) (Zmod.eqb (N.v29157 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v29173 s i) Zmod.one)) (Zmod.eqb (N.v29172 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v29185 s i) Zmod.one)) (Zmod.eqb (N.v29184 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v29197 s i) Zmod.one)) (Zmod.eqb (N.v29196 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v29209 s i) Zmod.one)) (Zmod.eqb (N.v29208 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v29224 s i) Zmod.one)) (Zmod.eqb (N.v29223 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v29236 s i) Zmod.one)) (Zmod.eqb (N.v29235 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v29248 s i) Zmod.one)) (Zmod.eqb (N.v29247 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v29263 s i) Zmod.one)) (Zmod.eqb (N.v29262 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v29275 s i) Zmod.one)) (Zmod.eqb (N.v29274 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v29287 s i) Zmod.one)) (Zmod.eqb (N.v29286 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v29302 s i) Zmod.one)) (Zmod.eqb (N.v29301 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v29314 s i) Zmod.one)) (Zmod.eqb (N.v29313 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v29326 s i) Zmod.one)) (Zmod.eqb (N.v29325 s i) Zmod.one)
; orb (negb (Zmod.eqb (N.v29341 s i) Zmod.one)) (Zmod.eqb (N.v29340 s i) Zmod.one)
].
Lemma checks_9 s i : reference_checks_9 s i = native_checks_9 s i.
Proof. unfold reference_checks_9, native_checks_9.
  rewrite ?node_28057.
  rewrite ?node_28058.
  rewrite ?node_28072.
  rewrite ?node_28073.
  rewrite ?node_28084.
  rewrite ?node_28085.
  rewrite ?node_28096.
  rewrite ?node_28097.
  rewrite ?node_28111.
  rewrite ?node_28112.
  rewrite ?node_28123.
  rewrite ?node_28124.
  rewrite ?node_28135.
  rewrite ?node_28136.
  rewrite ?node_28150.
  rewrite ?node_28151.
  rewrite ?node_28162.
  rewrite ?node_28163.
  rewrite ?node_28174.
  rewrite ?node_28175.
  rewrite ?node_28189.
  rewrite ?node_28190.
  rewrite ?node_28201.
  rewrite ?node_28202.
  rewrite ?node_28213.
  rewrite ?node_28214.
  rewrite ?node_28228.
  rewrite ?node_28229.
  rewrite ?node_28240.
  rewrite ?node_28241.
  rewrite ?node_28252.
  rewrite ?node_28253.
  rewrite ?node_28267.
  rewrite ?node_28268.
  rewrite ?node_28279.
  rewrite ?node_28280.
  rewrite ?node_28291.
  rewrite ?node_28292.
  rewrite ?node_28306.
  rewrite ?node_28307.
  rewrite ?node_28318.
  rewrite ?node_28319.
  rewrite ?node_28330.
  rewrite ?node_28331.
  rewrite ?node_28344.
  rewrite ?node_28345.
  rewrite ?node_28355.
  rewrite ?node_28356.
  rewrite ?node_28367.
  rewrite ?node_28368.
  rewrite ?node_28382.
  rewrite ?node_28383.
  rewrite ?node_28394.
  rewrite ?node_28395.
  rewrite ?node_28406.
  rewrite ?node_28407.
  rewrite ?node_28421.
  rewrite ?node_28422.
  rewrite ?node_28433.
  rewrite ?node_28434.
  rewrite ?node_28445.
  rewrite ?node_28446.
  rewrite ?node_28460.
  rewrite ?node_28461.
  rewrite ?node_28472.
  rewrite ?node_28473.
  rewrite ?node_28484.
  rewrite ?node_28485.
  rewrite ?node_28499.
  rewrite ?node_28500.
  rewrite ?node_28511.
  rewrite ?node_28512.
  rewrite ?node_28523.
  rewrite ?node_28524.
  rewrite ?node_28538.
  rewrite ?node_28539.
  rewrite ?node_28550.
  rewrite ?node_28551.
  rewrite ?node_28562.
  rewrite ?node_28563.
  rewrite ?node_28577.
  rewrite ?node_28578.
  rewrite ?node_28589.
  rewrite ?node_28590.
  rewrite ?node_28601.
  rewrite ?node_28602.
  rewrite ?node_28616.
  rewrite ?node_28617.
  rewrite ?node_28628.
  rewrite ?node_28629.
  rewrite ?node_28640.
  rewrite ?node_28641.
  rewrite ?node_28655.
  rewrite ?node_28656.
  rewrite ?node_28667.
  rewrite ?node_28668.
  rewrite ?node_28679.
  rewrite ?node_28680.
  rewrite ?node_28694.
  rewrite ?node_28695.
  rewrite ?node_28706.
  rewrite ?node_28707.
  rewrite ?node_28718.
  rewrite ?node_28719.
  rewrite ?node_28733.
  rewrite ?node_28734.
  rewrite ?node_28745.
  rewrite ?node_28746.
  rewrite ?node_28757.
  rewrite ?node_28758.
  rewrite ?node_28772.
  rewrite ?node_28773.
  rewrite ?node_28784.
  rewrite ?node_28785.
  rewrite ?node_28796.
  rewrite ?node_28797.
  rewrite ?node_28811.
  rewrite ?node_28812.
  rewrite ?node_28823.
  rewrite ?node_28824.
  rewrite ?node_28835.
  rewrite ?node_28836.
  rewrite ?node_28850.
  rewrite ?node_28851.
  rewrite ?node_28862.
  rewrite ?node_28863.
  rewrite ?node_28874.
  rewrite ?node_28875.
  rewrite ?node_28889.
  rewrite ?node_28890.
  rewrite ?node_28901.
  rewrite ?node_28902.
  rewrite ?node_28913.
  rewrite ?node_28914.
  rewrite ?node_28925.
  rewrite ?node_28926.
  rewrite ?node_28939.
  rewrite ?node_28940.
  rewrite ?node_28950.
  rewrite ?node_28951.
  rewrite ?node_28962.
  rewrite ?node_28963.
  rewrite ?node_28977.
  rewrite ?node_28978.
  rewrite ?node_28989.
  rewrite ?node_28990.
  rewrite ?node_29001.
  rewrite ?node_29002.
  rewrite ?node_29016.
  rewrite ?node_29017.
  rewrite ?node_29028.
  rewrite ?node_29029.
  rewrite ?node_29040.
  rewrite ?node_29041.
  rewrite ?node_29055.
  rewrite ?node_29056.
  rewrite ?node_29067.
  rewrite ?node_29068.
  rewrite ?node_29079.
  rewrite ?node_29080.
  rewrite ?node_29094.
  rewrite ?node_29095.
  rewrite ?node_29106.
  rewrite ?node_29107.
  rewrite ?node_29118.
  rewrite ?node_29119.
  rewrite ?node_29133.
  rewrite ?node_29134.
  rewrite ?node_29145.
  rewrite ?node_29146.
  rewrite ?node_29157.
  rewrite ?node_29158.
  rewrite ?node_29172.
  rewrite ?node_29173.
  rewrite ?node_29184.
  rewrite ?node_29185.
  rewrite ?node_29196.
  rewrite ?node_29197.
  rewrite ?node_29208.
  rewrite ?node_29209.
  rewrite ?node_29223.
  rewrite ?node_29224.
  rewrite ?node_29235.
  rewrite ?node_29236.
  rewrite ?node_29247.
  rewrite ?node_29248.
  rewrite ?node_29262.
  rewrite ?node_29263.
  rewrite ?node_29274.
  rewrite ?node_29275.
  rewrite ?node_29286.
  rewrite ?node_29287.
  rewrite ?node_29301.
  rewrite ?node_29302.
  rewrite ?node_29313.
  rewrite ?node_29314.
  rewrite ?node_29325.
  rewrite ?node_29326.
  rewrite ?node_29340.
  rewrite ?node_29341.
  reflexivity.
Qed.

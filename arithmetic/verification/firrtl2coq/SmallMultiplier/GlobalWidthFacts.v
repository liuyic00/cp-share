From Coq Require Import NArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths.
From ArithmeticCommon Require Import EnvironmentFacts ScalarTyping.
Lemma sint_value_typed_size width bits
 (correct:hvalue_is_type_correct (Gval(Fsint width)bits)(Gtyp(Fsint width))=true) : size bits=width.
Proof. cbn [hvalue_is_type_correct] in correct. move/andP:correct=>[/eqP H _]. exact H. Qed.
Lemma clock_value_typed_size bits
 (correct:hvalue_is_type_correct (Gval Fclock bits)(Gtyp Fclock)=true) : size bits=1%nat.
Proof. cbn [hvalue_is_type_correct] in correct. by move/eqP:correct. Qed.
Lemma adapt_uint_same width bits (sized:size bits=width) :
 adapt_hvalue_as_type (Gval(Fuint width)bits)(Gtyp(Fuint width))=Some(Gval(Fuint width)bits).
Proof. cbn [adapt_hvalue_as_type]. rewrite -sized take_size /zext_to subnn /zext cats0. reflexivity. Qed.
Lemma adapt_sint_same width bits (sized:size bits=width) :
 adapt_hvalue_as_type (Gval(Fsint width)bits)(Gtyp(Fsint width))=Some(Gval(Fsint width)bits).
Proof. cbn [adapt_hvalue_as_type]. rewrite -sized take_size /sext_to subnn /sext cats0. reflexivity. Qed.
Lemma one_bit_form (bs:bits) (sized:size bs=1%nat) : exists b,bs=[::b].
Proof. destruct bs as [|b rest];[discriminate|]. destruct rest as [|c rest];[exists b;reflexivity|discriminate]. Qed.

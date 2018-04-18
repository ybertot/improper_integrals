Require Import Reals Coquelicot.Coquelicot Fourier.
Require Import filter_Rlt.

Hint Mode ProperFilter' - + : typeclass_instances.

(* TODO : move to coquelicot. *)
Lemma filter_prod_le {T : Type} (F G F' G' : (T -> Prop) -> Prop) :
  filter_le F F' -> filter_le G G' -> filter_le (filter_prod F G)
    (filter_prod F' G').
Proof.  now intros FF GG S [S1 S2 FS GS Imp]; exists S1 S2; auto. Qed.

Lemma is_RInt_gen_filter_le {T : NormedModule R_AbsRing}
  F G F' G' {FF : Filter F} {FG : Filter G}
  {FF' : Filter F'} {FG' : Filter G'} (f : R -> T) v :
  filter_le F' F -> filter_le G' G -> is_RInt_gen f F G v ->
  is_RInt_gen f F' G' v.
Proof.
intros lef leg intf P PP; unfold filtermapi.
now apply (filter_prod_le _ _ _ _ lef leg), intf.
Qed.

Lemma is_RInt_gen_comp {Fa Fb : (R -> Prop) -> Prop} {FFa : Filter Fa}
  {FFb : Filter Fb} (f : R -> R) (dg g : R -> R) l :
  filter_prod Fa Fb (fun p =>
      forall y, Rmin (fst p) (snd p) <= y <= Rmax (fst p) (snd p) ->
             continuous f (g y) /\
             is_derive g y (dg y) /\ continuous dg y) ->
  is_RInt_gen f (filtermap g Fa) (filtermap g Fb) l ->
  is_RInt_gen (fun x => scal (dg x) (f (g x))) Fa Fb l.
Proof.
intros dp intf P PP.
destruct dp as [S1 S2 FS1 FS2 dp].
destruct (intf P PP) as [S S' FS FS' fp1].
exists (fun x => S (g x) /\ S1 x) (fun x => S' (g x) /\ S2 x);
      try now apply filter_and; auto.
intros x y [sgx s1x] [sgy s2y]; simpl.
exists (RInt f (g x) (g y)); split.
  destruct (fp1 (g x) (g y)); try tauto.
  apply (is_RInt_comp f g dg).
     intros z zcond. 
     now destruct (dp x y s1x s2y z); auto.
  intros z zcond.
  now destruct (dp x y s1x s2y z); auto.
destruct (fp1 (g x) (g y) sgx sgy) as [v [isint Pv]]; simpl in isint.
now rewrite -> (is_RInt_unique _ _ _ _ isint).
Qed.

Lemma is_RInt_gen_equiv F G F' G' (f : R -> R) v:
  (forall s, F s <-> F' s) -> (forall s, G s <-> G' s) ->
  is_RInt_gen f F G v -> is_RInt_gen f F' G' v.
Proof.
intros eqF eqG intf P PP'; unfold filtermapi.
assert (tmp := filter_prod_le F' G' F G); unfold filter_le in tmp; apply tmp.
    now intros A; rewrite eqF.
  now intros A; rewrite eqG.
now apply (intf P PP').
Qed.

Lemma ex_RInt_gen_unique
  (F G : (R -> Prop) -> Prop) {FF : ProperFilter F}
  {FG : ProperFilter G} (f : R -> R) :
  ex_RInt_gen f F G -> exists ! v, is_RInt_gen f F G v.
Proof.
intros [v Pv]; exists (RInt_gen f F G); unfold unique.
rewrite -> (is_RInt_gen_unique _ _ Pv) at 1; split;[assumption | ].
now intros v' Pv'; rewrite -> (is_RInt_gen_unique _ _ Pv').
Qed.

Lemma is_RInt_gen_at_right_at_point (f : R -> R) (a : R) F {FF : ProperFilter F}
  v :
  locally a (continuous f) -> is_RInt_gen f (at_right a) F v ->
  is_RInt_gen f (at_point a) F v.
Proof.
intros [delta1 pd1].
destruct (pd1 a (ball_center a delta1)
          (ball (f a) (mkposreal _ Rlt_0_1)) (locally_ball _ _)) as
    [delta2 Pd2].
intros intf.
set (M := Rabs (f a) + 1).
assert (M0 : 0 < M) by (assert (t:= Rabs_pos (f a)); unfold M; fourier).
assert (close : forall y, y <> a -> ball a delta2 y -> Rabs (f y) < M).
  intros y ay b_y; unfold M.
  replace (f y) with (f a + (f y - f a)) by ring.
  apply Rle_lt_trans with (1 := Rabs_triang _ _).
  now apply Rplus_lt_compat_l, Pd2; auto.
assert (atrd1 : at_right a (ball a delta1)) by (exists delta1; tauto).
assert (exrint_close : forall a', ball a delta1 a' -> ex_RInt f a a').
  intros a' baa'.
  apply (ex_RInt_continuous f); intros z pz; apply pd1.
  destruct (Rle_dec a a') as [aa' | a'a].
    rewrite -> Rmin_left, Rmax_right in pz; auto.
    change (Rabs (z - a) < delta1).
    rewrite Rabs_right; cycle 1.
      destruct pz; fourier.
    destruct pz; apply Rle_lt_trans with (a' - a); try fourier.
    rewrite <- (Rabs_right (a' - a)); try fourier.
    tauto.
  change (Rabs (z - a) < delta1).
  apply Rnot_le_lt in a'a.
  destruct (Rle_dec a z) as [az | za].
    rewrite -> Rmin_right, Rmax_left in pz; destruct pz; try fourier.
    rewrite Rabs_right; try fourier.
    case delta1; intros; simpl; fourier.
  apply Rnot_le_lt in za.
  rewrite -> Rmin_right, Rmax_left in pz; try fourier.
  rewrite Rabs_left; [ | fourier].
  destruct pz; apply Rle_lt_trans with (a - a'); try fourier.
  rewrite <- (Rabs_right (a - a')); try fourier.
  now change (ball a' delta1 a); apply ball_sym; tauto.
intros P [eps Peps].
assert (pre_ep2 : 0 < eps / 2 * /M).
  apply Rmult_lt_0_compat;[ | now apply Rinv_0_lt_compat].
  now destruct eps; simpl; fourier.
set (ep2 := mkposreal _ pre_ep2).
destruct (intf (ball v (pos_div_2 eps))) as [Q R FQ FR vfi'].
  now apply locally_ball.
exists (eq a) R; auto.
  now easy.
intros x y ax Ry; simpl; rewrite <- ax; clear ax x.
assert (atrd2 : at_right a (ball a delta2)) by (exists delta2; tauto).
assert (atre2 : at_right a (ball a ep2)) by (exists ep2; tauto).
destruct (filter_ex _ (filter_and _ _ atrd1 (filter_and _ _ atrd2
                          (filter_and _ _ FQ atre2)))) as
      [a' Pa'].
assert (ex_RInt f a a') by (apply exrint_close; tauto).
exists (RInt f a y); split; cycle 1.
  apply Peps.
  replace (pos eps) with (eps/2 + M * (eps / 2 * / M)); cycle 1.
    now field; apply Rgt_not_eq.
  apply ball_triangle with (RInt f a' y).
    destruct (vfi' a' y) as [a'y Pa'y]; try tauto.
    now simpl in Pa'y; rewrite (is_RInt_unique _ _ _ _ (proj1 Pa'y)); tauto.
  assert (ex_RInt f a' y).
   destruct (vfi' a' y) as [a'y Pa'y]; try tauto; exists a'y; tauto.
  change (Rabs (RInt f a y - RInt f a' y) < M * (eps / 2 * / M)).
  apply Rle_lt_trans with (RInt (fun x => Rabs (f x)) (Rmin a a') (Rmax a a')).
    replace (RInt f a y - RInt f a' y) with (RInt f a a'); cycle 1.
      apply Rplus_eq_reg_r with (RInt f a' y).
      assert (tmp := RInt_Chasles f a a' y); change plus with Rplus in tmp.
      (* BUG: need to figure out how to make ring work without the Rplus_0_r. *)
      now rewrite -> tmp;[symmetry; ring | | ]; auto.
    destruct (Rle_dec a a') as [aa' | a'a].
      rewrite -> Rmin_left, Rmax_right; try fourier.
      apply abs_RInt_le; assumption.
    apply Rnot_le_lt in a'a.
    rewrite <- (opp_RInt_swap f), Rabs_Ropp, Rmin_right, Rmax_left; try fourier; cycle 1.
      now apply ex_RInt_swap.
    apply abs_RInt_le;[ apply Rlt_le | apply ex_RInt_swap]; assumption.
  apply Rle_lt_trans with (RInt (fun _ => M) (Rmin a a') (Rmax a a')).
  apply RInt_le.
          now apply Rminmax.
        apply (ex_RInt_continuous (fun x => Rabs (f x))).
        rewrite -> Rmin_left, Rmax_right; try apply Rminmax.
        intros z pz; apply continuous_comp;[ | now apply continuous_Rabs].
        apply pd1, Rle_lt_trans with (Rabs (a' - a));[ | tauto].
        unfold abs, minus, plus, opp; simpl.
        destruct (Rle_dec a a') as [aa' | a'a].
          now rewrite -> Rmin_left, Rmax_right in pz; destruct pz;
            try rewrite !Rabs_right; fourier.
        rewrite -> Rmin_right, Rmax_left in pz; destruct pz;
          apply Rnot_le_lt in a'a;
          try rewrite (Rabs_left (a' - a)); try fourier.
        destruct (Req_dec z a) as [za | nza].
          rewrite -> za,Rplus_opp_r, Rabs_R0; fourier.
        rewrite Rabs_left; try fourier.
        now apply Rnot_le_lt; intros abs; case nza; apply Rle_antisym; fourier.
      now apply ex_RInt_const.
    intros z pz; apply Rlt_le, close.
      destruct (Rle_dec a a') as [aa' | a'a].
        rewrite -> Rmin_left, Rmax_right in pz; destruct pz; try fourier.
        now apply Rgt_not_eq; assumption.
      rewrite -> Rmin_right, Rmax_left in pz; destruct pz;
      apply Rnot_le_lt in a'a; try fourier.
      now apply Rlt_not_eq; assumption.
    apply Rlt_trans with (Rabs (a' - a));[ | tauto].
    unfold abs, minus, plus, opp; simpl.
    destruct (Rle_dec a a') as [aa' | a'a].
      now rewrite -> Rmin_left, Rmax_right in pz; destruct pz;
        try rewrite !Rabs_right; fourier.
    rewrite -> Rmin_right, Rmax_left in pz; destruct pz;
      try rewrite (Rabs_left (a' - a)); apply Rnot_le_lt in a'a; try fourier.
    destruct (Req_dec z a) as [za | nza].
      now rewrite -> za,Rplus_opp_r, Rabs_R0; fourier.
    now rewrite Rabs_left; fourier.
  rewrite -> RInt_const, Rmult_comm.
  apply Rmult_lt_compat_l;[fourier | ].
  destruct (Rle_dec a a') as [aa' | a'a].
    rewrite -> Rmax_right, Rmin_left; try fourier.
    now rewrite <- (Rabs_right (a' - a));[tauto | fourier].
  rewrite -> Rmax_left, Rmin_right; apply Rnot_le_lt in a'a ; try fourier.
  replace (a - a') with (- (a' - a)) by ring.
  now rewrite <- (Rabs_left (a' - a)); try fourier; tauto.
apply (RInt_correct f).
apply (ex_RInt_Chasles f a a' y); auto.
now destruct (vfi' a' y) as [a'y pa'y]; try tauto; exists a'y.
Qed.

Lemma is_RInt_gen_at_left_at_point (f : R -> R) (a : R) F {FF : ProperFilter F}
  v :
  locally a (continuous f) -> is_RInt_gen f F (at_left a) v ->
  is_RInt_gen f F (at_point a) v.
Proof.
intros [delta1 pd1].
destruct (pd1 a (ball_center a delta1)
          (ball (f a) (mkposreal _ Rlt_0_1)) (locally_ball _ _)) as
    [delta2 Pd2].
intros intf.
set (M := Rabs (f a) + 1).
assert (M0 : 0 < M) by (assert (t:= Rabs_pos (f a)); unfold M; fourier).
assert (close : forall y, y <> a -> ball a delta2 y -> Rabs (f y) < M).
  intros y ay b_y; unfold M.
  replace (f y) with (f a + (f y - f a)) by ring.
  apply Rle_lt_trans with (1 := Rabs_triang _ _).
  now apply Rplus_lt_compat_l, Pd2; auto.
assert (atld1 : at_left a (ball a delta1)) by (exists delta1; tauto).
assert (exrint_close : forall a', ball a delta1 a' -> ex_RInt f a' a).
  intros a' baa'.
  apply (ex_RInt_continuous f); intros z pz; apply pd1.
  destruct (Rle_dec a a') as [aa' | a'a].
    rewrite -> Rmin_right, Rmax_left in pz; auto.
    change (Rabs (z - a) < delta1).
    rewrite Rabs_right; cycle 1.
      destruct pz; fourier.
    destruct pz; apply Rle_lt_trans with (a' - a); try fourier.
    rewrite <- (Rabs_right (a' - a)); try fourier.
    tauto.
  change (Rabs (z - a) < delta1).
  apply Rnot_le_lt in a'a.
  destruct (Rle_dec a z) as [az | za].
    rewrite -> Rmin_left, Rmax_right in pz; destruct pz; try fourier.
    rewrite Rabs_right; try fourier.
    case delta1; intros; simpl; fourier.
  apply Rnot_le_lt in za.
  rewrite -> Rmin_left, Rmax_right in pz; try fourier.
  rewrite Rabs_left; [ | fourier].
  destruct pz; apply Rle_lt_trans with (a - a'); try fourier.
  rewrite <- (Rabs_right (a - a')); try fourier.
  now change (ball a' delta1 a); apply ball_sym; tauto.
intros P [eps Peps].
assert (pre_ep2 : 0 < eps / 2 * /M).
  apply Rmult_lt_0_compat;[ | now apply Rinv_0_lt_compat].
  now destruct eps; simpl; fourier.
set (ep2 := mkposreal _ pre_ep2).
destruct (intf (ball v (pos_div_2 eps))) as [Q R FQ FR vfi'].
  now apply locally_ball.
exists Q (eq a); auto.
  now easy.
intros x y Qx ay; simpl; rewrite <- ay; clear ay y.
assert (atld2 : at_left a (ball a delta2)) by (exists delta2; tauto).
assert (atle2 : at_left a (ball a ep2)) by (exists ep2; tauto).
destruct (filter_ex _ (filter_and _ _ atld1 (filter_and _ _ atld2
                          (filter_and _ _ FR atle2)))) as
      [a' Pa'].
assert (H : ex_RInt f a' a) by (apply exrint_close; tauto).
assert (H' : ex_RInt f a a') by now apply ex_RInt_swap.
exists (RInt f x a); split; cycle 1.
  apply Peps.
  replace (pos eps) with (eps/2 + M * (eps / 2 * / M)); cycle 1.
    now field; apply Rgt_not_eq.
  apply ball_triangle with (RInt f x a').
    destruct (vfi' x a') as [xa' Pxa']; try tauto.
    now simpl in Pxa'; rewrite (is_RInt_unique _ _ _ _ (proj1 Pxa')); tauto.
  assert (H0: ex_RInt f x a').
   destruct (vfi' x a') as [xa' Pxa']; try tauto; exists xa'; tauto.
  assert (H'0 : ex_RInt f a' x) by now apply ex_RInt_swap.
  change (Rabs (RInt f x a - RInt f x a') < M * (eps / 2 * / M)).
  apply Rle_lt_trans with (RInt (fun x => Rabs (f x)) (Rmin a a') (Rmax a a')).
    replace (RInt f x a - RInt f x a') with (RInt f a' a); cycle 1.
      apply Rplus_eq_reg_r with (RInt f x a').
      assert (tmp := RInt_Chasles f x a' a); change plus with Rplus in tmp.
      (* BUG: need to figure out how to make ring work without the Rplus_0_r. *)
      now rewrite Rplus_comm, -> tmp;[symmetry; ring | | ]; auto.
    destruct (Rle_dec a a') as [aa' | a'a].
      rewrite -> Rmin_left, Rmax_right; try fourier.
      rewrite <- opp_RInt_swap; auto; unfold opp; simpl.
        rewrite (Rabs_Ropp (RInt f a a')); auto.
        apply abs_RInt_le; assumption.
    apply Rnot_le_lt in a'a.
    rewrite <- (opp_RInt_swap f), Rabs_Ropp, Rmin_right, Rmax_left; try fourier; cycle 1.
      now apply ex_RInt_swap.
    rewrite <-opp_RInt_swap; auto; rewrite Rabs_Ropp.
    apply abs_RInt_le;[ apply Rlt_le | apply ex_RInt_swap]; assumption.
  apply Rle_lt_trans with (RInt (fun _ => M) (Rmin a a') (Rmax a a')).
  apply RInt_le.
          now apply Rminmax.
        apply (ex_RInt_continuous (fun x => Rabs (f x))).
        rewrite -> Rmin_left, Rmax_right; try apply Rminmax.
        intros z pz; apply continuous_comp;[ | now apply continuous_Rabs].
        apply pd1, Rle_lt_trans with (Rabs (a' - a));[ | tauto].
        unfold abs, minus, plus, opp; simpl.
        destruct (Rle_dec a a') as [aa' | a'a].
          now rewrite -> Rmin_left, Rmax_right in pz; destruct pz;
            try rewrite !Rabs_right; fourier.
        rewrite -> Rmin_right, Rmax_left in pz; destruct pz;
          apply Rnot_le_lt in a'a;
          try rewrite (Rabs_left (a' - a)); try fourier.
        destruct (Req_dec z a) as [za | nza].
          rewrite -> za,Rplus_opp_r, Rabs_R0; fourier.
        rewrite Rabs_left; try fourier.
        now apply Rnot_le_lt; intros abs; case nza; apply Rle_antisym; fourier.
      now apply ex_RInt_const.
    intros z pz; apply Rlt_le, close.
      destruct (Rle_dec a a') as [aa' | a'a].
        rewrite -> Rmin_left, Rmax_right in pz; destruct pz; try fourier.
        now apply Rgt_not_eq; assumption.
      rewrite -> Rmin_right, Rmax_left in pz; destruct pz;
      apply Rnot_le_lt in a'a; try fourier.
      now apply Rlt_not_eq; assumption.
    apply Rlt_trans with (Rabs (a' - a));[ | tauto].
    unfold abs, minus, plus, opp; simpl.
    destruct (Rle_dec a a') as [aa' | a'a].
      now rewrite -> Rmin_left, Rmax_right in pz; destruct pz;
        try rewrite !Rabs_right; fourier.
    rewrite -> Rmin_right, Rmax_left in pz; destruct pz;
      try rewrite (Rabs_left (a' - a)); apply Rnot_le_lt in a'a; try fourier.
    destruct (Req_dec z a) as [za | nza].
      now rewrite -> za,Rplus_opp_r, Rabs_R0; fourier.
    now rewrite Rabs_left; fourier.
  rewrite -> RInt_const, Rmult_comm.
  apply Rmult_lt_compat_l;[fourier | ].
  destruct (Rle_dec a a') as [aa' | a'a].
    rewrite -> Rmax_right, Rmin_left; try fourier.
    now rewrite <- (Rabs_right (a' - a));[tauto | fourier].
  rewrite -> Rmax_left, Rmin_right; apply Rnot_le_lt in a'a ; try fourier.
  replace (a - a') with (- (a' - a)) by ring.
  now rewrite <- (Rabs_left (a' - a)); try fourier; tauto.
apply (RInt_correct f).
apply (ex_RInt_Chasles f x a' a); auto.
now destruct (vfi' x a') as [xa' pxa']; try tauto; exists xa'.
Qed.
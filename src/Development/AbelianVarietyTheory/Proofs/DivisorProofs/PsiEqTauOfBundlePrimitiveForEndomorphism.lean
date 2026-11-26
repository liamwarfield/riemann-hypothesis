module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonSpDualNumber

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiEqTauFromSignRelationFourTorsion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiEqTauFromSignRelationFourTorsion
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.PsiSignRel

open GlobalTheory.UT.SymFrame

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O D.X]

theorem act_zero' (o : D.OAct O) : o.onB.act (0 : O) = 1 := by
  have h := o.onB.map_add 0 0
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

theorem act_add' (o : D.OAct O) (a c : O) : o.onB.act a * o.onB.act c = o.onB.act (a + c) :=
  (o.onB.map_add a c).symm

theorem act_comp' (o : D.OAct O) (a c : O) : o.onB.act a ≫ o.onB.act c = o.onB.act (c * a) :=
  (o.onB.map_mul c a).symm

theorem act_natCast' (o : D.OAct O) (n : ℕ) : o.onB.act (n : O) = 𝟙 D.P.A ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, act_zero', pow_zero]
  | succ n ih => rw [Nat.cast_succ, ← act_add', ih, o.onB.map_one, pow_succ]

theorem act_pow' (o : D.OAct O) (a : O) (n : ℕ) : o.onB.act a ^ n = o.onB.act ((n : O) * a) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, act_zero']
  | succ n ih => rw [pow_succ, ih, act_add', Nat.cast_succ, add_one_mul]

theorem prod_gam {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] (x : T ⟶ A) {U : Type} [CommGroup U]
    (k : (T.left ⟶ A.left) → U) :
    ∏ i : Fin 4, k (x.left ≫ (![(𝟙 A ^ 5).left, (𝟙 A ^ 4).left, 𝟙 _, (1 : A ⟶ A).left] : Fin 4 → _) i) ^
      (![2, -3, -2, 3] : Fin 4 → ℤ) i =
      k (x ^ 5).left ^ 2 * (k (x ^ 4).left ^ 3)⁻¹ * (k x.left ^ 2)⁻¹ * k (1 : T ⟶ A).left ^ 3 := by
  rw [Fin.prod_univ_four]
  show k (x ≫ 𝟙 A ^ 5).left ^ (2 : ℤ) * k (x ≫ 𝟙 A ^ 4).left ^ (-3 : ℤ) * k (x ≫ 𝟙 A).left ^ (-2 : ℤ) *
    k (x ≫ 1).left ^ (3 : ℤ) = _
  rw [MonObj.comp_pow, MonObj.comp_pow, MonObj.comp_one, Category.comp_id, zpow_neg, zpow_neg, zpow_ofNat, zpow_ofNat,
    zpow_ofNat, zpow_ofNat]


set_option maxHeartbeats 1600000 in
theorem core_id (hG : GlobalFnsSt) (o : D.OAct O) (w : O) (u : GlobalTheory.PsiRescale.FourGen D.P.L (o.onB.act w)) (hu : Normd u)
    (gam : LB.Gen (LB.LinComb D.P.L (K := Fin 4) ![(𝟙 D.P.A ^ 5).left, (𝟙 D.P.A ^ 4).left, 𝟙 _, (1 : D.P.A ⟶ D.P.A).left] ![2, -3, -2, 3]))
    (hgam : Normd gam)
    (ra : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (o.onB.act (star (1 + w))) (o.onB.act (1 + w))) rosatiε))
    (hra : GlobalTheory.TorusExt.IsRos D.P.L (o.onB.act (star (1 + w))) (o.onB.act (1 + w)) ra)
    (rw' : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (o.onB.act (star w)) (o.onB.act w)) rosatiε))
    (hrw : GlobalTheory.TorusExt.IsRos D.P.L (o.onB.act (star w)) (o.onB.act w) rw')
    (hw : w + star w = 1) {T : Over (Spec (CommRingCat.of R))} (b : T ⟶ D.P.A) (z : T.left) {J} (hJ : Good D.P.L z J) :
    val u (b ^ 4).left z J * val₂ ra z J ((b ^ 4) ≫ o.onB.act (1 + w)) b ^ 2 * val gam (b ≫ o.onB.act (1 + w)).left z J =
      th D z J (b ^ 4 * b ^ 4) ((b ^ 4) ≫ o.onB.act (star w * w)) b ^ 2 * th D z J (b ^ 4) (b ^ 4) b ^ 2 *
        val gam b.left z J ^ 2 * val₂ rw' z J ((b ^ 4) ≫ o.onB.act w) b ^ 2 * val gam (b ≫ o.onB.act w).left z J := by
  have hm : ∀ t : O, IsMonHom (o.onB.act t) := o.onB.hom
  have Gu := (grep_gen (Y := D.P.A) u hu.1 (o.onB.act 4).left).congr (P' := fun _ _ h =>
      h (o.onB.act 4 * (o.onB.act 4 ≫ o.onB.act w)).left * (h (o.onB.act 4).left ^ 2)⁻¹ *
        (h (o.onB.act 4 ≫ o.onB.act w).left)⁻¹ * h (1 : D.P.A ⟶ D.P.A).left ^ 2)
    (fun _ _ h => GlobalTheory.PsiWZeroPull.prod_four _ _ h) (fun _ _ _ _ _ => rfl)
  have Gra := (grep_gen (Y := D.P.A) ra hra.1 (lift (o.onB.act 4 ≫ o.onB.act (1 + w)) (𝟙 D.P.A)).left).congr
    (fun _ _ h => prod_ros _ _ _ _ h) (fun _ _ _ _ _ => rfl)
  have Grw := (grep_gen (Y := D.P.A) rw' hrw.1 (lift (o.onB.act 4 ≫ o.onB.act w) (𝟙 D.P.A)).left).congr
    (fun _ _ h => prod_ros _ _ _ _ h) (fun _ _ _ _ _ => rfl)
  have Gga := (grep_gen (Y := D.P.A) gam hgam.1 (o.onB.act (1 + w)).left).congr (fun _ _ h => prod_gam _ h)
    (fun _ _ _ _ _ => rfl)
  have Ggw := (grep_gen (Y := D.P.A) gam hgam.1 (o.onB.act w).left).congr (fun _ _ h => prod_gam _ h)
    (fun _ _ _ _ _ => rfl)
  have Ggb := (grep_gen (Y := D.P.A) gam hgam.1 (Over.Hom.left (𝟙 D.P.A))).congr (fun _ _ h => prod_gam _ h)
    (fun _ _ _ _ _ => rfl)
  have Gt2 := grep_cub (D := D) (Y := D.P.A) (o.onB.act 4 * o.onB.act 4) (o.onB.act 4 ≫ o.onB.act (star w * w)) (𝟙 D.P.A)
  have Gt1 := grep_cub (D := D) (Y := D.P.A) (o.onB.act 4) (o.onB.act 4) (𝟙 D.P.A)
  have key := (((Gu.mul (Gra.pow 2)).mul Gga).mul (((((Gt2.pow 2).mul (Gt1.pow 2)).mul (Ggb.pow 2)).mul
    (Grw.pow 2)).mul Ggw).inv).triv hG (fun U _ h => by
      clear Gu Gra Grw Gga Ggw Ggb Gt2 Gt1
      have e1 : 𝟙 D.P.A = o.onB.act 1 := o.onB.map_one.symm
      have e0 : (1 : D.P.A ⟶ D.P.A) = o.onB.act 0 := (act_zero' o).symm
      have hsw : star w = 1 - w := eq_sub_of_add_eq' hw
      simp only [e1, e0, act_add', act_comp', act_pow', star_add, star_one, hsw]
      ring_nf
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one]
      abel) (fun y I hI => by
      clear Gu Gra Grw Gga Ggw Ggb Gt2 Gt1
      have C : IsCub (cubV D.cub (T := 𝟙_ _) y I) := isCub_cubV D.cub hI
      have o1 : ∀ t : O, (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A).left ≫ (o.onB.act t).left =
          (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A).left := fun t => by
        rw [← Over.comp_left, MonObj.one_comp]
      have l1 : ∀ t t' : O, (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A).left ≫
          (lift (o.onB.act t ≫ o.onB.act t') (𝟙 D.P.A)).left =
          (lift (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A) 1).left := fun t t' => by
        rw [← Over.comp_left, comp_lift, Category.comp_id, ← Category.assoc, MonObj.one_comp, MonObj.one_comp]
      beta_reduce
      rw [o1, l1, l1, o1, o1, Over.id_left, Category.comp_id, normd_one hu hI, normd_one hgam hI]
      have r1 := hra.val_origin hI
      have r2 := hrw.val_origin hI
      unfold val₂ at r1 r2
      rw [r1, r2]
      simp only [MonObj.comp_mul, MonObj.one_comp, Category.comp_id, _root_.mul_one, C.face, one_pow, inv_one, normd_one hgam hI]) T b z J hJ
  have c4 : b ≫ o.onB.act 4 = b ^ 4 := by
    have := act_natCast' o 4
    rw [Nat.cast_ofNat] at this
    rw [this, comp_id_pow]
  beta_reduce at key
  simp only [← Over.comp_left, comp_lift, ← Category.assoc, c4, MonObj.comp_mul, Category.comp_id] at key
  exact mul_inv_eq_one.1 key


set_option maxHeartbeats 800000 in
theorem sign_rel : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (O : Type) [CommRing O] [StarRing O] [Module O D.X] (o : D.OAct O) (w : O), w + star w = 1 → ∀ u : GlobalTheory.PsiRescale.FourGen D.P.L (o.onB.act w), Normd u → ∀ gam : LB.Gen (LB.LinComb D.P.L (K := Fin 4) ![(𝟙 D.P.A ^ 5).left, (𝟙 D.P.A ^ 4).left, 𝟙 _, (1 : D.P.A ⟶ D.P.A).left] ![2, -3, -2, 3]), Normd gam → ∀ p q r : QkPt D F 4, q.y = w • p.y → r.y = (1 + w) • p.y → GtAct o w p.g q.g → GtAct o (1 + w) p.g r.g → ∀ (z : (TF (R := R) F).left) J, Good D.P.L z J → ∀ s s' s'' : ((TF (R := R) F).left.presheaf.stalk z)ˣ, s * (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi (p.y)) (jFK (R := R) F) z J) * rigV D (TF (R := R) F).hom z J) = val (p.g.s p.y) (𝟙 _) z J ^ 2 * val gam p.g.b.left z J → s' * (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi (q.y)) (jFK (R := R) F) z J) * rigV D (TF (R := R) F).hom z J) = val (q.g.s q.y) (𝟙 _) z J ^ 2 * val gam q.g.b.left z J → s'' * (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi (r.y)) (jFK (R := R) F) z J) * rigV D (TF (R := R) F).hom z J) = val (r.g.s r.y) (𝟙 _) z J ^ 2 * val gam r.g.b.left z J → s'' = s ^ 2 * s' → @id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.tau p.y (w • p.y)) (jFK (R := R) F) z J) * val u (cP D (TF (R := R) F) p.y).left z J = @id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi (p.y)) (jFK (R := R) F) z J) * rigV D (TF (R := R) F).hom z J := by
  intro R _ _ D F _ _ O _ _ _ o w hw u hu gam hgam p q r hq hr hgq hgr z J hJ s s' s'' hs hs' hs'' hss
  have hG : GlobalFnsSt := GlobalTheory.firstFiveLaws.1.globalFns
  have hb4 : cP D (TF (R := R) F) p.y = p.g.b ^ 4 := cPoint_y p
  obtain ⟨qb, qv⟩ := (GlobalTheory.TorusExt.gtAct_iff_val hG o w p.g q.g).1 hgq
  obtain ⟨rb, rv⟩ := (GlobalTheory.TorusExt.gtAct_iff_val hG o (1 + w) p.g r.g).1 hgr
  have eq1 := qv (w • p.y) z J hJ
  have eq2 := rv ((1 + w) • p.y) z J hJ
  have sm1 : star w • w • p.y = (star w * w) • p.y := smul_smul _ _ _
  have sm2 : star (1 + w) • (1 + w) • p.y = (p.y + p.y) + (star w * w) • p.y := by
    rw [smul_smul, show star (1 + w) * (1 + w) = 1 + 1 + star w * w by
      rw [star_add, star_one]; linear_combination hw, add_smul, add_smul, one_smul]
  have e3 : (1 + w) • p.y = p.y + w • p.y := by rw [add_smul, one_smul]
  rw [sm1, GlobalTheory.TorusExt.cPoint_smul o, hb4] at eq1
  rw [sm2, GlobalTheory.TorusExt.cPoint_smul o, hb4] at eq2
  have g1 := GlobalTheory.TorusExt.charVal_add p.g hJ p.y p.y
  have g2 := GlobalTheory.TorusExt.charVal_add p.g hJ (p.y + p.y) ((star w * w) • p.y)
  rw [cPoint_add, GlobalTheory.TorusExt.cPoint_smul o, hb4] at g2
  rw [hb4] at g1
  have cid := core_id hG o w u hu gam hgam (GlobalTheory.TorusExt.rosGen hG o (1 + w)) (GlobalTheory.TorusExt.rosGen_isRos hG o (1 + w))
    (GlobalTheory.TorusExt.rosGen hG o w) (GlobalTheory.TorusExt.rosGen_isRos hG o w) hw p.g.b z hJ
  have vτ : @id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.tau p.y (w • p.y)) (jFK (R := R) F) z J) =
      @id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi ((1 + w) • p.y)) (jFK (R := R) F) z J) *
        (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi p.y) (jFK (R := R) F) z J))⁻¹ *
        (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi (w • p.y)) (jFK (R := R) F) z J))⁻¹ *
        (rigV D (TF (R := R) F).hom z J)⁻¹ := by
    rw [e3]
    exact (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) ((val_inv _ _).trans
        (congrArg (·⁻¹) ((val_pull hJ _ _ _).trans rfl))))
  have gq : val gam q.g.b.left z J = val gam (p.g.b ≫ o.onB.act w).left z J := by rw [qb]
  have gr : val gam r.g.b.left z J = val gam (p.g.b ≫ o.onB.act (1 + w)).left z J := by rw [rb]
  rw [hq, gq] at hs'
  rw [hr, gr] at hs''
  rw [vτ, hb4]
  simp only [id_eq] at hs hs' hs'' ⊢
  apply Additive.ofMul.injective
  have E := fun {a c : ((TF (R := R) F).left.presheaf.stalk z)ˣ} (e : a = c) => congrArg Additive.ofMul e
  have hs := E hs; have hs' := E hs'; have hs'' := E hs''; have hss := E hss
  have eq1 := E eq1; have eq2 := E eq2; have g1 := E g1; have g2 := E g2; have cid := E cid
  simp only [ofMul_mul, ofMul_inv, ofMul_pow] at hs hs' hs'' hss eq1 eq2 g1 g2 cid ⊢
  linear_combination (norm := module) hs'' - 2 • hs - hs' - hss + 2 • eq2 - 2 • eq1 + 2 • g2 + 2 • g1 + cid

end GlobalTheory.PsiSignRel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiEqTauFromSignRelationFourTorsionStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_eq_tau_from_sign_relation_four_torsion : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (O : Type) [CommRing O] [StarRing O] [Module O D.X] (o : D.OAct O) (w : O), w + star w = 1 → ∀ u : GlobalTheory.PsiRescale.FourGen D.P.L (o.onB.act w), Normd u → ∀ gam : LB.Gen (LB.LinComb D.P.L (K := Fin 4) ![(𝟙 D.P.A ^ 5).left, (𝟙 D.P.A ^ 4).left, 𝟙 _, (1 : D.P.A ⟶ D.P.A).left] ![2, -3, -2, 3]), Normd gam → ∀ p q r : QkPt D F 4, q.y = w • p.y → r.y = (1 + w) • p.y → GtAct o w p.g q.g → GtAct o (1 + w) p.g r.g → ∀ (z : (TF (R := R) F).left) J, Good D.P.L z J → ∀ s s' s'' : ((TF (R := R) F).left.presheaf.stalk z)ˣ, s * (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi (p.y)) (jFK (R := R) F) z J) * rigV D (TF (R := R) F).hom z J) = val (p.g.s p.y) (𝟙 _) z J ^ 2 * val gam p.g.b.left z J → s' * (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi (q.y)) (jFK (R := R) F) z J) * rigV D (TF (R := R) F).hom z J) = val (q.g.s q.y) (𝟙 _) z J ^ 2 * val gam q.g.b.left z J → s'' * (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi (r.y)) (jFK (R := R) F) z J) * rigV D (TF (R := R) F).hom z J) = val (r.g.s r.y) (𝟙 _) z J ^ 2 * val gam r.g.b.left z J → s'' = s ^ 2 * s' → @id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.tau p.y (w • p.y)) (jFK (R := R) F) z J) * val u (cP D (TF (R := R) F) p.y).left z J = @id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi (p.y)) (jFK (R := R) F) z J) * rigV D (TF (R := R) F).hom z J := by
  first | exact @GlobalTheory.PsiSignRel.sign_rel | exact GlobalTheory.PsiSignRel.sign_rel | (intros; apply GlobalTheory.PsiSignRel.sign_rel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricThetaElementLevelFourSquare
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricThetaElementLevelFourSquare
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section

namespace GlobalTheory.ThetaSquare
open GlobalTheory.SymLiftOdd GlobalTheory.UT.SymFrame

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}

theorem eq_liftFun_mul (hL : L.IsLB) {k : ℤ} (s s' : LB.Sec (LPow A L k T)) (a : Γ(T.left, ⊤))
    (h : ∀ y J, Good L y J →
      sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) s' (𝟙 _) y J =
        gs (fst T A).left y ⊤ a * sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) s (𝟙 _) y J)
    (j) : s'.f j = liftFun A _ a * s.f j := by
  refine fn_ext fun y hy => ?_
  choose I hI using fun χ : (T ⊗ A).left ⟶ A.left => exists_chart hL (χ y)
  have e₁ := sec_trans (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) s' (𝟙 _) y hy (Good.mem hI _ (𝟙 _))
  have e₂ := sec_trans (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) s (𝟙 _) y hy (Good.mem hI _ (𝟙 _))
  have e₃ : gs (𝟙 _) y _ (liftFun A ((LPow A L k T).U j) a) = gs (fst T A).left y ⊤ a :=
    (gs_res (𝟙 _) y le_top hy _).trans ((gs_pull (𝟙 _) (fst T A).left y ⊤ trivial a).trans (by rw [Category.id_comp]))
  refine e₁.trans (Eq.trans ?_ ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) e₃ e₂)).symm)
  exact (congrArg _ (h y I hI)).trans (mul_left_comm _ _ _)

theorem indep (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {P v} (h : GRep L (T ⊗ A) P v)
    (hP : ∀ (U : Type) [CommGroup U] (h : ((T ⊗ A).left ⟶ A.left) → U), P U h = 1) (m m' : T ⊗ A ⟶ A)
    (y : (T ⊗ A).left) (J) (hJ : Good L y J) : v _ (lift (fst T A) m) y J = v _ (lift (fst T A) m') y J := by
  obtain ⟨K, _, φ, ε, s, hs, p, hv⟩ := h
  obtain ⟨a, ha⟩ := exists_constT hG hA hL (fun U _ h => (p U h).trans (hP U h)) hs
  exact (hv _ _ y J hJ).symm.trans ((ha m y J hJ).trans ((ha m' y J hJ).symm.trans (hv _ _ y J hJ)))

theorem grep_sigma {σ : LB.Gen (LB.LinComb L (K := Fin 2) ![(ι[A]).left, 𝟙 A.left] ![1, -1])} (hσ : σ.IsGen)
    {Y : Over S} (w : Y ⟶ A) :
    GRep L Y (fun _ _ h => h (w⁻¹).left * (h w.left)⁻¹) (fun _ r z J => val σ (r ≫ w).left z J) :=
  (grep_gen σ hσ w.left).congr
    (fun _ _ h => by
      rw [Fin.prod_univ_two]
      show h (w⁻¹).left ^ (1 : ℤ) * h (w.left ≫ 𝟙 _) ^ (-1 : ℤ) = _
      rw [Category.comp_id, zpow_one, zpow_neg_one])
    (fun _ _ _ _ _ => rfl)

theorem grep_two {n : T ⊗ A ⟶ A} {a b : ℤ}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, n.left] ![a, b])} (hα : α.IsGen) (w : T ⊗ A ⟶ A) :
    GRep L (T ⊗ A) (fun _ _ h => h w.left ^ a * h (lift (fst T A) w ≫ n).left ^ b)
      (fun _ r z J => val α (r ≫ lift (fst T A) w).left z J) :=
  (grep_gen α hα (lift (fst T A) w).left).congr
    (fun _ _ h => by
      rw [Fin.prod_univ_two]
      show h (lift (fst T A) w ≫ snd T A).left ^ a * h (lift (fst T A) w ≫ n).left ^ b = _
      rw [lift_snd])
    (fun _ _ _ _ _ => rfl)

theorem square_val (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB)
    {σ : LB.Gen (LB.LinComb L (K := Fin 2) ![(ι[A]).left, 𝟙 A.left] ![1, -1])} (hσ : σ.IsGen)
    (hσ₁ : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ σ (eSec A)) (LB.oneGen L))
    (θ : ThetaGrp A L ((4 : ℕ) : ℤ) T) (hx : θ.pt ^ 4 = 1) (nu : LB.Gen (negLB A L ((4 : ℕ) : ℤ) T))
    (hnu : ∀ y J, Good L y J → ∀ m, negVal nu y J m = (val σ m.left y J ^ 4)⁻¹)
    (hs : LB.Gen.Corr L _ _ _ _ (symGen A L ((4 : ℕ) : ℤ) θ nu) (LB.oneGen L))
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ 2).left] ![((4 : ℕ) : ℤ), -((1 : ℕ) : ℤ)])}
    (hα : α.IsGen) (y : (T ⊗ A).left) (J) (hJ : Good L y J) :
    thetaVal θ y J (snd T A) * (thetaVal θ y J ((fst T A ≫ θ.pt) * snd T A) *
      val α (lift (fst T A) ((fst T A ≫ θ.pt) * ((fst T A ≫ θ.pt) * snd T A))).left y J) =
      val σ ((fst T A ≫ θ.pt) ^ 2).left y J * val α (lift (fst T A) (snd T A)).left y J := by
  have := hA.comm
  have hX : (fst T A ≫ θ.pt) ^ 4 = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
  have s₁ : val σ (1 : T ⊗ A ⟶ A).left y J = 1 :=
    (val_pull hJ σ (eSec A) (T ⊗ A).hom).symm.trans ((val_corr hJ hσ₁ _).trans (val_one _))
  have sy := (val_symGen θ nu rfl hJ 1).symm.trans ((val_corr hJ hs _).trans (val_one _))
  rw [hnu y J hJ, hnu y J hJ, s₁, _root_.mul_one, inv_one] at sy
  have gθ := fun w => grep_two (L := L) (n := translPt A θ.pt) (a := ((4 : ℕ) : ℤ)) (b := -((4 : ℕ) : ℤ))
    (α := θ.φ) θ.isGen w
  have cl : ∀ m w : T ⊗ A ⟶ A, lift (fst T A) m ≫ lift (fst T A) w = lift (fst T A) (lift (fst T A) m ≫ w) :=
    fun m w => by rw [comp_lift, lift_fst]
  have H₁ := indep hG hA hL (((gθ (snd T A)).mul ((gθ ((fst T A ≫ θ.pt) * snd T A)).mul
    (grep_two hα ((fst T A ≫ θ.pt) * ((fst T A ≫ θ.pt) * snd T A))))).mul (grep_two hα (snd T A)).inv)
    (fun U _ h => by
      have e : ((fst T A ≫ θ.pt) * ((fst T A ≫ θ.pt) * snd T A)) ^ 2 = snd T A ^ 2 := by
        rw [← _root_.mul_assoc, mul_pow, ← sq, ← pow_mul, hX, _root_.one_mul]
      simp only [lift_translPt, MonObj.comp_pow, lift_snd, e]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_one]
      module) (snd T A) (fst T A ≫ θ.pt)⁻¹ y J hJ
  have H₂ := indep hG hA hL ((((grep_sigma hσ (snd T A)⁻¹).pow 4).inv.mul ((grep_two hα (snd T A)).mul
    (grep_two hα (snd T A)⁻¹).inv)).mul (grep_sigma hσ (snd T A ^ 2)).inv)
    (fun U _ h => by
      simp only [MonObj.comp_pow, lift_snd, inv_inv, inv_pow]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]
      module) (fst T A ≫ θ.pt) 1 y J hJ
  simp only [cl, MonObj.comp_mul, MonObj.comp_pow, GrpObj.comp_inv, lift_snd, lift_fst_assoc, mul_inv_cancel, _root_.mul_one,
    inv_one, one_pow, s₁] at H₁ H₂
  replace H₁ := congrArg Additive.ofMul H₁
  replace H₂ := congrArg Additive.ofMul H₂
  replace sy := congrArg Additive.ofMul sy
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one, thetaVal] at H₁ H₂ sy ⊢
  linear_combination (norm := module) H₁ + H₂ + sy

theorem exists_symmetric_square : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (x : TFK (R := R) F ⟶ A.A), x ^ 4 = 1 → ∀ σ : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(ι[A.A]).left, 𝟙 A.A.left] ![1, -1]), σ.IsGen → LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ σ (eSec A.A)) (LB.oneGen A.L) → ∃ θ : ThetaGrp A.A A.L ((4 : ℕ) : ℤ) (TFK (R := R) F), θ.pt = x ∧ (∃ nu : LB.Gen (negLB A.A A.L ((4 : ℕ) : ℤ) (TFK (R := R) F)), nu.IsGen ∧ LB.Gen.Corr A.L _ _ _ _ (symGen A.A A.L ((4 : ℕ) : ℤ) θ nu) (LB.oneGen A.L)) ∧ ∃ c : F, (∀ z J, Good A.L z J → (val σ (x ^ 2).left z J).val = @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c)) ∧ ∀ (ψ : TFK (R := R) F ⊗ A.A ⟶ TFK (R := R) F ⊗ A.A) (m : TFK (R := R) F ⊗ A.A ⟶ A.A) (hm : ψ ≫ snd _ _ = m), ψ ≫ fst _ _ = fst _ _ → m = snd _ _ ^ 2 → ∀ α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := R) F) A.A).left, m.left] ![((4 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]), α.IsGen → ∀ (t : SecA A F 1) (t₁ t₂ t₃ : SecA A F 4), IsTwistPull A.A A.L ψ m hm ((4 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α t t₁ → IsActOf A.A A.L ((4 : ℕ) : ℤ) θ t₁ t₂ → IsActOf A.A A.L ((4 : ℕ) : ℤ) θ t₂ t₃ → ∀ j, t₃.f j = liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * t₁.f j := by
  intro R _ _ A F _ _ _ x hx σ hσ hσ₁
  have hG : GlobalFnsSt := GlobalTheory.firstFiveLaws.1.globalFns
  have hL := A.isLB
  have := A.isAb.comm
  obtain ⟨θ₀, h₀⟩ := GlobalTheory.ThetaLift.exists_theta_of_field (FractionRing R) A (TFK (R := R) F) F (Iso.refl _) 4 x hx
  obtain ⟨nu, hnu, vn⟩ := ((grep_sigma hσ (snd (TFK (R := R) F) A.A)).pow 4).inv.out hL
    ![(snd (TFK (R := R) F) A.A).left, (snd (TFK (R := R) F) A.A ≫ ι[A.A]).left] ![((4 : ℕ) : ℤ), -((4 : ℕ) : ℤ)]
    (fun U _ h => by
      rw [Fin.prod_univ_two]
      show _ = h (snd (TFK (R := R) F) A.A).left ^ ((4 : ℕ) : ℤ) * h ((snd (TFK (R := R) F) A.A)⁻¹).left ^ (-((4 : ℕ) : ℤ))
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
  have vn' : ∀ y J, Good A.L y J → ∀ m, negVal (L := A.L) (k := ((4 : ℕ) : ℤ)) nu y J m = (val σ m.left y J ^ 4)⁻¹ :=
    fun y J hJ m => (vn _ _ y J hJ).trans (by beta_reduce; rw [lift_snd])
  obtain ⟨a, ha⟩ := exists_symConst hG A.isAb hL θ₀ (nu := nu) hnu
  obtain ⟨b, hb⟩ : ∃ b : Γ((TFK (R := R) F).left, ⊤)ˣ, a = b ^ 2 := by
    let e := (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (k := F) (e a.val) two_pos
    have e₁ : (e.symm r) ^ 2 = a.val := by rw [← map_pow, hr, RingEquiv.symm_apply_apply]
    have u : IsUnit (e.symm r) := (isUnit_pow_iff two_ne_zero).1 (e₁ ▸ a.isUnit)
    exact ⟨u.unit, Units.ext e₁.symm⟩
  obtain ⟨θ, hpt, hv⟩ := exists_scale hL θ₀ b⁻¹
  have hθ : θ.pt = x := hpt.trans h₀
  have hs : LB.Gen.Corr A.L _ _ _ _ (symGen A.A A.L ((4 : ℕ) : ℤ) θ nu) (LB.oneGen A.L) := corr_of_val hL fun y J hJ => by
    have e₁ := (val_symGen θ₀ nu h₀ hJ (snd _ _)).symm.trans (ha _ y J hJ)
    rw [val_one, id_eq_lift, val_symGen θ nu hθ hJ, hv y J hJ, hv y J hJ, map_inv]
    rw [hb, map_pow] at e₁
    apply Additive.ofMul.injective
    replace e₁ := congrArg Additive.ofMul e₁
    simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_one] at e₁ ⊢
    linear_combination (norm := module) e₁
  obtain ⟨K, _, φ, ε, s, hs', p, vs⟩ := grep_sigma hσ (x ^ 2)
  obtain ⟨c, hc⟩ := H1.exists_const A.L hL (𝟙 _) (fun v => ⟨v, by simp⟩) s hs' (fun U _ h => (p U h).trans (by
    have e : (x ^ 2)⁻¹ = x ^ 2 := by rw [inv_eq_iff_mul_eq_one, ← pow_add]; exact hx
    beta_reduce
    rw [e, mul_inv_cancel]))
  have ec : (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom c) = c :=
    (Scheme.ΓSpecIso (CommRingCat.of F)).hom_inv_id_apply c
  refine ⟨θ, hθ, ⟨nu, hnu, hs⟩, (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom c, fun z J hJ => ?_, ?_⟩
  · have e₁ := vs _ (𝟙 _) z J hJ
    have e₂ := hc _ (𝟙 _) z J hJ
    beta_reduce at e₁
    rw [Category.id_comp, Over.id_left] at e₁
    rw [Category.id_comp] at e₂
    exact (congrArg Units.val e₁).symm.trans (e₂.trans (congrArg (gs _ z ⊤) ec.symm))
  · rintro ψ m hm hψ rfl α hα t t₁ t₂ t₃ h₁ h₂ h₃ j
    rw [ec]
    refine eq_liftFun_mul hL t₁ t₃ c (fun y J hJ => ?_) j
    subst hθ
    have key := square_val hG A.isAb hL hσ hσ₁ θ hx nu vn' hs hα y J hJ
    have e₁ := vs _ (fst _ A.A) y J hJ
    have e₂ := hc _ (fst _ A.A).left y J hJ
    beta_reduce at e₁
    rw [MonObj.comp_pow] at e₁
    rw [Category.comp_id, e₁] at e₂
    have hX : (fst (TFK (R := R) F) A.A ≫ θ.pt) ^ 4 = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
    have eψ : lift (fst (TFK (R := R) F) A.A) ((fst _ _ ≫ θ.pt) * ((fst _ _ ≫ θ.pt) * snd _ _)) ≫ ψ =
        lift (fst _ _) (snd _ _) ≫ ψ := by
      refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
      · rw [Category.assoc, Category.assoc, hψ, lift_fst, lift_fst]
      · rw [Category.assoc, Category.assoc, hm, MonObj.comp_pow, MonObj.comp_pow, lift_snd, lift_snd,
          ← _root_.mul_assoc, mul_pow, ← sq, ← pow_mul, hX, _root_.one_mul]
    rw [← e₂, id_eq_lift, ThetaLin.sval_of_isTwistPull A.A h₃ _ y hJ, ThetaLin.sval_of_isTwistPull A.A h₂ _ y hJ,
      ThetaLin.sval_of_isTwistPull A.A h₁ _ y hJ, ThetaLin.sval_of_isTwistPull A.A h₁ _ y hJ]
    simp only [← Over.comp_left]
    rw [lift_translT, lift_translT, eψ]
    have alg : ∀ {M : Type} [CommMonoid M] (a b c d e : Mˣ) (w : M), a * (b * c) = d * e →
        a.val * (b.val * (c.val * w)) = d.val * (e.val * w) := fun a b c d e w h => by
      have h' := congrArg (fun u => Units.val u * w) h
      simpa only [Units.val_mul, _root_.mul_assoc] using h'
    exact alg _ _ _ _ _ _ key

end GlobalTheory.ThetaSquare

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricThetaElementLevelFourSquareStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symmetric_thetaElement_level_four_square : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (x : TFK (R := R) F ⟶ A.A), x ^ 4 = 1 → ∀ σ : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(ι[A.A]).left, 𝟙 A.A.left] ![1, -1]), σ.IsGen → LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ σ (eSec A.A)) (LB.oneGen A.L) → ∃ θ : ThetaGrp A.A A.L ((4 : ℕ) : ℤ) (TFK (R := R) F), θ.pt = x ∧ (∃ nu : LB.Gen (negLB A.A A.L ((4 : ℕ) : ℤ) (TFK (R := R) F)), nu.IsGen ∧ LB.Gen.Corr A.L _ _ _ _ (symGen A.A A.L ((4 : ℕ) : ℤ) θ nu) (LB.oneGen A.L)) ∧ ∃ c : F, (∀ z J, Good A.L z J → (val σ (x ^ 2).left z J).val = @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c)) ∧ ∀ (ψ : TFK (R := R) F ⊗ A.A ⟶ TFK (R := R) F ⊗ A.A) (m : TFK (R := R) F ⊗ A.A ⟶ A.A) (hm : ψ ≫ snd _ _ = m), ψ ≫ fst _ _ = fst _ _ → m = snd _ _ ^ 2 → ∀ α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := R) F) A.A).left, m.left] ![((4 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]), α.IsGen → ∀ (t : SecA A F 1) (t₁ t₂ t₃ : SecA A F 4), IsTwistPull A.A A.L ψ m hm ((4 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α t t₁ → IsActOf A.A A.L ((4 : ℕ) : ℤ) θ t₁ t₂ → IsActOf A.A A.L ((4 : ℕ) : ℤ) θ t₂ t₃ → ∀ j, t₃.f j = liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * t₁.f j := by
  first | exact @GlobalTheory.ThetaSquare.exists_symmetric_square | exact GlobalTheory.ThetaSquare.exists_symmetric_square | (intros; apply GlobalTheory.ThetaSquare.exists_symmetric_square <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetrySignsTwoTorsionRelationOfLbIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetrySignsTwoTorsionRelationOfLbIso
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.SignSym

section Move
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem exists_gen_onA (U : UnifPre I D A G) {n : ℕ} (fG : Fin n → (G ⟶ G)) (fA : Fin n → (A.A ⟶ A.A))
    (hf : ∀ k, (Over.pullback (jK R)).map (fG k) ≫ U.gen.hom = U.gen.hom ≫ fA k) (ε : Fin n → ℤ)
    (φ : Fin n → (G.left ⟶ G.left)) (hφ : ∀ k, φ k = (fG k).left)
    (φA : Fin n → (A.A.left ⟶ A.A.left)) (hφA : ∀ k, φA k = (fA k).left)
    (t : LB.Gen (LB.LinComb U.LG.L φ ε)) (ht : t.IsGen) :
    ∃ a : LB.Gen (LB.LinComb A.L φA ε), a.IsGen := by
  obtain ⟨w, hw⟩ := U.ext
  let π : A.A ⟶ (Over.pullback (jK R)).obj G := U.gen.inv
  obtain ⟨a, ha, -⟩ := H1.exists_gen_move U.LG.isLB (DVR.linComb_isLB _ A.isLB _ _) w ((isGen_iff w).1 hw)
    φ (fun k => (π ≫ (Over.pullback (jK R)).map (fG k)).left) ε (π.left ≫ pullback.fst G.hom (jK R))
    (fun k => by
      rw [hφ k]
      exact (Category.assoc _ _ _).trans ((congrArg (π.left ≫ ·) (pullback.lift_fst _ _ _)).trans
          (Category.assoc _ _ _).symm)) t ht
  obtain ⟨b, hb⟩ := PsiPull.exists_gen_flat _ _ _ a ha
  obtain ⟨α, hα, -⟩ := exists_gen A.isLB (φ' := φA) (ε' := ε)
    (fun V _ h => Finset.prod_congr rfl fun k _ => by
      have e : π ≫ (Over.pullback (jK R)).map (fG k) ≫ U.gen.hom = fA k := by
        rw [hf k, ← Category.assoc, U.gen.inv_hom_id, Category.id_comp]
      rw [hφA k]
      exact congrArg (fun q : A.A ⟶ A.A => h q.left ^ ε k) e) b hb
  exact ⟨α, hα⟩

end Move
end GlobalTheory.SignSym

namespace GlobalTheory.SignSym

theorem sign_sym : AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ w : O, LBIso U.LG.L (cubeLB G ![𝟙 G, oG.act w] U.LG.L) → ∃ σ : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(ι[A.A]).left, 𝟙 A.A.left] ![1, -1]), σ.IsGen ∧ LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ σ (eSec A.A)) (LB.oneGen A.L) ∧ ∀ (T : Over (Spec (CommRingCat.of (FractionRing R)))) (x : T ⟶ A.A), x ^ 2 = 1 → ∀ z J, Good A.L z J → val σ (x * (x ≫ oA.act w)).left z J = val σ x.left z J ^ 2 * val σ (x ≫ oA.act w).left z J := by
  intro R _ _ _ I hI D A G _ _ hG U O _ _ _ o oA oG hlin w hw
  have hL := GlobalTheory.firstFiveLaws
  have hGF := hL.1.globalFns
  have := U.gen_hom
  haveI := oG.hom w
  haveI := oA.hom w
  obtain ⟨-, E, eG, eA, -, -, -⟩ := IntEnd.exists_nsmul_and_neg hL R I hI D A G hG U
  have rId : (Over.pullback (jK R)).map (𝟙 G) ≫ U.gen.hom = U.gen.hom ≫ 𝟙 A.A := by
    rw [(Over.pullback (jK R)).map_id, Category.id_comp, Category.comp_id]
  have rW : (Over.pullback (jK R)).map (oG.act w) ≫ U.gen.hom = U.gen.hom ≫ oA.act w := hlin.ext w
  have rInv : (Over.pullback (jK R)).map (ι[G]) ≫ U.gen.hom = U.gen.hom ≫ ι[A.A] := by
    have h := E.ext
    rw [eG, eA, Hom.inv_def, Hom.inv_def, Category.id_comp, Category.id_comp] at h
    exact h
  have rOne : (Over.pullback (jK R)).map (1 : G ⟶ G) ≫ U.gen.hom = U.gen.hom ≫ (1 : A.A ⟶ A.A) := by
    rw [(Over.pullback (jK R)).map_one, MonObj.one_comp, MonObj.comp_one]
  have rSum : (Over.pullback (jK R)).map (𝟙 G * oG.act w) ≫ U.gen.hom = U.gen.hom ≫ (𝟙 A.A * oA.act w) := by
    rw [(Over.pullback (jK R)).map_mul, MonObj.mul_comp, MonObj.comp_mul, rId, rW]

  obtain ⟨σ₀, hσ₀⟩ := exists_gen_onA U.toUnifPre ![ι[G], 𝟙 G] ![ι[A.A], 𝟙 A.A]
    (fun k => by fin_cases k; exacts [rInv, rId]) ![1, -1] _ (fun k => by fin_cases k <;> rfl)
    ![(ι[A.A]).left, 𝟙 A.A.left] (fun k => by fin_cases k <;> rfl) U.symG U.symG_gen
  obtain ⟨⟨ρ, hρ, -⟩, -⟩ := GlobalTheory.JetSer.exists_unique_normPrim _ G U.LG (oG.act w) hw
  obtain ⟨β, hβ⟩ := exists_gen_onA U.toUnifPre ![𝟙 G, 𝟙 G * oG.act w, 𝟙 G, oG.act w, 1]
    ![𝟙 A.A, 𝟙 A.A * oA.act w, 𝟙 A.A, oA.act w, 1]
    (fun k => by fin_cases k; exacts [rId, rSum, rId, rW, rOne]) GlobalTheory.JetSer.primε (GlobalTheory.JetSer.primφ (oG.act w)) (fun k => by fin_cases k <;> rfl)
    (GlobalTheory.JetSer.primφ (oA.act w)) (fun k => by fin_cases k <;> rfl) ρ hρ

  let z₀ : A.A ⟶ A.A := 1
  have o₁ : z₀.left ≫ (ι[A.A]).left = z₀.left := by
    rw [← Over.comp_left, ← Hom.inv_def, inv_one]
  have o₂ : z₀.left ≫ 𝟙 A.A.left = z₀.left := Category.comp_id _
  obtain ⟨σ, hσ, vσ⟩ := exists_gen A.isLB (φ' := ![(ι[A.A]).left, 𝟙 A.A.left]) (ε' := ![1, -1])
    (fun V _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, o₁, o₂]
      rw [neg_neg, ← zpow_add, neg_add_cancel, zpow_zero, _root_.mul_one])
    (LB.mulGen A.L _ _ _ _ σ₀ (LB.invGen A.L _ _ (LB.pullGen A.L _ _ σ₀ z₀.left)))
    (mulGen_isGen _ _ _ _ _ _ _ hσ₀ (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ hσ₀ _)))
  have vσ' : ∀ (Z : Scheme.{0}) (r : Z ⟶ A.A.left) z J, Good A.L z J →
      val σ r z J = val σ₀ r z J * (val σ₀ (r ≫ z₀.left) z J)⁻¹ :=
    fun Z r z J hJ => (vσ Z r z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg _ ((val_inv _ _).trans
      (congrArg (·⁻¹) (val_pull hJ _ _ _)))))
  have e₁ : (1 : 𝟙_ (Over (Spec (CommRingCat.of (FractionRing R)))) ⟶ A.A) = η[A.A] := by simp [Hom.one_def]
  have e₀ : eSec A.A ≫ z₀.left = eSec A.A := by
    show η[A.A].left ≫ (1 : A.A ⟶ A.A).left = η[A.A].left
    rw [← Over.comp_left, MonObj.comp_one, e₁]
  have hσ1 : ∀ y J, Good A.L y J → val σ (eSec A.A) y J = 1 := fun y J hJ => by
    rw [vσ' _ _ y J hJ, e₀, mul_inv_cancel]
  have hσn : LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ σ (eSec A.A)) (LB.oneGen A.L) :=
    corr_of_val A.isLB fun y J hJ => by
      rw [val_pull hJ, Category.id_comp, val_one]
      exact hσ1 y J hJ
  refine ⟨σ, hσ, hσn, fun T x hx z J hJ => ?_⟩

  have hY : Function.Surjective A.A.hom.appTop.hom := (hGF _ _ A.isAb).2
  have hι : ι[A.A] = (𝟙 A.A)⁻¹ := by rw [Hom.inv_def, Category.id_comp]
  have hinv : ∀ {Y : Over (Spec (CommRingCat.of (FractionRing R)))} (f : Y ⟶ A.A), f ≫ ι[A.A] = f⁻¹ := fun f => by
    rw [Hom.inv_def]
  have c₁ : ι[A.A] ≫ oA.act w = oA.act w ≫ ι[A.A] := by
    have := IntEnd.id_zpow_comm (oA.act w) (-1)
    rw [zpow_neg_one, ← hι] at this
    exact this
  have c₂ : ι[A.A] ≫ (𝟙 A.A * oA.act w) = (𝟙 A.A * oA.act w) ≫ ι[A.A] := by
    rw [MonObj.comp_mul, Category.comp_id, c₁, hinv, hinv, mul_inv, hι]
  have nv : ∀ y I, Good A.L y I → val σ (1 : 𝟙_ (Over (Spec (CommRingCat.of (FractionRing R)))) ⟶ A.A).left y I = 1 :=
    fun y I hI => by rw [e₁]; exact hσ1 y I hI
  have H := ((SymFrame.hasGen_pull hβ (𝟙 A.A)).mul (SymFrame.hasGen_pull hβ (ι[A.A])).inv).unique A.isLB
    ((((SymFrame.hasGen_pull hσ (𝟙 A.A * oA.act w)).mul (SymFrame.hasGen_pull hσ (𝟙 A.A)).inv).mul
      (SymFrame.hasGen_pull hσ (𝟙 A.A)).inv).mul (SymFrame.hasGen_pull hσ (oA.act w)).inv)
    (fun V _ h => ?_) hY 1 (fun y I hI => ?_) T x z J hJ
  · have xi : x ≫ ι[A.A] = x := by
      rw [hinv]; exact inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hx)
    have xs : x ≫ (𝟙 A.A * oA.act w) = x * (x ≫ oA.act w) := by rw [MonObj.comp_mul, Category.comp_id]
    rw [xi, xs, Category.comp_id, mul_inv_cancel] at H
    apply Additive.ofMul.injective
    have a := congrArg Additive.ofMul H
    simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one] at a ⊢
    calc _ = (Additive.ofMul (val σ (x * x ≫ oA.act w).left z J) + -Additive.ofMul (val σ x.left z J) +
          -Additive.ofMul (val σ x.left z J) + -Additive.ofMul (val σ (x ≫ oA.act w).left z J)) +
          (2 • Additive.ofMul (val σ x.left z J) + Additive.ofMul (val σ (x ≫ oA.act w).left z J)) := by abel
      _ = _ := by rw [← a, zero_add]
  · simp only [GlobalTheory.JetSer.primφ, GlobalTheory.JetSer.primε, Fin.prod_univ_five, Fin.prod_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Matrix.cons_val_succ,
      Over.id_left, Category.id_comp, Category.comp_id, ← Over.comp_left, c₁, c₂, MonObj.comp_one]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    abel
  · rw [Category.comp_id, hinv, inv_one, MonObj.comp_mul, Category.comp_id, MonObj.one_comp, _root_.mul_one,
      mul_inv_cancel, nv y I hI]
    simp

end GlobalTheory.SignSym
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetrySignsTwoTorsionRelationOfLbIsoStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetry_signs_two_torsion_relation_of_lbIso : AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ w : O, LBIso U.LG.L (cubeLB G ![𝟙 G, oG.act w] U.LG.L) → ∃ σ : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(ι[A.A]).left, 𝟙 A.A.left] ![1, -1]), σ.IsGen ∧ LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ σ (eSec A.A)) (LB.oneGen A.L) ∧ ∀ (T : Over (Spec (CommRingCat.of (FractionRing R)))) (x : T ⟶ A.A), x ^ 2 = 1 → ∀ z J, Good A.L z J → val σ (x * (x ≫ oA.act w)).left z J = val σ x.left z J ^ 2 * val σ (x ≫ oA.act w).left z J := by
  first | exact @GlobalTheory.SignSym.sign_sym | exact GlobalTheory.SignSym.sign_sym | (intros; apply GlobalTheory.SignSym.sign_sym <;> assumption)
end
end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.PsiSign
open GlobalTheory.UT.SymFrame GlobalTheory.UT.PsiPull GlobalTheory.UT.CoefBasic

section Canon
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

theorem toHas {Y : Over (Spec (CommRingCat.of R))} {P v} (h : GRep D.P.L Y P v) : GlobalTheory.SymFrame.HasGen D.P.L Y P v := h

theorem val_double (hG : GlobalFnsSt) {a : D.P.A ⟶ D.P.A} (ha : a = 𝟙 D.P.A ^ 2) {x y : D.X} (hx : x = 2 • y)
    (u : LB.Gen (LB.LinComb D.P.L (Sum.elim (D.Oφ (𝟙 _) x) (D.Oφ a y)) (Sum.elim Oε Oinvε))) (hu : Normd u)
    {T : Over (Spec (CommRingCat.of R))} (b : T ⟶ D.P.A) (z : T.left) (J) (hJ : Good D.P.L z J) :
    val u b.left z J * th D z J (cP D T y) b b * (th D z J (cP D T y) (cP D T y) b)⁻¹ = 1 := by
  subst ha hx
  have ru : GRep D.P.L D.P.A _ (fun _ r z J => val u r.left z J) :=
    ⟨_, inferInstance, _, _, u, hu.1, fun U _ h => prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _
      (prod_O (𝟙 _) (2 • y) h) (prod_Oinv (𝟙 D.P.A ^ 2) y h), fun _ _ _ _ _ => rfl⟩
  have key := ((ru.mul (grep_cub (cP D _ y) (𝟙 _) (𝟙 _))).mul (grep_cub (cP D _ y) (cP D _ y) (𝟙 _)).inv).triv hG
    (fun U _ h => by
      rw [cPoint_nsmul, pow_two, pow_two, mul_comm (𝟙 D.P.A) (cP D D.P.A y * cP D D.P.A y),
        mul_comm (𝟙 D.P.A * 𝟙 D.P.A) (cP D D.P.A y), ← _root_.mul_assoc (cP D D.P.A y) (𝟙 _) (𝟙 _)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel)
    (fun w I hI => by
      have C : IsCub (cubV D.cub (T := 𝟙_ _) w I) := isCub_cubV D.cub hI
      beta_reduce
      rw [Category.comp_id, normd_one hu hI, C.face₃, C.face₃]
      simp) T b z J hJ
  beta_reduce at key
  rwa [comp_cP, Category.comp_id] at key

theorem exists_gam (hG : GlobalFnsSt) {a : D.P.A ⟶ D.P.A} (ha : a = 𝟙 D.P.A ^ 2) (κ : LB.Gen (kapLB D a 4 1))
    (hκ : Normd κ) (ν : LB.Gen (nuLB D 4)) (hν : Normd ν) :
    ∃ gam : LB.Gen (LB.LinComb D.P.L (K := Fin 4)
      ![(𝟙 D.P.A ^ 5).left, (𝟙 D.P.A ^ 4).left, 𝟙 _, (1 : D.P.A ⟶ D.P.A).left] ![2, -3, -2, 3]), Normd gam ∧
      ∀ (T : Over (Spec (CommRingCat.of R))) (g b : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J →
        th D z J (g ^ 4) (g ^ 4) b * (th D z J (g ^ 4) b b)⁻¹ * val κ b.left z J * val gam g.left z J =
          val κ (b * g * g).left z J * cubN (th D z J) 4 1 g (b * g) * cubN (th D z J) 4 (g ^ 4) g b *
            (th D z J (g ^ 4) b g)⁻¹ * val ν g.left z J := by
  subst ha
  obtain ⟨gam, hgam, -⟩ := (((grep_kap (n := 2) κ hκ.1 (𝟙 D.P.A ^ 2)).mul (grep_cubN (𝟙 _) (𝟙 _) 4)).mul
    (grep_nu ν hν.1 (𝟙 _))).normd
    ![(𝟙 D.P.A ^ 5).left, (𝟙 D.P.A ^ 4).left, 𝟙 _, (1 : D.P.A ⟶ D.P.A).left] ![2, -3, -2, 3] (fun U _ h => by
      rw [Fin.prod_univ_four, ← pow_mul, ← pow_succ, ← pow_two (𝟙 D.P.A)]
      apply Additive.ofMul.injective
      simp [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module) (fun w I hI => by
      have C : IsCub (cubV D.cub (T := 𝟙_ _) w I) := isCub_cubV D.cub hI
      beta_reduce
      rw [comp_id_pow, one_pow, Category.comp_id, normd_one hκ hI, normd_one hν hI, C.N_one]
      simp)
  refine ⟨gam, hgam, fun T g b z J hJ => ?_⟩
  let β : D.P.A ⊗ D.P.A ⟶ D.P.A := fst _ _
  let ξ : D.P.A ⊗ D.P.A ⟶ D.P.A := snd _ _
  have rg : GRep D.P.L (D.P.A ⊗ D.P.A) (fun _ _ h => h (β ^ 5).left ^ (2 : ℤ) * h (β ^ 4).left ^ (-3 : ℤ) *
      h β.left ^ (-2 : ℤ) * h (1 : D.P.A ⊗ D.P.A ⟶ D.P.A).left ^ (3 : ℤ)) (fun _ r z J => val gam (r ≫ β).left z J) :=
    (grep_gen gam hgam.1 β.left).congr (fun _ _ h => by
      rw [Fin.prod_univ_four, ← left_pow β 5, ← left_pow β 4, ← left_one β]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Category.comp_id]) (fun _ _ _ _ _ => rfl)
  have H := (toHas ((((grep_cub (β ^ 4) (β ^ 4) ξ).mul (grep_cub (β ^ 4) ξ ξ).inv).mul
    (grep_kap (n := 2) κ hκ.1 ξ)).mul rg)).unique D.P.isLB
    ((((toHas ((grep_kap (n := 2) κ hκ.1 (ξ * β * β)).mul (grep_cubN β (ξ * β) 4))).mul
      (GlobalTheory.SymFrame.hasGen_cubN D.cub (β ^ 4) β ξ 4)).mul (toHas (grep_cub (β ^ 4) ξ β).inv)).mul
      (toHas (grep_nu ν hν.1 β)))
    (fun U _ h => by
      have a₁ : (ξ * β * β) ^ 2 = β ^ 4 * ξ * ξ := by
        apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_pow]; module
      have a₂ : β ^ 4 * (ξ * β) = β ^ 4 * ξ * β := (_root_.mul_assoc _ _ _).symm
      have a₃ : β * (ξ * β) = ξ * β * β := mul_comm _ _
      rw [a₁, a₂, a₃, mul_comm β ξ, pow_succ β 4, pow_two ξ]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      push_cast
      module)
    (by
      rw [← Over.w (snd D.P.A D.P.A)]
      exact surj_comp (surj_snd hG D.P.isAb _) (hG _ _ D.P.isAb).2) (lift 1 1) (fun y I hI => by
      have C : IsCub (cubV D.cub (T := 𝟙_ _) y I) := isCub_cubV D.cub hI
      simp only [β, ξ, MonObj.comp_mul, MonObj.comp_pow, lift_fst, lift_snd,
        _root_.mul_one, inv_one, one_pow, C.face, C.N_one, normd_one hν hI, normd_one hκ hI, normd_one hgam hI])
    T (lift g b) z J hJ
  simpa only [β, ξ, MonObj.comp_mul, MonObj.comp_pow, lift_fst, lift_snd] using H

end Canon

theorem pull_val : AllUF fun {R} _ _ {_} {D} {A} {G} _ _ U F _ _ => ∀ (E : EndU U.toUnifPre),
    Function.Injective E.h → ∀ ν : ℕ, 1 ≤ ν →
    (∃ β : LB.Gen (LB.LinComb U.LG.L (K := Fin 2) ![𝟙 _, E.aG.left] ![(ν : ℤ), -((1 : ℕ) : ℤ)]), β.IsGen) →
    ∀ κ : LB.Gen (kapLB D.toPre E.aB ν 1), Normd κ → ∀ w₀ : W0 U.toUnifPre, w₀.IsGen →
    ∃ α : LB.Gen (LB.LinComb A.L (K := Fin 2)
      ![(snd (TFK (R := R) F) A.A).left, (snd (TFK (R := R) F) A.A ≫ E.aA).left] ![(ν : ℤ), -((1 : ℕ) : ℤ)]), α.IsGen ∧
      ∀ (t : SecA A F 1) (t' : SecA A F ν) s s', U.ExpandsF F 1 w₀ t s → U.ExpandsF F ν w₀ t' s' →
      IsTwistPull A.A A.L (lift (fst _ _) (snd (TFK (R := R) F) A.A ≫ E.aA)) _ (lift_snd _ _) ν (1 : ℕ) α t t' →
      ∀ χ (b : TF (R := R) F ⟶ D.toPre.P.A) (z : (TF (R := R) F).left) J, Good D.toPre.P.L z J →
        sval (s'.s (E.h χ)) (lift (𝟙 (TF (R := R) F)) b).left z J * (rigV D.toPre (TF (R := R) F).hom z J).val =
          sval (s.s χ) (lift (𝟙 (TF (R := R) F)) (b ≫ E.aB)).left z J *
            (val (E.u χ) b.left z J * val κ b.left z J * rigV D.toPre (TF (R := R) F).hom z J ^ ν).val := by
  intro R _ _ _ I hI D A G _ _ hG U F _ _ _ E hE ν hν ⟨β, hβ⟩ κ hκ w₀ hw
  have hL := GlobalTheory.firstFiveLaws
  have := E.homA
  obtain ⟨ρ, hw₀⟩ := GlobalTheory.SymFrame.exists_normW U.toUnifPre w₀ hw
  obtain ⟨α₀, hα₀⟩ := exists_gen_generic E _ _ β hβ (TFK (R := R) F)
  obtain ⟨α, hα, hαn⟩ := exists_normalised A.isLB hw₀.2.1 (snd (TFK (R := R) F) A.A ≫ E.aA) (by
    rw [← Over.comp_left, ptSecT, lift_snd_assoc, MonObj.one_comp]; rfl) _ _ α₀ hα₀
  refine ⟨α, hα, fun t t' s s' ht ht' htt χ b z J hJ => ?_⟩
  have H := (GlobalTheory.T.expansion_pullback_section_endomorphism hL R I hI D A G hG U F E hE ν 1 le_rfl hν ⟨β, hβ⟩).2 w₀ ρ hw₀ _ _ (lift_snd _ _) (lift_fst _ _)
    rfl α hα hαn t t' s s' ht ht' htt κ hκ
  obtain ⟨g, rfl⟩ := (gt_onto_divisible_kernel hL R I hI D F).1 b
  obtain ⟨g', hg', -⟩ := (GlobalTheory.T.uniformizationEndomorphism_calculus hL R I hI D A G hG U F E E E).1 g
  obtain ⟨w', hw'⟩ := (coef_basic R D.toPre F ν g).1
  obtain ⟨w, hw, hv⟩ := exists_gen D.toPre.P.isLB (φ' := DegPre.lineφ D.toPre F g'.b) (ε' := DegPre.lineε 1)
    (fun V _ h => by
      refine (prod_sum₂ (K := Fin 2) (K' := Fin 3) (U := V) _ (prod_line ν g.b h) (prod_kap g.b E.aB ν h)).trans ?_
      rw [prod_line, hg'.1]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_pow]
      module)
    (LB.mulGen D.toPre.P.L _ _ _ _ w' (LB.pullGen D.toPre.P.L _ _ κ g.b.left))
    (mulGen_isGen _ _ _ _ _ _ _ hw' (pullGen_isGen _ _ _ _ hκ.1 _))
  have hww : ∀ z J, Good D.toPre.P.L z J → val w' (𝟙 _) z J * val κ g.b.left z J = val w (𝟙 _) z J := fun z J hJ => by
    rw [hv _ _ z J hJ, val_mul hJ, val_pull hJ, Category.id_comp]
  have a₁ := isCoef_coef g hw' (E.h χ) s' z J hJ
  have a₂ := isCoef_coef g' hw χ s z J hJ
  rw [(H g g' hg' w' w hw' hw hww).1 χ] at a₁
  rw [← hww z J hJ, hg'.2 χ z J hJ, pow_one] at a₂
  rw [← hg'.1]
  refine (Units.mul_left_inj (val (g.s (E.h χ)) (𝟙 _) z J * val w' (𝟙 _) z J)).1 ?_
  simp only [Units.val_mul, Units.val_pow_eq_pow_val] at a₂ ⊢
  linear_combination (rigV D.toPre (TF (R := R) F).hom z J).val ^ ν * a₂ -
    (rigV D.toPre (TF (R := R) F).hom z J).val * a₁

theorem alg_units {M : Type} [CommRing M] {s p₀ p₁ p₂ p₃ q : M} (hs : IsUnit s) {l r a u k₀ k₁ n₁ n₂ w y : Mˣ}
    (h₁ : p₁ = p₀ * (n₁ * w).val) (h₂ : p₂ = p₁ * (n₂ * (y * w)).val) (h₃ : p₂ = l.val * p₃)
    (h₄ : p₃ * r.val = q * (u * k₀ * r ^ 4).val) (h₅ : q = s * (a * r).val) (h₆ : p₀ * r.val = s * (k₁ * r ^ 4).val) :
    l * (a * r) * (u * k₀) = k₁ * n₁ * n₂ * y * w ^ 2 := by
  obtain ⟨s, rfl⟩ := hs
  have e := congrArg (· * r.val) h₃
  beta_reduce at e
  rw [_root_.mul_assoc l.val, h₄, h₅, h₂, h₁, mul_right_comm, mul_right_comm p₀, h₆] at e
  simp only [← Units.val_mul, Units.val_inj] at e
  apply Additive.ofMul.injective
  have b := congrArg Additive.ofMul e
  simp only [ofMul_mul, ofMul_pow] at b ⊢
  linear_combination (norm := module) -b

theorem sign_eq : AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∃ gam : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 4) ![(𝟙 D.toPre.P.A ^ 5).left, (𝟙 D.toPre.P.A ^ 4).left, 𝟙 _, (1 : D.toPre.P.A ⟶ D.toPre.P.A).left] ![2, -3, -2, 3]), Normd gam ∧ ∀ (p : QkPt D.toPre F 4) (x : TFK (R := R) F ⟶ A.A), QkToAkU U.toUnifPre F 4 p x → ∀ σ : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(ι[A.A]).left, 𝟙 A.A.left] ![1, -1]), σ.IsGen → LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ σ (eSec A.A)) (LB.oneGen A.L) → ∀ (z : (TF (R := R) F).left) JA J, Good A.L (Z := (TFK (R := R) F).left) z JA → Good D.toPre.P.L z J → @id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val σ (x ^ 2).left z JA) * (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.toPre.psi (p.y)) (jFK (R := R) F) z J) * rigV D.toPre (TF (R := R) F).hom z J) = val (p.g.s p.y) (𝟙 _) z J ^ 2 * val gam p.g.b.left z J := by
  intro R _ _ _ I hI D A G _ _ hG U F _ _ _
  have hL := GlobalTheory.firstFiveLaws
  have hGF := hL.1.globalFns
  have := hI.1
  have : CharZero (FractionRing R) := charZero_of_injective_algebraMap (IsFractionRing.injective R _)
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap (FractionRing R) F).injective
  obtain ⟨E, eG, eA, eB, eh, -⟩ := (GlobalTheory.IntEnd.exists_nsmul_and_neg hL R I hI D A G hG U).1 2
  have := E.homB
  have hE : Function.Injective E.h := fun a b e => by
    rw [eh, eh] at e
    have h : (2 : ℤ) • (a - b) = 0 := by rw [smul_sub, two_smul, two_smul, ← two_nsmul, ← two_nsmul, e, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h).resolve_left two_ne_zero)
  have hβ : ∃ β : LB.Gen (LB.LinComb U.LG.L (K := Fin 2) ![𝟙 _, E.aG.left] ![((4 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]),
      β.IsGen := by
    rw [eG]; exact exists_gen_mulPull_pow_unif R I D A G U.toUnifPre 2 1 4 rfl
  obtain ⟨κ, hκ⟩ := (GlobalTheory.T.expansion_pullback_section_endomorphism hL R I hI D A G hG U F E hE 4 1 le_rfl (by omega) hβ).1
  obtain ⟨ν, hν⟩ := exists_nu (D := D.toPre) hL.1.mulPull 4
  obtain ⟨gam, hgam, canon⟩ := exists_gam hGF eB κ hκ ν hν
  refine ⟨gam, hgam, fun p x hx σ hσ nσ z JA J hJA hJ => ?_⟩
  have C : IsCub (th D.toPre (T := TF (R := R) F) z J) := isCub_cubV D.toPre.cub hJ
  obtain ⟨w₀, hw₀⟩ := U.ext
  obtain ⟨h4, hx'⟩ := hx w₀ hw₀
  obtain ⟨θ, hθ, hsym, c, hc, hsq⟩ := GlobalTheory.T.exists_symmetric_thetaElement_level_four_square R A F x h4 σ hσ nσ
  obtain ⟨w, hw, hΦ⟩ := hx' θ hθ
  have sq := GlobalTheory.SymFrame.sq_frame_of_symmetric hL R I hI D A G hG U F 4 (by omega) p θ w₀ w hw₀ hw hΦ hsym ν hν z J hJ
  obtain ⟨α, hα, pull⟩ := pull_val R I hI D A G hG U F E hE 4 (by omega) hβ κ hκ w₀ hw₀
  obtain ⟨bij, lin⟩ := expBijF_and_expandsF_lin hL R I hI D A G hG U
  obtain ⟨s, hs⟩ := FamFree.exists_fam_support (D := D.toPre) (F := F) hGF hL.2.1.secTwist D.tau_bimult le_rfl 0
  obtain ⟨v, j, hv, hu⟩ := exists_torsion_ne_zero hL.1 (s.s 0) ((hs 0).2 ⟨0, by simp⟩) (l := 4 + 1) (by omega)
  obtain ⟨b₁, rfl⟩ := exists_comp_eq hL.1 E.aB (by omega) κ hκ.1 (Nat.one_le_pow _ _ (by omega))
    (Nat.Coprime.pow_left j (by norm_num)) v hv
  obtain ⟨b, rfl⟩ : ∃ b, b * p.g.b * p.g.b = b₁ := ⟨b₁ * p.g.b⁻¹ * p.g.b⁻¹, by simp⟩
  obtain ⟨t, ht, -⟩ := (bij F 1 le_rfl w₀ hw₀).2 s
  obtain ⟨t₁, h₁⟩ := GlobalTheory.SymFrame.exists_twist A.A A.isLB (ψ := lift (fst _ _) (snd (TFK (R := R) F) A.A ≫ E.aA))
    (hm := lift_snd _ _) hα t
  obtain ⟨t₂, h₂⟩ := ThetaNu.exists_isActOf A.isLB θ t₁
  obtain ⟨t₃, h₃⟩ := ThetaNu.exists_isActOf A.isLB θ t₂
  obtain ⟨ts, -⟩ := bij F 4 (by omega) w₀ hw₀
  obtain ⟨s₁, hs₁, -⟩ := ts t₁
  obtain ⟨s₂, hs₂, -⟩ := ts t₂
  obtain ⟨s₃, hs₃, -⟩ := ts t₃
  have e := hsq _ _ (lift_snd _ _) (lift_fst _ _) (by rw [eA, MonObj.comp_pow, Category.comp_id]) α hα t t₁ t₂ t₃ h₁ h₂ h₃
  have z₀ : U.ExpandsF F 4 w₀ SecOps.secZero ((-1 : F) • s₁ + s₁) := lin F 4 w₀ t₁ t₁ _ s₁ s₁ (-1) hs₁ hs₁ fun j => by
    rw [map_neg, map_one, liftFun, map_neg, map_neg, map_one, map_one, neg_one_mul, neg_add_cancel]; rfl
  have e₃ : s₃ = c • s₁ := by
    have := (ts t₃).unique hs₃ (lin F 4 w₀ t₁ _ t₃ s₁ _ c hs₁ z₀ fun j => (e j).trans (add_zero _).symm)
    rwa [neg_one_smul, neg_add_cancel, add_zero] at this
  have cy : cP D.toPre (TF (R := R) F) p.y = p.g.b ^ 4 := cPoint_y p
  have a₁ := GlobalTheory.SymFrame.phi_at hGF p w hw (hΦ _ _ _ _ hs₁ hs₂ h₂) 0 p.y (zero_add _) (b * p.g.b) z hJ
  have a₂ := GlobalTheory.SymFrame.phi_at hGF p w hw (hΦ _ _ _ _ hs₂ hs₃ h₃) p.y (E.h p.y) (by rw [eh, two_nsmul]) b z hJ
  have a₃ : sval (s₃.s (E.h p.y)) (lift (𝟙 (TF (R := R) F)) b).left z J =
      (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val σ (x ^ 2).left z JA)).val *
        sval (s₁.s (E.h p.y)) (lift (𝟙 (TF (R := R) F)) b).left z J := by
    rw [e₃, sval_smul _ _ _ _ z hJ, ← Over.comp_left, lift_fst]
    exact congrArg₂ (· * ·) (hc z JA hJA).symm rfl
  have a₄ := pull t t₁ s s₁ ht hs₁ h₁ p.y b z J hJ
  have a₅ := fe_zero hGF D.tau_bimult s p.y (one_nsmul _).symm (b ≫ E.aB) z J hJ
  have a₆ := pull t t₁ s s₁ ht hs₁ h₁ 0 (b * p.g.b * p.g.b) z J hJ
  have e₀ : ∀ χ, χ = 0 → ∀ r : (TF (R := R) F).left ⟶ _, sval (s₁.s χ) r z J = sval (s₁.s 0) r z J := by
    rintro _ rfl _; rfl
  have eb : (b ≫ E.aB) * cP D.toPre (TF (R := R) F) p.y = (b * p.g.b * p.g.b) ≫ E.aB := by
    rw [cy, eB, comp_id_pow, comp_id_pow]
    apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_pow]; module
  rw [e₀ _ (map_zero E.h), val_twist_zero hGF E.aB (map_zero E.h) (E.u 0) (E.u_norm 0) _ z J hJ, _root_.one_mul] at a₆
  rw [eb, cubN, Finset.prod_range_one, pow_zero, _root_.mul_one, C.face, _root_.one_mul, pow_one] at a₅
  have z₁ : val (p.g.s 0) (𝟙 _) z J = 1 := TorusExt.charVal_zero p.g hJ
  rw [cPoint_zero, C.face, inv_one, _root_.mul_one, z₁, _root_.one_mul] at a₁
  rw [cy] at a₂
  have k₁ := alg_units (hu z J hJ) a₁ a₂ a₃ a₄ a₅ a₆
  have k₂ := val_double hGF eB (eh p.y) (E.u p.y) (E.u_norm _) b z J hJ
  have k₃ := canon _ p.g.b b z J hJ
  rw [cy] at k₂
  apply Additive.ofMul.injective
  have b₀ := congrArg Additive.ofMul sq
  have b₁ := congrArg Additive.ofMul k₁
  have b₂ := congrArg Additive.ofMul k₂
  have b₃ := congrArg Additive.ofMul k₃
  simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one] at b₀ b₁ b₂ b₃ ⊢
  linear_combination (norm := module) b₁ + b₀ - b₂ - b₃

theorem corr_of_ext {R : Type} [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F] {X : Scheme.{0}}
    {L : LB X} (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K'] {φ : K → ((TK R).left ⟶ X)} {ε : K → ℤ}
    {φ' : K' → ((TK R).left ⟶ X)} {ε' : K' → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε'))
    (h : ∀ (z : Spec (CommRingCat.of F)) J, Good L z J → val t (jFK (R := R) F) z J = val t' (jFK (R := R) F) z J) :
    LB.Gen.Corr L _ _ _ _ t t' := by
  refine corr_of_val hL fun z J hJ => ?_
  obtain ⟨z'⟩ : Nonempty (Spec (CommRingCat.of F)) := inferInstanceAs (Nonempty (PrimeSpectrum F))
  obtain rfl : z = jFK (R := R) F z' := Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) _ _
  let ρ := jFK (R := R) F
  have : Surjective ρ := ⟨fun x => ⟨z', Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) _ _⟩⟩
  have : Flat ρ := inferInstanceAs (Flat (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) F))))
  have : Epi ρ := Flat.epi_of_flat_of_surjective ρ
  obtain ⟨J', hJ', e⟩ := exists_good L hL (Z := Spec (CommRingCat.of F)) z'
    (fun ψ : (TK R).left ⟶ X => ρ ≫ ψ) J (fun a b e => congrArg J ((cancel_epi ρ).1 e)) (fun ψ => hJ ψ)
  obtain rfl : (fun ψ => J' (ρ ≫ ψ)) = J := funext e
  have hinj : Function.Injective (ρ.stalkMap z').hom := by
    let _ := (ρ.stalkMap z').hom.toAlgebra
    have : Module.Flat ((TK R).left.presheaf.stalk (ρ z')) ((Spec (CommRingCat.of F)).presheaf.stalk z') :=
      Flat.stalkMap ρ z'
    have : IsLocalHom (algebraMap ((TK R).left.presheaf.stalk (ρ z')) ((Spec (CommRingCat.of F)).presheaf.stalk z')) :=
      inferInstanceAs (IsLocalHom (ρ.stalkMap z').hom)
    have : Module.FaithfullyFlat ((TK R).left.presheaf.stalk (ρ z')) ((Spec (CommRingCat.of F)).presheaf.stalk z') :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact FaithfulSMul.algebraMap_injective ((TK R).left.presheaf.stalk (ρ z')) _
  exact Units.ext (hinj ((EvalZero.val_comp_map t ρ (𝟙 _) ρ (Category.comp_id _) z' hJ').symm.trans
    ((congrArg Units.val (h z' J' hJ')).trans (EvalZero.val_comp_map t' ρ (𝟙 _) ρ (Category.comp_id _) z' hJ'))))

theorem exists_act : AllUF fun {R} _ _ {_} {D} {A} {G} _ _ U F _ _ => ∀ (O : Type) [CommRing O] [StarRing O]
    [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG →
    (∀ a, LBIso (cubeLB G ![fst G G ≫ oG.act a, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ oG.act (star a)] U.LG.L)) →
    ∀ (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre F k) (x : TFK (R := R) F ⟶ A.A), QkToAkU U.toUnifPre F k p x → ∀ a : O,
      ∃ q : QkPt D.toPre F k, q.y = a • p.y ∧ GtAct o a p.g q.g ∧ QkToAkU U.toUnifPre F k q (x ≫ oA.act a) := by
  intro R _ _ _ I hI D A G _ _ hG U F _ _ _ O _ _ _ o oA oG hlin hadj k hk p x hx a
  have hL := GlobalTheory.firstFiveLaws
  have hT := GlobalTheory.twistBaseChange
  obtain ⟨E, eG, eA, -, -, eact⟩ := GlobalTheory.T.exists_uniformizationEndomorphism_of_linear hL R I hI D A G hG U O o oA oG hlin a
  obtain ⟨E', eG', -, -, eh', -⟩ := GlobalTheory.T.exists_uniformizationEndomorphism_of_linear hL R I hI D A G hG U O o oA oG hlin (star a)
  obtain ⟨b₁, b₂⟩ := GlobalTheory.T.uniformisation_adjoint_endomorphisms_commute hL (twistBCSpan_of hT) TWM.vRatioGt (TWM.tw_of_laws hL.1 hT) (UUA.uu hL.1 hT) R I hI D A G hG U F E E'
    (by rw [eG, eG']; exact hadj a)
  obtain ⟨ex, add, -⟩ := GlobalTheory.T.uniformizationEndomorphism_calculus hL R I hI D A G hG U F E E E
  choose f hf _ using ex
  letI := TorusExt.gtGroup D.toPre F
  let φ : GtPtF D.toPre F →+ GtPtF D.toPre F := AddMonoidHom.mk' f fun g g' =>
    (TorusExt.isAdd_iff_eq _ _ _).1 (add g g' _ _ _ _ ((TorusExt.isAdd_iff_eq _ _ _).2 rfl) (hf _) (hf _) (hf _))
  obtain ⟨h, hn, hι⟩ := p.eq
  let q : QkPt D.toPre F k := ⟨E'.h p.y, f p.g, f h, (TorusExt.isNsmul_iff_eq _ _ _).2 (by
    rw [(TorusExt.isNsmul_iff_eq _ _ _).1 hn]; exact map_nsmul φ k p.g), b₁ _ _ _ hι (hf h)⟩
  exact ⟨q, (eh' _).trans (by rw [star_star]), (eact F _ _).1 (hf _), eA ▸ b₂ k hk p q x rfl (hf _) hx⟩

theorem psi_eq_tau_of_bundle_primitive_for_endomorphism : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → (∀ a, LBIso (cubeLB G ![fst G G ≫ oG.act a, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ oG.act (star a)] U.LG.L)) → ∀ w : O, w + star w = 1 → LBIso U.LG.L (cubeLB G ![𝟙 G, oG.act w] U.LG.L) → TraceFormTwistIso D.toPre o w := by
  intro R _ _ _ hR D A G _ _ hG U O _ _ _ o oA oG hlin hadj w hw hprim
  have := hR.2
  have hL := GlobalTheory.firstFiveLaws
  have := o.onB.hom w
  have := oA.hom w
  let F := AlgebraicClosure (FractionRing R)
  obtain ⟨u₀, hu₀⟩ := GlobalTheory.T.polarisationBundle_symmetric_pullback_of_uniformisation R _ hR.1 D A G hG U O o oA oG hlin w hprim
  obtain ⟨u, hu, hn⟩ := GlobalTheory.PsiRescale.exists_normalised D.toPre.P.isLB (o.onB.act w) u₀ hu₀
  obtain ⟨σ, hσ, nσ, vσ⟩ := GlobalTheory.T.symmetry_signs_two_torsion_relation_of_lbIso R _ hR.1 D A G hG U O o oA oG hlin w hprim
  obtain ⟨gam, hgam, key⟩ := sign_eq R _ hR.1 D A G hG U F
  refine ⟨u, hu, hn, fun y => corr_of_ext F D.toPre.P.isLB _ _ fun z J hJ => ?_⟩
  obtain ⟨h, hh⟩ := TorusExt.exists_iota (F := F) D.tau_bimult y
  obtain ⟨g, hg⟩ := (gt_onto_divisible_kernel hL R _ hR.1 D F).2.1 4 (by omega) h
  let p : QkPt D.toPre F 4 := ⟨y, g, h, hg, hh⟩
  obtain ⟨f, hf, -⟩ := GlobalTheory.TorsionIso.torsion_eq hL R _ hR.1 D A G hG U F 4 (by omega)
  have hx := (hf p _).2 rfl
  obtain ⟨q, qy, qg, hq⟩ := exists_act R _ hR.1 D A G hG U F O o oA oG hlin hadj 4 (by omega) p _ hx w
  obtain ⟨r, ry, rg, hr⟩ := exists_act R _ hR.1 D A G hG U F O o oA oG hlin hadj 4 (by omega) p _ hx (1 + w)
  obtain ⟨w₀, hw₀⟩ := U.ext
  have h4 : f p ^ 4 = 1 := (hx w₀ hw₀).1
  obtain ⟨JA, hJA⟩ := GlobalTheory.UU.exists_good_pt A.isLB (Z := (TFK (R := R) F).left) z
  have e₁ : (f p ≫ oA.act w) ^ 2 = (f p ^ 2) ≫ oA.act w := by rw [pow_two, pow_two, MonObj.mul_comp]
  have e₂ : (f p ≫ oA.act (1 + w)) ^ 2 = (f p ^ 2) * ((f p ^ 2) ≫ oA.act w) := by
    rw [oA.map_add, oA.map_one, ← e₁, ← mul_pow]
    exact congrArg (· ^ 2) ((MonObj.comp_mul _ _ _).trans (congrArg₂ (· * ·) (Category.comp_id _) rfl))
  have h2 : (f p ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact h4
  have hv := vσ (TFK (R := R) F) (f p ^ 2) h2 z JA hJA
  rw [← e₂, ← e₁] at hv
  have H := GlobalTheory.T.psi_eq_tau_from_sign_relation_four_torsion R D.toPre F O o w hw u ⟨hu, hn⟩ gam hgam p q r qy ry qg rg z J hJ _ _ _
    (key p _ hx σ hσ nσ z JA J hJA hJ) (key q _ hq σ hσ nσ z JA J hJA hJ) (key r _ hr σ hσ nσ z JA J hJA hJ) hv
  have r₁ : val D.toPre.rigK (jFK (R := R) F) z J = rigV D.toPre (TF (R := R) F).hom z J := val_pull hJ _ _ _
  have r₂ : jFK (R := R) F ≫ D.toPre.xK y = (cP D.toPre (TF (R := R) F) y).left := (Category.assoc _ _ _).symm
  rw [val_mul hJ, val_mul hJ, val_pull hJ, r₁, r₂]
  exact H

end GlobalTheory.PsiSign
end

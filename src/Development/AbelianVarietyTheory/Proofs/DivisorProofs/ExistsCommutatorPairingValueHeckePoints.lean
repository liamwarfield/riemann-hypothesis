module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeSectionsLinearSimilitudeMemKernelPolarisatiStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommutatorPairingValueHeckePoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommutatorPairingValueHeckePoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeckeWeilLift

open GlobalTheory.CechPic

section General

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB (A ⊗ A).left} (hL : L.IsLB)

def qc {T : Over S} (a b : T ⟶ A) : Pic T.left := pull (lift a b).left (cls L hL)

theorem pull_eq_qc {T : Over S} (f : T ⟶ A ⊗ A) :
    pull f.left (cls L hL) = qc hL (f ≫ fst A A) (f ≫ snd A A) := by
  unfold qc; rw [lift_comp_fst_snd]

omit [IsCommMonObj A] in
theorem translPt_fst {T : Over S} (x : T ⟶ A ⊗ A) :
    Out.translPt (A ⊗ A) x ≫ fst A A = (fst T (A ⊗ A) ≫ x ≫ fst A A) * (snd T (A ⊗ A) ≫ fst A A) := by
  have e : Out.translPt (A ⊗ A) x = (fst T (A ⊗ A) ≫ x) * snd T (A ⊗ A) := rfl
  rw [e, MonObj.mul_comp, Category.assoc]

omit [IsCommMonObj A] in
theorem translPt_snd {T : Over S} (x : T ⟶ A ⊗ A) :
    Out.translPt (A ⊗ A) x ≫ snd A A = (fst T (A ⊗ A) ≫ x ≫ snd A A) * (snd T (A ⊗ A) ≫ snd A A) := by
  have e : Out.translPt (A ⊗ A) x = (fst T (A ⊗ A) ≫ x) * snd T (A ⊗ A) := rfl
  rw [e, MonObj.mul_comp, Category.assoc]

variable {hL}


include hL in
theorem exists_theta_left
    (hB : ∀ (T : Over S) (x x' y : T ⟶ A), qc hL (x * x') y = qc hL x y + qc hL x' y)
    {T : Over S} (t : T ⟶ 𝟙_ (Over S)) (h : 𝟙_ (Over S) ⟶ A)
    (ht : ∃ u : (L.pull (lift (toUnit A ≫ h) (𝟙 A)).left).Gen, u.IsGen) :
    ∃ θ : Out.ThetaGrp (A ⊗ A) L 1 T, θ.pt = t ≫ lift h 1 := by
  have z : pull (lift (toUnit A ≫ h) (𝟙 A)).left (cls L hL) = 0 := by
    rw [← cls_pull hL _ (pull_isLB hL _)]; exact (cls_eq_zero_iff _).2 ht
  set b := snd T (A ⊗ A) ≫ snd A A
  have e1 : fst T (A ⊗ A) ≫ (t ≫ lift h 1) ≫ fst A A = b ≫ toUnit A ≫ h := by
    rw [Category.assoc, lift_fst, ← Category.assoc, ← Category.assoc,
      toUnit_unique (fst T (A ⊗ A) ≫ t) (b ≫ toUnit A)]
  have e2 : fst T (A ⊗ A) ≫ (t ≫ lift h 1) ≫ snd A A = 1 := by
    rw [Category.assoc, lift_snd, MonObj.comp_one, MonObj.comp_one]
  have e3 : qc hL (b ≫ toUnit A ≫ h) b = 0 := by
    unfold qc
    rw [show lift (b ≫ toUnit A ≫ h) b = b ≫ lift (toUnit A ≫ h) (𝟙 A) by
      rw [comp_lift, Category.comp_id], Over.comp_left, pull_comp, z, map_zero]
  obtain ⟨u, hu⟩ : ∃ u : LB.Gen (Out.thetaLB (A ⊗ A) L 1 (t ≫ lift h 1)), u.IsGen := by
    refine (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).1 ?_
    rw [cls_linComb hL, Fin.sum_univ_two]
    show (1 : ℤ) • pull (snd T (A ⊗ A)).left _ + (-1 : ℤ) • pull (Out.translPt (A ⊗ A) (t ≫ lift h 1)).left _ = 0
    rw [pull_eq_qc, pull_eq_qc, translPt_fst, translPt_snd, e1, e2, _root_.one_mul, hB, e3]
    simp
  exact ⟨⟨_, u, hu⟩, rfl⟩


include hL in
theorem exists_theta_right
    (hB' : ∀ (T : Over S) (x y y' : T ⟶ A), qc hL x (y * y') = qc hL x y + qc hL x y')
    {T : Over S} (t : T ⟶ 𝟙_ (Over S)) (h : 𝟙_ (Over S) ⟶ A)
    (ht : ∃ u : (L.pull (lift (𝟙 A) (toUnit A ≫ h)).left).Gen, u.IsGen) :
    ∃ θ : Out.ThetaGrp (A ⊗ A) L 1 T, θ.pt = t ≫ lift 1 h := by
  have z : pull (lift (𝟙 A) (toUnit A ≫ h)).left (cls L hL) = 0 := by
    rw [← cls_pull hL _ (pull_isLB hL _)]; exact (cls_eq_zero_iff _).2 ht
  set a := snd T (A ⊗ A) ≫ fst A A
  have e1 : fst T (A ⊗ A) ≫ (t ≫ lift 1 h) ≫ snd A A = a ≫ toUnit A ≫ h := by
    rw [Category.assoc, lift_snd, ← Category.assoc, ← Category.assoc,
      toUnit_unique (fst T (A ⊗ A) ≫ t) (a ≫ toUnit A)]
  have e2 : fst T (A ⊗ A) ≫ (t ≫ lift 1 h) ≫ fst A A = 1 := by
    rw [Category.assoc, lift_fst, MonObj.comp_one, MonObj.comp_one]
  have e3 : qc hL a (a ≫ toUnit A ≫ h) = 0 := by
    unfold qc
    rw [show lift a (a ≫ toUnit A ≫ h) = a ≫ lift (𝟙 A) (toUnit A ≫ h) by
      rw [comp_lift, Category.comp_id], Over.comp_left, pull_comp, z, map_zero]
  obtain ⟨u, hu⟩ : ∃ u : LB.Gen (Out.thetaLB (A ⊗ A) L 1 (t ≫ lift 1 h)), u.IsGen := by
    refine (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).1 ?_
    rw [cls_linComb hL, Fin.sum_univ_two]
    show (1 : ℤ) • pull (snd T (A ⊗ A)).left _ + (-1 : ℤ) • pull (Out.translPt (A ⊗ A) (t ≫ lift 1 h)).left _ = 0
    rw [pull_eq_qc, pull_eq_qc, translPt_fst, translPt_snd, e1, e2, _root_.one_mul, hB', e3]
    simp
  exact ⟨⟨_, u, hu⟩, rfl⟩

end General

end GlobalTheory.HeckeWeilLift

namespace GlobalTheory.HeckeWeilLift

open GlobalTheory.CechPic GlobalTheory.DiagPairing

theorem exists_weilIs_hecke : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ h₁ ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, ∀ h₂ ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, ∃ u : Γ((𝟙_ (Over S)).left, ⊤)ˣ, Out.WeilIs (G2 o.A) (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) 1 (lift h₁ 1 : 𝟙_ (Over S) ⟶ G2 o.A) (lift 1 h₂) u := by
  intro p _ D R _ b g c k N hc hk hN hNp hsim hsurj hdiv S s o h₁ hh₁ h₂ hh₂
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hD : (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB := pull_isLB o.isLB _
  have hB : ∀ (T : Over S) (x x' y : T ⟶ o.A), pc o.isLB (x * x') y = pc o.isLB x y + pc o.isLB x' y :=
    fun T x x' y => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S o.A _ o.ab hD o.ample o.P o.isLB o.rig₁
        o.rig₂ T x x' y).1
      have e := (cls_eq_zero_iff (LB.isLB_linComb o.isLB _ _)).2 ⟨t, ht⟩
      rw [cls_linComb o.isLB, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have hB' : ∀ (T : Over S) (x y y' : T ⟶ o.A), pc o.isLB x (y * y') = pc o.isLB x y + pc o.isLB x y' :=
    fun T x y y' => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S o.A _ o.ab hD o.ample o.P o.isLB o.rig₁
        o.rig₂ T y y' x).2
      have e := (cls_eq_zero_iff (LB.isLB_linComb o.isLB _ _)).2 ⟨t, ht⟩
      rw [cls_linComb o.isLB, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have hQ : (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).IsLB := LB.isLB_linComb o.isLB _ _
  have hcls : cls _ hQ = (k ^ 2 / c) • cls o.P o.isLB := by
    refine (cls_linComb o.isLB (K := Fin (k ^ 2 / c)) (fun _ => 𝟙 _) (fun _ => 1) hQ).trans ?_
    simp [pull_id]
  have hQB : ∀ (T : Over S) (x x' y : T ⟶ o.A), qc hQ (x * x') y = qc hQ x y + qc hQ x' y :=
    fun T x x' y => by
      unfold qc
      rw [hcls, map_nsmul, map_nsmul, map_nsmul]
      exact (congrArg _ (hB T x x' y)).trans (smul_add _ _ _)
  have hQB' : ∀ (T : Over S) (x y y' : T ⟶ o.A), qc hQ x (y * y') = qc hQ x y + qc hQ x y' :=
    fun T x y y' => by
      unfold qc
      rw [hcls, map_nsmul, map_nsmul, map_nsmul]
      exact (congrArg _ (hB' T x y y')).trans (smul_add _ _ _)
  obtain ⟨t₁, -⟩ := GlobalTheory.T.heckeSections_linearSimilitude_mem_kernel_polarisation p D R b g c k N hc hk hN hNp hsim hsurj hdiv S s o h₁ hh₁
  obtain ⟨-, t₂⟩ := GlobalTheory.T.heckeSections_linearSimilitude_mem_kernel_polarisation p D R b g c k N hc hk hN hNp hsim hsurj hdiv S s o h₂ hh₂
  have hA2 : IsAbelianScheme (G2 o.A) := AbelianSchemeGerms.isAbelianScheme_tensor o.A o.A o.ab o.ab
  exact CommutatorPairing.exists_weilIs hG hA2 hQ
    (fun _ => ⟨⊤, trivial, exists_theta_left hQB (Out.overResι ⊤) h₁ t₁⟩)
    (fun _ => ⟨⊤, trivial, exists_theta_right hQB' (Out.overResι ⊤) h₂ t₂⟩)

end GlobalTheory.HeckeWeilLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommutatorPairingValueHeckePointsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_commutatorPairing_value_heckePoints : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ h₁ ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, ∀ h₂ ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, ∃ u : Γ((𝟙_ (Over S)).left, ⊤)ˣ, Out.WeilIs (G2 o.A) (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) 1 (lift h₁ 1 : 𝟙_ (Over S) ⟶ G2 o.A) (lift 1 h₂) u := by
  first | (exact @GlobalTheory.HeckeWeilLift.exists_weilIs_hecke) | (exact GlobalTheory.HeckeWeilLift.exists_weilIs_hecke) | (intros; apply GlobalTheory.HeckeWeilLift.exists_weilIs_hecke <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalGluedHodgeGraphFiltrationHasComplement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalGluedHodgeGraphFiltrationHasComplement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.HTGlue

variable {k : Type} [Field k] {d : ℕ}

theorem crys_ext (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀)
    {e e' : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀}
    (h : ∀ c, e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c) =
      e' ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c)) : e = e' := by
  have hm := GlobalTheory.SqZeroCrys.isBC_trivSqZeroExt k (Fin d → k) A₀ hA (GlobalTheory.FODef.sqZero k (Fin d → k))
    (GlobalTheory.FODef.constMorV k (Fin d → k) A₀)
  let eqv := LinearEquiv.ofBijective _ hm
  have h1 : ∀ c, (GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c = eqv (1 ⊗ₜ c) := fun c =>
    (one_smul (TrivSqZeroExt k (Fin d → k)) ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c)).symm
  have key : e ∘ₗ eqv.toLinearMap = e' ∘ₗ eqv.toLinearMap := by
    refine TensorProduct.AlgebraTensorModule.ext fun r c => ?_
    have hr : (r ⊗ₜ c : TrivSqZeroExt k (Fin d → k) ⊗[k] primDR A₀) = r • (1 ⊗ₜ c) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hr, map_smul, ← h1, h c]
  refine LinearMap.ext fun y => ?_
  obtain ⟨t, rfl⟩ := eqv.surjective y
  exact LinearMap.congr_fun key t

theorem crys_pull_smul (A₀ : Over (Sp k)) [GrpObj A₀]
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀)
    (a : k) (c : primDR A₀) :
    e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull (a • c)) =
      TrivSqZeroExt.inl a * e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c) := by
  rw [LinearMap.map_smulₛₗ]
  exact e.map_smul (algebraMap k (TrivSqZeroExt k (Fin d → k)) a) ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c)

theorem crys_pull_add (A₀ : Over (Sp k)) [GrpObj A₀]
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀)
    (a b : primDR A₀) :
    e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull (a + b)) =
      e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull a) + e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull b) := by
  rw [LinearMap.map_add (f := _)]
  exact e.map_add _ _

def fstVal (A₀ : Over (Sp k)) [GrpObj A₀]
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀) :
    HdR A₀ where
  toFun c := (e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c)).fst
  map_add' a b := by
    rw [crys_pull_add]
    rfl
  map_smul' a c := by
    rw [crys_pull_smul]
    simp

def sndVal (A₀ : Over (Sp k)) [GrpObj A₀]
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀)
    (j : Fin d) : HdR A₀ where
  toFun c := (e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c)).snd j
  map_add' a b := by
    rw [crys_pull_add]
    rfl
  map_smul' a c := by
    rw [crys_pull_smul]
    simp

def constSub (A₀ : Over (Sp k)) [GrpObj A₀] (S : Submodule k (HdR A₀)) :
    Submodule (TrivSqZeroExt k (Fin d → k))
      (Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀) where
  carrier := {e | ∃ x ∈ S, ∃ z : Fin d → HdR A₀, (∀ j, z j ∈ S) ∧
      ∀ c : primDR A₀, e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c) =
        TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (fun j => z j c)}
  add_mem' := by
    rintro e e' ⟨x, hx, z, hz, he⟩ ⟨x', hx', z', hz', he'⟩
    refine ⟨x + x', add_mem hx hx', z + z', fun j => add_mem (hz j) (hz' j), fun c => ?_⟩
    rw [LinearMap.add_apply, he c, he' c]
    ext
    · simp
    · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, Pi.add_apply,
        LinearMap.add_apply, zero_add, add_zero, Pi.zero_apply]
  zero_mem' := ⟨0, zero_mem _, 0, fun _ => zero_mem _, fun c => by rw [LinearMap.zero_apply]; ext <;> simp⟩
  smul_mem' := by
    rintro r e ⟨x, hx, z, hz, he⟩
    refine ⟨r.fst • x, Submodule.smul_mem _ _ hx, fun j => r.fst • z j + r.snd j • x,
      fun j => add_mem (Submodule.smul_mem _ _ (hz j)) (Submodule.smul_mem _ _ hx), fun c => ?_⟩
    rw [LinearMap.smul_apply, he c, smul_eq_mul]
    ext
    · simp
    · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
        TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, Pi.add_apply, Pi.smul_apply,
        LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, add_zero, zero_add,
        MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, Pi.zero_apply]


set_option maxHeartbeats 1000000 in
theorem mem_sup_of_coords (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀)
    (f : Fin d → (HdR A₀ →ₗ[k] HdR A₀)) (M₀ : Submodule k (HdR A₀))
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀)
    (x₁ m : HdR A₀) (hx₁ : x₁ ∈ Fil A₀) (hm : m ∈ M₀) (hxm : ∀ c, x₁ c + m c = (e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c)).fst)
    (z w : Fin d → HdR A₀) (hz : ∀ j, z j ∈ Fil A₀) (hw : ∀ j, w j ∈ M₀)
    (hzw : ∀ j c, z j c + w j c = (e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c)).snd j - f j x₁ c) :
    e ∈ glueFil A₀ f ⊔ constSub A₀ M₀ := by
  obtain ⟨g, hg⟩ := exists_coords (Fin d → k) A₀ hA
    ((Algebra.linearMap k (TrivSqZeroExt k (Fin d → k))) ∘ₗ x₁ + (TrivSqZeroExt.inrHom k (Fin d → k)) ∘ₗ
      LinearMap.pi fun j => f j x₁ + z j)
  have hgv : ∀ c, g ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c) =
      TrivSqZeroExt.inl (x₁ c) + TrivSqZeroExt.inr (fun j => (f j x₁ + z j) c) := fun c => by
    rw [hg c]; ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have hgm : g ∈ glueFil A₀ f := ⟨x₁, hx₁, z, hz, hgv⟩
  obtain ⟨h, hh⟩ := exists_coords (Fin d → k) A₀ hA
    ((Algebra.linearMap k (TrivSqZeroExt k (Fin d → k))) ∘ₗ m + (TrivSqZeroExt.inrHom k (Fin d → k)) ∘ₗ
      LinearMap.pi fun j => w j)
  have hhv : ∀ c, h ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c) =
      TrivSqZeroExt.inl (m c) + TrivSqZeroExt.inr (fun j => w j c) := fun c => by
    rw [hh c]; ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have hhm : h ∈ constSub A₀ M₀ := ⟨m, hm, w, hw, hhv⟩
  refine Submodule.mem_sup.2 ⟨g, hgm, h, hhm, crys_ext A₀ hA fun c => ?_⟩
  rw [LinearMap.add_apply, hgv c, hhv c]
  ext
  · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, hxm c]
  · rename_i j
    simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr,
      Pi.add_apply, zero_add, LinearMap.add_apply]
    linear_combination (hzw j c)

theorem isCompl_glueFil (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀)
    (f : Fin d → (HdR A₀ →ₗ[k] HdR A₀)) (M₀ : Submodule k (HdR A₀)) (hM : IsCompl (Fil A₀) M₀) :
    IsCompl (glueFil A₀ f) (constSub (d := d) A₀ M₀) := by
  constructor
  · rw [Submodule.disjoint_def]
    rintro e ⟨x, hx, z, hz, he⟩ ⟨m, hm, w, hw, he'⟩
    have hxm : x = m := LinearMap.ext fun c => by
      have := congrArg TrivSqZeroExt.fst ((he c).symm.trans (he' c))
      simpa using this
    have hx0 : x = 0 := by
      rw [← Submodule.mem_bot k, ← hM.inf_eq_bot]
      exact ⟨hx, hxm ▸ hm⟩
    have hzw : ∀ j, z j = w j := fun j => LinearMap.ext fun c => by
      have := congrFun (congrArg TrivSqZeroExt.snd ((he c).symm.trans (he' c))) j
      simpa [hx0] using this
    have hz0 : ∀ j, z j = 0 := fun j => by
      rw [← Submodule.mem_bot k, ← hM.inf_eq_bot]
      exact ⟨hz j, (hzw j) ▸ hw j⟩
    refine crys_ext A₀ hA fun c => ?_
    rw [he c, LinearMap.zero_apply]
    ext <;> simp [hx0, hz0]
  · rw [codisjoint_iff, eq_top_iff]
    rintro e -
    have hdec : ∀ u : HdR A₀, ∃ a ∈ Fil A₀, ∃ b ∈ M₀, a + b = u := fun u => by
      have hu : u ∈ Fil A₀ ⊔ M₀ := by rw [hM.sup_eq_top]; trivial
      rw [Submodule.mem_sup] at hu
      exact hu
    choose pa hpa pb hpb hpab using hdec
    exact mem_sup_of_coords A₀ hA f M₀ e _ _ (hpa _) (hpb _) (fun c => LinearMap.congr_fun (hpab (fstVal A₀ e)) c)
      (fun j => pa (sndVal A₀ e j - f j (pa (fstVal A₀ e))))
      (fun j => pb (sndVal A₀ e j - f j (pa (fstVal A₀ e)))) (fun _ => hpa _) (fun _ => hpb _)
      (fun j c => LinearMap.congr_fun (hpab (sndVal A₀ e j - f j (pa (fstVal A₀ e)))) c)

end GlobalTheory.HTGlue


open GlobalTheory.HTGlue in
theorem GlobalTheory.HTGlue.glueFil_hasCompl : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), (∀ j, IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) (f j)) → (∃ M : Submodule (TrivSqZeroExt k (Fin d → k)) (Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A), IsCompl (GlobalTheory.HTGlue.glueFil o₀.A f) M) := by
  intro p _ D R _ b N _ _ k _ _ t o₀ β _ φ _ d f _
  obtain ⟨M₀, hM⟩ := Submodule.exists_isCompl (Fil o₀.A)
  exact ⟨_, isCompl_glueFil o₀.A o₀.ab f M₀ hM⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalGluedHodgeGraphFiltrationHasComplementStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalGluedHodgeGraphFiltration_hasComplement : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), (∀ j, IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) (f j)) → (∃ M : Submodule (TrivSqZeroExt k (Fin d → k)) (Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A), IsCompl (GlobalTheory.HTGlue.glueFil o₀.A f) M) := by
  first | (exact @GlobalTheory.HTGlue.glueFil_hasCompl) | (exact GlobalTheory.HTGlue.glueFil_hasCompl) | (intros; apply GlobalTheory.HTGlue.glueFil_hasCompl  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSumsVanishAtPlaces
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharpolyLattice

theorem pts_equiv (k : Type) [Field k] [IsAlgClosed k] (B : GlobalTheory.AV.AbVar k) :
    ∃ e : (Over.mk (𝟙 (Sp k)) ⟶ B.X) ≃* B.Pt,
      ∀ (f : B ⟶ B) (q : Over.mk (𝟙 (Sp k)) ⟶ B.X), e (q ≫ f.hom) = e q ≫ f.hom := by
  have hb : Function.Bijective (algebraMap k (AlgebraicClosure k)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  haveI : IsIso (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))) :=
    (RingEquiv.ofBijective _ hb).toCommRingCatIso.isIso_hom
  haveI : IsIso (spMap (algebraMap k (AlgebraicClosure k))) :=
    inferInstanceAs (IsIso (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))
  let i : ptOver k (AlgebraicClosure k) ≅ Over.mk (𝟙 (Sp k)) :=
    Over.isoMk (asIso (spMap (algebraMap k (AlgebraicClosure k)))) (Category.comp_id _)
  refine ⟨{ toFun := fun q => i.hom ≫ q
            invFun := fun q => i.inv ≫ q
            left_inv := fun q => by simp
            right_inv := fun q => by simp
            map_mul' := fun q q' => MonObj.comp_mul _ _ _ }, fun f q => ?_⟩
  exact (Category.assoc i.hom q f.hom).symm

theorem charpoly_reduce {R S : Type} [CommRing R] [CommRing S] (π : R →+* S)
    (hπ : Function.Surjective π) (n : R) (hn : π n = 0)
    {N Q : Type} [AddCommGroup N] [Module R N] [Module.Free R N] [Module.Finite R N]
    [AddCommGroup Q] [Module S Q] (e : N →+ Q) (he : Function.Surjective e)
    (hsmul : ∀ (r : R) (x : N), e (r • x) = π r • e x) (hk : ∀ x, e x = 0 → ∃ y, x = n • y)
    (g : N →ₗ[R] N) (G : Q →ₗ[S] Q) (hg : ∀ x, e (g x) = G (e x)) :
    ∃ (_ : Module.Free S Q) (_ : Module.Finite S Q),
      LinearMap.charpoly G = (LinearMap.charpoly g).map π := by
  classical
  let b := Module.Free.chooseBasis R N
  have hsum : ∀ c : Module.Free.ChooseBasisIndex R N → R,
      e (∑ i, c i • b i) = ∑ i, π (c i) • e (b i) := fun c => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => hsmul _ _
  have hli : LinearIndependent S fun i => e (b i) := by
    refine Fintype.linearIndependent_iff.2 fun s hs i => ?_
    choose c hc using fun i => hπ (s i)
    obtain ⟨y, hy⟩ := hk (∑ i, c i • b i) (by rw [hsum]; simpa only [hc] using hs)
    have h := congrArg (fun z => b.repr z i) hy
    simp only [Module.Basis.repr_sum_self, map_smul, Finsupp.smul_apply, smul_eq_mul] at h
    rw [← hc, h, map_mul, hn, zero_mul]
  have hsp : ⊤ ≤ Submodule.span S (Set.range fun i => e (b i)) := by
    intro q _
    obtain ⟨x, rfl⟩ := he q
    rw [← b.sum_repr x, hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let b' := Module.Basis.mk hli hsp
  have hb' : ∀ i, b' i = e (b i) := fun i => Module.Basis.mk_apply hli hsp i
  refine ⟨Module.Free.of_basis b', Module.Finite.of_basis b', ?_⟩
  haveI := Module.Free.of_basis b'
  haveI := Module.Finite.of_basis b'
  rw [← LinearMap.charpoly_toMatrix G b', ← LinearMap.charpoly_toMatrix g b, ← Matrix.charpoly_map]
  congr 1
  ext i j
  rw [Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, hb', ← hg]
  conv_lhs => rw [← b.sum_repr (g (b j)), hsum]
  simp only [← hb']
  rw [Module.Basis.repr_sum_self]


open GlobalTheory.HTLat in
theorem lev_pow_smul {M : Type} [CommGroup M] {l : ℕ} [Fact l.Prime]
    (s : Tate l M) (j n : ℕ) : (((l : ℤ_[l]) ^ j) • s).lev n = s.lev n ^ l ^ j := by
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  rfl


open GlobalTheory.HTLat in
theorem tate_lev_eq_one_iff (M : Type) [CommGroup M] (l : ℕ) [Fact l.Prime]
    (t : GlobalTheory.HTLat.Tate l M) (j : ℕ) :
    t.lev j = 1 ↔ ∃ s : GlobalTheory.HTLat.Tate l M, t = ((l : ℤ_[l]) ^ j) • s := by
  constructor
  · intro ht
    refine ⟨Tate.mk (fun n => t.lev (j + n)) fun n => ⟨by rw [Tate.lev_add_pow, ht], Tate.lev_succ t (j + n)⟩,
      Tate.ext fun n => ?_⟩
    rw [lev_pow_smul, Tate.lev_mk, add_comm, Tate.lev_add_pow]
  · rintro ⟨s, rfl⟩
    rw [lev_pow_smul, Tate.lev_pow]


open GlobalTheory.HTLat in
theorem tate_lev_surj (M : Type) [CommGroup M] (l : ℕ) [Fact l.Prime] (r : ℕ)
    (hc : ∀ n : ℕ, Nat.card {x : M // x ^ (l ^ n) = 1} = l ^ (r * n)) (j : ℕ) (x : M)
    (hx : x ^ (l ^ j) = 1) : ∃ t : GlobalTheory.HTLat.Tate l M, t.lev j = x := by
  choose L hL using GlobalTheory.TateFree.exists_pow_eq hc
  let u : ∀ m : ℕ, {y : M // y ^ l ^ (j + m) = 1} := fun m =>
    Nat.rec (motive := fun m => {y : M // y ^ l ^ (j + m) = 1}) ⟨x, hx⟩
      (fun m y => ⟨L (j + m) y.1 y.2, (hL _ _ _).1⟩) m
  have hu : ∀ m, (u (m + 1)).1 ^ l = (u m).1 := fun m => (hL _ _ _).2
  have hu' : ∀ m, (u m).1 ^ l ^ m = x := fun m => by
    induction m with
    | zero => exact pow_one x
    | succ m ih => rw [pow_succ', pow_mul, hu, ih]
  refine ⟨Tate.mk (fun m => (u m).1 ^ l ^ j) fun m => ⟨?_, ?_⟩, hu' j⟩
  · rw [← pow_mul, ← pow_add]
    exact (u m).2
  · rw [← pow_mul, mul_comm, pow_mul, hu]

end GlobalTheory.CharpolyLattice

namespace GlobalTheory.AV.AbVar


open GlobalTheory.CharpolyLattice GlobalTheory.HTLat in
theorem charpoly_eq_lattice_model : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : GlobalTheory.AV.AbVar k) (f : B ⟶ B)
    (L : Type) [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
    (φ : L →ₗ[ℤ] L) (l : ℕ), l.Prime → (l : k) ≠ 0 →
    ∀ ev : ℕ → L → (Over.mk (𝟙 (Sp k)) ⟶ B.X),
    (∀ j x y, ev j (x + y) = ev j x * ev j y) →
    (∀ j x, ev j (φ x) = ev j x ≫ f.hom) →
    (∀ j x, ev j x = 1 ↔ ∃ y, x = l ^ j • y) →
    (∀ j (q : Over.mk (𝟙 (Sp k)) ⟶ B.X), q ^ (l ^ j) = 1 ↔ ∃ x, ev j x = q) →
    LinearMap.charpoly φ = GlobalTheory.AV.AbVar.charpoly (End.of f) := by
  intro k _ _ B f L _ _ _ φ l hl hlk ev hadd hequi hker him
  haveI : Fact l.Prime := ⟨hl⟩
  obtain ⟨e, he⟩ := pts_equiv k B
  obtain ⟨hfree, hfin, -, hfinV, -⟩ := tl_free_finrank k l hlk B
  have hc : ∀ n : ℕ, Nat.card {x : B.Pt // x ^ (l ^ n) = 1} = l ^ (2 * B.dim * n) := by
    intro n
    rw [card_torsion_pt k B (l ^ n) (by push_cast; exact pow_ne_zero _ hlk), ← pow_mul, mul_comm n]
  let E : ℕ → L →+ Additive B.Pt := fun j =>
    AddMonoidHom.mk' (fun x => Additive.ofMul (e (ev j x))) fun x y => by
      rw [hadd, map_mul]; rfl
  have hE : ∀ j (n : ℕ) x, e (ev j (n • x)) = e (ev j x) ^ n := fun j n x =>
    congrArg Additive.toMul (map_nsmul (E j) n x)
  have key : ∀ j : ℕ, (LinearMap.charpoly φ).map (Int.castRingHom (ZMod (l ^ j))) =
      (LinearMap.charpoly (tend l B (End.of f))).map (PadicInt.toZModPow j) := by
    intro j
    haveI : NeZero (l ^ j) := ⟨pow_ne_zero _ hl.ne_zero⟩
    let K := (powMonoidHom (l ^ j) : B.Pt →* B.Pt).ker
    have hK : ∀ x : B.Pt, x ∈ K ↔ x ^ (l ^ j) = 1 := fun x => MonoidHom.mem_ker
    letI : Module (ZMod (l ^ j)) (Additive K) := AddCommGroup.zmodModule fun x =>
      congrArg Additive.ofMul (Subtype.ext (by
        change ((Additive.toMul x : K) : B.Pt) ^ (l ^ j) = 1
        exact (hK _).1 (Additive.toMul x).2))
    have hsm : ∀ (c : ZMod (l ^ j)) (q : Additive K), c • q = c.val • q := fun c q => by
      conv_lhs => rw [← ZMod.natCast_zmod_val c]
      exact Nat.cast_smul_eq_nsmul _ _ _
    have hπ : ((l : ZMod (l ^ j))) ^ j = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
    let G0 : Additive K →+ Additive K := AddMonoidHom.mk'
      (fun q => Additive.ofMul ⟨((Additive.toMul q : K) : B.Pt) ≫ f.hom, (hK _).2 (by
        rw [← ptMap_apply, ← map_pow, (hK _).1 (Additive.toMul q).2, map_one])⟩)
      fun q q' => congrArg Additive.ofMul (Subtype.ext (MonObj.mul_comp _ _ _))
    let G : Additive K →ₗ[ZMod (l ^ j)] Additive K := G0.toZModLinearMap (l ^ j)
    let eL : L →+ Additive K := AddMonoidHom.mk'
      (fun x => Additive.ofMul ⟨e (ev j x), (hK _).2 (by
        rw [← hE, (hker j _).2 ⟨x, rfl⟩, map_one])⟩)
      fun x y => congrArg Additive.ofMul (Subtype.ext (by
        change e (ev j (x + y)) = e (ev j x) * e (ev j y)
        rw [hadd, map_mul]))
    let eT : Tate l B.Pt →+ Additive K := AddMonoidHom.mk'
      (fun t => Additive.ofMul ⟨t.lev j, (hK _).2 (t.lev_pow j)⟩) fun s t => rfl
    obtain ⟨_, _, h1⟩ := charpoly_reduce (Int.castRingHom (ZMod (l ^ j))) ZMod.intCast_surjective
      ((l : ℤ) ^ j) (by rw [map_pow, map_natCast, hπ]) eL
      (fun q => by
        obtain ⟨x, hx⟩ := (him j (e.symm (Additive.toMul q : K))).1 (by
          rw [← map_pow, (hK _).1 (Additive.toMul q).2, map_one])
        refine ⟨x, congrArg Additive.ofMul (Subtype.ext ?_)⟩
        change e (ev j x) = _
        rw [hx, MulEquiv.apply_symm_apply]
        rfl)
      (fun r x => by rw [map_zsmul, eq_intCast, Int.cast_smul_eq_zsmul])
      (fun x hx => by
        have h0 : e (ev j x) = 1 := congrArg Subtype.val (congrArg Additive.toMul hx)
        obtain ⟨y, hy⟩ := (hker j x).1 ((map_eq_one_iff e e.injective).1 h0)
        exact ⟨y, by rw [hy, ← Nat.cast_pow, natCast_zsmul]⟩)
      φ G (fun x => congrArg Additive.ofMul (Subtype.ext (by
        change e (ev j (φ x)) = e (ev j x) ≫ f.hom
        rw [hequi, he])))
    obtain ⟨_, _, h2⟩ := charpoly_reduce (PadicInt.toZModPow j) (ZMod.ringHom_surjective _)
      ((l : ℤ_[l]) ^ j) (by rw [map_pow, map_natCast, hπ]) eT
      (fun q => by
        obtain ⟨t, ht⟩ := tate_lev_surj B.Pt l (2 * B.dim) hc j _ ((hK _).1 (Additive.toMul q).2)
        exact ⟨t, congrArg Additive.ofMul (Subtype.ext ht)⟩)
      (fun a t => by
        rw [hsm]
        rfl)
      (fun t ht => by
        obtain ⟨s, hs⟩ := (tate_lev_eq_one_iff B.Pt l t j).1
          (congrArg Subtype.val (congrArg Additive.toMul ht))
        exact ⟨s, hs⟩)
      (tend l B (End.of f)) G (fun t => rfl)
    exact h1.symm.trans h2
  have hT : (charpoly (End.of f)).map (algebraMap ℤ ℤ_[l]) =
      (tend l B (End.of f)).charpoly := by
    apply Polynomial.map_injective (algebraMap ℤ_[l] ℚ_[l]) (IsFractionRing.injective ℤ_[l] ℚ_[l])
    rw [Polynomial.map_map, ← LinearMap.charpoly_baseChange]
    have hcomp : (algebraMap ℤ_[l] ℚ_[l]).comp (algebraMap ℤ ℤ_[l]) = algebraMap ℤ ℚ_[l] :=
      Subsingleton.elim _ _
    rw [hcomp]
    obtain ⟨⟨hm, hd, hev⟩, -⟩ := GlobalTheory.T.abelianVarietyEndCharpoly_spec k B (End.of f)
    have hQ := GlobalTheory.T.abelianVariety_degreePolynomial_map_eq_charpoly_rationalTate k l
      hlk B (End.of f) ((charpoly (End.of f)).map (algebraMap ℤ ℚ)) (hm.map _)
      (by rw [Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int (algebraMap ℤ ℚ)), hd])
      (fun n => by rw [Polynomial.eval_intCast_map, Int.cast_id, hev n]; simp)
    rw [Polynomial.map_map] at hQ
    have hcompQ : (algebraMap ℚ ℚ_[l]).comp (algebraMap ℤ ℚ) = algebraMap ℤ ℚ_[l] :=
      Subsingleton.elim _ _
    rw [hcompQ] at hQ
    exact hQ
  have hinj : Function.Injective (Polynomial.map (Int.castRingHom ℤ_[l])) :=
    Polynomial.map_injective _ Int.cast_injective
  apply hinj
  rw [show Int.castRingHom ℤ_[l] = algebraMap ℤ ℤ_[l] from RingHom.ext_int _ _, hT]
  apply AddMonoidAlgebra.ext
  apply Finsupp.ext
  intro i
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  have h := congrArg (fun P : Polynomial (ZMod (l ^ n)) => P.coeff i) (key n)
  simpa only [Polynomial.coeff_map, eq_intCast, map_intCast] using h

end GlobalTheory.AV.AbVar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsInCoordinatesFromBasePullDeg
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsInCoordinatesFromBasePullDeg
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

noncomputable section
namespace GlobalTheory.USep.TauPullB

variable {V V₁ : Type} [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] {ρ : V →+* V₁} {Q : DegPre V} {D : DegPre V₁}

theorem exists_moved (p : IsPullDeg ρ Q D) (τ₀ : GlobalTheory.UChart.Gens Q) (hτ : ∀ a b, (τ₀ a b).IsGen) :
    ∃ τ₁ : GlobalTheory.UChart.Gens D, (∀ a b, (τ₁ a b).IsGen) ∧ ∀ (a b : D.X) (Z : Scheme.{0}) (r : Z ⟶ Sp V₁) (z : Z)
      (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι) (J' : (Z ⟶ D.P.A.left) → D.P.L.ι), Good Q.P.L z J → Good D.P.L z J' →
      val (τ₀ (p.xe a) (p.xe b)) (r ≫ spMap ρ) z J =
        (ArcPull.om p.w z J J' (r ≫ (D.c (a + b)).left))⁻¹ * ArcPull.om p.w z J J' (r ≫ (D.c a).left) *
          ArcPull.om p.w z J J' (r ≫ (D.c b).left) * (ArcPull.om p.w z J J' (r ≫ (D.c 0).left))⁻¹ *
          val (τ₁ a b) r z J' := by
  have key : ∀ a b : D.X, ∃ t : LB.Gen (LB.LinComb D.P.L (K := Fin 4)
      ![(D.c (a + b)).left, (D.c a).left, (D.c b).left, (D.c 0).left] ![-1, 1, 1, -1]), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp V₁) (z : Z) J J', Good Q.P.L z J → Good D.P.L z J' →
      val (τ₀ (p.xe a) (p.xe b)) (r ≫ spMap ρ) z J =
        (ArcPull.om p.w z J J' (r ≫ (D.c (a + b)).left))⁻¹ * ArcPull.om p.w z J J' (r ≫ (D.c a).left) *
          ArcPull.om p.w z J J' (r ≫ (D.c b).left) * (ArcPull.om p.w z J J' (r ≫ (D.c 0).left))⁻¹ *
          val t r z J' := by
    intro a b
    have hψ : ∀ k : Fin 4, (![(D.c (a + b)).left, (D.c a).left, (D.c b).left, (D.c 0).left] k) ≫
        (p.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf ρ)) =
        spMap ρ ≫ (![(Q.c (p.xe a + p.xe b)).left, (Q.c (p.xe a)).left, (Q.c (p.xe b)).left, (Q.c 0).left] k) := by
      intro k
      fin_cases k
      · simpa [map_add (f := _)] using p.c_pr (a + b)
      · simpa using p.c_pr a
      · simpa using p.c_pr b
      · simpa [map_zero] using p.c_pr 0
    obtain ⟨t, ht, hv⟩ := ArcPull.exists_down_om p.w_gen Q.P.isLB D.P.isLB (spMap ρ) hψ (τ₀ (p.xe a) (p.xe b))
      (hτ _ _)
    refine ⟨t, ht, fun Z r z J J' hJ hJ' => ?_⟩
    rw [hv Z r z J J' hJ hJ']
    simp only [Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, zpow_neg, zpow_one]
  choose τ₁ h₁ h₂ using key
  exact ⟨τ₁, h₁, fun a b => h₂ a b⟩

end GlobalTheory.USep.TauPullB

noncomputable section
namespace GlobalTheory.USep.TauPullB

variable {V V₁ : Type} [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] {ρ : V →+* V₁} {Q : DegPre V} {D : DegPre V₁}

theorem c_zero (D : DegPre V₁) : D.c 0 = 1 := by
  have h := D.c_add 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

theorem xK_zero (D : DegPre V₁) : (1 : TK V₁ ⟶ D.P.A).left = (toUnit (TK V₁)).left ≫ (D.c 0).left := by
  rw [c_zero, ← Over.comp_left, MonObj.comp_one]

end GlobalTheory.USep.TauPullB

noncomputable section
namespace GlobalTheory.USep.TauPullB

variable {V V₁ : Type} [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] {ρ : V →+* V₁} {Q : DegPre V} {D : DegPre V₁}

theorem tauIn_moved (hρ : Function.Injective ρ) (p : IsPullDeg ρ Q D) (τ₀ : GlobalTheory.UChart.Gens Q) (τ₁ : GlobalTheory.UChart.Gens D)
    (h₁ : ∀ a b, (τ₁ a b).IsGen) (hmv : ∀ (a b : D.X) (Z : Scheme.{0}) (r : Z ⟶ Sp V₁) (z : Z)
      (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι) (J' : (Z ⟶ D.P.A.left) → D.P.L.ι), Good Q.P.L z J → Good D.P.L z J' →
      val (τ₀ (p.xe a) (p.xe b)) (r ≫ spMap ρ) z J =
        (ArcPull.om p.w z J J' (r ≫ (D.c (a + b)).left))⁻¹ * ArcPull.om p.w z J J' (r ≫ (D.c a).left) *
          ArcPull.om p.w z J J' (r ≫ (D.c b).left) * (ArcPull.om p.w z J J' (r ≫ (D.c 0).left))⁻¹ *
          val (τ₁ a b) r z J') {N : ℕ} (s : Fin N → V) (ε : Fin N → LinearMap.BilinForm ℤ Q.X)
    (ε₁ : Fin N → LinearMap.BilinForm ℤ D.X) (hε : ∀ k a b, ε₁ k a b = ε k (p.xe a) (p.xe b))
    (hT : GlobalTheory.UChart.TauIn Q τ₀ s ε) : GlobalTheory.UChart.TauIn D τ₁ (fun k => ρ (s k)) ε₁ := by
  intro a b
  obtain ⟨-, k, hk, hv⟩ := hT (p.xe a) (p.xe b)
  refine ⟨h₁ a b, Units.map (ArcPull.fracMap hρ).toMonoidHom k, ?_, fun z J' hJ' => ?_⟩
  · rw [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, hk, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_zpow₀, ArcPull.fracMap_algebraMap, hε]
  · choose J hJ using fun χ : (TK V₁).left ⟶ Q.P.A.left => exists_chart Q.P.isLB (χ z)
    have hJ : Good Q.P.L z J := hJ
    have hcorr : LB.Gen.Corr Q.P.L _ _ _ _ (Q.tau (p.xe a) (p.xe b))
        (DVR.scaleGen (unitOn k) (LB.pullGen Q.P.L _ _ (τ₀ (p.xe a) (p.xe b)) (toUnit (TK V)).left)) :=
      corr_of_val Q.P.isLB fun y I hI => by
        rw [hv y I hI, TauTwist.val_scale _ _ _ hI, val_pull hI, Category.id_comp]; rfl
    have e1 := ArcPull.tau_val p (ArcPull.genMap hρ) (𝟙 _) (ArcPull.fracMap_sq hρ) hJ hJ' a b
    have e2 := val_corr hJ hcorr (ArcPull.genMap hρ)
    rw [TauTwist.val_scale _ _ _ hJ, val_pull hJ] at e2
    have e3 : ArcPull.genMap hρ ≫ (toUnit (TK V)).left = (toUnit (TK V₁)).left ≫ spMap ρ :=
      (ArcPull.fracMap_sq hρ).symm.trans (Category.id_comp _)
    rw [e3, hmv a b _ (toUnit (TK V₁)).left z J J' hJ hJ'] at e2
    have e4 : TauTwist.unitAt (ArcPull.genMap hρ) z k =
        TauTwist.unitAt (𝟙 _) z (Units.map (ArcPull.fracMap hρ).toMonoidHom k) :=
      (congrArg (fun q => TauTwist.unitAt q z k) (Category.id_comp (ArcPull.genMap hρ)).symm).trans
        (TauTwist.unitAt_spMap _ _ _ _)
    have o : ∀ x : D.X, 𝟙 _ ≫ D.xK x = (toUnit (TK V₁)).left ≫ (D.c x).left := fun x => by
      rw [Category.id_comp]; rfl
    rw [o, o, o, Category.id_comp, xK_zero] at e1
    rw [e4] at e2
    have e := e1.symm.trans e2
    rw [← TauTwist.unitAt_apply]
    generalize (ArcPull.om p.w z J J' ((toUnit (TK V₁)).left ≫ (D.c (a + b)).left))⁻¹ *
      ArcPull.om p.w z J J' ((toUnit (TK V₁)).left ≫ (D.c a).left) *
      ArcPull.om p.w z J J' ((toUnit (TK V₁)).left ≫ (D.c b).left) *
      (ArcPull.om p.w z J J' ((toUnit (TK V₁)).left ≫ (D.c 0).left))⁻¹ = O at e
    rw [mul_left_comm] at e
    exact mul_left_cancel e

end GlobalTheory.USep.TauPullB

noncomputable section
namespace GlobalTheory.USep.TauPullB

variable {V V₁ : Type} [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] {ρ : V →+* V₁} {Q : DegPre V} {D : DegPre V₁}

def trGen {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ φ' : K → (Y ⟶ X)} {ε : K → ℤ} (h : φ = φ')
    (t : LB.Gen (LB.LinComb L φ ε)) : LB.Gen (LB.LinComb L φ' ε) := h ▸ t

theorem trGen_isGen {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ φ' : K → (Y ⟶ X)} {ε : K → ℤ}
    (h : φ = φ') {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) : (trGen h t).IsGen := by
  subst h; exact ht

theorem val_trGen {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ φ' : K → (Y ⟶ X)} {ε : K → ℤ}
    (h : φ = φ') (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) :
    val (trGen h t) r z J = val t r z J := by
  subst h; rfl

theorem fromBase_moved (p : IsPullDeg ρ Q D) (τ₀ : GlobalTheory.UChart.Gens Q) (τ₁ : GlobalTheory.UChart.Gens D)
    (h₁ : ∀ a b, (τ₁ a b).IsGen) (hmv : ∀ (a b : D.X) (Z : Scheme.{0}) (r : Z ⟶ Sp V₁) (z : Z)
      (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι) (J' : (Z ⟶ D.P.A.left) → D.P.L.ι), Good Q.P.L z J → Good D.P.L z J' →
      val (τ₀ (p.xe a) (p.xe b)) (r ≫ spMap ρ) z J =
        (ArcPull.om p.w z J J' (r ≫ (D.c (a + b)).left))⁻¹ * ArcPull.om p.w z J J' (r ≫ (D.c a).left) *
          ArcPull.om p.w z J J' (r ≫ (D.c b).left) * (ArcPull.om p.w z J J' (r ≫ (D.c 0).left))⁻¹ *
          val (τ₁ a b) r z J') (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V)
    (hF : GlobalTheory.UChart.FromBase Q τ₀ ib) : GlobalTheory.UChart.FromBase D τ₁ (ρ.comp ib) := by
  obtain ⟨B₀, iG, M₀, c₀, σ, β, w, hB₀, hM₀, hgp, hw, hc, hσ, hval⟩ := hF
  have key : ∀ (x y : Q.X) (Z : Scheme.{0}) (r : Z ⟶ Sp V) (z : Z) (JQ : (Z ⟶ Q.P.A.left) → Q.P.L.ι)
      (J₀ : (Z ⟶ B₀.left) → M₀.ι), Good Q.P.L z JQ → Good M₀ z J₀ →
      val (σ x y) (r ≫ spMap ib) z J₀ = (ArcPull.om w z J₀ JQ (r ≫ GlobalTheory.UChart.cpt Q (x + y)))⁻¹ *
        ArcPull.om w z J₀ JQ (r ≫ GlobalTheory.UChart.cpt Q x) * ArcPull.om w z J₀ JQ (r ≫ GlobalTheory.UChart.cpt Q y) *
        (ArcPull.om w z J₀ JQ (r ≫ GlobalTheory.UChart.cpt Q 0))⁻¹ * val (τ₀ x y) r z JQ := by
    intro x y
    have hψ : ∀ k : Fin 4, (![GlobalTheory.UChart.cpt Q (x + y), GlobalTheory.UChart.cpt Q x, GlobalTheory.UChart.cpt Q y,
        GlobalTheory.UChart.cpt Q 0] k) ≫ β = spMap ib ≫ (![c₀ (x + y), c₀ x, c₀ y, c₀ 0] k) := by
      intro k; fin_cases k <;> exact hc _
    obtain ⟨g, -, hvg⟩ := ArcPull.exists_down_om hw hM₀ Q.P.isLB (spMap ib) hψ (σ x y) (hσ x y)
    have hcor : LB.Gen.Corr Q.P.L _ _ _ _ (τ₀ x y) g := corr_of_val Q.P.isLB fun y' I hI => by
      choose I₀ hI₀ using fun χ : Sp V ⟶ B₀.left => exists_chart hM₀ (χ y')
      have e1 := hval x y y' I I₀ hI hI₀
      have e2 := hvg _ (𝟙 _) y' I₀ I hI₀ hI
      simp only [Category.id_comp, Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, zpow_neg, zpow_one] at e2
      have hg : ∀ t : Q.X, gm (GlobalTheory.UChart.cpt Q t) y' _ (w.s (fun _ => I₀ (GlobalTheory.UChart.cpt Q t ≫ β), I (GlobalTheory.UChart.cpt Q t))) =
          ArcPull.om w y' I₀ I (GlobalTheory.UChart.cpt Q t) := fun t => rfl
      simp only [hg] at e1
      show val (τ₀ x y) (𝟙 (Sp V)) y' I = val g (𝟙 (Sp V)) y' I
      rw [e1]
      erw [e2]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    intro Z r z JQ J₀ hJQ hJ₀
    rw [hvg Z r z J₀ JQ hJ₀ hJQ, ← val_corr hJQ hcor r]
    simp only [Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, zpow_neg, zpow_one]
  obtain ⟨w₂, hT⟩ := exists_comp Q.P.isLB w p.w ((isGen_iff w).1 hw) ((isGen_iff p.w).1 p.w_gen) hM₀ D.P.isLB
  have hw₂ : w₂.IsGen :=
    (isGen_iff w₂).2 (hT.pgen_comp Q.P.isLB ((isGen_iff w).1 hw) ((isGen_iff p.w).1 p.w_gen))
  have hφ : ∀ a b : D.X, ![c₀ (p.xe a + p.xe b), c₀ (p.xe a), c₀ (p.xe b), c₀ 0] =
      ![c₀ (p.xe (a + b)), c₀ (p.xe a), c₀ (p.xe b), c₀ (p.xe 0)] := fun a b => by rw [map_add (f := _), map_zero]
  have ec : ∀ t : D.X, GlobalTheory.UChart.cpt D t ≫ (p.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf ρ)) =
      spMap ρ ≫ GlobalTheory.UChart.cpt Q (p.xe t) := fun t => p.c_pr t
  refine ⟨B₀, iG, M₀, fun a => c₀ (p.xe a), fun a b => trGen (hφ a b) (σ (p.xe a) (p.xe b)),
    (p.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf ρ)) ≫ β, w₂, hB₀, hM₀, ?_, hw₂, ?_,
    fun a b => trGen_isGen _ (hσ _ _), ?_⟩
  · rw [spMap_comp]; exact (pull_grp p).comp hgp
  · intro a
    rw [spMap_comp, ← Category.assoc, ec, Category.assoc, hc, Category.assoc]
  · intro a b zz J J₀ hJ hJ₀
    choose JQ hJQ using fun χ : Sp V₁ ⟶ Q.P.A.left => exists_chart Q.P.isLB (χ zz)
    have hJQ : Good Q.P.L zz JQ := hJQ
    have tri : ∀ (t : D.X) (t' : Q.X), GlobalTheory.UChart.cpt D t ≫ (p.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf ρ)) =
        spMap ρ ≫ GlobalTheory.UChart.cpt Q t' →
        gm (GlobalTheory.UChart.cpt D t) zz _ (w₂.s (fun _ => J₀ (GlobalTheory.UChart.cpt D t ≫
          (p.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf ρ)) ≫ β), J (GlobalTheory.UChart.cpt D t))) =
          ArcPull.om w zz J₀ JQ (spMap ρ ≫ GlobalTheory.UChart.cpt Q t') * ArcPull.om p.w zz JQ J ((D.c t).left) := by
      intro t t' e
      have := hT _ (GlobalTheory.UChart.cpt D t) zz (J₀ (GlobalTheory.UChart.cpt D t ≫
        (p.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf ρ)) ≫ β))
        (JQ (GlobalTheory.UChart.cpt D t ≫ (p.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf ρ)))) (J (GlobalTheory.UChart.cpt D t))
        (hJ₀ _) (hJQ _) (hJ _)
      refine this.trans ?_
      simp only [ArcPull.om]
      rw [← e]
      simp only [Category.assoc]
      rfl
    have m := hmv a b _ (𝟙 _) zz JQ J hJQ hJ
    have k := key (p.xe a) (p.xe b) _ (spMap ρ) zz JQ J₀ hJQ hJ₀
    simp only [Category.id_comp] at m
    rw [tri (a + b) (p.xe a + p.xe b) (by rw [← map_add (f := _)]; exact ec _), tri a _ (ec a), tri b _ (ec b),
      tri 0 0 (by rw [ec, map_zero]), val_trGen, spMap_comp, k, m]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

end GlobalTheory.USep.TauPullB

noncomputable section
namespace GlobalTheory.USep


open GlobalTheory.USep.TauPullB in
theorem tauIn_fromBase_pull : ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] (ρ : V →+* V₁), Function.Injective ρ → ∀ (Q : DegPre V) (D : DegPre V₁) (p : IsPullDeg ρ Q D) (τ₀ : GlobalTheory.UChart.Gens Q) (N : ℕ) (s : Fin N → V) (ε : Fin N → LinearMap.BilinForm ℤ Q.X) (ε₁ : Fin N → LinearMap.BilinForm ℤ D.X), (∀ k a b, ε₁ k a b = ε k (p.xe a) (p.xe b)) → GlobalTheory.UChart.TauIn Q τ₀ s ε → ∀ (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V), GlobalTheory.UChart.FromBase Q τ₀ ib → ∃ τ₁ : GlobalTheory.UChart.Gens D, GlobalTheory.UChart.TauIn D τ₁ (fun k => ρ (s k)) ε₁ ∧ GlobalTheory.UChart.FromBase D τ₁ (ρ.comp ib) := by
  intro V V₁ _ _ _ _ ρ hρ Q D p τ₀ N s ε ε₁ hε hT W₀ _ ib hF
  obtain ⟨τ₁, h₁, hmv⟩ := exists_moved p τ₀ fun a b => (hT a b).1
  exact ⟨τ₁, tauIn_moved hρ p τ₀ τ₁ h₁ hmv s ε ε₁ hε hT, fromBase_moved p τ₀ τ₁ h₁ hmv W₀ ib hF⟩

end GlobalTheory.USep
end
end
end
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsInCoordinatesFromBasePullDegStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodsInCoordinates_fromBase_pullDeg : ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] (ρ : V →+* V₁), Function.Injective ρ → ∀ (Q : DegPre V) (D : DegPre V₁) (p : IsPullDeg ρ Q D) (τ₀ : GlobalTheory.UChart.Gens Q) (N : ℕ) (s : Fin N → V) (ε : Fin N → LinearMap.BilinForm ℤ Q.X) (ε₁ : Fin N → LinearMap.BilinForm ℤ D.X), (∀ k a b, ε₁ k a b = ε k (p.xe a) (p.xe b)) → GlobalTheory.UChart.TauIn Q τ₀ s ε → ∀ (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V), GlobalTheory.UChart.FromBase Q τ₀ ib → ∃ τ₁ : GlobalTheory.UChart.Gens D, GlobalTheory.UChart.TauIn D τ₁ (fun k => ρ (s k)) ε₁ ∧ GlobalTheory.UChart.FromBase D τ₁ (ρ.comp ib) := by
  first | exact @GlobalTheory.USep.tauIn_fromBase_pull | exact GlobalTheory.USep.tauIn_fromBase_pull | (intros; apply GlobalTheory.USep.tauIn_fromBase_pull <;> assumption)
end
end

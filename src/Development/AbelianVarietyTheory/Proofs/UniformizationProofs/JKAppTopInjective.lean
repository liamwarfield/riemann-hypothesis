module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PreimageEqTopOfSurjective
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTorusQuotientSchemeOverNilpotentThickening
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocallyTrivialTorusQuotientFlatSurjectiveCosets
public import Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.RigidPullbackIdentification
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullFOfGenRel
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.JKAppTopInjective
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.PsiInt

theorem gs_scal {R : Type} [CommRing R] {Y Z : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y) (z : Z)
    (c : R) : gs r z ⊤ (scal p c) = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) :=
  calc gs r z ⊤ (scal p c) = gs (𝟙 _ ≫ r) z ⊤ (scal p c) := by rw [Category.id_comp]
    _ = gs (𝟙 _) z (r ⁻¹ᵁ ⊤) ((r.app ⊤).hom (scal p c)) := (gs_pull (𝟙 _) r z ⊤ (by trivial) _).symm
    _ = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) := rfl

theorem scal_jK {R : Type} [CommRing R] [IsDomain R] {Y : Scheme.{0}}
    (p : Y ⟶ Spec (CommRingCat.of (FractionRing R))) (c : R) :
    scal (p ≫ jK R) c = scal p (algebraMap R (FractionRing R) c) := by
  have e := congrArg (fun q => q.hom c)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  unfold scal
  rw [e]
  rfl

theorem jK_appTop_injective (R : Type) [CommRing R] [IsDomain R] : Function.Injective (jK R).appTop.hom := by
  have hs := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).2
  have hi := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv).1
  intro x y h
  obtain ⟨a, rfl⟩ := hs x
  obtain ⟨b, rfl⟩ := hs y
  have e := fun c => congrArg (fun q => q.hom c)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  have := hi ((e a).trans (h.trans (e b).symm))
  rw [IsFractionRing.injective R (FractionRing R) this]

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem cT_zero (T : Over (Spec (CommRingCat.of R))) : cT D T 0 = 1 := by
  have h : D.c 0 = D.c 0 * D.c 0 := by
    have := D.c_add 0 0
    rwa [add_zero] at this
  have h1 : D.c 0 = 1 := left_eq_mul.1 h
  rw [cT, h1, MonObj.comp_one]

theorem exists_defect
    (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)))
    (f : ∀ α, SecBT D (𝟙_ _) 1 α) (χ : D.X) (hg : (ga χ).IsGen) (p q : R) :
    ∃ d : SecBT D (𝟙_ _) 1 χ, ∀ (T : Over (Spec (CommRingCat.of R))) (y : T ⟶ D.P.A) (z : T.left) (J),
      Good D.P.L z J → sval d (lift (toUnit T) y).left z J =
        gs (𝟙 _) z ⊤ (scal T.hom q) * sval (f χ) (lift (toUnit T) y).left z J -
        gs (𝟙 _) z ⊤ (scal T.hom p) * ((val (ga χ) (toUnit T).left z J * rigV D z J).val *
          sval (f 0) (lift (toUnit T) (y * cT D T χ)).left z J) := by
  let Y : Over (Spec (CommRingCat.of R)) := 𝟙_ _ ⊗ D.P.A
  let τ : Y ⟶ Y := lift (toUnit Y) (snd _ _ * cT D Y χ)
  have hF : FormEq (famφT D (𝟙_ _) χ) (DegPre.famε 1)
      (Sum.elim (fun k => τ.left ≫ famφT D (𝟙_ _) 0 k)
        (fun k => (toUnit Y).left ≫ Sum.elim (fun _ : PUnit => (D.c χ).left) (fun _ : PUnit => eSec D.P.A) k))
      (Sum.elim (DegPre.famε 1) (Sum.elim (fun _ => -1) (fun _ => 1))) := by
    intro U _ h
    have e₁ : τ.left ≫ famφT D (𝟙_ _) 0 1 = famφT D (𝟙_ _) χ 1 := by
      change (τ ≫ (snd _ _ * cT D Y 0)).left = (snd _ _ * cT D Y χ).left
      rw [cT_zero, _root_.mul_one, lift_snd]
    have e₂ : τ.left ≫ famφT D (𝟙_ _) 0 2 = famφT D (𝟙_ _) χ 3 := by
      change (τ ≫ cT D Y 0).left = (1 : Y ⟶ D.P.A).left
      rw [cT_zero, MonObj.comp_one]
    have e₃ : τ.left ≫ famφT D (𝟙_ _) 0 3 = famφT D (𝟙_ _) χ 3 := by
      change (τ ≫ (1 : Y ⟶ D.P.A)).left = (1 : Y ⟶ D.P.A).left
      rw [MonObj.comp_one]
    have e₄ : (toUnit Y).left ≫ (D.c χ).left = famφT D (𝟙_ _) χ 2 := rfl
    have e₅ : (toUnit Y).left ≫ eSec D.P.A = famφT D (𝟙_ _) χ 3 := rfl
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, Fin.prod_univ_four,
      e₁, e₂, e₃, e₄, e₅]
    simp [DegPre.famε, _root_.mul_assoc]
  obtain ⟨d, hd⟩ := exists_sec_relation_defect Y.left D.P.A.left Y.left D.P.L D.P.isLB _ _ _ _ _ _ _ _ _ τ.left
    (f 0) (f χ) (LB.pullGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ (ga χ) D.rig) (toUnit Y).left)
    (scal Y.hom p) (scal Y.hom q)
    (DVR.pullGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ hg D.rig_gen) _) hF
  refine ⟨d, fun T y z J hJ => ?_⟩
  have e₁ : (lift (toUnit T) y).left ≫ Y.hom = T.hom := Over.w _
  have e₂ : (lift (toUnit T) y).left ≫ τ.left = (lift (toUnit T) (y * cT D T χ)).left := by
    rw [← Over.comp_left]
    congr 1
    simp only [τ, comp_lift, MonObj.comp_mul, lift_snd, cT, ← Category.assoc]
    congr 2
    · exact toUnit_unique _ _
    · congr 1
      exact toUnit_unique _ _
  have e₃ : (lift (toUnit T) y).left ≫ (toUnit Y).left = (toUnit T).left := by
    rw [← Over.comp_left]
    exact congrArg _ (toUnit_unique _ _)
  rw [hd _ _ z J hJ, gs_scal, gs_scal Y.hom _ z p, e₁, e₂, val_pull hJ, e₃, val_mul hJ, mul_comm (sval (f 0) _ z J)]
  congr 5

theorem psiRel_integral : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing R)ˣ) (f : ∀ α, SecBT D (𝟙_ _) 1 α), PsiScal D ga a → PsiRel D (𝟙_ _) f → ∀ (χ : D.X) (p q : R), algebraMap R (FractionRing R) q * (a χ).val = algebraMap R (FractionRing R) p → ∀ (T : Over (Spec (CommRingCat.of R))) (y : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J → gs (𝟙 _) z ⊤ (scal T.hom q) * sval (f χ) (lift (toUnit T) y).left z J = gs (𝟙 _) z ⊤ (scal T.hom p) * ((val (ga χ) (toUnit T).left z J * rigV D z J).val * sval (f 0) (lift (toUnit T) (y * cT D T χ)).left z J) := by
  intro R _ _ D ga a f hS hR χ p q hpq T y z J hJ
  obtain ⟨d, hd⟩ := exists_defect D ga f χ (hS χ).1 p q
  haveI : Flat D.P.A.hom := by
    haveI := D.P.smoothDim
    haveI : Smooth D.P.A.hom := SmoothOfRelativeDimension.smooth D.P.g _
    infer_instance
  haveI : IsAffine (𝟙_ (Over (Spec (CommRingCat.of R)))).left := inferInstanceAs (IsAffine (Spec _))
  haveI : IsAffine (TK R).left := inferInstanceAs (IsAffine (Spec _))
  have hinj : Function.Injective (toUnit (TK R)).left.appTop.hom := by
    have e : (toUnit (TK R)).left = jK R := by simp
    rw [e]
    exact jK_appTop_injective R
  have h0 := sec_eq_zero_of_sval_whiskerRight_eq_zero _ D.P.A (𝟙_ _) (TK R) (toUnit _) hinj _ D.P.L D.P.isLB _ _ _ d
    (fun w I hI => by
      have e : toUnit (TK R) ▷ D.P.A = lift (toUnit (TK R ⊗ D.P.A)) (snd _ _) := by
        ext1
        · exact toUnit_unique _ _
        · simp
      have e' : (TK R ⊗ D.P.A).hom = (fst (TK R) D.P.A).left ≫ jK R := (Over.w (fst (TK R) D.P.A)).symm
      have e₁ := hR χ _ (toUnit _) (fst (TK R) D.P.A) (snd _ _) w I hI
      have e₂ := (hS χ).2 _ (fst (TK R) D.P.A) w I hI
      have e₃ : gs (𝟙 _) w ⊤ (scal (TK R ⊗ D.P.A).hom q) * gs (𝟙 _) w ⊤ (scal (fst (TK R) D.P.A).left (a χ).val) =
          gs (𝟙 _) w ⊤ (scal (TK R ⊗ D.P.A).hom p) := by
        rw [← gs_mul _ w ⊤ trivial, e']
        congr 1
        refine (congrArg (· * _) (scal_jK _ q)).trans (Eq.trans ?_ (scal_jK _ p).symm)
        rw [← hpq]
        unfold scal
        rw [map_mul, map_mul]
      rw [e, hd _ _ w I hI, e₁, Units.val_mul, Units.val_mul, e₂, ← e₃]
      ring)
  refine sub_eq_zero.1 ((hd T y z J hJ).symm.trans ?_)
  refine (congrArg (gs _ z _) (h0 _)).trans ((gs_eq _ z _ (hJ.mem _ _) _).trans ?_)
  exact (congrArg _ (map_zero _)).trans (map_zero _)

end GlobalTheory.PsiInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUnitLevels
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.RedTotal

section Units

variable {S : Type} [CommRing S] (J : Ideal S)

theorem appTop_specMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (a : Γ(Spec (CommRingCat.of A), ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ((Spec.map (CommRingCat.ofHom f)).appTop.hom a) =
      f ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom a) :=
  congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))

theorem ΓSpecIso_injective (A : Type) [CommRing A] :
    Function.Injective (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.injective

theorem fn_ext_levels [IsHausdorff J S] {a b : Γ(Spec (CommRingCat.of S), ⊤)}
    (h : ∀ e, (adicLevelι J (e + 1)).appTop.hom a = (adicLevelι J (e + 1)).appTop.hom b) : a = b := by
  apply ΓSpecIso_injective
  have := IsHausdorff.StrictMono.funext' J (a := fun n => n + 1) (strictMono_id.add_const 1)
    (f := fun _ : Unit => (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom a)
    (g := fun _ : Unit => (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom b) fun n _ =>
      (appTop_specMap _ a).symm.trans ((congrArg _ (h n)).trans (appTop_specMap _ b))
  exact congrFun this ()

theorem exists_fn_levels [IsAdicComplete J S] (ρ : ∀ e : ℕ, Γ(Spec (CommRingCat.of (S ⧸ J ^ (e + 1))), ⊤))
    (h : ∀ e, (adicLevelMap J (Nat.le_succ (e + 1))).appTop.hom (ρ (e + 1)) = ρ e) :
    ∃ a : Γ(Spec (CommRingCat.of S), ⊤), ∀ e, (adicLevelι J (e + 1)).appTop.hom a = ρ e := by
  have ha : StrictMono fun n : ℕ => n + 1 := strictMono_id.add_const 1
  let f : ∀ n : ℕ, Polynomial ℤ →+* S ⧸ J ^ (n + 1) := fun n =>
    Polynomial.eval₂RingHom (Int.castRingHom _) ((Scheme.ΓSpecIso (CommRingCat.of _)).hom.hom (ρ n))
  have hf : ∀ n, f n Polynomial.X = (Scheme.ΓSpecIso (CommRingCat.of _)).hom.hom (ρ n) := fun n =>
    Polynomial.eval₂_X _ _
  have hc : ∀ {m : ℕ}, (Ideal.Quotient.factorPow J (ha.monotone m.le_succ)).comp (f (m + 1)) = f m := by
    intro m
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    rw [RingHom.comp_apply, hf, hf, ← h m]
    exact (appTop_specMap _ _).symm
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom
    (IsAdicComplete.StrictMono.liftRingHom J ha f hc Polynomial.X), fun e => ΓSpecIso_injective _ ?_⟩
  rw [appTop_specMap, Iso.inv_hom_id_apply, ← hf]
  exact congrArg (fun q => q Polynomial.X) (IsAdicComplete.StrictMono.mk_comp_liftRingHom J ha f hc (n := e))

theorem exists_unit_levels [IsAdicComplete J S] (ρ : ∀ e : ℕ, Γ(Spec (CommRingCat.of (S ⧸ J ^ (e + 1))), ⊤)ˣ)
    (h : ∀ e, (adicLevelMap J (Nat.le_succ (e + 1))).appTop.hom (ρ (e + 1)).val = (ρ e).val) :
    ∃ a : Γ(Spec (CommRingCat.of S), ⊤)ˣ, ∀ e, pullU (adicLevelι J (e + 1)) ⊤ a = ρ e := by
  obtain ⟨a, ha⟩ := exists_fn_levels J (fun e => (ρ e).val) h
  obtain ⟨b, hb⟩ := exists_fn_levels J (fun e => ((ρ e)⁻¹).val) fun e => by
    have : Units.map (adicLevelMap J (Nat.le_succ (e + 1))).appTop.hom.toMonoidHom (ρ (e + 1)) = ρ e :=
      Units.ext (h e)
    rw [← this]; rfl
  have hab : a * b = 1 := fn_ext_levels J fun e => by
    rw [map_mul, ha, hb, map_one, Units.mul_inv]
  exact ⟨⟨a, b, hab, (mul_comm _ _).trans hab⟩, fun e => Units.ext (ha e)⟩

end Units

section Gens

variable {S : Type} [CommRing S] (J : Ideal S) {X : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem corr_of_levels [IsHausdorff J S] (hL : L.IsLB) {φ : K → (Spec (CommRingCat.of S) ⟶ X)} {ε : K → ℤ}
    {φ' : K' → (Spec (CommRingCat.of S) ⟶ X)} {ε' : K' → ℤ} (h : FormEq φ ε φ' ε')
    {u : LB.Gen (LB.LinComb L φ ε)} (hu : u.IsGen) {u' : LB.Gen (LB.LinComb L φ' ε')} (hu' : u'.IsGen)
    (hv : ∀ e z C, Good L z C → val u (adicLevelι J (e + 1)) z C = val u' (adicLevelι J (e + 1)) z C) :
    LB.Gen.Corr L φ ε φ' ε' u u' := by
  obtain ⟨a, ha⟩ := TorusCoord.exists_ratio hL h u hu u' hu'
  have h2 : a = 1 := Units.ext (fn_ext_levels J fun e =>
    (FormalPoint.appTop_eq_one_of_gm _ a fun z => by
      obtain ⟨C, hC⟩ := exists_good_pt hL z
      exact mul_eq_right.1 ((ha _ _ z C hC).symm.trans (hv e z C hC))).trans (map_one _).symm)
  exact corr_of_val hL fun y C hC => by rw [ha _ _ y C hC, h2, map_one, _root_.one_mul]

theorem exists_gen_levels [IsLocalRing S] [IsAdicComplete J S] (hL : L.IsLB)
    (φ : K → (Spec (CommRingCat.of S) ⟶ X)) (ε : K → ℤ) {Y : ℕ → Scheme.{0}} {ψ : ∀ e, K' → (Y e ⟶ X)}
    {ε' : K' → ℤ} (u : ∀ e, LB.Gen (LB.LinComb L (ψ e) ε')) (hu : ∀ e, (u e).IsGen)
    (y : ∀ e : ℕ, Spec (CommRingCat.of (S ⧸ J ^ (e + 1))) ⟶ Y e)
    (h : ∀ e, FormEq (fun k => adicLevelι J (e + 1) ≫ φ k) ε (fun k => y e ≫ ψ e k) ε')
    (hc : ∀ e z C, Good L z C →
      val (u (e + 1)) (adicLevelMap J (Nat.le_succ (e + 1)) ≫ y (e + 1)) z C = val (u e) (y e) z C) :
    ∃ s : LB.Gen (LB.LinComb L φ ε), s.IsGen ∧ ∀ e (Z : Scheme.{0}) (k : Z ⟶ _) z C, Good L z C →
      val (u e) (k ≫ y e) z C = val s (k ≫ adicLevelι J (e + 1)) z C := by
  obtain ⟨s₀, hs₀⟩ := DVR.exists_gen_of_local L hL φ ε
  choose ρ hρ using fun e => TorusCoord.exists_ratio hL (fun U _ f => (h e U f).symm)
    (LB.pullGen L _ _ (u e) (y e)) (DVR.pullGen_isGen _ _ _ _ (hu e) _)
    (LB.pullGen L _ _ s₀ (adicLevelι J (e + 1))) (DVR.pullGen_isGen _ _ _ _ hs₀ _)
  have hρ' : ∀ e (Z : Scheme.{0}) (k : Z ⟶ _) z C, Good L z C →
      val (u e) (k ≫ y e) z C = gm k z ⊤ (ρ e) * val s₀ (k ≫ adicLevelι J (e + 1)) z C := fun e Z k z C hC =>
    (val_pull hC _ _ _).symm.trans ((hρ e Z k z C hC).trans (congrArg₂ (· * ·) rfl (val_pull hC _ _ _)))
  obtain ⟨a, ha⟩ := exists_unit_levels J ρ fun e => by
    refine (FormalPoint.appTop_eq_of_gm _ (𝟙 _) (ρ (e + 1)) (ρ e) fun z => ?_).trans (by simp)
    obtain ⟨C, hC⟩ := exists_good_pt hL z
    have e₁ := hρ' (e + 1) _ (adicLevelMap J (Nat.le_succ (e + 1))) z C hC
    have e₂ := hρ' e _ (𝟙 _) z C hC
    rw [Category.id_comp, Category.id_comp] at e₂
    rw [hc e z C hC, adicLevelMap_ι, e₂] at e₁
    exact (mul_right_cancel e₁).symm
  refine ⟨scaleGen a s₀, scaleGen_isGen a hs₀, fun e Z k z C hC => ?_⟩
  rw [val_scaleGen a s₀ _ hC, hρ' e Z k z C hC, ← ha e]
  exact congrArg (· * _) (gm_pull k _ z ⊤ trivial a)

end Gens

section Main

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}

theorem formEq_mult {T : Over (Spec (CommRingCat.of R))} (b : T ⟶ D.P.A) (χ χ' : D.X) :
    FormEq (Sum.elim (DegPre.gtφT D T b (χ + χ'))
        (fun k => (lift (DegPre.cT D T χ) (lift (DegPre.cT D T χ') b)).left ≫ thφ D.P.A (x3 D.P.A) k))
      (Sum.elim DegPre.gtε thε)
      (Sum.elim (DegPre.gtφT D T b χ) (DegPre.gtφT D T b χ')) (Sum.elim DegPre.gtε DegPre.gtε) := by
  intro U _ f
  have p : ∀ α, ∏ k, f (DegPre.gtφT D T b α k) ^ DegPre.gtε k =
      (f (DVR.cP D T α * b).left)⁻¹ * f (DVR.cP D T α).left * f b.left * (f (1 : T ⟶ D.P.A).left)⁻¹ := fun α => by
    have := FormalPoint.prod_gtφT (𝟙 T) b α f
    simpa only [Over.id_left, Category.id_comp] using this
  have q := prod_cub (DVR.cP D T χ) (DVR.cP D T χ') b f
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [p, p, p]
  refine (congrArg (_ * ·) q).trans ?_
  rw [DVR.cPoint_add]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

variable {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] (U : PreU I D A G) {S : Type} [CommRing S] {φ : R →+* S}



omit [IsDomain R] [GrpObj G] [IsCommMonObj G] in
open FormalPoint in
theorem reduction_succ (x : Over.mk (spMap φ) ⟶ G) (e : ℕ) :
    adicLevelMap (I.map φ) (Nat.le_succ (e + 1)) ≫ reduction I x (e + 1) = reduction I x e ≫ thickMap R I e G := by
  have h₄ : thickMap R I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  rw [← cancel_mono (fstG I (e + 1) G).left, Category.assoc, Category.assoc, h₄, reduction_fstG, reduction_fstG]
  exact adicLevelMap_ι_assoc _ _ _

variable [IsLocalRing S]



end Main

end GlobalTheory.RedTotal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsAffineOpen
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.TorusQuotLift

theorem isMonHom_of_points {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H] (φ : G ⟶ H)
    (key : ∀ {T : Over S} (x y : T ⟶ G), (x * y) ≫ φ = (x ≫ φ) * (y ≫ φ)) : IsMonHom φ := by
  refine ⟨?_, ?_⟩
  ·
    have hsq := key (T := 𝟙_ (Over S)) 1 1
    rw [_root_.mul_one] at hsq
    have hid : ((1 : 𝟙_ (Over S) ⟶ G) ≫ φ) = 1 := by
      have h2 : ((1 : 𝟙_ (Over S) ⟶ G) ≫ φ) * ((1 : 𝟙_ (Over S) ⟶ G) ≫ φ) =
          ((1 : 𝟙_ (Over S) ⟶ G) ≫ φ) * 1 := by rw [← hsq, _root_.mul_one]
      exact mul_left_cancel h2
    have eG : (1 : 𝟙_ (Over S) ⟶ G) = η := by
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    have eH : (1 : 𝟙_ (Over S) ⟶ H) = η := by
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    rw [eG, eH] at hid
    exact hid
  ·
    have hm := key (T := G ⊗ G) (fst G G) (snd G G)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at hm
    have ht : (φ ⊗ₘ φ) = lift (fst G G ≫ φ) (snd G G ≫ φ) := by
      ext <;> simp
    rw [ht]
    exact hm

private lemma pullback_fst_comp_mul_left {S S' : Scheme.{0}} {G : Over S} [GrpObj G] (f : S' ⟶ S) {T : Over S'}
    (u v : T ⟶ (Over.pullback f).obj G) :
    (u * v).left ≫ pullback.fst G.hom f =
      ((Over.homMk (U := Over.mk (T.hom ≫ f)) (V := G) (u.left ≫ pullback.fst G.hom f)
          (by rw [Category.assoc, pullback.condition, ← Category.assoc]; exact congrArg (· ≫ f) (Over.w u))) *
        (Over.homMk (U := Over.mk (T.hom ≫ f)) (V := G) (v.left ≫ pullback.fst G.hom f)
          (by rw [Category.assoc, pullback.condition, ← Category.assoc]; exact congrArg (· ≫ f) (Over.w v)))).left := by
  rw [Hom.mul_def, Hom.mul_def, Functor.obj.μ_def, Over.comp_left, Over.comp_left, Over.comp_left,
    Category.assoc, Category.assoc]
  have hmap : ((Over.pullback f).map μ[G]).left ≫ pullback.fst G.hom f =
      pullback.fst (G ⊗ G).hom f ≫ μ[G].left :=
    GlobalTheory.TorusLift.map_left_fst f μ[G]
  rw [hmap, ← Category.assoc, ← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, Over.μ_pullback_left_fst_fst]
    erw [pullback.lift_fst_assoc, pullback.lift_fst]
    · rfl
    all_goals exact (Over.w _).trans (Over.w _).symm
  · rw [Category.assoc, Category.assoc, Over.μ_pullback_left_fst_snd]
    erw [pullback.lift_snd_assoc, pullback.lift_snd]
    · rfl
    all_goals exact (Over.w _).trans (Over.w _).symm

theorem exists_iso_pullback {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {F : G'.left ⟶ G.left} (h : IsGrpPullback G' G f F) :
    ∃ e : G' ≅ (Over.pullback f).obj G, IsMonHom e.hom ∧ e.hom.left ≫ pullback.fst G.hom f = F := by
  obtain ⟨hpb, hmul⟩ := h
  let e : G' ≅ (Over.pullback f).obj G :=
    Over.isoMk hpb.isoPullback (by simp)
  have he : e.hom.left ≫ pullback.fst G.hom f = F := by
    simp [e]
  refine ⟨e, ?_, he⟩
  apply isMonHom_of_points
  intro T x y
  apply GlobalTheory.TorusLift.hom_ext_fst f
  rw [pullback_fst_comp_mul_left]
  rw [Over.comp_left, Category.assoc, he]
  symm
  apply hmul T x y
  · simp [he]
  · simp [he]

theorem exists_isAffineOpen {R : Type} [CommRing R] [IsLocalRing R] {X : Type} [AddCommGroup X]
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] (Q : TQ G X) :
    ∃ W : G.left.Opens, IsAffineOpen W ∧ Q.i.left ⁻¹ᵁ W = ⊤ := by
  have := Q.q_affine
  let s₀ : Spec (CommRingCat.of R) := IsLocalRing.closedPoint R
  obtain ⟨_, ⟨V, hV, rfl⟩, hbV, -⟩ := Q.B.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ ((η[Q.B]).left s₀)) isOpen_univ
  refine ⟨Q.q.left ⁻¹ᵁ V, hV.preimage Q.q.left, ?_⟩

  have hw : Q.i.left ≫ Q.q.left = (splitTorus _ X).hom ≫ (η[Q.B]).left := by
    have := congrArg CommaMorphism.left Q.isKernel.w
    simpa using this

  have htop : (η[Q.B]).left ⁻¹ᵁ V = ⊤ :=
    (IsLocalRing.closedPoint_mem_iff (R := R) _).mp hbV
  have hpre : Q.i.left ⁻¹ᵁ (Q.q.left ⁻¹ᵁ V) = (splitTorus _ X).hom ⁻¹ᵁ ((η[Q.B]).left ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, hw, Scheme.Hom.comp_preimage]
  rw [hpre, htop, Scheme.Hom.preimage_top]

theorem exists_torus (A : Type) [CommRing A] [IsLocalRing A] (J : Ideal A) (hJ : IsNilpotent J) (X : Type)
    [AddCommGroup X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (G₀ : Over (Spec (CommRingCat.of (A ⧸ J)))) [GrpObj G₀] (F : G₀.left ⟶ G.left)
    (h : IsGrpPullback G₀ G (red J) F) (Q₀ : TQ G₀ X) :
    ∃ i : splitTorus _ X ⟶ G, IsMonHom i ∧ TorusCompat (red J) F Q₀.i i := by
  have hi₀hom := Q₀.i_hom
  obtain ⟨e, he_hom, he_fst⟩ := exists_iso_pullback h

  have hJtop : J ≠ ⊤ := by
    intro hJt
    obtain ⟨n, hn⟩ := hJ
    rw [hJt, Ideal.top_pow, Ideal.zero_eq_bot] at hn
    exact top_ne_bot hn
  have : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJtop
  have : IsLocalRing (A ⧸ J) := IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective

  let i₀ : (Over.pullback (red J)).obj (splitTorus (Spec (CommRingCat.of A)) X) ⟶
      (Over.pullback (red J)).obj G :=
    (SplitTorus.bcIso (red J) X).inv ≫ Q₀.i ≫ e.hom
  have hi₀ : IsMonHom i₀ := by
    dsimp only [i₀]
    infer_instance
  obtain ⟨W₀, hW₀, hW₀top⟩ := exists_isAffineOpen Q₀
  have hcomp : i₀.left ≫ e.inv.left = (SplitTorus.bcIso (red J) X).inv.left ≫ Q₀.i.left := by
    simp [i₀]
  have hW : ∃ W : ((Over.pullback (red J)).obj G).left.Opens, IsAffineOpen W ∧ i₀.left ⁻¹ᵁ W = ⊤ := by
    have : IsIso e.inv.left :=
      ⟨e.hom.left, by rw [← Over.comp_left, e.inv_hom_id, Over.id_left],
        by rw [← Over.comp_left, e.hom_inv_id, Over.id_left]⟩
    refine ⟨e.inv.left ⁻¹ᵁ W₀, hW₀.preimage _, ?_⟩
    rw [← Scheme.Hom.comp_preimage, hcomp, Scheme.Hom.comp_preimage, hW₀top, Scheme.Hom.preimage_top]
  obtain ⟨i, ⟨hi, hmap⟩, -⟩ := GlobalTheory.TorusLift.main A J hJ X G i₀ hi₀ hW
  refine ⟨i, hi, ?_⟩
  rw [torusCompat_iff, ← SplitTorus.bcIso_hom_fst, Category.assoc, ← GlobalTheory.TorusLift.map_left_fst, hmap]
  simp only [i₀, Over.comp_left, Category.assoc, he_fst]
  rw [← Category.assoc, ← Over.comp_left, Iso.hom_inv_id, Over.id_left, Category.id_comp]

theorem main : (∀ (A : Type) [CommRing A] [IsLocalRing A] (J : Ideal A), IsNilpotent J → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (G₀ : Over (Spec (CommRingCat.of (A ⧸ J)))) [GrpObj G₀] (F : G₀.left ⟶ G.left), IsGrpPullback G₀ G (red J) F → ∀ Q₀ : TQ G₀ X, ∃ Q : TQ G X, TorusCompat (red J) F Q₀.i Q.i) := by
  intro A _ _ J hJ X _ _ _ G _ _ _ G₀ _ F h Q₀
  obtain ⟨i, hi, hc⟩ := exists_torus A J hJ X G G₀ F h Q₀
  obtain ⟨B, q, j, hjpb, -, haff, hloc⟩ := GlobalTheory.T.exists_torus_quotient_scheme_over_nilpotent_thickening A J hJ X G G₀ F h Q₀ i hi hc
  obtain ⟨hmono, hflat, hsurj, hsmooth, hcoset⟩ := GlobalTheory.T.locallyTrivial_torusQuotient_flat_surjective_cosets _ X G B i q hi haff hloc
  have : IsAffineHom q.left := haff
  obtain ⟨grpB, hcommB, hq, hker⟩ := GlobalTheory.grpObj_of_flat_coset_quotient _ G (splitTorus _ X) B i q
    hi hmono hflat hsurj inferInstance hcoset
  have hBsmooth : Smooth B.hom := hsmooth inferInstance

  have hB₀ := Q₀.isAb
  have hsnd : pullback.snd B.hom (red J) = hjpb.isoPullback.inv ≫ Q₀.B.hom := by
    rw [Iso.eq_inv_comp, IsPullback.isoPullback_hom_snd]
  have hPG := GlobalTheory.NilProper.isProper_and_geometricallyConnected_of_isNilpotent A J hJ B
  have hAb : IsAbelianScheme B := by
    constructor
    case comm => exact hcommB
    case smooth => exact hBsmooth
    case proper =>
      refine hPG.1 ?_
      rw [hsnd]
      have := hB₀.proper
      infer_instance
    case geomConnected =>
      refine hPG.2 ?_
      rw [hsnd]
      have := hB₀.geomConnected
      have hst : MorphismProperty.IsStableUnderBaseChange (@GeometricallyConnected.{0}) := inferInstance
      have hRI : MorphismProperty.RespectsIso (@GeometricallyConnected.{0}) :=
        MorphismProperty.IsStableUnderBaseChange.respectsIso
      exact (MorphismProperty.cancel_left_of_respectsIso (@GeometricallyConnected.{0}) _ _).mpr this
  have hloc' : ∀ (b : B.left) (χ : X), ∃ V : B.left.Opens, b ∈ V ∧
      ∃ u : Γ(G.left, q.left ⁻¹ᵁ V)ˣ, IsWt i _ u.val χ := by
    intro b χ
    obtain ⟨V, hbV, -, -, -, -, u, hu⟩ := hloc b
    exact ⟨V, hbV, u (Multiplicative.ofAdd χ), hu χ⟩
  exact ⟨⟨B, hAb, q, i, hq, hi, hflat, hsurj, haff, hker, hloc'⟩, hc⟩

end GlobalTheory.TorusQuotLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RedIffReduction
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.UU.RedOnto

open GlobalTheory.FormalPoint

section Level

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : PreU I D A G)
  {T : Over (Spec (CommRingCat.of R))}

def Coords (e : ℕ) (g : GtPt D T) {Z : Scheme.{0}} (r : Z ⟶ T.left)
    (y : Z ⟶ (thickObj R I e G).left) : Prop :=
  y ≫ (U.gt e).pG.left = r ≫ g.b.left ∧
    ∀ (χ : D.X) (z : Z) (J), Good D.P.L z J → val ((U.gt e).t χ) y z J = val (g.s χ) r z J

variable {U}

theorem Coords.comp {e : ℕ} {g : GtPt D T} {Z W : Scheme.{0}} {r : Z ⟶ T.left}
    {y : Z ⟶ (thickObj R I e G).left} (h : Coords U e g r y) (k : W ⟶ Z) :
    Coords U e g (k ≫ r) (k ≫ y) := by
  unfold Coords at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨by rw [Category.assoc, h1, Category.assoc], fun χ w J hJ => ?_⟩

  have hc : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ ((U.gt e).t χ) y) (LB.pullGen D.P.L _ _ (g.s χ) r) :=
    corr_of_val D.P.isLB fun z J' hJ' => by
      rw [val_pull hJ', val_pull hJ', Category.id_comp, Category.id_comp]
      exact h2 χ z J' hJ'
  have hk := val_corr hJ hc k
  rwa [val_pull hJ, val_pull hJ] at hk

theorem Coords.unique {e : ℕ} {g : GtPt D T} {Z : Scheme.{0}} {r : Z ⟶ T.left}
    {y y' : Z ⟶ (thickObj R I e G).left} (h : Coords U e g r y) (h' : Coords U e g r y') : y = y' := by
  unfold Coords at h h'
  exact GlobalTheory.TorusCoord.ext_of_val (U.gt e) y y' (h.1.trans h'.1.symm)
    fun χ w J hJ => (h.2 χ w J hJ).trans (h'.2 χ w J hJ).symm


variable (U) in
theorem exists_coords (e : ℕ) (g : GtPt D T) {Z : Scheme.{0}} (r : Z ⟶ T.left)
    (σ : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) (h : σ ≫ thick R I e = r ≫ T.hom) :
    ∃ y, Coords U e g r y := by
  obtain ⟨x, hx1, hx2⟩ := GlobalTheory.FormalPoint.exists_point (U.gt e) g (Z := Over.mk σ)
    (Over.homMk r h.symm)
  refine ⟨x, ?_⟩
  unfold Coords
  refine ⟨hx1, fun χ z J hJ => ?_⟩
  have hv := hx2 χ Z (𝟙 Z) z J hJ
  rw [Category.id_comp, Category.id_comp] at hv
  exact hv

theorem Coords.succ {e : ℕ} {g : GtPt D T} {Z : Scheme.{0}} {r : Z ⟶ T.left}
    {y : Z ⟶ (thickObj R I e G).left} (h : Coords U e g r y) :
    Coords U (e + 1) g r (y ≫ thickMap R I e G) := by
  unfold Coords at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨by rw [Category.assoc, U.gt_q e]; exact h1, fun χ z J hJ => ?_⟩
  rw [← val_pull hJ ((U.gt (e + 1)).t χ) (thickMap R I e G) y, val_corr hJ (U.gt_t e χ) y]
  exact h2 χ z J hJ

private theorem comp_hom_eq_of_coords {e : ℕ} {g : GtPt D T} {Z : Scheme.{0}} {r : Z ⟶ T.left}
    {y : Z ⟶ (thickObj R I e G).left} (h : Coords U e g r y) :
    r ≫ T.hom = y ≫ (thickObj R I e G).hom ≫ thick R I e := by
  obtain ⟨h1, -⟩ := h
  have e1 : g.b.left ≫ D.P.A.hom = T.hom := Over.w g.b
  have e2 : (U.gt e).pG.left ≫ D.P.A.hom = (thickObj R I e G).hom ≫ thick R I e := Over.w (U.gt e).pG
  calc r ≫ T.hom = (r ≫ g.b.left) ≫ D.P.A.hom := by rw [Category.assoc, e1]
    _ = (y ≫ (U.gt e).pG.left) ≫ D.P.A.hom := by rw [h1]
    _ = y ≫ (thickObj R I e G).hom ≫ thick R I e := by rw [Category.assoc, e2]

theorem comp_fstG_eq {g : GtPt D T} {x : T ⟶ G} (hx : U.Red x g) {e : ℕ} {Z : Scheme.{0}}
    {r : Z ⟶ T.left} {y : Z ⟶ (thickObj R I e G).left} (h : Coords U e g r y) :
    y ≫ (fstG I e G).left = r ≫ x.left := by
  have hb := comp_hom_eq_of_coords h
  have ex : x.left ≫ G.hom = T.hom := Over.w x

  obtain ⟨a, ha⟩ := GlobalTheory.FormalPoint.exists_lift_fstG (Z := Over.mk (y ≫ (thickObj R I e G).hom))
    (Over.homMk (r ≫ x.left) (by
      show (r ≫ x.left) ≫ G.hom = (y ≫ (thickObj R I e G).hom) ≫ thick R I e
      rw [Category.assoc, ex, hb, Category.assoc]))
  have ha' : a.left ≫ (fstG I e G).left = r ≫ x.left := congrArg CommaMorphism.left ha
  have hc : Coords U e g r a.left := hx e Z r a.left ha'
  rw [← Coords.unique hc h]
  exact ha'

end Level

section Complete

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {S : Type} [CommRing S] {φ : R →+* S} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : PreU I D A G)

theorem red_iff_reduction (g : GtPt D (Over.mk (spMap φ))) (x : Over.mk (spMap φ) ⟶ G) :
    U.Red x g ↔ ∀ e, Coords U e g (adicLevelι (I.map φ) (e + 1)) (reduction I x e) := by
  constructor
  · intro hx e
    exact hx e _ _ _ (GlobalTheory.FormalPoint.reduction_fstG I x e)
  · intro h e Z r xe hxe
    have ex : x.left ≫ G.hom = spMap φ := Over.w x
    have ef : (fstG I e G).left ≫ G.hom = (thickObj R I e G).hom ≫ thick R I e := Over.w (fstG I e G)
    have hs : r ≫ spMap φ = (xe ≫ (thickObj R I e G).hom) ≫ thick R I e := by
      rw [← ex, ← Category.assoc, ← hxe]
      simp only [Category.assoc, ef]

    obtain ⟨l, hl⟩ := GlobalTheory.FormalPoint.exists_factor_level I φ r _ hs
    have hc := Coords.comp (h e) l
    have hred : l ≫ GlobalTheory.FormalPoint.reduction I x e = xe := by
      rw [← cancel_mono (fstG I e G).left, Category.assoc, GlobalTheory.FormalPoint.reduction_fstG, ← Category.assoc,
        hl, hxe]
    rw [hl, hred] at hc
    exact hc

variable [IsLocalRing S]


variable {U} in
theorem red_unique [IsHausdorff (I.map φ) S] {g : GtPt D (Over.mk (spMap φ))}
    {x x' : Over.mk (spMap φ) ⟶ G} (h : U.Red x g) (h' : U.Red x' g) : x = x' := by
  have hr := (red_iff_reduction U g x).1 h
  have hr' := (red_iff_reduction U g x').1 h'
  apply Over.OverMorphism.ext
  apply GlobalTheory.hom_ext_of_isHausdorff (I.map φ)
  intro n
  rw [← GlobalTheory.FormalPoint.reduction_fstG I x n, ← GlobalTheory.FormalPoint.reduction_fstG I x' n, Coords.unique (hr n) (hr' n)]

theorem existsUnique_red [IsAdicComplete (I.map φ) S] (g : GtPt D (Over.mk (spMap φ))) :
    ∃! x : Over.mk (spMap φ) ⟶ G, U.Red x g := by
  have hy : ∀ e, ∃ y, Coords U e g (adicLevelι (I.map φ) (e + 1)) y := fun e =>
    exists_coords U e g (adicLevelι (I.map φ) (e + 1)) (GlobalTheory.FormalPoint.levelMap I φ e)
      (GlobalTheory.FormalPoint.levelMap_thick I φ e)
  choose y hy using hy
  have htf : ∀ n, thickMap R I n G ≫ (fstG I (n + 1) G).left = (fstG I n G).left := by
    intro n
    unfold thickMap fstG
    simp only [pullback.map, Category.comp_id, Over.homMk_left, pullback.lift_fst]

  have hcomp : ∀ n, GlobalTheory.adicLevelMap (I.map φ) (Nat.le_succ (n + 1)) ≫ y (n + 1) = y n ≫ thickMap R I n G := by
    intro n
    refine Coords.unique ?_ (Coords.succ (hy n))
    have hk := Coords.comp (hy (n + 1)) (GlobalTheory.adicLevelMap (I.map φ) (Nat.le_succ (n + 1)))
    rwa [GlobalTheory.adicLevelMap_ι] at hk
  have hf : GlobalTheory.IsAdicFamily (I.map φ) (fun n => y n ≫ (fstG I n G).left) := by
    intro n
    show GlobalTheory.adicLevelMap (I.map φ) (Nat.le_succ (n + 1)) ≫ y (n + 1) ≫ (fstG I (n + 1) G).left =
      y n ≫ (fstG I n G).left
    rw [← Category.assoc, hcomp n, Category.assoc, htf n]
  have hs : ∀ n, (y n ≫ (fstG I n G).left) ≫ G.hom = adicLevelι (I.map φ) (n + 1) ≫ spMap φ := by
    intro n
    have ef : (fstG I n G).left ≫ G.hom = (thickObj R I n G).hom ≫ thick R I n := Over.w (fstG I n G)
    rw [Category.assoc, ef]
    exact (comp_hom_eq_of_coords (hy n)).symm

  obtain ⟨x₀, ⟨hx₀, hxn⟩, -⟩ := GlobalTheory.existsUnique_over_of_isAdicFamily (spMap φ) G.hom hf hs
  have hred : U.Red (Over.homMk x₀ hx₀ : Over.mk (spMap φ) ⟶ G) g := by
    refine (red_iff_reduction U g _).2 fun e => ?_
    have he : GlobalTheory.FormalPoint.reduction I (Over.homMk x₀ hx₀ : Over.mk (spMap φ) ⟶ G) e = y e := by
      rw [← cancel_mono (fstG I e G).left, GlobalTheory.FormalPoint.reduction_fstG]
      exact hxn e
    rw [he]
    exact hy e
  exact ⟨_, hred, fun x' hx' => red_unique hx' hred⟩

end Complete

theorem main : (AllPre fun {V} _ _ _ {D} {_} {G} _ _ U => ∀ (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], FinExt V W → ∀ g : GtPt D (TA V W), ∃! x : TA V W ⟶ G, U.Red x g) := by
  intro V _ _ _ _ D A G _ _ U W _ _ _ hW g
  obtain ⟨-, -, -, -, hc⟩ := hW
  exact existsUnique_red (φ := algebraMap V W) U g

end GlobalTheory.UU.RedOnto

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullDegEquivApply
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PullDegCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification (CarriesAt PullIdent ptK_comp)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(X, U)ˣ) :
    res h₂ (res h₁ s) = res (h₂.trans h₁) s := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem res_self {X : Scheme.{0}} {U : X.Opens} (h : U ≤ U) (s : Γ(X, U)ˣ) : res h s = s := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  have : (homOfLE h).op = 𝟙 _ := rfl
  rw [this, CategoryTheory.Functor.map_id]
  rfl

theorem res_eq_iff {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (h' : U ≤ V) (s t : Γ(X, U)ˣ) :
    res h s = res h t ↔ s = t :=
  ⟨fun e => by
    have := congrArg (res h') e
    rwa [res_res, res_res, res_self, res_self] at this, fun e => e ▸ rfl⟩

section Bundle

variable {X X' Y : Scheme.{0}} (L : LB X) (L' : LB X') (F : X' ⟶ X)

theorem corr_iff_eq (p : Y ⟶ X) (n : ℤ)
    (b c : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => p) (fun _ => n))) :
    LB.Gen.Corr L _ _ _ _ b c ↔ b = c := by
  constructor
  · intro h
    obtain ⟨b⟩ := b
    obtain ⟨c⟩ := c
    congr 1
    funext j
    have := h j j (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    exact (res_eq_iff _ (le_inf le_rfl le_rfl) _ _).1 this
  · rintro rfl j j' _ _ h
    obtain rfl : j = j' := funext fun k => h k k rfl
    rfl

theorem exists_mapsAt_iff (w : LB.Iso L' (L.pull F)) (p' : Y ⟶ X') (p : Y ⟶ X) (hp : p' ≫ F = p) (n : ℤ)
    (a : LB.Gen (LB.LinComb L' (K := PUnit) (fun _ => p') (fun _ => n)))
    (c : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => p) (fun _ => n))) :
    (∃ b : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => p' ≫ F) (fun _ => n)),
      GeneratorPullback.MapsAt L L' (J := PUnit) (fun _ => F) w p' n a b ∧ LB.Gen.Corr L _ _ _ _ b c) ↔
    CarriesAt L L' F w p' p hp n a c := by
  subst hp
  constructor
  · rintro ⟨b, hb, hc⟩ j j'
    obtain rfl := (corr_iff_eq L _ n b c).1 hc
    exact hb (fun _ => j) j'
  · intro h
    exact ⟨c, fun jN jL => h (jN PUnit.unit) jL, (corr_iff_eq L _ n c c).2 rfl⟩

end Bundle

section Grp

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']

theorem rig_iff [IsCommMonObj G] [IsCommMonObj G'] (F : G'.left ⟶ G.left) (f : S' ⟶ S)
    (he : eSec G' ≫ F = f ≫ eSec G) (L : LB G.left) (L' : LB G'.left) (w : LB.Iso L' (L.pull F))
    (r : LB.Gen (L.pull (eSec G))) (r' : LB.Gen (L'.pull (eSec G'))) :
    LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec G') (fun _ => 1)) r' (rigPullOf F f he L r) ↔
    CarriesAt L L' F w (eSec G') (f ≫ eSec G) he 1 r' (LB.pullGen L _ _ r f) := by
  have key : ∀ (j : L.ι) (j' : L'.ι),
      (res (inf_le_left : _ ⊓ (L'.pull (eSec G')).U (fun _ => j') ≤ _) ((rigPullOf F f he L r).s (fun _ _ => j)) =
        @id (Γ((𝟙_ (Over S')).left, ((L.pull F).pull (eSec G')).U (fun _ _ => j) ⊓ (L'.pull (eSec G')).U (fun _ => j'))ˣ)
          ((LB.linCombIso w (K := PUnit) (fun _ => eSec G') (fun _ => 1)).s (fun _ _ => j, fun _ => j')) *
          res inf_le_right (r'.s (fun _ => j'))) ↔
      res (GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.chart_le_target L L' F (eSec G') (f ≫ eSec G) he j j')
          ((LB.pullGen L _ _ r f).s (fun _ => j)) =
        (pullU (eSec G') _ (w.s (fun _ => j, j'))) ^ (1 : ℤ) *
          res (GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.chart_le_source L L' F (eSec G') j j') (r'.s (fun _ => j')) := by
    intro j j'
    have h₁ : ((L.pull F).pull (eSec G')).U (fun _ _ => j) ⊓ (L'.pull (eSec G')).U (fun _ => j') ≤
        eSec G' ⁻¹ᵁ (LB.div (L.pull F) L').U (fun _ => j, j') :=
      fun y hy => ⟨Set.mem_iInter.1 hy.1 PUnit.unit, Set.mem_iInter.1 hy.2 PUnit.unit⟩
    have h₂ : eSec G' ⁻¹ᵁ (LB.div (L.pull F) L').U (fun _ => j, j') ≤
        ((L.pull F).pull (eSec G')).U (fun _ _ => j) ⊓ (L'.pull (eSec G')).U (fun _ => j') :=
      fun y hy => ⟨Set.mem_iInter.2 fun _ => hy.1, Set.mem_iInter.2 fun _ => hy.2⟩
    rw [← res_eq_iff h₁ h₂, map_mul, map_zpow]
    refine Eq.congr ?_ (congrArg₂ (· * ·) (Fintype.prod_unique fun _ : PUnit =>
      res h₁ (pullU (eSec G') _ (w.s (fun _ => j, j'))) ^ (1 : ℤ)) ?_)
    · exact (res_res _ _ _).trans ((res_res _ _ _).trans (res_res _ _ _)).symm
    · exact (res_res _ _ _).symm
  exact ⟨fun h j j' => (key j j').1 (h (fun _ _ => j, fun _ => j')),
    fun h p => (key (p.1 PUnit.unit PUnit.unit) (p.2 PUnit.unit)).2 (h _ _)⟩

theorem isGrpPullback_iff {f : S' ⟶ S} {F : G'.left ⟶ G.left} (cart : IsPullback F G'.hom G.hom f) :
    IsGrpPullback G' G f F ↔ (μ[G']).left ≫ F =
      pullback.map G'.hom G'.hom G.hom G.hom F F f cart.w.symm cart.w.symm ≫ (μ[G]).left := by
  have m : ∀ (T : Over S') (x y : T ⟶ G') (x₀ y₀ : Over.mk (T.hom ≫ f) ⟶ G),
      x₀.left = x.left ≫ F → y₀.left = y.left ≫ F → (lift x₀ y₀).left = (lift x y).left ≫
        pullback.map G'.hom G'.hom G.hom G.hom F F f cart.w.symm cart.w.symm := by
    intro T x y x₀ y₀ hx hy
    apply pullback.hom_ext
    · have e₁ : (lift x₀ y₀).left ≫ pullback.fst G.hom G.hom = x₀.left := congrArg (·.left) (lift_fst x₀ y₀)
      have e₂ : (lift x y).left ≫ pullback.fst G'.hom G'.hom = x.left := congrArg (·.left) (lift_fst x y)
      refine e₁.trans (hx.trans ?_)
      rw [← e₂, Category.assoc, Category.assoc]
      exact congrArg _ (pullback.lift_fst _ _ _).symm
    · have e₁ : (lift x₀ y₀).left ≫ pullback.snd G.hom G.hom = y₀.left := congrArg (·.left) (lift_snd x₀ y₀)
      have e₂ : (lift x y).left ≫ pullback.snd G'.hom G'.hom = y.left := congrArg (·.left) (lift_snd x y)
      refine e₁.trans (hy.trans ?_)
      rw [← e₂, Category.assoc, Category.assoc]
      exact congrArg _ (pullback.lift_snd _ _ _).symm
  constructor
  · intro h
    have e := h.2 _ (fst G' G') (snd G' G') (pushPt cart.w _) (pushPt cart.w _) rfl rfl
    have e' := m _ (fst G' G') (snd G' G') (pushPt cart.w _) (pushPt cart.w _) rfl rfl
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp, Over.comp_left, e', lift_fst_snd, Over.id_left] at e
    exact e.symm.trans (congrArg (· ≫ _) (Category.id_comp _))
  · intro h
    refine ⟨cart, fun T x y x₀ y₀ hx hy => ?_⟩
    rw [Hom.mul_def, Hom.mul_def, Over.comp_left, Over.comp_left, m T x y x₀ y₀ hx hy, Category.assoc]
    exact (Category.assoc _ _ _).trans (congrArg _ h.symm)

end Grp

section Main

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}

abbrev OpenChoice (φ : R →+* R') (D : DegPre R) : Type :=
  Σ W : (Spec (CommRingCat.of R)).Opens,
    PsiOn D W × {g : (TK R').left ⟶ (TW W).left // g ≫ W.ι = jK R' ≫ specOf φ}

def PsiCarried (p : PullIdent φ D D') (o : OpenChoice φ D) : Prop :=
  ∀ χ : D'.X, CarriesAt D.P.L D'.P.L p.F p.w (D'.xK χ) (o.2.2.1 ≫ (toUnit (TW o.1) ≫ D.c (p.xe χ)).left)
    (ptK_comp φ p.F (D.c (p.xe χ)) (D'.c χ) (p.c_eq χ) o.1 o.2.2.1 o.2.2.2) (-1) (D'.psi χ)
    (LB.pullGen D.P.L _ _ (o.2.1.psi (p.xe χ)) o.2.2.1)

def toOpenChoice (h : IsPullDeg φ D D') : OpenChoice φ D := ⟨h.W, h.psiW, h.g, h.g_comm⟩

theorem psi_pr_carries (h : IsPullDeg φ D D') (χ : D'.X) :
    CarriesAt D.P.L D'.P.L (h.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) h.w (D'.xK χ)
      (h.g ≫ (toUnit (TW h.W) ≫ D.c (h.xe χ)).left)
      (ptK_comp φ _ (D.c (h.xe χ)) (D'.c χ) (h.c_pr χ) h.W h.g h.g_comm) (-1) (D'.psi χ)
      (LB.pullGen D.P.L _ _ (h.psiW.psi (h.xe χ)) h.g) :=
  (exists_mapsAt_iff D.P.L D'.P.L _ h.w _ _ _ (-1) _ _).1 (h.psi_pr χ)

def toIdent (h : IsPullDeg φ D D') : PullIdent φ D D' where
  F := h.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)
  cart := (pull_grp h).1
  F_one := h.he
  F_mul := (isGrpPullback_iff (pull_grp h).1).1 (pull_grp h)
  w := h.w
  w_gen := h.w_gen
  w_rig := (rig_iff _ _ h.he _ _ h.w D.rig D'.rig).1 h.w_rig
  xe := h.xe
  c_eq := h.c_pr
  w_psi := ⟨h.W, h.psiW, h.g, h.g_comm, psi_pr_carries h⟩

theorem exists_toIdent_eq (p : PullIdent φ D D') (o : OpenChoice φ D) (H : PsiCarried p o) :
    ∃ h : IsPullDeg φ D D', toIdent h = p ∧ toOpenChoice h = o := by
  obtain ⟨e, me, he⟩ := grpPullback_iso ((isGrpPullback_iff p.cart).2 p.F_mul)
    (isGrpPullback_pullback D.P.A (specOf φ))
  obtain ⟨F, cart, F₁, Fm, w, wg, wr, xe, ce, wp⟩ := p
  dsimp only at he
  subst he
  exact ⟨⟨e, me, w, wg, F₁, (rig_iff _ _ F₁ _ _ w D.rig D'.rig).2 wr, xe, ce, o.1, o.2.1, o.2.2.1, o.2.2.2,
    fun χ => (exists_mapsAt_iff D.P.L D'.P.L _ w _ _ _ (-1) _ _).2 (H χ)⟩, rfl, rfl⟩

theorem toIdent_surjective : Function.Surjective (toIdent : IsPullDeg φ D D' → PullIdent φ D D') := fun p => by
  obtain ⟨W, ψW, g, hg, H⟩ := p.w_psi
  obtain ⟨h, e, -⟩ := exists_toIdent_eq p ⟨W, ψW, g, hg⟩ H
  exact ⟨h, e⟩

theorem nonempty_iff : Nonempty (IsPullDeg φ D D') ↔ Nonempty (PullIdent φ D D') :=
  ⟨fun ⟨h⟩ => ⟨toIdent h⟩, fun ⟨p⟩ => let ⟨h, _⟩ := toIdent_surjective p; ⟨h⟩⟩

end Main

end GlobalTheory.PullDegCompare
end
end

module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PotentialSemistableOfRationalLTorsion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantBoundedByShortestVector

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSemiAbelianModelPadicPrincipallyPolarised
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PrincipallyPolarizedAbelianVarietyPotentialSemiA
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PrincipallyPolarizedAbelianVarietyPotentialSemiA
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SemiPol

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

theorem exists_prime_unit (V : Type) [CommRing V] [IsLocalRing V] :
    ∃ l : ℕ, l.Prime ∧ 3 ≤ l ∧ IsUnit (l : V) := by
  have h : IsUnit ((2 : V) * ((3 : ℕ) : V) + -((5 : ℕ) : V)) := by
    have : (2 : V) * ((3 : ℕ) : V) + -((5 : ℕ) : V) = 1 := by push_cast; ring
    rw [this]; exact isUnit_one
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h with h | h
  · exact ⟨3, Nat.prime_three, le_rfl, isUnit_of_mul_isUnit_right h⟩
  · exact ⟨5, Nat.prime_five, by norm_num, by simpa using h⟩

theorem exists_pullback {S S' : Scheme.{0}} (f : S' ⟶ S) (P : Out.PolAV S) :
    ∃ (P' : Out.PolAV S') (φ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A f φ := by
  obtain ⟨P', φ, hφ, -, mul, -⟩ :=
    polBaseChange_of_relAmple_local GlobalTheory.AmpleLocal.relAmple_of_locally S S' f P
  refine ⟨P', φ, hφ, fun T x y x₀ y₀ hx hy => ?_⟩
  have e₁ : x₀ = Out.toBase hφ.w x := Over.OverMorphism.ext hx
  have e₂ : y₀ = Out.toBase hφ.w y := Over.OverMorphism.ext hy
  rw [e₁, e₂, ← mul]
  rfl

theorem fixed_of_rational {K K₁ Ω Ω₁ : Type} [Field K] [Field K₁] [Field Ω] [Field Ω₁] [Algebra K K₁] [Algebra K Ω]
    [Algebra K₁ Ω] [IsScalarTower K K₁ Ω] [Algebra K₁ Ω₁] (j : Ω ≃ₐ[K₁] Ω₁)
    {A : Over (Sp K)} [GrpObj A] {A₁ : Over (Sp K₁)} [GrpObj A₁] {φ : A₁.left ⟶ A.left}
    (h : IsGrpPullback A₁ A (spMap (algebraMap K K₁)) φ) (l : ℕ)
    (hr : ∀ x : Over.mk (spMap (algebraMap K Ω)) ⟶ A, x ^ l = 1 →
      ∃ y : Sp K₁ ⟶ A.left, spMap (algebraMap K₁ Ω) ≫ y = x.left)
    (τ : Ω₁ ≃ₐ[K₁] Ω₁) (x : Over.mk (spMap (algebraMap K₁ Ω₁)) ⟶ A₁) (hx : x ^ l = 1) :
    spMap τ.toRingEquiv.toRingHom ≫ x.left = x.left := by
  obtain ⟨e, he⟩ := exists_mulEquiv_of_isGrpPullback h (spMap (algebraMap K₁ Ω₁))
    (spMap (algebraMap K₁ Ω₁) ≫ spMap (algebraMap K K₁)) rfl
  let u : Over.mk (spMap (algebraMap K Ω)) ⟶ Over.mk (spMap (algebraMap K₁ Ω₁) ≫ spMap (algebraMap K K₁)) :=
    Over.homMk (spMap j.symm.toRingEquiv.toRingHom) (by
      show spMap _ ≫ spMap _ ≫ spMap _ = spMap _
      rw [sp_comp, sp_comp]
      congr 1
      ext c
      simp [← IsScalarTower.algebraMap_apply])
  obtain ⟨y, hy⟩ := hr (u ≫ e x) (by rw [← MonObj.comp_pow, ← map_pow, hx, map_one, MonObj.comp_one])
  have hy' : spMap (algebraMap K₁ Ω) ≫ y = spMap j.symm.toRingEquiv.toRingHom ≫ x.left ≫ φ := by
    rw [hy, ← he]; rfl
  have h₁ : spMap (algebraMap K₁ Ω₁) ≫ y = x.left ≫ φ := by
    have e₁ : spMap j.toRingEquiv.toRingHom ≫ spMap (algebraMap K₁ Ω) = spMap (algebraMap K₁ Ω₁) := by
      rw [sp_comp]; congr 1; ext c; simp
    have e₂ : spMap j.toRingEquiv.toRingHom ≫ spMap j.symm.toRingEquiv.toRingHom = 𝟙 _ := by
      rw [sp_comp, ← Spec.map_id]; congr 1; ext c; simp
    refine (congrArg (· ≫ y) e₁.symm).trans ((Category.assoc _ _ _).trans ?_)
    rw [hy', ← Category.assoc, e₂]
    exact Category.id_comp _
  have hτ : spMap τ.toRingEquiv.toRingHom ≫ spMap (algebraMap K₁ Ω₁) = spMap (algebraMap K₁ Ω₁) := by
    rw [sp_comp]; congr 1; ext c; simp
  refine h.1.hom_ext ?_ ?_
  · refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (_ ≫ ·) h₁.symm).trans ?_
    rw [← Category.assoc, hτ, h₁]
  · refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (_ ≫ ·) (Over.w x)).trans ?_
    exact hτ.trans (Over.w x).symm

theorem exists_finset (K : Type) [Field K] [CharZero K] (P : Out.PolAV (Sp K)) (Ω : Type) [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] (l : ℕ) (hl : l.Prime) :
    ∃ s : Finset Ω, ∀ (K₁ : Type) [Field K₁] [Algebra K K₁] [Algebra K₁ Ω] [IsScalarTower K K₁ Ω],
      (∀ c ∈ s, c ∈ (algebraMap K₁ Ω).fieldRange) →
      ∀ x : Over.mk (spMap (algebraMap K Ω)) ⟶ P.A, x ^ l = 1 →
        ∃ y : Sp K₁ ⟶ P.A.left, spMap (algebraMap K₁ Ω) ≫ y = x.left := by
  classical
  have hc := (GlobalTheory.T.torsion_points_polarised_abelianVariety_galois K P Ω l hl).1 1
  rw [pow_one] at hc
  have hfin : Finite {x : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) // x ^ l = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ hl.ne_zero)
  have hsm := P.smoothDim
  have hsm' : Smooth P.A.hom := SmoothOfRelativeDimension.smooth P.g _
  have hft : LocallyOfFiniteType P.A.hom := inferInstance
  have key : ∀ x : {x : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) // x ^ l = 1}, ∃ s : Finset Ω,
      ∀ (K₁ : Type) [Field K₁] [Algebra K K₁] [Algebra K₁ Ω] [IsScalarTower K K₁ Ω],
      (∀ c ∈ s, c ∈ (algebraMap K₁ Ω).fieldRange) →
        ∃ y : Sp K₁ ⟶ P.A.left, spMap (algebraMap K₁ Ω) ≫ y = x.1.left := by
    intro x
    obtain ⟨E, -, h₂, h₃⟩ := GlobalTheory.SS.exists_fieldOfValues P.A.left Ω x.1.left
    obtain ⟨L, hL, rfl⟩ := h₃ K P.A.hom hft (Over.w x.1) inferInstance
    obtain ⟨s, hs⟩ : (Subalgebra.toSubmodule L.toSubalgebra).FG :=
      (Submodule.fg_iff_finiteDimensional _).2 hL
    refine ⟨s, fun K₁ _ _ _ _ hK => (h₂ K₁ _).1 fun c hc => ?_⟩
    have : Subalgebra.toSubmodule L.toSubalgebra ≤
        Subalgebra.toSubmodule (IsScalarTower.toAlgHom K K₁ Ω).range := by
      rw [← hs, Submodule.span_le]
      exact fun d hd => hK d hd
    exact this hc
  choose s hs using key
  have := Fintype.ofFinite {x : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) // x ^ l = 1}
  exact ⟨Finset.univ.biUnion s, fun K₁ _ _ _ _ hK x hx => hs ⟨x, hx⟩ K₁ fun c hc =>
    hK c (Finset.mem_biUnion.2 ⟨_, Finset.mem_univ _, hc⟩)⟩

theorem potModel_semiAbelian : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K], Finite (IsLocalRing.ResidueField V) → ∀ P : Out.PolAV (Sp K), PotModel V K P.A (fun _ _ _ G _ => IsSemiAbelian G) := by
  intro V K _ _ _ _ _ _ _ _ hres P
  obtain ⟨l, hl, h3, hu⟩ := exists_prime_unit V
  let Ω := AlgebraicClosure K
  obtain ⟨s, hs⟩ := exists_finset K P Ω l hl
  have hV : CharZero V := (algebraMap V K).charZero
  have hinj : Function.Injective (algebraMap V Ω) := by
    rw [IsScalarTower.algebraMap_eq V K Ω]
    exact (algebraMap K Ω).injective.comp (IsFractionRing.injective V K)
  have hf : FaithfulSMul V Ω := (faithfulSMul_iff_algebraMap_injective V Ω).2 hinj
  have ha : Algebra.IsAlgebraic V Ω :=
    (IsFractionRing.comap_isAlgebraic_iff (A := V) (K := K) (C := Ω)).2 inferInstance
  obtain ⟨W, hW, hWc, -, hWf, -, hWl, hWs, -⟩ := exists_complete_dvr_finite_subalgebra V Ω s
  let K₁ := FractionRing W
  have hinj₁ : Function.Injective ((algebraMap W K₁).comp (algebraMap V W)) :=
    (IsFractionRing.injective W K₁).comp fun a b h => hinj (congrArg Subtype.val h)
  let _ : Algebra K K₁ := (IsFractionRing.lift hinj₁ : K →+* K₁).toAlgebra
  let _ : Algebra K₁ Ω := (IsFractionRing.lift (g := algebraMap W Ω) Subtype.val_injective : K₁ →+* Ω).toAlgebra
  have c₁ : ∀ a, algebraMap K K₁ (algebraMap V K a) = algebraMap W K₁ (algebraMap V W a) := fun a =>
    IsFractionRing.lift_algebraMap hinj₁ a
  have c₂ : ∀ a : W, algebraMap K₁ Ω (algebraMap W K₁ a) = a := fun a =>
    IsFractionRing.lift_algebraMap (g := algebraMap W Ω) Subtype.val_injective a
  have hT : IsScalarTower K K₁ Ω := IsScalarTower.of_algebraMap_eq' (by
    refine IsLocalization.ringHom_ext (nonZeroDivisors V) (RingHom.ext fun a => ?_)
    simp only [RingHom.comp_apply]
    rw [c₁, c₂, ← IsScalarTower.algebraMap_apply]
    rfl)
  have hK₁ : CharZero K₁ := charZero_of_injective_algebraMap (algebraMap K K₁).injective
  have hal : Algebra.IsAlgebraic K₁ Ω := Algebra.IsAlgebraic.tower_top (K := K) K₁
  have hac : IsAlgClosure K₁ Ω := ⟨inferInstance, hal⟩
  have hres₁ : Finite (IsLocalRing.ResidueField W) :=
    Module.finite_of_finite (IsLocalRing.ResidueField V)
  obtain ⟨P₁, φ, hφ⟩ := exists_pullback (spMap (algebraMap K K₁)) P
  refine GlobalTheory.SS.potModel_trans V K W K₁ (RingHom.ext fun a => (c₁ a).symm) hWf hWl P.A P₁.A φ hφ _ ?_
  refine GlobalTheory.T.potentialSemistable_of_rational_lTorsion W K₁ hres₁ l hl h3 (by simpa using hu.map (algebraMap V W)) P₁ ?_
  refine fixed_of_rational (IsAlgClosure.equiv K₁ Ω (AlgebraicClosure K₁)) hφ l (hs K₁ fun c hc => ?_)
  obtain ⟨a, ha, b, hb, hb0, h⟩ := hWs c hc
  refine ⟨algebraMap W K₁ ⟨a, ha⟩ / algebraMap W K₁ ⟨b, hb⟩, ?_⟩
  rw [map_div₀, c₂, c₂]
  exact (div_eq_iff hb0).2 h.symm

end GlobalTheory.SemiPol
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PrincipallyPolarizedAbelianVarietyPotentialSemiAStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principallyPolarizedAbelianVariety_potentialSemiAbelianModel : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K], Finite (IsLocalRing.ResidueField V) → ∀ P : Out.PolAV (Sp K), PotModel V K P.A (fun _ _ _ G _ => IsSemiAbelian G) := by
  first | exact @GlobalTheory.SemiPol.potModel_semiAbelian | exact GlobalTheory.SemiPol.potModel_semiAbelian | (intros; apply GlobalTheory.SemiPol.potModel_semiAbelian <;> assumption)
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem finiteDimensional_of_finite_of_isFractionRing (V K W L : Type) [CommRing V] [IsDomain V] [Field K]
    [Algebra V K] [IsFractionRing V K] [CommRing W] [IsDomain W] [Field L] [Algebra V W] [Algebra W L] [Algebra K L]
    [IsFractionRing W L] [Module.Finite V W]
    (e : (algebraMap W L).comp (algebraMap V W) = (algebraMap K L).comp (algebraMap V K)) :
    FiniteDimensional K L := by
  letI : Algebra V L := ((algebraMap W L).comp (algebraMap V W)).toAlgebra
  haveI : IsScalarTower V W L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower V K L := IsScalarTower.of_algebraMap_eq' e
  haveI : FaithfulSMul V W := by
    rw [faithfulSMul_iff_algebraMap_injective]
    have h : Function.Injective ((algebraMap W L).comp (algebraMap V W)) := by
      rw [e]; exact (algebraMap K L).injective.comp (IsFractionRing.injective V K)
    exact Function.Injective.of_comp (f := algebraMap W L) h
  exact Module.Finite.of_isLocalization V W (nonZeroDivisors V)

theorem exists_ringHom_integralClosure (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] (W L : Type) [CommRing W] [IsDomain W] [Field L]
    [Algebra (integralClosure ℤ_[p] K) W] [Algebra W L] [Algebra K L] [IsFractionRing W L]
    [Module.Finite (integralClosure ℤ_[p] K) W]
    (e : (algebraMap W L).comp (algebraMap (integralClosure ℤ_[p] K) W) =
      (algebraMap K L).comp (algebraMap (integralClosure ℤ_[p] K) K)) :
    ∃ (K' : IntermediateField ℚ_[p] (PadicAlgCl p)) (h : K ≤ K'), FiniteDimensional ℚ_[p] K' ∧
      ∃ (τ : L →+* K') (f : W →+* integralClosure ℤ_[p] K'),
        τ.comp (algebraMap K L) = (IntermediateField.inclusion h).toRingHom ∧
        τ.comp (algebraMap W L) = (algebraMap (integralClosure ℤ_[p] K') K').comp f := by
  haveI := finiteDimensional_of_finite_of_isFractionRing _ K W L e
  let σ : L →ₐ[K] PadicAlgCl p := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let K' : IntermediateField ℚ_[p] (PadicAlgCl p) := σ.fieldRange.restrictScalars ℚ_[p]
  have h : K ≤ K' := fun x hx => ⟨algebraMap K L ⟨x, hx⟩, σ.commutes _⟩
  let τ : L →+* K' := σ.toRingHom.codRestrict K' fun x => ⟨x, rfl⟩
  have hτ : τ.comp (algebraMap K L) = (IntermediateField.inclusion h).toRingHom :=
    RingHom.ext fun x => Subtype.ext (σ.commutes x)
  have hK' : FiniteDimensional ℚ_[p] K' := by
    letI : Algebra ℚ_[p] L := ((algebraMap K L).comp (algebraMap ℚ_[p] K)).toAlgebra
    haveI : IsScalarTower ℚ_[p] K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : Module.Finite ℚ_[p] L := Module.Finite.trans K L
    let τ' : L →ₐ[ℚ_[p]] K' := { τ with commutes' := fun x => Subtype.ext (σ.commutes (algebraMap ℚ_[p] K x)) }
    refine Module.Finite.of_surjective τ'.toLinearMap ?_
    rintro ⟨_, x, rfl⟩
    exact ⟨x, rfl⟩
  have hint : ∀ w : W, IsIntegral ℤ_[p] (τ (algebraMap W L w)) := fun w => by
    have h₁ : (algebraMap (integralClosure ℤ_[p] K) W).IsIntegralElem w := Algebra.IsIntegral.isIntegral w
    letI alg : Algebra (integralClosure ℤ_[p] K) K' :=
      ((IntermediateField.inclusion h).toRingHom.comp (algebraMap (integralClosure ℤ_[p] K) K)).toAlgebra
    haveI tower : IsScalarTower ℤ_[p] (integralClosure ℤ_[p] K) K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have h₂ := h₁.map (τ.comp (algebraMap W L))
    rw [RingHom.comp_assoc, e, ← RingHom.comp_assoc, hτ] at h₂
    change IsIntegral (integralClosure ℤ_[p] K) (τ (algebraMap W L w)) at h₂
    exact @isIntegral_trans _ _ _ _ _ _ alg _ _ tower _ _ h₂
  exact ⟨K', h, hK', τ, (τ.comp (algebraMap W L)).codRestrict _ hint, hτ, RingHom.ext fun _ => rfl⟩

theorem exists_semiAbelian_model_padic_polAV : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] (P : Out.PolAV (Sp K)), ∃ (K' : IntermediateField ℚ_[p] (PadicAlgCl p)) (h : K ≤ K'), FiniteDimensional ℚ_[p] K' ∧ ∃ (G : Over (Sp (integralClosure ℤ_[p] K'))) (_ : GrpObj G), IsSemiAbelian G ∧ ∃ φ : pullback G.hom (spMap (algebraMap (integralClosure ℤ_[p] K') K')) ⟶ P.A.left, IsGrpPullback ((Over.pullback (spMap (algebraMap (integralClosure ℤ_[p] K') K'))).obj G) P.A (spMap (IntermediateField.inclusion h).toRingHom) φ := by
  intro p _ K _ P
  haveI := GlobalTheory.DiscEval.isAdicComplete_integralClosure K
  obtain ⟨W, L, _, _, _, _, _, _, _, _, e, hfin, -, -, G, _, ⟨i, hi⟩, hG⟩ :=
    GlobalTheory.T.principallyPolarizedAbelianVariety_potentialSemiAbelianModel (integralClosure ℤ_[p] K) K (GlobalTheory.DiscEval.finite_residueField_integralClosure K) P
  obtain ⟨K', h, hK', τ, f, hτ, hf⟩ := exists_ringHom_integralClosure p K W L e
  refine ⟨K', h, hK', (Over.pullback (spMap f)).obj G, inferInstance, IsSemiAbelian.pullback _ G hG, ?_⟩
  exact GlobalTheory.SplitReduction.exists_isGrpPullback_of_square hf hτ G P.A
    (((isGrpPullback_of_iso i).comp (isGrpPullback_pullback P.A (spMap (algebraMap K L)))).congr
      (Category.id_comp _) rfl)

end GlobalTheory.SS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LinCombValueAct
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH
noncomputable section
namespace GlobalTheory.ZH.SecComb
open GlobalTheory.ZH.SecValue

theorem pull_liftFun {S : Scheme.{0}} {A T : Over S} [GrpObj A] (ψ : T ⊗ A ⟶ T ⊗ A) (hψ : ψ ≫ fst T A = fst T A)
    {U W : (T ⊗ A).left.Opens} (h : W ≤ ψ.left ⁻¹ᵁ U) (r : Γ(T.left, ⊤)) :
    ((T ⊗ A).left.presheaf.map (homOfLE h).op).hom ((ψ.left.app U).hom (liftFun A U r)) = liftFun A W r := by
  have e : ψ.left ≫ (fst T A).left = (fst T A).left := by rw [← Over.comp_left, hψ]
  have e₁ : ∀ V : (T ⊗ A).left.Opens, liftFun A V r = ((fst T A).left.appLE ⊤ V le_top).hom r := fun _ => rfl
  rw [e₁, e₁]
  refine (congrArg (fun q => q.hom r) (Scheme.Hom.appLE_comp_appLE ψ.left (fst T A).left ⊤ U W le_top h)).trans ?_
  simp only [e]

theorem ring_sum {B B' C I : Type} [CommRing B] [CommRing B'] [CommRing C] [Fintype I] (f' : B' →+* C) (f : B →+* C)
    (u : C) {c s : I → B} {c' s' : I → B'} {t : B} {t' : B'} (ht : t = ∑ l, c l * s l) (ht' : t' = ∑ l, c' l * s' l)
    (hc : ∀ l, f' (c' l) = f (c l)) (h : ∀ l, f' (s' l) = u * f (s l)) : f' t' = u * f t := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [ht, ht', map_sum, map_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [map_mul, map_mul, h, hc, mul_left_comm]

theorem isTwistPull_sum {S : Scheme.{0}} {A T : Over S} [GrpObj A] {L : LB A.left} (ψ : T ⊗ A ⟶ T ⊗ A)
    (hψ : ψ ≫ fst T A = fst T A) (m : T ⊗ A ⟶ A) (hm : ψ ≫ snd T A = m) (a b : ℤ) (α) {I : Type} [Fintype I]
    (c : I → Γ(T.left, ⊤)) {s : I → LB.Sec (LPow A L b T)} {s' : I → LB.Sec (LPow A L a T)}
    {t : LB.Sec (LPow A L b T)} {t' : LB.Sec (LPow A L a T)}
    (ht : ∀ j, t.f j = ∑ l, liftFun A _ (c l) * (s l).f j) (ht' : ∀ j, t'.f j = ∑ l, liftFun A _ (c l) * (s' l).f j)
    (h : ∀ l, IsTwistPull A L ψ m hm a b α (s l) (s' l)) : IsTwistPull A L ψ m hm a b α t t' := fun j =>
  ring_sum _ (RingHom.comp _ _) _ (ht _) (ht' _)
    (fun l => (res_liftHom A _ (c l)).trans (pull_liftFun ψ hψ (chart_le_pull A L ψ m hm j) (c l)).symm) fun l => h l j

section
variable {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}

theorem valM_zero (x) (e : FrAt x) : ValM (0 : SecM A.A A.L k (TFK (R := R) F)) x e 0 := fun z J hJ => by
  have h := ThetaAct.sv_add (0 : SecM A.A A.L k (TFK (R := R) F)) 0 (ptSecT A.A x).left z hJ
  rw [add_zero, left_eq_add] at h
  refine h.trans ?_
  simp only [id, CoefBasic.cst_eq, map_zero]
  exact (zero_mul (M₀ := (TFK (R := R) F).left.presheaf.stalk z) _).symm

theorem valM_sum {x} {e : FrAt x} {J : Type} (s : Finset J)
    {σ : J → SecM A.A A.L k (TFK (R := R) F)} {c : J → F} (h : ∀ l, ValM (σ l) x e (c l)) :
    ValM (∑ l ∈ s, σ l) x e (∑ l ∈ s, c l) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using valM_zero x e
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a).add ih

theorem exists_valAt (t : SecA A F k) {x} {e : FrAt x} (he : e.IsGen) : ∃ c, ValAt t x e c := by
  obtain ⟨w, hw⟩ := ThetaPtExist.exists_isValueAt A.isLB t x (powFrame A.A A.L x e k) (EvVal.powFrame_isGen A.A A.L x e he k)
  obtain ⟨c, rfl⟩ := kon_surj w
  refine ⟨c, fun z J hJ => ?_⟩
  have := ThetaPtMove.sv_of_isValueAt hw (𝟙 _) z hJ
  rw [Category.id_comp] at this
  exact this

end

theorem lin_comb_value_act : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), (∀ (t : SecA A F k) x (e : FrAt x), e.IsGen → ∃! a : F, ValAt t x e a) ∧ ∀ (I : Type) [Fintype I] (c : I → F) (s : I → SecA A F k), (∃ t, IsComb s c t) ∧ ∀ t, IsComb s c t → (∀ x (e : FrAt x) (a : I → F), (∀ i, ValAt (s i) x e (a i)) → ValAt t x e (∑ i, c i * a i)) ∧ ∀ (θ : ThetaGrp A.A A.L k (TFK (R := R) F)) (s' : I → SecA A F k) t', (∀ i, IsActOf A.A A.L k θ (s i) (s' i)) → IsComb s' c t' → IsActOf A.A A.L k θ t t' := by
  intro R _ _ A F _ _ k
  refine ⟨fun t x e he => ?_, fun I _ c s => ⟨?_, fun t ht => ⟨fun x e a ha => ?_, fun θ s' t' hs ht' => ?_⟩⟩⟩
  · obtain ⟨a, ha⟩ := exists_valAt t he
    exact ⟨a, ha, fun b hb => ValM.unique (σ := SecM.ofSec A.A t) hb ha⟩
  · exact ⟨SecM.toSec A.A (∑ l, kon R F (c l) • SecM.ofSec A.A (s l)), (isComb_iff _ _ _).2 rfl⟩
  · have h := valM_sum (Finset.univ : Finset I) fun l => ValM.smul (σ := SecM.ofSec A.A (s l)) (ha l) (c l)
    rw [← (isComb_iff _ _ _).1 ht] at h
    exact h
  · exact isTwistPull_sum _ (lift_fst _ _) _ _ _ _ _ (fun l => kon R F (c l)) ht ht' hs

end GlobalTheory.ZH.SecComb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemOrthogonalLabelsAreTorusPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemOrthogonalLabelsAreTorusPoints
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

noncomputable section
namespace GlobalTheory.TestFibre

theorem perp_torus_point : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), PtsOver u x → ∀ t : S.perp l.yy.ker, ∃ (τ : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ) (q : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)), q.y = 0 ∧ IsTor τ q.g ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) q (x t) ∧ ∀ a β, l.yy a = QuotientAddGroup.mk β → (τ (Multiplicative.ofAdd β) : PadicAlgCl p) = y₀ (algebraMap o S.R S.ζ) ^ (S.r * S.N * (eStd S.g _ (t : S.Gam) a).val) := by
  intro h h₂ hT o Ω _ _ _ _ S ρ p _ y₀ u l _ x hx t
  obtain ⟨x', h₁, hadd, -, hs⟩ := utest_torsion_points o Ω S ρ p y₀ u
  obtain rfl : x = x' := funext fun a => Over.OverMorphism.ext
    (u.cart.1.hom_ext ((hx a).trans (h₁ a).symm) (by rw [Over.w, Over.w]))
  obtain ⟨q, τ, a, b, c, d⟩ := PerpCharacter.exists_torus_point_eStd (laws_all h h₂).1 hT o Ω S ρ p y₀ u l x h₁ hadd hs
    t t.2
  exact ⟨τ, q, a, b, c, fun a β e => (d a β e).trans (by rw [map_pow, map_pow])⟩

end GlobalTheory.TestFibre
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemOrthogonalLabelsAreTorusPointsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSystem_orthogonal_labels_are_torus_points : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), PtsOver u x → ∀ t : S.perp l.yy.ker, ∃ (τ : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ) (q : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)), q.y = 0 ∧ IsTor τ q.g ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) q (x t) ∧ ∀ a β, l.yy a = QuotientAddGroup.mk β → (τ (Multiplicative.ofAdd β) : PadicAlgCl p) = y₀ (algebraMap o S.R S.ζ) ^ (S.r * S.N * (eStd S.g _ (t : S.Gam) a).val) := by
  first | exact @GlobalTheory.TestFibre.perp_torus_point | exact GlobalTheory.TestFibre.perp_torus_point | (intros; apply GlobalTheory.TestFibre.perp_torus_point <;> assumption)
end
end

module

public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAdmissibleIntegralBasisChangeOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRayFieldInRestrictScalars
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.Fld

theorem IsRayField.isRayFieldIn_restrictScalars {K : IntermediateField ℚ ℂ} [NumberField K]
    {M : IntermediateField K ℂ} [hM : NumberField M] {𝔮 : Ideal (𝓞 K)} (h : IsRayField K M 𝔮) :
    IsRayFieldIn (K.val : K →+* ℂ) 𝔮 (M.restrictScalars ℚ) := by
  have hmem : ∀ x : K, (K.val : K →+* ℂ) x ∈ M.restrictScalars ℚ := fun x => by
    rw [IntermediateField.mem_restrictScalars]
    exact M.algebraMap_mem x
  have : NumberField (M.restrictScalars ℚ) := hM
  refine ⟨hmem, inferInstance, ?_⟩
  letI := algOf (K.val : K →+* ℂ) (M.restrictScalars ℚ) hmem
  exact h.of_algEquiv
    { toFun := fun y => ⟨y.1, y.2⟩
      invFun := fun y => ⟨y.1, y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }

theorem adjoin_weberSet_one (K : Type) [Field K] [CharZero K] [Algebra K ℂ] (L : PeriodPair) :
    IntermediateField.adjoin K (FieldSize.weberSet L 1) = K⟮(latticeCurve L).j⟯ := by
  have hset : FieldSize.weberSet L 1 = {L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)} := by
    ext w
    simp only [FieldSize.weberSet, Nat.cast_one, div_one, Set.mem_insert_iff, Set.mem_ofPred_eq,
      Set.mem_singleton_iff]
    constructor
    · rintro (hw | ⟨z, hz, hz', -⟩)
      · exact hw
      · exact absurd hz hz'
    · exact fun hw => Or.inl hw
  have hΔ0 : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 ≠ 0 := by
    rw [← latticeCurve_Δ L]; exact latticeCurve_Δ_ne_zero L
  have hj : (latticeCurve L).j = 1728 * (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) := by
    rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ', latticeCurve_c₄,
      latticeCurve_Δ]
    field_simp
    ring
  have h1728 : ∀ S : IntermediateField K ℂ, (1728 : ℂ) ∈ S := fun S => by
    simp
  rw [hset, hj]
  set w := L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    have hw : (1728 : ℂ)⁻¹ * (1728 * w) = w := by field_simp
    have hm : (1728 : ℂ)⁻¹ * (1728 * w) ∈ K⟮1728 * w⟯ :=
      mul_mem (inv_mem (h1728 _)) (IntermediateField.mem_adjoin_simple_self K _)
    rwa [hw] at hm
  · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    exact mul_mem (h1728 _) (IntermediateField.mem_adjoin_simple_self K _)

theorem isRayFieldIn_hilbertField : WeberRayFieldSt → ∀ (d : ℕ) (F : IntermediateField ℚ ℂ) (A : WeierstrassCurve F),
    d.Prime → d % 4 = 3 → 3 < d → IsGoodCMCurve d F A → ∃ _ : NumberField ℚ⟮sqrtNegNat d⟯,
      discr ℚ⟮sqrtNegNat d⟯ = -(d : ℤ) ∧ Module.finrank ℚ ℚ⟮sqrtNegNat d⟯ = 2 ∧
        IsRayFieldIn (ℚ⟮sqrtNegNat d⟯.val : ℚ⟮sqrtNegNat d⟯ →+* ℂ) ⊤ (hilbertField d F) := by
  intro hW d F A hd h4 h3 hG
  set x := sqrtNegNat d with hxdef
  have hx : x ^ 2 = -(d : ℂ) := sqrtNegNat_sq d
  have hint : IsIntegral ℚ x := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℚ), Polynomial.monic_X_pow_add_C _ two_ne_zero, ?_⟩
    simp [hx]
  have : FiniteDimensional ℚ ℚ⟮x⟯ := IntermediateField.adjoin.finiteDimensional hint
  have hNF : NumberField ℚ⟮x⟯ := NumberField.mk
  obtain ⟨-, hfin, habs⟩ := isGalois_finrank_discr_adjoin_sqrt_neg_prime d x hd h4 hx
  have hd0 : 0 < d := hd.pos
  have hTC : IsTotallyComplex ℚ⟮x⟯ :=
    isTotallyComplex_of_sq_eq_neg hd0 (x := IntermediateField.AdjoinSimple.gen ℚ x)
      (Subtype.ext (by simpa using hx))
  have hdisc : discr ℚ⟮x⟯ = -(d : ℤ) := by
    have hnc : NumberField.InfinitePlace.nrComplexPlaces ℚ⟮x⟯ = 1 := by
      have := IsTotallyComplex.finrank (K := ℚ⟮x⟯)
      omega
    have hs := sign_discr (K := ℚ⟮x⟯)
    rw [hnc, pow_one] at hs
    have hneg : discr ℚ⟮x⟯ < 0 := Int.sign_eq_neg_one_iff_neg.1 hs
    have h := Int.natAbs_eq (discr ℚ⟮x⟯)
    rw [habs] at h
    omega
  have hG' := hG
  obtain ⟨-, -, L, hL, -, -, -⟩ := hG
  have hlat : ∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 ℚ⟮x⟯, algebraMap ℚ⟮x⟯ ℂ (a : ℚ⟮x⟯) = z := by
    intro z
    rw [hL z]
    constructor
    · rintro ⟨hz, hzi⟩
      have hi : IsIntegral ℤ (⟨z, hz⟩ : ℚ⟮x⟯) :=
        (isIntegral_algHom_iff ((ℚ⟮x⟯).val.toRingHom.toIntAlgHom) Subtype.val_injective).1 hzi
      exact ⟨⟨⟨z, hz⟩, hi⟩, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨(a : ℚ⟮x⟯).2,
        (RingOfIntegers.isIntegral_coe a).map ((ℚ⟮x⟯).val.toRingHom.toIntAlgHom)⟩
  have hdlt : discr ℚ⟮x⟯ < -4 := by rw [hdisc]; omega
  obtain ⟨_, hAb, hRay⟩ := hW ℚ⟮x⟯ hfin hdlt L hlat 1 one_pos
  have hone : Ideal.span {((1 : ℕ) : 𝓞 ℚ⟮x⟯)} = ⊤ := by simp
  rw [hone] at hRay
  have hRF : IsRayField ℚ⟮x⟯ (IntermediateField.adjoin ℚ⟮x⟯ (FieldSize.weberSet L 1)) ⊤ := ⟨hAb, hRay⟩
  refine ⟨hNF, hdisc, hfin, ?_⟩
  have hIn := hRF.isRayFieldIn_restrictScalars
  rw [adjoin_weberSet_one] at hIn
  have hEq : (ℚ⟮x⟯⟮(latticeCurve L).j⟯).restrictScalars ℚ = hilbertField d F := by
    rw [hilbertField_eq hG' hL]
    exact IntermediateField.adjoin_simple_adjoin_simple ℚ (latticeCurve L).j (α := x)
  rw [← hEq]
  exact hIn

end GlobalTheory.Mem.Fld
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionsGenerateIdealProjective
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionsGenerateIdealProjective
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.ProjBlowup

variable {R : Type} [CommRing R] {N : ℕ} {X : Scheme.{0}}

theorem exists_formOn_eq (a : Fin (N + 1)) (s : Γ(PSpace R N, chart R N a)) :
    ∃ (d : ℕ) (F : MvPolynomial (Fin (N + 1)) R) (hF : F.IsHomogeneous d),
      formOn (chart R N a) a le_rfl d F hF = s := by
  obtain ⟨p, rfl⟩ := (chartAlgEquiv R N a).surjective s
  obtain ⟨x, rfl⟩ := (polyEquivAway R N a).symm.surjective p
  obtain ⟨n, f, hf, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _ (X_mem R N a) x
  refine ⟨n, f, by simpa using hf, ?_⟩
  rw [← chartAlgEquiv_dehom, ← awayToPoly_mk R N a n f hf]
  rfl

def pullForm (φ : X ⟶ PSpace R N) (W : X.Opens) (i : Fin (N + 1)) (hi : W ≤ φ ⁻¹ᵁ chart R N i)
    (d : ℕ) (F : MvPolynomial (Fin (N + 1)) R) (hF : F.IsHomogeneous d) : Γ(X, W) :=
  (φ.appLE (chart R N i) W hi).hom (formOn (chart R N i) i le_rfl d F hF)

section

variable {φ : X ⟶ PSpace R N} {W V : X.Opens} {i j : Fin (N + 1)} {hi : W ≤ φ ⁻¹ᵁ chart R N i}
  {d : ℕ} {F : MvPolynomial (Fin (N + 1)) R}

theorem resG_pullForm (h : V ≤ W) (hF : F.IsHomogeneous d) :
    resG X h (pullForm φ W i hi d F hF) = pullForm φ V i (h.trans hi) d F hF :=
  resG_appLE φ hi h _

theorem pullForm_zero : pullForm φ W i hi d 0 (isHomogeneous_zero _ R d) = 0 := by
  rw [pullForm, formOn_zero, map_zero]

theorem pullForm_eq_pow_mul (hj : W ≤ φ ⁻¹ᵁ chart R N j) (hF : F.IsHomogeneous d) :
    pullForm φ W i hi d F hF = pullRatio φ W i hi j ^ d * pullForm φ W j hj d F hF := by
  have hW : W ≤ φ ⁻¹ᵁ (chart R N i ⊓ chart R N j) := le_inf hi hj
  have := congrArg (φ.appLE _ W hW).hom
    (formOn_eq_ratioOn_pow_mul (U := chart R N i ⊓ chart R N j) (hi := inf_le_left) inf_le_right hF)
  rw [map_mul, map_pow, appLE_ratioOn, ← resG_formOn (hi := le_rfl) inf_le_left,
    ← resG_formOn (hi := le_rfl) inf_le_right, appLE_resG, appLE_resG] at this
  exact this

theorem pullForm_X_pow_mul (n : ℕ) (hF : F.IsHomogeneous d) {e : ℕ}
    (hG : (MvPolynomial.X j ^ n * F).IsHomogeneous e) :
    pullForm φ W i hi e _ hG = pullRatio φ W i hi j ^ n * pullForm φ W i hi d F hF := by
  rw [pullForm, pullForm, pullRatio, formOn_eq_aeval, formOn_eq_aeval, map_mul, map_pow, aeval_X, map_mul,
    map_pow]

end

def pullO (φ : X ⟶ PSpace R N) (e : ℕ) : LB X where
  ι := Fin (N + 1)
  U i := φ ⁻¹ᵁ chart R N i
  g i j := (Units.mkOfMulEqOne (pullRatio φ _ i inf_le_left j) (pullRatio φ _ j inf_le_right i)
    (pullRatio_mul_pullRatio.trans pullRatio_self)) ^ e

def pullFormSec (φ : X ⟶ PSpace R N) {e : ℕ} (F : MvPolynomial (Fin (N + 1)) R) (hF : F.IsHomogeneous e) :
    (pullO φ e).Sec where
  f i := pullForm φ _ i le_rfl e F hF
  compat i j := by
    refine (resG_pullForm inf_le_left hF).trans ((pullForm_eq_pow_mul (j := j) inf_le_right hF).trans ?_)
    exact congrArg₂ (· * ·) (Units.val_pow_eq_pow_val (Units.mkOfMulEqOne _ _ _) e).symm
      (resG_pullForm inf_le_right hF).symm

abbrev affChart (φ : X ⟶ PSpace R N) [IsClosedImmersion φ] (i : Fin (N + 1)) : X.affineOpens :=
  ⟨φ ⁻¹ᵁ chart R N i, (isAffineOpen_chart R N i).preimage φ⟩

theorem exists_pow_mul_pullForm_mem (φ : X ⟶ PSpace R N) [IsClosedImmersion φ] (J : X.IdealSheafData)
    {a : Fin (N + 1)} {d : ℕ} {F : MvPolynomial (Fin (N + 1)) R} (hF : F.IsHomogeneous d)
    (h : pullForm φ _ a le_rfl d F hF ∈ J.ideal (affChart φ a)) (b : Fin (N + 1)) :
    ∃ n, pullRatio φ _ b le_rfl a ^ n * pullForm φ _ b le_rfl d F hF ∈ J.ideal (affChart φ b) := by
  let r : Γ(X, (affChart φ b).1) := pullRatio φ _ b le_rfl a
  have ha : X.basicOpen r ≤ φ ⁻¹ᵁ chart R N a := basicOpen_pullRatio.le.trans inf_le_right
  have h1 : resG X ha (pullForm φ _ a le_rfl d F hF) ∈ J.ideal (X.affineBasicOpen r) :=
    J.ideal_le_comap_ideal (U := X.affineBasicOpen r) (V := affChart φ a) ha h
  have h2 : resG X (X.basicOpen_le r) (pullForm φ _ b le_rfl d F hF) ∈ J.ideal (X.affineBasicOpen r) := by
    rw [resG_pullForm] at h1 ⊢
    rw [pullForm_eq_pow_mul (j := a) ha]
    exact Ideal.mul_mem_left _ _ h1
  rw [← J.map_ideal_basicOpen] at h2
  have inst := (affChart φ b).2.isLocalization_basicOpen r
  obtain ⟨_, ⟨n, rfl⟩, hn⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff (.powers r)
    Γ(X, X.basicOpen r) _ _).1 h2
  exact ⟨n, hn⟩

theorem exists_form_of_mem (φ : X ⟶ PSpace R N) [IsClosedImmersion φ] (J : X.IdealSheafData)
    (a : Fin (N + 1)) (g : Γ(X, (affChart φ a).1)) (hg : g ∈ J.ideal (affChart φ a)) :
    ∃ e₀, ∀ e, e₀ ≤ e → ∃ (F : MvPolynomial (Fin (N + 1)) R) (hF : F.IsHomogeneous e),
      pullForm φ _ a le_rfl e F hF = g ∧ ∀ b, pullForm φ _ b le_rfl e F hF ∈ J.ideal (affChart φ b) := by
  obtain ⟨s, rfl⟩ := φ.app_surjective _ (isAffineOpen_chart R N a) g
  obtain ⟨d, F, hF, rfl⟩ := exists_formOn_eq a s
  have e₁ : pullForm φ _ a le_rfl d F hF = (φ.app (chart R N a)).hom (formOn (chart R N a) a le_rfl d F hF) := by
    rw [pullForm, Scheme.Hom.app_eq_appLE]
  choose n hn using exists_pow_mul_pullForm_mem φ J hF (e₁ ▸ hg)
  refine ⟨Finset.univ.sup n + d, fun e he => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (le_of_add_le_right he)
  refine ⟨MvPolynomial.X a ^ k * F, (isHomogeneous_X_pow a k).mul hF, ?_, fun b => ?_⟩
  · rw [pullForm_X_pow_mul k hF, pullRatio_self, one_pow, one_mul]
    exact e₁
  · obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le'
      ((Finset.le_sup (f := n) (Finset.mem_univ b)).trans (Nat.le_of_add_le_add_right he))
    rw [pullForm_X_pow_mul _ hF, pow_add, mul_assoc]
    exact Ideal.mul_mem_left _ _ (hn b)

theorem exists_generates (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R)
    (hs : IsProjOver s) (J : X.IdealSheafData) :
    ∃ (L : LB X) (m : ℕ) (σ : Fin (m + 1) → L.Sec), Generates J σ := by
  classical
  obtain ⟨N, φ, _, -⟩ := hs
  have fg : ∀ a, (J.ideal (affChart φ a)).FG := fun a => by
    have : IsNoetherianRing Γ(PSpace R N, chart R N a) :=
      isNoetherianRing_of_ringEquiv _ (chartAlgEquiv R N a).toRingEquiv
    have : IsNoetherianRing Γ(X, (affChart φ a).1) :=
      isNoetherianRing_of_surjective _ _ _ (φ.app_surjective _ (isAffineOpen_chart R N a))
    exact IsNoetherian.noetherian _
  choose S hS using fg
  choose e₀ he₀ using fun p : Σ a, S a =>
    exists_form_of_mem φ J p.1 p.2.1 (hS p.1 ▸ Ideal.subset_span p.2.2)
  choose F hF hFa hFb using fun p => he₀ p (Finset.univ.sup e₀) (Finset.le_sup (Finset.mem_univ p))
  let q := (Fintype.equivFinOfCardEq (Fintype.card_option (α := Σ a, S a))).symm
  let τ : Option (Σ a, S a) → (pullO φ (Finset.univ.sup e₀)).Sec := fun o =>
    o.elim (pullFormSec φ 0 (isHomogeneous_zero _ R _)) fun p => pullFormSec φ (F p) (hF p)
  refine ⟨_, _, fun j => τ (q j), (isCoordFamily_pullRatio φ).cover, fun k V h => ?_⟩
  have key : J.ideal (affChart φ k) = Ideal.span (Set.range fun j => (τ (q j)).f k) := by
    refine le_antisymm ?_ (Ideal.span_le.2 ?_)
    · rw [← hS k]
      refine Ideal.span_mono fun g hg => ⟨q.symm (some ⟨k, g, hg⟩), ?_⟩
      simp only [q.apply_symm_apply]
      exact hFa ⟨k, g, hg⟩
    · rintro _ ⟨j, rfl⟩
      dsimp only
      cases q j with
      | none =>
        exact (congrArg (· ∈ J.ideal (affChart φ k)) (pullForm_zero (φ := φ) (hi := le_rfl))).mpr (zero_mem _)
      | some p => exact hFb p k
  rw [← J.map_ideal (V := affChart φ k) h, key]
  erw [Ideal.map_span, ← Set.range_comp]
  rfl

end GlobalTheory.ProjBlowup
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionsGenerateIdealProjectiveStatement
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.ProjBlowup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sections_generate_ideal_projective : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsProjOver s → ∀ J : X.IdealSheafData, ∃ (L : LB X) (m : ℕ) (σ : Fin (m + 1) → L.Sec), Generates J σ := by
  first | exact @GlobalTheory.ProjBlowup.exists_generates | exact GlobalTheory.ProjBlowup.exists_generates | (intros; apply GlobalTheory.ProjBlowup.exists_generates <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootsOfUnityMemRayClassFieldOfMultiple
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootsOfUnityMemRayClassFieldOfMultiple
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.RayZeta

variable {K M L : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Field L] [NumberField L]
  [Algebra K M] [Algebra K L] [Algebra M L] [IsScalarTower K M L]

private theorem eq_of_pow_eq_one_of_sub_mem_prime {R : Type} [CommRing R] [IsDomain R] (P : Ideal R)
    [P.IsPrime] (p : ℕ) (hp : (p : R) ∉ P) {x y : R} (hx : x ^ p = 1) (hy : y ^ p = 1)
    (hxy : x - y ∈ P) : x = y := by
  by_contra hne
  have hS : ∑ k ∈ Finset.range p, x ^ k * y ^ (p - 1 - k) = 0 := by
    have := geom_sum₂_mul x y p
    rw [hx, hy, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hne)
  have hmem : (p : R) * x ^ (p - 1) ∈ P := by
    have : (p : R) * x ^ (p - 1) = ∑ k ∈ Finset.range p, (x ^ (p - 1) - x ^ k * y ^ (p - 1 - k)) := by
      rw [Finset.sum_sub_distrib, hS, Finset.sum_const, Finset.card_range, nsmul_eq_mul, sub_zero]
    rw [this]
    refine Ideal.sum_mem _ fun k hk => ?_
    have hk' : k + (p - 1 - k) = p - 1 := by
      have := Finset.mem_range.mp hk; omega
    obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow x y (p - 1 - k)
    have : x ^ (p - 1) - x ^ k * y ^ (p - 1 - k) = x ^ k * ((x - y) * c) := by
      rw [← hc, mul_sub, ← pow_add, hk']
    rw [this]
    exact P.mul_mem_left _ (P.mul_mem_right _ hxy)
  rcases Ideal.IsPrime.mem_or_mem ‹_› hmem with h | h
  · exact hp h
  · have hx0 : x ∈ P := Ideal.IsPrime.mem_of_pow_mem ‹_› _ h
    have : (1 : R) ∈ P := by
      rw [← hx]
      rcases Nat.eq_zero_or_pos p with rfl | hp0
      · simp at hp
      · exact P.pow_mem_of_mem hx0 _ hp0
    exact Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one _).mpr this)

theorem _root_.GlobalTheory.Mem.RayZeta.root_mem_rayField : ∀ (K M L : Type) [Field K] [NumberField K]
    [Field M] [NumberField M] [Field L] [NumberField L]
    [Algebra K M] [Algebra K L] [Algebra M L] [IsScalarTower K M L] [IsGalois K L] (𝔮 : Ideal (𝓞 K))
    (p : ℕ), p ≠ 0 →
    𝔮 ≤ Ideal.span {(p : 𝓞 K)} → _root_.GlobalTheory.Mem.Fld.IsRayField K M 𝔮 →
    Subgroup.closure {σ : L ≃ₐ[K] L | ∃ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔮 ∧
      _root_.GlobalTheory.NT.IsFrob L v σ} = ⊤ →
    (∀ (I : Ideal (𝓞 K)) (α β : 𝓞 K), _root_.GlobalTheory.NT.RayPair 𝔮 α β → I * Ideal.span {β} = Ideal.span {α} →
      Ideal.absNorm I ≡ 1 [MOD p]) → ∀ ζ : L, ζ ^ p = 1 → ζ ∈ Set.range (algebraMap M L) := by
  intro K M L _ _ _ _ _ _ _ _ _ _ _ 𝔮 p hp hq hM hgen hnorm ζ hζ
  obtain ⟨hab, hunr, -, hray⟩ := hM
  haveI : IsGalois K M := hab.toIsGalois
  have hpow : ∀ a b : ℕ, a ≡ b [MOD p] → ζ ^ a = ζ ^ b := by
    intro a b h
    rw [← Nat.mod_add_div a p, ← Nat.mod_add_div b p, pow_add, pow_add, pow_mul, pow_mul, hζ,
      one_pow, one_pow, (h : a % p = b % p)]
  have hζint : IsIntegral ℤ ζ := IsIntegral.of_pow (Nat.pos_of_ne_zero hp) (hζ ▸ isIntegral_one)
  let z : 𝓞 L := ⟨ζ, hζint⟩
  have hz : z ^ p = 1 := by
    exact NumberField.RingOfIntegers.ext hζ
  have hfrob : ∀ (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K)), ¬ v.asIdeal ∣ 𝔮 →
      _root_.GlobalTheory.NT.IsFrob L v σ → σ ζ = ζ ^ Ideal.absNorm v.asIdeal := by
    intro σ v hv hF
    obtain ⟨P, hP, hlies, hx⟩ := hF
    have hpP : ((p : ℕ) : 𝓞 L) ∉ P := by
      intro hmem
      apply hv
      rw [Ideal.dvd_iff_le]
      refine hq.trans ?_
      rw [Ideal.span_le, Set.singleton_subset_iff, Ideal.over_def P v.asIdeal, Ideal.under,
        SetLike.mem_coe, Ideal.mem_comap, map_natCast]
      exact hmem
    have h1 : (σ • z) ^ p = 1 := by rw [← smul_pow', hz, smul_one]
    have := eq_of_pow_eq_one_of_sub_mem_prime P p hpP h1 (by rw [← pow_mul, mul_comm, pow_mul, hz, one_pow]) (hx z)
    exact congrArg (fun w : 𝓞 L => (w : L)) this
  let Q : (L ≃ₐ[K] L) → Prop := fun σ => ∃ I : Ideal (𝓞 K), I ≠ ⊥ ∧ IsCoprime I 𝔮 ∧
    (∀ χ : (M ≃ₐ[K] M) →* ℂˣ, _root_.GlobalTheory.NT.heckeIdeal M χ I =
      (χ (AlgEquiv.restrictNormalHom M σ) : ℂ)) ∧ σ ζ = ζ ^ Ideal.absNorm I
  have hmul : ∀ σ τ, Q σ → Q τ → Q (σ * τ) := by
    rintro σ τ ⟨I, hI0, hIq, hIχ, hIζ⟩ ⟨J, hJ0, hJq, hJχ, hJζ⟩
    refine ⟨I * J, fun h => (Ideal.mul_eq_bot.mp h).elim hI0 hJ0, hIq.mul_left hJq, fun χ => ?_, ?_⟩
    · rw [_root_.GlobalTheory.NT.Model.heckeIdeal_mul M χ hI0 hJ0, hIχ, hJχ, map_mul, map_mul, Units.val_mul]
    · rw [AlgEquiv.mul_apply, hJζ, map_pow, hIζ, ← pow_mul, map_mul]
  have hone : Q 1 := by
    refine ⟨1, by rw [Ideal.one_eq_top]; exact top_ne_bot, isCoprime_one_left, fun χ => ?_, ?_⟩
    · rw [_root_.GlobalTheory.NT.Model.heckeIdeal_top, map_one, map_one, Units.val_one]
    · rw [map_one, pow_one, AlgEquiv.one_apply]
  have hgenQ : ∀ σ ∈ {σ : L ≃ₐ[K] L | ∃ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔮 ∧
      _root_.GlobalTheory.NT.IsFrob L v σ}, Q σ := by
    rintro σ ⟨v, hv, hF⟩
    refine ⟨v.asIdeal, v.ne_bot, ?_, fun χ => ?_, hfrob σ v hv hF⟩
    · rw [Ideal.isCoprime_iff_sup_eq]
      by_contra hne
      apply hv
      rw [Ideal.dvd_iff_le]
      have := v.isMaximal.eq_of_le hne le_sup_left
      rw [this]
      exact le_sup_right
    · rw [_root_.GlobalTheory.NT.Model.heckeIdeal_prime,
        _root_.GlobalTheory.NT.heckeVal_of_unramIn M χ (hunr v hv)
          (_root_.GlobalTheory.RayMaximal.isFrob_restrictNormal (L := M) hF)]
      rfl
  have hall : ∀ σ, Q σ := by
    intro σ
    have hσ : σ ∈ Subgroup.closure {σ : L ≃ₐ[K] L | ∃ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔮 ∧
      _root_.GlobalTheory.NT.IsFrob L v σ} := hgen ▸ Subgroup.mem_top σ
    induction hσ using Subgroup.closure_induction with
    | mem σ hσ => exact hgenQ σ hσ
    | one => exact hone
    | mul σ τ _ _ hσ hτ => exact hmul σ τ hσ hτ
    | inv σ _ hσ =>
      have hpowQ : ∀ n : ℕ, Q (σ ^ n) := by
        intro n
        induction n with
        | zero => simpa using hone
        | succ n ih => rw [pow_succ]; exact hmul _ _ ih hσ
      have : σ⁻¹ = σ ^ (orderOf σ - 1) := by
        refine (eq_inv_of_mul_eq_one_left ?_).symm
        rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos σ), pow_orderOf_eq_one]
      rw [this]
      exact hpowQ _
  haveI := IsGalois.tower_top_of_isGalois K M L
  rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
  intro τ
  obtain ⟨I, hI0, hIq, hIχ, hIζ⟩ := hall (τ.restrictScalars K)
  have hres : AlgEquiv.restrictNormalHom M (τ.restrictScalars K) = 1 := by
    ext m
    apply (algebraMap M L).injective
    show algebraMap M L ((τ.restrictScalars K).restrictNormal M m) = _
    rw [AlgEquiv.restrictNormal_commutes]
    simp
  obtain ⟨α, β, hαβ, hI⟩ := (hray I hI0 hIq).mp fun χ => by
    rw [hIχ, hres, map_one, Units.val_one]
  have := hpow _ _ (hnorm I α β hαβ hI)
  rw [pow_one] at this
  exact hIζ.trans this

end GlobalTheory.Mem.RayZeta

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootsOfUnityMemRayClassFieldOfMultipleStatement
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rootsOfUnity_mem_rayClassField_of_multiple : ∀ (K M L : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Field L] [NumberField L] [Algebra K M] [Algebra K L] [Algebra M L] [IsScalarTower K M L] [IsGalois K L] (𝔮 : Ideal (𝓞 K)) (p : ℕ), p ≠ 0 → 𝔮 ≤ Ideal.span {(p : 𝓞 K)} → IsRayField K M 𝔮 → Subgroup.closure {σ : L ≃ₐ[K] L | ∃ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔮 ∧ IsFrob L v σ} = ⊤ → (∀ (I : Ideal (𝓞 K)) (α β : 𝓞 K), RayPair 𝔮 α β → I * Ideal.span {β} = Ideal.span {α} → Ideal.absNorm I ≡ 1 [MOD p]) → ∀ ζ : L, ζ ^ p = 1 → ζ ∈ Set.range (algebraMap M L) := by
  first | exact @GlobalTheory.Mem.RayZeta.root_mem_rayField | exact GlobalTheory.Mem.RayZeta.root_mem_rayField | (intros; apply GlobalTheory.Mem.RayZeta.root_mem_rayField <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTorsionParamLattice
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.TorsionDegree

theorem exists_torsion_param_lattice (L : PeriodPair) (n : ℕ) [NeZero n] :
    ∃ t : (Fin 2 → ZMod n) →+ (latticeCurve L).toAffine.Point, Function.Injective t ∧
      ∀ P, n • P = 0 → ∃ v, t v = P := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  let f : ℂ → ℤ →+ (latticeCurve L).toAffine.Point := fun ω =>
    (latticePointHom L).comp (zmultiplesHom ℂ (ω / n))
  have hf : ∀ ω (a : ℤ), f ω a = latticePoint L (a * (ω / n)) := fun ω a => by
    simp [f]
  have h0 : ∀ ω ∈ L.lattice, f ω n = 0 := fun ω hω => by
    rw [hf, latticePoint_eq_zero_iff]
    convert hω using 1
    push_cast
    field_simp
  let t : (Fin 2 → ZMod n) →+ (latticeCurve L).toAffine.Point :=
    (ZMod.lift n ⟨f L.ω₁, h0 _ L.ω₁_mem_lattice⟩).comp (Pi.evalAddMonoidHom (fun _ => ZMod n) 0) +
    (ZMod.lift n ⟨f L.ω₂, h0 _ L.ω₂_mem_lattice⟩).comp (Pi.evalAddMonoidHom (fun _ => ZMod n) 1)
  have ht : ∀ a b : ℤ, t ![(a : ZMod n), (b : ZMod n)] = latticePoint L ((a * L.ω₁ + b * L.ω₂) / n) := by
    intro a b
    simp only [t, AddMonoidHom.add_apply, AddMonoidHom.comp_apply, Pi.evalAddMonoidHom_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, ZMod.lift_coe, hf]
    rw [← latticePoint_add]
    congr 1
    ring
  refine ⟨t, (injective_iff_map_eq_zero t).2 fun v hv => ?_, fun P hP => ?_⟩
  · obtain ⟨a, ha⟩ := ZMod.intCast_surjective (v 0)
    obtain ⟨b, hb⟩ := ZMod.intCast_surjective (v 1)
    have e : v = ![(a : ZMod n), (b : ZMod n)] := by
      ext i; fin_cases i <;> simp [ha, hb]
    rw [e, ht, latticePoint_eq_zero_iff, PeriodPair.mem_lattice] at hv
    obtain ⟨c, d, hcd⟩ := hv
    have h1 : ((a - n * c : ℤ) : ℝ) • L.ω₁ + ((b - n * d : ℤ) : ℝ) • L.ω₂ = 0 := by
      rw [eq_div_iff hn'] at hcd
      simp only [Complex.real_smul]
      push_cast
      linear_combination -hcd
    obtain ⟨h2, h3⟩ := LinearIndependent.pair_iff.1 L.indep _ _ h1
    have h2' : a = n * c := by
      have : a - n * c = 0 := by exact_mod_cast h2
      omega
    have h3' : b = n * d := by
      have : b - n * d = 0 := by exact_mod_cast h3
      omega
    rw [e, h2', h3']
    ext i; fin_cases i <;> simp
  · obtain ⟨z, rfl⟩ := latticePoint_surjective L P
    have h1 : latticePoint L (n • z) = 0 := by
      rw [← latticePointHom_apply, map_nsmul, latticePointHom_apply]; exact hP
    rw [latticePoint_eq_zero_iff] at h1
    obtain ⟨a, b, hab⟩ := PeriodPair.mem_lattice.1 h1
    refine ⟨_, (ht a b).trans ?_⟩
    rw [hab, nsmul_eq_mul, mul_div_cancel_left₀ _ hn']

theorem exists_torsion_param (W : WeierstrassCurve ℂ) [W.IsElliptic] (n : ℕ) [NeZero n] :
    ∃ t : (Fin 2 → ZMod n) →+ W.toAffine.Point, Function.Injective t ∧
      ∀ P, n • P = 0 → ∃ v, t v = P := by
  obtain ⟨L, C, hC⟩ := exists_variableChange_eq_latticeCurve W
  let e := variableChangePointEquiv C hC
  obtain ⟨t, hi, hs⟩ := exists_torsion_param_lattice L n
  refine ⟨e.toAddMonoidHom.comp t, e.injective.comp hi, fun P hP => ?_⟩
  obtain ⟨v, hv⟩ := hs (e.symm P) (by rw [← map_nsmul, hP, map_zero])
  exact ⟨v, by simp [hv]⟩

theorem exists_linearEquiv {G G' : Type} [AddCommGroup G] [AddCommGroup G'] (n : ℕ) [NeZero n]
    (t : (Fin 2 → ZMod n) →+ G') (hi : Function.Injective t) (hs : ∀ P, n • P = 0 → ∃ v, t v = P)
    (ι φ : G →+ G') (hι : Function.Injective ι) (hφ : Function.Injective φ)
    (hr : ∀ P, n • P = 0 → ∃ Q, ι Q = P) :
    ∃ g : (Fin 2 → ZMod n) ≃ₗ[ZMod n] (Fin 2 → ZMod n), ∀ v Q, ι Q = t v → φ Q = t (g v) := by
  have hv : ∀ v : Fin 2 → ZMod n, n • v = 0 := fun v => by
    ext i; simp
  have h1 : ∀ v, ∃ Q, ι Q = t v := fun v => hr _ (by rw [← map_nsmul, hv, map_zero])
  choose s hs' using h1
  have h2 : ∀ v, ∃ w, t w = φ (s v) := fun v => hs _ (by
    have : n • s v = 0 := hι (by rw [map_nsmul, hs', ← map_nsmul, hv, map_zero, map_zero])
    rw [← map_nsmul, this, map_zero])
  choose u hu using h2
  have hadd : ∀ v w, u (v + w) = u v + u w := fun v w => hi (by
    rw [map_add (f := _), hu, hu, hu, ← map_add (f := _)]
    congr 1
    exact hι (by rw [map_add (f := _), hs', hs', hs', map_add (f := _)]))
  let U := (AddMonoidHom.mk' u hadd).toZModLinearMap n
  have hU : Function.Injective U := fun v w h => hi (by
    have h' : u v = u w := h
    rw [← hs', ← hs', hφ ((hu v).symm.trans (h' ▸ hu w))])
  refine ⟨LinearEquiv.ofBijective U ⟨hU, Finite.surjective_of_injective hU⟩, fun v Q hQ => ?_⟩
  rw [hι (hQ.trans (hs' v).symm), ← hu]
  rfl

theorem card_linearEquiv (n : ℕ) :
    Nat.card ((Fin 2 → ZMod n) ≃ₗ[ZMod n] (Fin 2 → ZMod n)) = Nat.card (GL (Fin 2) (ZMod n)) :=
  Nat.card_congr (Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _)).symm.toEquiv

theorem finrank_adjoin_le {k : Type} [Field k] [CharZero k] [Algebra k ℂ] (A : WeierstrassCurve k) [A.IsElliptic]
    (n : ℕ) [NeZero n] [FiniteDimensional k (IntermediateField.adjoin k (torsionCoords (A.baseChange ℂ) n))] :
    Module.finrank k (IntermediateField.adjoin k (torsionCoords (A.baseChange ℂ) n)) ≤
      Nat.card (GL (Fin 2) (ZMod n)) := by
  classical
  set S := torsionCoords (A.baseChange ℂ) n with hS
  set M := IntermediateField.adjoin k S with hM
  have : (A.baseChange ℂ).IsElliptic := inferInstanceAs (A.map _).IsElliptic
  obtain ⟨t, hi, hs⟩ := exists_torsion_param (A.baseChange ℂ) n
  let m : (M →ₐ[k] ℂ) → (A.baseChange M).toAffine.Point →+ (A.baseChange ℂ).toAffine.Point :=
    fun φ => WeierstrassCurve.Affine.Point.map (W' := A.toAffine) φ
  have hm : ∀ φ, Function.Injective (m φ) := fun φ => WeierstrassCurve.Affine.Point.map_injective φ
  have hpt : ∀ (x y : ℂ) (h : (A.baseChange ℂ).toAffine.Nonsingular x y) (hx : x ∈ M) (hy : y ∈ M),
      (A.baseChange M).toAffine.Nonsingular ⟨x, hx⟩ ⟨y, hy⟩ := fun x y h hx hy =>
    (A.toAffine.baseChange_nonsingular (f := M.val) M.val.injective ⟨x, hx⟩ ⟨y, hy⟩).mp h
  have hr : ∀ P, n • P = 0 → ∃ Q, m M.val Q = P := by
    rintro (_ | ⟨x, y, h⟩) hP
    · exact ⟨0, rfl⟩
    · exact ⟨.some _ _ (hpt x y h (IntermediateField.subset_adjoin k S ⟨x, y, h, hP, Or.inl rfl⟩)
        (IntermediateField.subset_adjoin k S ⟨x, y, h, hP, Or.inr rfl⟩)), rfl⟩
  choose g hg using fun φ => exists_linearEquiv n t hi hs (m M.val) (m φ) (hm _) (hm φ) hr
  have hginj : Function.Injective g := by
    intro φ ψ h
    refine IntermediateField.algHom_ext_of_eq_adjoin k hM ?_
    rintro z ⟨x, y, hxy, h0, hz⟩
    obtain ⟨v, hv⟩ := hs _ h0
    have hx := IntermediateField.subset_adjoin k S ⟨x, y, hxy, h0, Or.inl rfl⟩
    have hy := IntermediateField.subset_adjoin k S ⟨x, y, hxy, h0, Or.inr rfl⟩
    have e : m φ (.some _ _ (hpt x y hxy hx hy)) = m ψ (.some _ _ (hpt x y hxy hx hy)) := by
      rw [hg φ v _ hv.symm, hg ψ v _ hv.symm, h]
    have e' := WeierstrassCurve.Affine.Point.some.inj e
    rcases hz with rfl | rfl
    · exact e'.1
    · exact e'.2
  rw [← card_linearEquiv, ← AlgHom.card k M ℂ, ← Nat.card_eq_fintype_card]
  have : Finite ((Fin 2 → ZMod n) ≃ₗ[ZMod n] (Fin 2 → ZMod n)) :=
    Finite.of_injective _ (DFunLike.coe_injective (F := (Fin 2 → ZMod n) ≃ₗ[ZMod n] (Fin 2 → ZMod n)))
  exact Nat.card_le_card_of_injective g hginj

theorem finrank_sup_adjoin {K L : Type} [Field K] [Field L] [Algebra K L] (H : IntermediateField K L) (S : Set L)
    [FiniteDimensional K H] [FiniteDimensional H (IntermediateField.adjoin H S)] :
    FiniteDimensional K (H ⊔ IntermediateField.adjoin K S : IntermediateField K L) ∧
      Module.finrank K (H ⊔ IntermediateField.adjoin K S : IntermediateField K L) =
        Module.finrank K H * Module.finrank H (IntermediateField.adjoin H S) := by
  rw [← IntermediateField.restrictScalars_adjoin_eq_sup]
  have : IsScalarTower K H (IntermediateField.adjoin H S) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Free H (IntermediateField.adjoin H S) := Module.Free.of_divisionRing _ _
  have : Module.Free K H := Module.Free.of_divisionRing _ _
  have h : FiniteDimensional K (IntermediateField.adjoin H S) := Module.Finite.trans H _
  exact ⟨h,
    (Module.finrank_mul_finrank K H (IntermediateField.adjoin H S)).symm⟩

theorem finrank_torsionField_le : ∀ (d : ℕ) (F : IntermediateField ℚ ℂ) [FiniteDimensional ℚ F] (A : WeierstrassCurve F) [A.IsElliptic], FiniteDimensional ℚ (torsionField d A) ∧ Module.finrank ℚ (torsionField d A) ≤ Module.finrank ℚ (hilbertField d F) * Nat.card (GL (Fin 2) (ZMod 12)) := by
  intro d F _ A _
  have hint : IsIntegral ℚ (sqrtNegNat d) :=
    IsIntegral.of_pow (n := 2) (by norm_num) (by
      rw [sqrtNegNat_sq]
      exact (isIntegral_natCast d).neg)
  have : FiniteDimensional ℚ ℚ⟮sqrtNegNat d⟯ := IntermediateField.adjoin.finiteDimensional hint
  have hH : FiniteDimensional ℚ (hilbertField d F) := by
    unfold hilbertField; infer_instance
  set H := hilbertField d F with hHdef
  let A' : WeierstrassCurve H := A.map (IntermediateField.inclusion (le_sup_right : F ≤ H)).toRingHom
  have hA : A'.baseChange ℂ = A.baseChange ℂ := by
    simp only [A', WeierstrassCurve.baseChange, WeierstrassCurve.map_map]
    rfl
  have : (A.baseChange ℂ).IsElliptic := inferInstanceAs (A.map _).IsElliptic
  have : A'.IsElliptic := by
    simp only [A']
    exact WeierstrassCurve.instIsEllipticMap _ _
  have hfin := finite_torsionCoords (A.baseChange ℂ) 12 (by norm_num)
  have halg := FieldsEx.isAlgebraic_of_torsionCoords_finite F A 12 hfin
  have : Finite (torsionCoords (A'.baseChange ℂ) 12) := hA ▸ hfin.to_subtype
  have hM : FiniteDimensional H (IntermediateField.adjoin H (torsionCoords (A'.baseChange ℂ) 12)) :=
    IntermediateField.finiteDimensional_adjoin fun z hz => (halg z (hA ▸ hz)).isIntegral.tower_top
  have hle := finrank_adjoin_le A' 12
  obtain ⟨h1, h2⟩ := finrank_sup_adjoin H (torsionCoords (A'.baseChange ℂ) 12)
  have e : torsionField d A = H ⊔ IntermediateField.adjoin ℚ (torsionCoords (A'.baseChange ℂ) 12) := by
    rw [hA]
    rfl
  rw [e]
  exact ⟨h1, h2.le.trans (Nat.mul_le_mul_left _ hle)⟩

end GlobalTheory.Mem.TorsionDegree
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormOneDetEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormOneDetEqOne
namespace GlobalTheory.Mem.Col2.IdxEx

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

theorem apply_single_of_mem_unip {F : Type} [Field F] {n c : ℕ} {r : (Fin (n + c) → F) ≃ₗ[F] (Fin (n + c) → F)}
    (hr : r ∈ Loc.N1 F n c) (s l : Fin (n + c)) (hl : s ≤ l) :
    r (Pi.single s 1) l = (Pi.single s 1 : Fin (n + c) → F) l := by
  obtain ⟨h1, h2⟩ := hr
  by_cases hs : s.1 < n
  · have e : (Pi.single s 1 : Fin (n + c) → F) = Loc.inX F n c (Pi.single ⟨s.1, hs⟩ 1) := by
      funext m
      by_cases hm : m.1 < n
      · simp [Loc.inX, hm, Pi.single_apply, Fin.ext_iff]
      · have : m ≠ s := fun h => hm (h ▸ hs)
        simp [Loc.inX, hm, this]
    rw [e, h2]
  · have e : (Pi.single s 1 : Fin (n + c) → F) = Loc.eN F (n + c) (n + (s.1 - n)) := by
      funext m
      have : n + (s.1 - n) = s.1 := by omega
      simp [Loc.eN, this, Pi.single_apply, Fin.ext_iff]
    have h3 := h1.1.2.2 (s.1 - n) l (by
      have : s.1 ≤ l.1 := hl
      simp only [Set.mem_setOf_eq]
      omega)
    rw [e]
    exact sub_eq_zero.1 h3

theorem det_eq_one_of_mem_unip :
    ∀ (F : Type) [Field F] (n c : ℕ), ∀ r ∈ Loc.N1 F n c, LinearEquiv.det r = 1 := by
  intro F _ n c r hr
  apply Units.ext
  rw [LinearEquiv.coe_det, ← LinearMap.det_toMatrix', Matrix.det_of_upperTriangular]
  · refine Finset.prod_eq_one fun s _ => ?_
    have := apply_single_of_mem_unip hr s s le_rfl
    rw [LinearMap.toMatrix'_apply]
    simpa using this
  · intro l s hls
    have hls' : s < l := hls
    have := apply_single_of_mem_unip hr s l hls'.le
    rw [LinearMap.toMatrix'_apply]
    simpa [hls'.ne'] using this

end GlobalTheory.Mem.Col2.IdxEx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormOneDetEqOneStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_one_det_eq_one : ∀ (F : Type) [Field F] (n c : ℕ), ∀ r ∈ Loc.N1 F n c, LinearEquiv.det r = 1 := by
  first | exact @GlobalTheory.Mem.Col2.IdxEx.det_eq_one_of_mem_unip | exact GlobalTheory.Mem.Col2.IdxEx.det_eq_one_of_mem_unip | (intros; apply GlobalTheory.Mem.Col2.IdxEx.det_eq_one_of_mem_unip <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelStepZeroAtTwistPrimeFull
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelStepZeroAtTwistPrimeFull
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

namespace GlobalTheory.Mem.Col2.IdxExZeroQ

section Loc

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

theorem parL_self (q kj n c : ℕ) (h : n ≤ kj) : LocE.parL P q kj n c = stdAt E (n + c) P := by
  ext x
  unfold LocE.parL
  rw [GlobalTheory.CongLevel.mem_sclLat, GlobalTheory.GO.ChRoot.mem_stdAt']
  refine forall_congr' fun l => ?_
  rw [if_neg (by omega)]
  simp

theorem lamY_zero (q n c : ℕ) : LocE.lamY P q n c 0 = stdAt E (n + c) P :=
  Submodule.ext fun _ => GlobalTheory.GO.ChRoot.mem_lamY_zero

omit [StarRing E] in
theorem lamQB_empty {K : Type} [Field K] (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (kj n : ℕ) (hn : n ≤ kj) {N : ℕ}
    (h : HomE E N N) : LocE.lamQB ξ kj n h = 1 := by
  unfold LocE.lamQB
  haveI : IsEmpty (Fin (n - kj)) := ⟨fun i => by have := i.2; omega⟩
  have h1 : redP P (1 : E) = 1 := by simpa using reduction_coe P 1
  rw [Matrix.det_isEmpty]
  unfold LocE.unitV
  rw [dite_eq_left (by rw [h1]; exact isUnit_one)]
  have : ∀ hu : IsUnit (redP P (1 : E)), hu.unit = 1 := fun hu => Units.ext (by simp [h1])
  rw [this, map_one]
  simp

end Loc

theorem zero_level : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs → cst.Ok → GrpQ (R := R) sel mu cst 0 P 1 ⟨⊤, 1⟩ ∧ ChrQ Ch sel mu cst 0 P 1 ⟨⊤, 1⟩ := by
  intro X Pr R Ch sel S mu cst P hP hc
  have hN : R.N 0 ≤ R.k + 0 := by rw [Ranks.N_zero]; omega
  have hJ : Jat (Pr := Pr) (R := R) cst.sharp 0 P.1 = stabL X.E _ (stdAt X.E (R.N 0 + cOf R 0) P.1) := by
    unfold Jat
    rw [if_neg hP]
    unfold LocE.JQ
    rw [parL_self _ _ _ _ hN, inf_idem]
  have e : ∀ r : AutY X R 0, (MulAut.conj (1 : AutY X R 0)⁻¹).toMonoidHom r = r := by
    intro r
    simp
  constructor
  · unfold GrpQ
    symm
    rw [eq_top_iff]
    intro g _
    rw [Subgroup.mem_subgroupOf]
    refine ⟨GlobalTheory.CongLevel.extE _ g.1, ⟨GlobalTheory.CongLevel.extendByIdOnLastCoordsLinearEquiv_mem_firstRowGroup _ g.1, ?_⟩, GlobalTheory.CongLevel.extE_inX _ g.1⟩
    show (MulAut.conj (1 : AutY X R 0)⁻¹).toMonoidHom (GlobalTheory.CongLevel.extE (cOf R 0) g.1) ∈ Jat (Pr := Pr) cst.sharp 0 P.1
    rw [e, hJ, ← lamY_zero (qOf P.1)]
    exact GlobalTheory.CongLevel.extE_stab _ _ _ _ _ g.2
  · intro g r hr _
    have h2 : (MulAut.conj (1 : AutY X R 0)⁻¹).toMonoidHom r ∈ Jat (Pr := Pr) cst.sharp 0 P.1 := hr.2
    rw [e, hJ] at h2
    have hint : IntAt P.1 (1 * Loc.n1Arg r) :=
      GlobalTheory.GO.ChRoot.intAt_n1Arg 1 r fun x hx => by rw [one_smul]; exact (h2 x).2 hx
    rw [one_mul] at hint
    unfold chiInv lamRow
    rw [if_neg hP, hc.psi_int P _ hint, lamQB_empty _ _ _ hN]
    simp

end GlobalTheory.Mem.Col2.IdxExZeroQ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelStepZeroAtTwistPrimeFullStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_stepZero_at_twistPrime_full : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs → cst.Ok → GrpQ (R := R) sel mu cst 0 P 1 ⟨⊤, 1⟩ ∧ ChrQ Ch sel mu cst 0 P 1 ⟨⊤, 1⟩ := by
  first | exact @GlobalTheory.Mem.Col2.IdxExZeroQ.zero_level | exact GlobalTheory.Mem.Col2.IdxExZeroQ.zero_level | (intros; apply GlobalTheory.Mem.Col2.IdxExZeroQ.zero_level <;> assumption)
end
end

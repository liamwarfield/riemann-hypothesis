module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenDomainWeightBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeLevelCharacterBound
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CountingVolumeLeSelfIntersectionNefHermitianBund
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFacts
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdempotentTransfer.NormAtAddLe

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyCoordinateCombinationsNoCommonZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyCoordinateCombinationsNoCommonZero
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.TrueGeo

namespace GlobalTheory.FubiniStudyFrame

theorem exists_ne_zero_of_rel {K V : Type} [Field K] [AddCommGroup V] [Module K V] {n N : ℕ}
    (σ : K →+* ℂ) (u : Fin n → V) (b : Module.Basis (Fin N) K V) (c : Matrix (Fin n) (Fin N) K)
    (A : Matrix (Fin N) (Fin N) ℂ) (w : Fin n → ℂ) (hw : w ≠ 0)
    (hrel : ∀ lam : Fin n → K, ∑ k, lam k • u k = 0 → ∑ k, σ (lam k) * w k = 0)
    (hb : ∀ j, b j = ∑ k, c k j • u k) (hA : A.det ≠ 0) :
    ∃ a, ∑ k, (c.map σ * A) k a * w k ≠ 0 := by
  classical
  have hx : Matrix.vecMul w (c.map σ) ≠ 0 := by
    intro hx
    apply hw
    funext l
    set r := b.repr (u l)
    have hl : ∑ k, ((Pi.single l (1 : K) : Fin n → K) k - ∑ j, c k j * r j) • u k = 0 := by
      have e : ∑ k, (∑ j, c k j * r j) • u k = u l := by
        calc ∑ k, (∑ j, c k j * r j) • u k = ∑ j, r j • ∑ k, c k j • u k := by
              simp only [Finset.sum_smul, Finset.smul_sum, smul_smul]
              rw [Finset.sum_comm]
              exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]
          _ = ∑ j, r j • b j := by simp only [hb]
          _ = u l := b.sum_repr (u l)
      simp only [sub_smul, Finset.sum_sub_distrib, e, Pi.single_apply, ite_smul, one_smul,
        zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self]
    have h2 := hrel _ hl
    have h3 : ∀ j, ∑ k, w k * σ (c k j) = 0 := fun j => by
      have := congrFun hx j
      simpa [Matrix.vecMul, dotProduct] using this
    have h4 : ∑ k, σ ((Pi.single l (1 : K) : Fin n → K) k - ∑ j, c k j * r j) * w k =
        w l - ∑ j, σ (r j) * ∑ k, w k * σ (c k j) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sub, map_sum, map_mul, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum,
        Finset.sum_mul]
      congr 1
      · rw [Finset.sum_eq_single l]
        · simp
        · intro k _ hk; simp [Pi.single_apply, hk]
        · simp
      · rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [h4] at h2
    simpa [h3] using h2
  by_contra hne
  push_neg at hne
  have h0 : Matrix.vecMul (Matrix.vecMul w (c.map σ)) A = 0 := by
    rw [Matrix.vecMul_vecMul]
    funext a
    have := hne a
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  exact hA (Matrix.exists_vecMul_eq_zero_iff.1 ⟨_, hx, h0⟩)

theorem rel_field_of_rel_int {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {n : ℕ} (τ : 𝓞 K →+* ℂ) (u : Fin n → V)
    (w : Fin n → ℂ)
    (H : ∀ lam : Fin n → 𝓞 K, ∑ k, lam k • u k = 0 → ∑ k, τ (lam k) * w k = 0)
    (lam : Fin n → K) (h : ∑ k, lam k • u k = 0) :
    ∑ k, OfLattice.extEmb τ (lam k) * w k = 0 := by
  classical
  set σ := OfLattice.extEmb τ
  obtain ⟨⟨d, hd⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finset
    (nonZeroDivisors (𝓞 K)) (Finset.univ.image lam)
  have hk : ∀ k, IsLocalization.IsInteger (𝓞 K) (d • lam k) := fun k =>
    hint _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))
  choose lam' hlam' using hk
  have hσ : ∀ x : 𝓞 K, σ (algebraMap (𝓞 K) K x) = τ x := fun x =>
    RingHom.congr_fun (OfLattice.extEmb_comp τ) x
  have h1 : ∑ k, lam' k • u k = 0 := by
    have : ∀ k, lam' k • u k = d • (lam k • u k) := fun k => by
      rw [← algebraMap_smul K (lam' k) (u k), hlam' k, Algebra.smul_def, mul_smul,
        algebraMap_smul]
    simp only [this, ← Finset.smul_sum, h, smul_zero]
  have h2 := H lam' h1
  have h3 : ∀ k, τ (lam' k) = σ (algebraMap (𝓞 K) K d) * σ (lam k) := fun k => by
    rw [← hσ, hlam' k, Algebra.smul_def, map_mul]
  simp only [h3, mul_assoc, ← Finset.mul_sum] at h2
  have hd0 : σ (algebraMap (𝓞 K) K d) ≠ 0 := by
    rw [map_ne_zero, ne_eq, ← map_zero (algebraMap (𝓞 K) K),
      (IsFractionRing.injective (𝓞 K) K).eq_iff]
    exact nonZeroDivisors.ne_zero hd
  exact (mul_eq_zero.1 h2).resolve_left hd0

end GlobalTheory.FubiniStudyFrame


open GlobalTheory.FubiniStudyFrame in
theorem GlobalTheory.FubiniStudyFrame.noCommonZero_comb : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (m N : ℕ) (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (g : X ⟶ PSpace (𝓞 K) m) (u : Fin (m + 1) → V) (b : Module.Basis (Fin N) K V) (c : Matrix (Fin (m + 1)) (Fin N) K) (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ),
    g ≫ PSpace.str (𝓞 K) m = p →
    (∀ lam : Fin (m + 1) → 𝓞 K, ∑ k, lam k • u k = 0 → ∑ k, algX p ⊤ (lam k) • GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g = 0) →
    (∀ j, b j = ∑ k, c k j • u k) → (∀ σ, (A σ).det ≠ 0) →
    ∀ τ : 𝓞 K →+* ℂ, Weight.NoCommonZero fun a => ∑ k, (c.map (OfLattice.extEmb τ) * A (OfLattice.extEmb τ)) k a • secVal p τ (GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g) := by
  intro K V _ _ _ _ _ _ m N X _ p g u b c A _hg hrel hb hA τ i y hy
  classical
  set s := fun k => GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g with hs
  set w : Fin (m + 1) → ℂ := fun k => secVal p τ (s k) i y with hw_def
  have hsup := ProjSpace.iSup_nonzeroLocus_secPull (ProjSpace.iSup_nonzeroLocus_coord (𝓞 K) m) g
  have hw : w ≠ 0 := by
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show y.1 (IsLocalRing.closedPoint ℂ) ∈ ⨆ k, nonzeroLocus (s k) by rw [hsup]; trivial)
    intro h0
    exact (secVal_ne_zero_iff (s k) hy).2 (mem_ptsIn.2 hk) (congrFun h0 k)
  have H : ∀ lam : Fin (m + 1) → 𝓞 K, ∑ k, lam k • u k = 0 → ∑ k, τ (lam k) * w k = 0 := by
    intro lam h
    have e := congrArg (fun t => secVal p τ t i y) (hrel lam h)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum, secVal_smul, Finset.sum_apply, hw_def] using e
  obtain ⟨a, ha⟩ := exists_ne_zero_of_rel (OfLattice.extEmb τ) u b c (A (OfLattice.extEmb τ)) w hw
    (rel_field_of_rel_int τ u w H) hb (hA _)
  refine ⟨a, ?_⟩
  simpa [Finset.sum_apply, hw_def] using ha
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyCoordinateCombinationsNoCommonZeroStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.TrueGeo

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fubiniStudy_coordinate_combinations_noCommonZero : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (m N : ℕ) (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (g : X ⟶ PSpace (𝓞 K) m) (u : Fin (m + 1) → V) (b : Module.Basis (Fin N) K V) (c : Matrix (Fin (m + 1)) (Fin N) K) (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ),
    g ≫ PSpace.str (𝓞 K) m = p →
    (∀ lam : Fin (m + 1) → 𝓞 K, ∑ k, lam k • u k = 0 → ∑ k, algX p ⊤ (lam k) • GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g = 0) →
    (∀ j, b j = ∑ k, c k j • u k) → (∀ σ, (A σ).det ≠ 0) →
    ∀ τ : 𝓞 K →+* ℂ, Weight.NoCommonZero fun a => ∑ k, (c.map (OfLattice.extEmb τ) * A (OfLattice.extEmb τ)) k a • secVal p τ (GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g) := by
  first | exact @GlobalTheory.FubiniStudyFrame.noCommonZero_comb | exact GlobalTheory.FubiniStudyFrame.noCommonZero_comb | (intros; apply GlobalTheory.FubiniStudyFrame.noCommonZero_comb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatProjectiveModelOverRingOfIntegers
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatProjectiveModelOverRingOfIntegers
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.TrueGeo

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SpreadModel

open TopologicalSpace

theorem gen_specializes {O K : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] {p : X ⟶ Sp O} {j : Y ⟶ X} {q : Y ⟶ Sp K}
    (H : IsPullback j q p (spMap (algebraMap O K))) : j (genericPoint Y) ⤳ genericPoint X := by
  have hp (y : Y) : (p (j y)).asIdeal = ⊥ := by
    rw [← Scheme.Hom.comp_apply, H.w, Scheme.Hom.comp_apply]
    change Ideal.comap (algebraMap O K) (q y).asIdeal = ⊥
    rw [(Ideal.eq_bot_or_top _).resolve_right (q y).2.ne_top]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective O K)
  have hx : (p (genericPoint X)).asIdeal = ⊥ :=
    eq_bot_iff.2 (((PrimeSpectrum.asIdeal_le_asIdeal _ _).2 ((PrimeSpectrum.le_iff_specializes _ _).2
      ((genericPoint_specializes (j (genericPoint Y))).map p.continuous))).trans (hp _).le)
  have hr : genericPoint X ∈ Set.range j := by
    rw [← H.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
      Set.range_comp, H.isoPullback.hom.surjective.range_eq, Set.image_univ,
      Scheme.Pullback.range_fst]
    refine ⟨IsLocalRing.closedPoint K, PrimeSpectrum.ext (Eq.trans ?_ hx.symm)⟩
    change Ideal.comap (algebraMap O K) (IsLocalRing.maximalIdeal K) = ⊥
    rw [IsLocalRing.maximalIdeal_eq_bot]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective O K)
  obtain ⟨y, hy⟩ := hr
  exact hy ▸ (genericPoint_specializes y).map j.continuous

theorem app_algX {k k' : Type} [CommRing k] [CommRing k'] {σ : k →+* k'} {X Y : Scheme.{0}} {p : X ⟶ Sp k}
    {q : Y ⟶ Sp k'} {j : Y ⟶ X} (w : j ≫ p = q ≫ spMap σ) (a : k) :
    j.app ⊤ (algX p ⊤ a) = algX q ⊤ (σ a) := by
  have e₁ : j.app ⊤ (algX p ⊤ a) = algX (j ≫ p) ⊤ a := by
    simp only [algX, RingHom.comp_apply, Scheme.Hom.app_eq_appLE,
      ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
    simp only [Opens.map_top]
    rfl
  rw [e₁, w]
  have e₂ := congrArg (fun ψ => ψ.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom σ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e₂
  simp only [algX, RingHom.comp_apply]
  rw [e₂]
  simp [Scheme.Hom.appLE]
  rfl

theorem exists_spread : ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (D m : ℕ) (y : Fin (m + 1) → Ω) (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp K) (B : LB Y) (_ : B.IsLB) (t : Fin (m + 1) → B.Sec) (ψ : Ω →+* Y.functionField),
    IsProjOver q → topologicalKrullDim Y = D → (⨆ k, nonzeroLocus (t k) = ⊤) → Function.Bijective ψ →
    (∀ a : K, ψ (algebraMap K Ω a) = fnOf ⊤ (TopologicalSpace.Opens.mem_top _) (algX q ⊤ a)) →
    (∀ (k l : Fin (m + 1)) (i : B.ι) (h : genericPoint Y ∈ B.U i), ψ (y k) * fnOf _ h ((t l).f i) = ψ (y l) * fnOf _ h ((t k).f i)) →
    ∃ (X : Scheme.{0}) (_ : IsIntegral X) (p : X ⟶ Sp (𝓞 K)) (g : X ⟶ PSpace (𝓞 K) m) (ψ' : Ω →+* X.functionField),
      g ≫ PSpace.str (𝓞 K) m = p ∧ IsArithVar p D ∧ Function.Bijective ψ' ∧
      (∀ a : 𝓞 K, ψ' (algebraMap K Ω (a : K)) = fnOf ⊤ (TopologicalSpace.Opens.mem_top _) (algX p ⊤ a)) ∧
      ∀ (k l : Fin (m + 1)) (i : ((ProjSpace.O1 (𝓞 K) m).pull g).ι) (h : genericPoint X ∈ ((ProjSpace.O1 (𝓞 K) m).pull g).U i),
        ψ' (y k) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m l) g).f i) =
          ψ' (y l) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g).f i) := by
  intro K Ω _ _ _ _ D m y Y _ q B hB t ψ hq hD ht hψ hK hy
  let c := q ≫ spMap (algebraMap (𝓞 K) K)
  obtain ⟨X, π, j, hX, hπ, hfl, H, hg⟩ := IntModel.exists_flat_model (O := 𝓞 K) q hq
    (fun _ : Unit => PSpace (𝓞 K) m) (fun _ => PSpace.str (𝓞 K) m) (fun _ => ProjSpace.toProj c t ht)
    (fun _ => ⟨m, 𝟙 _, inferInstance, Category.id_comp _⟩) (fun _ => ProjSpace.toProj_str c t ht)
  obtain ⟨g, hg₁, hg₂⟩ := hg ()
  have := CommonModel.isProper_of_isProjOver hπ
  have hZ : Flat (spMap (Int.castRingHom (𝓞 K))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact (RingHom.flat_algebraMap_iff (R := ℤ) (S := 𝓞 K)).2 inferInstance
  have har : IsArithVar π D := ⟨inferInstance, inferInstance, hX, hπ, inferInstance,
    IntModel.topologicalKrullDim_eq_succ (RingOfIntegers.not_isField K) H hD⟩
  have hη := gen_specializes H
  have hpre : IsPreimmersion j :=
    have := IsPreimmersion.of_isLocalization (R := 𝓞 K) (S := K) (nonZeroDivisors (𝓞 K))
    MorphismProperty.of_isPullback H.flip this
  let e : X.functionField ≃+* Y.functionField := RingEquiv.ofBijective (SmallSec.fnMap j hη)
    ⟨(SmallSec.fnMap j hη).injective, SmallSec.fnMap_surjective j hη⟩
  have he (u) : e u = SmallSec.fnMap j hη u := rfl
  have he' (a : Ω) : e ((e.symm.toRingHom.comp ψ) a) = ψ a := e.apply_symm_apply _
  refine ⟨X, hX, π, g, e.symm.toRingHom.comp ψ, hg₂, har, e.symm.bijective.comp hψ, fun a => ?_, fun k l i h => ?_⟩
  · apply e.injective
    rw [he', hK, he, SmallSec.fnMap_fnOf j hη _ (Opens.mem_top _), app_algX H.w]
    rfl
  · apply e.injective
    have h' : genericPoint Y ∈ j ⁻¹ᵁ ((ProjSpace.O1 (𝓞 K) m).pull g).U i := hη.mem_open (Opens.isOpen _) h
    have hU₀ : j ⁻¹ᵁ ((ProjSpace.O1 (𝓞 K) m).pull g).U i ≤ (j ≫ g) ⁻¹ᵁ ProjSpace.chart (𝓞 K) m (i PUnit.unit) :=
      fun x hx => (pull_U _ g i).le hx
    have hU : j ⁻¹ᵁ ((ProjSpace.O1 (𝓞 K) m).pull g).U i ≤
        ProjSpace.toProj c t ht ⁻¹ᵁ ProjSpace.chart (𝓞 K) m (i PUnit.unit) := hg₁ ▸ hU₀
    have hf (a) : j.app _ ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m a) g).f i) =
        ProjSpace.pullRatio (ProjSpace.toProj c t ht) _ (i PUnit.unit) hU a := by
      refine Eq.trans ?_ (ProjSpace.pullRatio_of_eq hg₁ hU₀ _)
      rw [Scheme.Hom.app_eq_appLE]
      exact congrArg (fun ψ => ψ.hom (ProjSpace.ratio (𝓞 K) m (i PUnit.unit) a))
        (Scheme.Hom.appLE_comp_appLE j g _ _ _ (pull_U _ g i).le le_rfl)
    obtain ⟨n, hn⟩ := exists_chart hB (genericPoint Y)
    have key (a) := congrArg (fnOf _ (memInf h' hn)) (ProjSpace.sec_eq_pullRatio_toProj_mul c t ht (i PUnit.unit) a n
      (W := _ ⊓ B.U n) (inf_le_left.trans hU) inf_le_right)
    have hne : fnOf _ hn ((t (i PUnit.unit)).f n) ≠ 0 := by
      have hu := (ProjSpace.isUnit_resG_sec (t (i PUnit.unit)) n (W := _ ⊓ B.U n)
        (inf_le_left.trans (hU.trans (ProjSpace.toProj_preimage_chart c t ht _).le)) inf_le_right).map
          (fnOf _ (memInf h' hn))
      rw [fnOf_resG] at hu
      exact hu.ne_zero
    have key' (a) : fnOf _ hn ((t a).f n) = e (fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m a) g).f i)) *
        fnOf _ hn ((t (i PUnit.unit)).f n) := by
      have e₁ := key a
      rw [map_mul, fnOf_resG, fnOf_resG, ← ProjSpace.resG_pullRatio (hi := hU) inf_le_left, fnOf_resG] at e₁
      rw [he, SmallSec.fnMap_fnOf j hη h h', hf]
      exact e₁
    have h₀ := hy k l n hn
    rw [key' k, key' l, ← mul_assoc, ← mul_assoc] at h₀
    rw [map_mul, map_mul, he', he']
    exact mul_right_cancel₀ hne h₀

end GlobalTheory.SpreadModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatProjectiveModelOverRingOfIntegersStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.TrueGeo

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flat_projective_model_over_ringOfIntegers : ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (D m : ℕ) (y : Fin (m + 1) → Ω) (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp K) (B : LB Y) (_ : B.IsLB) (t : Fin (m + 1) → B.Sec) (ψ : Ω →+* Y.functionField),
    IsProjOver q → topologicalKrullDim Y = D → (⨆ k, nonzeroLocus (t k) = ⊤) → Function.Bijective ψ →
    (∀ a : K, ψ (algebraMap K Ω a) = fnOf ⊤ (TopologicalSpace.Opens.mem_top _) (algX q ⊤ a)) →
    (∀ (k l : Fin (m + 1)) (i : B.ι) (h : genericPoint Y ∈ B.U i), ψ (y k) * fnOf _ h ((t l).f i) = ψ (y l) * fnOf _ h ((t k).f i)) →
    ∃ (X : Scheme.{0}) (_ : IsIntegral X) (p : X ⟶ Sp (𝓞 K)) (g : X ⟶ PSpace (𝓞 K) m) (ψ' : Ω →+* X.functionField),
      g ≫ PSpace.str (𝓞 K) m = p ∧ IsArithVar p D ∧ Function.Bijective ψ' ∧
      (∀ a : 𝓞 K, ψ' (algebraMap K Ω (a : K)) = fnOf ⊤ (TopologicalSpace.Opens.mem_top _) (algX p ⊤ a)) ∧
      ∀ (k l : Fin (m + 1)) (i : ((ProjSpace.O1 (𝓞 K) m).pull g).ι) (h : genericPoint X ∈ ((ProjSpace.O1 (𝓞 K) m).pull g).U i),
        ψ' (y k) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m l) g).f i) =
          ψ' (y l) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g).f i) := by
  first | exact @GlobalTheory.SpreadModel.exists_spread | exact GlobalTheory.SpreadModel.exists_spread | (intros; apply GlobalTheory.SpreadModel.exists_spread <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinimalGenusBound
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenvectorMemSpanTwistedTraceImage
open scoped BigOperators Matrix
open Polynomial

namespace GlobalTheory


open scoped BigOperators Matrix in
open Polynomial in
theorem _root_.GlobalTheory.eigenvector_mem_span_twistedTrace_image :
    ∀ (H K V : Type) [Group H] [Fintype H] [Field K] [CharZero K] [AddCommGroup V] [Module K V] (st : H → V →ₗ[K] V), (∀ h h' x, st (h * h') x = st h' (st h x)) → ∀ (χ : H →* Kˣ) (s : Set V), Submodule.span K s = ⊤ → ∀ x : V, (∀ h, st h x = ((χ h : Kˣ) : K) • x) → x ∈ Submodule.span K ((fun y => ∑ h, (((χ h)⁻¹ : Kˣ) : K) • st h y) '' s) := by
  intro H K V _ _ _ _ _ _ st _ χ s hs x hx
  let P : V →ₗ[K] V := ∑ h, (((χ h)⁻¹ : Kˣ) : K) • st h
  have hP : (fun y => ∑ h, (((χ h)⁻¹ : Kˣ) : K) • st h y) = ⇑P := by
    funext y
    simp [P, LinearMap.sum_apply]
  have hPx : P x = (Fintype.card H : K) • x := by
    rw [← hP]
    simp only [hx, smul_smul, Units.inv_mul, one_smul, Finset.sum_const, Finset.card_univ]
    rw [Nat.cast_smul_eq_nsmul]
  have hcard : (Fintype.card H : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hxP : x = P ((Fintype.card H : K)⁻¹ • x) := by
    rw [map_smul, hPx, smul_smul, inv_mul_cancel₀ hcard, one_smul]
  rw [hP, Submodule.span_image, hs, hxP]
  exact Submodule.mem_map_of_mem Submodule.mem_top

end GlobalTheory
end

set_option synthInstance.maxHeartbeats 400000

open NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.AllWt GlobalTheory.LevDesc
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)

namespace GlobalTheory.CovGminTop

section Abstract

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]

theorem norm_sum_le_of_gram {N : (K →+* ℂ) → V → ℝ} (hG : HasGram N) (hc : ∀ σ x, N ((starRingEnd ℂ).comp σ) x = N σ x)
    {ι : Type} (s : Finset ι) (f : ι → V) (σ : K →+* ℂ) : N σ (∑ i ∈ s, f i) ≤ ∑ i ∈ s, N σ (f i) := by
  letI : StarRing K := starRingOfComm
  obtain ⟨n, ⟨b, X⟩, h⟩ := hG
  have e : ∀ x, N σ x = Formalism.HermitianLatticesTheory.normAt b X (InfinitePlace.mk σ) x := fun x => by
    rw [(h _).2]
    rcases InfinitePlace.embedding_mk_eq σ with e | e
    · rw [e]
    · rw [e]; exact (hc σ x).symm
  simp only [e]
  exact PI.Dv.Tr.normAt_sum_le' b X _ s f

theorem char_val {H : Type} [Group H] [Finite H] (χ : H →* Kˣ) (h : H) :
    IsIntegral ℤ ((χ h : Kˣ) : K) ∧ ∀ σ : K →+* ℂ, ‖σ ((χ h : Kˣ) : K)‖ = 1 := by
  have hn : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have h1 : ((χ h : Kˣ) : K) ^ Nat.card H = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
  refine ⟨IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (h1 ▸ isIntegral_one), fun σ => ?_⟩
  have : ‖σ ((χ h : Kˣ) : K)‖ ^ Nat.card H = 1 := by rw [← norm_pow, ← map_pow, h1, map_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 this

variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem exists_short_eigen {H : Type} [Group H] [Finite H] (st : H → V →ₗ[K] V)
    (hst : ∀ h h' x, st (h * h') x = st h' (st h x)) (χ : H →* Kˣ) (Λ : Submodule (𝓞 K) V) (hΛ : ∀ h, ∀ x ∈ Λ, st h x ∈ Λ)
    {N : (K →+* ℂ) → V → ℝ} (hG : HasGram N) (hc : ∀ σ x, N ((starRingEnd ℂ).comp σ) x = N σ x)
    (hs : ∀ σ (a : K) x, N σ (a • x) = ‖σ a‖ * N σ x) (hi : ∀ h σ x, N σ (st h x) = N σ x)
    (s : Set V) (hsΛ : s ⊆ Λ) (hsp : Submodule.span K s = ⊤) (B : ℝ) (hB : ∀ y ∈ s, ∀ σ, N σ y ≤ B) :
    ∃ s' : Set V, (∀ y ∈ s', (y ∈ Λ ∧ ∀ h, st h y = ((χ h : Kˣ) : K) • y) ∧ ∀ σ, N σ y ≤ Nat.card H * B) ∧
      ∀ x, (∀ h, st h x = ((χ h : Kˣ) : K) • x) → x ∈ Submodule.span K s' := by
  classical
  letI := Fintype.ofFinite H
  refine ⟨_, ?_, GlobalTheory.eigenvector_mem_span_twistedTrace_image H K V st hst χ s hsp⟩
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨⟨Λ.sum_mem fun h _ => ?_, fun g => ?_⟩, fun σ => ?_⟩
  · rw [← map_inv]
    let a : 𝓞 K := ⟨_, (char_val χ h⁻¹).1⟩
    have := Λ.smul_mem a (hΛ h y (hsΛ hy))
    rwa [← algebraMap_smul K a] at this
  · beta_reduce
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.smul_sum, ← Equiv.sum_comp (Equiv.mulRight g) fun h => _ • _ • st h y]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [map_smul, ← hst, smul_smul, Equiv.coe_mulRight, map_mul, mul_inv, ← Units.val_mul, mul_left_comm, mul_inv_cancel, mul_one]
  · refine (norm_sum_le_of_gram hG hc _ _ σ).trans ?_
    rw [Nat.card_eq_fintype_card, ← nsmul_eq_mul, ← Finset.card_univ]
    refine Finset.sum_le_card_nsmul _ _ _ fun h _ => ?_
    rw [hs, hi, ← map_inv, (char_val χ h⁻¹).2, one_mul]
    exact hB y hy σ

end Abstract

section Point

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem half_lt_laOf (τ : Psi p.T.Q.H) (k : Fin ((dat p i).p + (dat p i).q)) (hk : (k : ℕ) < (dat p i).p) :
    (((p.κ i).n / 2 : ℕ) : ℤ) < laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ k := by
  have h := GlobalTheory.HolRead.lastPos_wtA_of_kapIs D p.T p.κ p.fw.laws p.fw.kap i τ.1 τ.2
  have hm : (dat p i).mult τ.1 = (dat p i).p := by
    unfold Datum.mult
    exact if_pos τ.2
  rw [hm] at h
  have h2 : wtA (p.κ i) (τ.1, (dat p i).p - 1) ≤ wtA (p.κ i) (τ.1, k) := (dom_wtA (p.κ i)).1 τ.1 (show (k : ℕ) ≤ _ by omega)
  have h3 := h (by omega)
  unfold laOf weightOf
  rw [if_pos hk]
  beta_reduce
  omega

theorem one_le_kap (hp : 1 ≤ (dat p i).p) : 1 ≤ kap p i := by
  have hf : 1 ≤ D.R.f := by
    unfold Ranks.f Ranks.n
    have := D.R.two_le_m
    have := D.R.m_le_f
    omega
  have hne : Nonempty (Psi p.T.Q.H) := (Nat.card_pos_iff.1 (by rw [WtShape.card_psi p]; exact hf)).1
  obtain ⟨τ⟩ := hne
  have h := half_lt_laOf p i τ ⟨0, by omega⟩ hp
  have h1 : (1 : ℤ) ≤ laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ ⟨0, by omega⟩ := by omega
  have h2 : (1 : ℝ) ≤ laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ ⟨0, by omega⟩ := by exact_mod_cast h1
  refine le_trans ?_ (Finset.single_le_sum (f := fun τ => ∑ k, |(laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ k : ℝ)|)
    (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ τ))
  exact (h2.trans (le_abs_self _)).trans (Finset.single_le_sum (f := fun k => |(laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ k : ℝ)|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ _))

theorem gminAt_of_gens (Y : Cov p i) (hpq : 1 ≤ (dat p i).p + (dat p i).q) (hA : Y.d.l₂.A.Coprime Y.d.l₂.M)
    (hC : KeepsCusp Y.U (Gk p i))
    (hk : ∀ (γ : LevelAut (dat p i) Y.d.l₂) (f g : Y.V (Gk p i)), (g : Rul Y.d.Xo₂ Y.d.c₂) = pull Y.d.Xo₂ Y.d.c₂ γ f →
      (f ∈ latW Y.U (Gk p i) → g ∈ latW Y.U (Gk p i)) ∧ ∀ σ, Y.nrm (Gk p i) σ g = Y.nrm (Gk p i) σ f)
    (hG : Y.GoodAt (Gk p i)) (S : Subgroup (LevelAut (dat p i) Y.d.l₂)) (χ : S →* (Y.d.c₂.F)ˣ)
    (hN : latDeep p i Y = chiLat S Y.U (Gk p i) χ) (s : Set (Y.V (Gk p i))) (hs : s ⊆ latW Y.U (Gk p i))
    (hsp : Submodule.span Y.d.c₂.F s = ⊤) (B PP : ℝ) (hB : ∀ y ∈ s, ∀ σ, Y.nrm (Gk p i) σ y ≤ Real.exp B)
    (hPP : Real.log (Nat.card S) + B ≤ PP * kap p i) : GminAt p i Y PP := by
  let st : S → Y.V (Gk p i) →ₗ[Y.d.c₂.F] Y.V (Gk p i) := fun h =>
    (pull Y.d.Xo₂ Y.d.c₂ (h : LevelAut (dat p i) Y.d.l₂)).toLinearMap.restrict (hC h)
  obtain ⟨s', h1, h2⟩ := exists_short_eigen st
    (fun h h' x => Subtype.ext ((isRightAct_pull (Xo := Y.d.Xo₂) (c := Y.d.c₂) hpq hA).2 h h' x)) χ (latW Y.U (Gk p i))
    (fun h x hx => (hk h x _ rfl).1 hx) hG.1
    (fun σ f => by rw [normW, normW, petW, petW, GlobalTheory.CompHt.goodOf_conj σ])
    (fun σ a x => petW_smul _ _ _ _ _ σ a _) (fun h σ x => (hk h x _ rfl).2 σ) s hs hsp _ hB
  refine ⟨s', fun y hy => ?_, fun y hy σ => ((h1 y hy).2 σ).trans ?_, fun x hx => h2 x fun h => Subtype.ext ?_⟩
  · rw [hN]
    exact (mem_chiLat S Y.U _).2 ⟨(h1 y hy).1.1, fun h => congrArg Subtype.val ((h1 y hy).1.2 h)⟩
  · have hc : (0 : ℝ) < Nat.card S := by exact_mod_cast Nat.card_pos
    rw [← Real.exp_log hc, ← Real.exp_add]
    exact Real.exp_le_exp.2 hPP
  · rw [hN] at hx
    exact ((mem_chiLat S Y.U _).1 hx).2 h

end Point

theorem num_step {C Z l k PP : ℝ} (hC : 0 ≤ C) (hl : C + 45 ≤ Z) (hk : 1 ≤ k) (hPP : Z ^ 12 ≤ PP) (h : l ≤ 45 * Z ^ 2) :
    l + C * Z ^ 2 * k ≤ PP * k := by
  have h1 : 1 ≤ Z := by linarith
  have h2 : Z ^ 3 ≤ Z ^ 12 := pow_le_pow_right₀ h1 (by norm_num)
  have h3 : (C + 45) * Z ^ 2 ≤ Z ^ 3 := by
    rw [pow_succ' Z 2]; exact mul_le_mul_of_nonneg_right hl (by positivity)
  have h4 : (C + 45) * Z ^ 2 * k ≤ PP * k := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have h5 : 45 * Z ^ 2 ≤ 45 * Z ^ 2 * k := le_mul_of_one_le_right (by positivity) hk
  linarith

end GlobalTheory.CovGminTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CarryingSectionIntegralFrame
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

namespace GlobalTheory.CovMult

open GlobalTheory.SlopeRec GlobalTheory.FlatLine GlobalTheory.RefSum

section Places

variable {K : Type} [Field K] [NumberField K]

theorem exists_prime_mem (la : HeightOneSpectrum (𝓞 K)) : ∃ q : ℕ, q.Prime ∧ (q : 𝓞 K) ∈ la.asIdeal := by
  have h0 : Ideal.absNorm la.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact la.ne_bot
  have key : ∀ n : ℕ, n ≠ 0 → (n : 𝓞 K) ∈ la.asIdeal → ∃ q : ℕ, q.Prime ∧ (q : 𝓞 K) ∈ la.asIdeal := by
    intro n
    induction n using Nat.recOnMul with
    | zero => exact fun h => absurd rfl h
    | one => exact fun _ h => absurd ((Ideal.eq_top_iff_one _).2 (by simpa using h)) la.isPrime.ne_top
    | prime p hp => exact fun _ h => ⟨p, hp, h⟩
    | mul a b ha hb =>
      intro h hm
      rw [Nat.cast_mul] at hm
      exact (la.isPrime.mem_or_mem hm).elim (ha (left_ne_zero_of_mul h)) (hb (right_ne_zero_of_mul h))
  exact key _ h0 (Ideal.absNorm_mem _)

theorem vLa_nat_nonneg (la : HeightOneSpectrum (𝓞 K)) {n : ℕ} (hn : n ≠ 0) : 0 ≤ vLa la (n : K) := by
  have := vAdd_int_nonneg la (a := (n : 𝓞 K)) (by simpa using hn)
  simpa [vLa, Formalism.BasicNotions.vAdd] using this

theorem vLa_pos {la : HeightOneSpectrum (𝓞 K)} {q : ℕ} (hq : q ≠ 0) (h : (q : 𝓞 K) ∈ la.asIdeal) :
    0 < vLa la (q : K) := by
  have h1 : la.valuation K (q : K) < 1 := by
    have := (la.valuation_lt_one_iff_mem (K := K) (q : 𝓞 K)).2 h
    simpa using this
  have h0 : la.valuation K (q : K) ≠ 0 := (Valuation.ne_zero_iff _).2 (Nat.cast_ne_zero.2 hq)
  unfold vLa
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
  omega

theorem exists_spread {S : Finset ℕ} {a : ℕ → ℝ} {s : ℝ} (h : PrimeSum S a s) (e : HeightOneSpectrum (𝓞 K) →₀ ℝ)
    (t : (K →+* ℂ) → ℝ) : ∃ e' : HeightOneSpectrum (𝓞 K) →₀ ℝ, cost e' t ≤ cost e t + s ∧
      ∀ (la : HeightOneSpectrum (𝓞 K)) (q : ℕ), e la + (vLa la (q : K) : ℝ) * a q ≤ e' la := by
  classical
  obtain ⟨hp, h0, hS, hs⟩ := h
  have one : ∀ (q : ℕ), q ≠ 0 → ∀ (b : ℝ) (e : HeightOneSpectrum (𝓞 K) →₀ ℝ), ∃ e' : HeightOneSpectrum (𝓞 K) →₀ ℝ,
      cost e' t = cost e t + b * Real.log q ∧ ∀ la, e' la = e la + (vLa la (q : K) : ℝ) * b := by
    intro q hq b e
    have hf := fin_mul (finite_vAdd (K := K) (a := q) (Nat.cast_ne_zero.2 hq)) fun _ => b
    refine ⟨e + Finsupp.ofSupportFinite _ hf, ?_, fun la => rfl⟩
    have h1 := sum_vAdd_nat (K := K) hq
    have h2 : ((Finsupp.ofSupportFinite _ hf).sum fun la a => a * Real.log (Ideal.absNorm la.asIdeal : ℝ)) /
        (Module.finrank ℚ K : ℝ) = b * Real.log q := by
      rw [← h1, mul_finsum, Finsupp.sum, Finset.sum_div, finsum_eq_sum_of_support_subset (s := (Finsupp.ofSupportFinite _ hf).support)]
      · refine Finset.sum_congr rfl fun la _ => ?_
        simp only [Finsupp.ofSupportFinite_coe, lw]; ring
      · intro la hla
        simp only [Finset.mem_coe, Finsupp.mem_support_iff, Finsupp.ofSupportFinite_coe]
        intro h
        apply hla
        simp only
        rw [← mul_assoc, mul_comm b, h, zero_mul]
    rw [cost, cost, Finsupp.sum_add_index' (by simp) (fun _ _ _ => add_mul _ _ _), ← h2]
    ring
  have all : ∀ T : Finset ℕ, (∀ q ∈ T, q ≠ 0) → ∃ e' : HeightOneSpectrum (𝓞 K) →₀ ℝ,
      cost e' t = cost e t + ∑ q ∈ T, a q * Real.log q ∧ ∀ la, e' la = e la + ∑ q ∈ T, (vLa la (q : K) : ℝ) * a q := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact fun _ => ⟨e, by simp, by simp⟩
    | insert q T hq ih =>
      intro hT
      obtain ⟨e₁, h1, h2⟩ := ih fun r hr => hT r (Finset.mem_insert_of_mem hr)
      obtain ⟨e₂, h3, h4⟩ := one q (hT q (Finset.mem_insert_self _ _)) (a q) e₁
      exact ⟨e₂, by rw [h3, h1, Finset.sum_insert hq]; ring, fun la => by rw [h4, h2, Finset.sum_insert hq]; ring⟩
  obtain ⟨e', h1, h2⟩ := all S fun q hq => (hp q hq).ne_zero
  have hn : ∀ la, ∀ q ∈ S, 0 ≤ (vLa la (q : K) : ℝ) * a q := fun la q hq =>
    mul_nonneg (by exact_mod_cast vLa_nat_nonneg la (hp q hq).ne_zero) (h0 q)
  refine ⟨e', by linarith, fun la q => ?_⟩
  rw [h2]
  by_cases hq : q ∈ S
  · exact add_le_add_right (Finset.single_le_sum (hn la) hq) _
  · rw [hS q hq, mul_zero]
    exact add_le_add_right (Finset.sum_nonneg (hn la)) _

end Places

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}

theorem depthOn_le (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) {cst a : ℝ} {G : WTZ E} {q : ℕ} (hq : q ≠ 0)
    (ha : refExp_vp U cst G q ≤ (a : EReal)) {la : HeightOneSpectrum (𝓞 c.F)} (hla : (q : 𝓞 c.F) ∈ la.asIdeal)
    {T : CDVR} {io : c.F →+* T.Fr} {e : ℕ} (ho : OverLa la T.V io e) {y : IntFr Xo c T io} (hy : y.IsAlg)
    {φ : ℝ} (hφ : HasPhi y φ) {Z : Comp Xo c} (hZ : letI := io.toAlgebra; LiesOn Z y.1) :
    depthOn U Z G (fun f => nval T.V e (evI y f)) ≤ (((vLa la (q : c.F) : ℝ) * a + cst * φ / e : ℝ) : EReal) := by
  letI := io.toAlgebra
  have hb := (refExp_vp_le_iff U).1 ha ⟨la, hla⟩ T io e ho y hy φ hφ
  rw [← EReal.coe_add] at hb
  have hm := vLa_pos hq hla
  have hv : vV T.V (q : T.Fr) = e * vLa la (q : c.F) := by rw [← ho.2, map_natCast]
  have hm' : (0 : ℝ) < vLa la (q : c.F) := by exact_mod_cast hm
  have he : (0 : ℝ) < e := by exact_mod_cast ho.1
  have hn : (((vV T.V (q : T.Fr)).toNat : ℕ) : ℝ) = e * vLa la (q : c.F) := by
    have : (((vV T.V (q : T.Fr)).toNat : ℕ) : ℤ) = e * vLa la (q : c.F) := by
      rw [← hv, Int.toNat_of_nonneg (hv ▸ mul_nonneg (Nat.cast_nonneg _) hm.le)]
    exact_mod_cast this
  refine le_of_forall_gt_imp_ge_of_dense fun b hb' => ?_
  induction b using EReal.rec with
  | bot => exact absurd hb' not_lt_bot
  | top => exact le_top
  | coe b =>
    have hb1 := EReal.coe_lt_coe_iff.1 hb'
    have hlt : depthAt_vp U G q y < ((b / vLa la (q : c.F) : ℝ) : EReal) := by
      refine hb.trans_lt (EReal.coe_lt_coe_iff.2 ?_)
      rw [lt_div_iff₀ hm', hv]
      refine lt_of_eq_of_lt ?_ hb1
      push_cast; field_simp
    unfold depthAt_vp depth_vw at hlt
    obtain ⟨w, hw⟩ := iInf_lt_iff.1 hlt
    obtain ⟨hwl, hw⟩ := iInf_lt_iff.1 hw
    have hne : evI y (w : Rul Xo c) ≠ 0 := fun h0 => by
      simp only [h0, nval_zero] at hw
      exact not_top_lt hw
    obtain ⟨g, hg, hgl⟩ := GlobalTheory.CompRestr.exists_cuspOn_restrict E H Dw l Xo c r U hU Z _ w
    have hev : evI y (g : Rul Xo c) = evI y (w : Rul Xo c) := hg T.Fr y.1 hZ
    refine (iInf₂_le g (hgl hwl)).trans ?_
    simp only [nval_of_ne hne] at hw
    beta_reduce
    rw [hev, nval_of_ne hne, EReal.coe_le_coe_iff]
    have h2 := EReal.coe_lt_coe_iff.1 hw
    rw [hn, ← div_div, div_lt_div_iff_of_pos_right hm'] at h2
    exact h2.le

theorem exists_bound (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) {a : ℕ → ℝ} {G : WTZ E}
    (ha : ∀ q : ℕ, q.Prime → refExp_vp U (1 / 2500) G q ≤ (a q : EReal)) {Z : Comp Xo c} {θ : Rul Xo c} {w : Ix Dw → ℤ}
    (hθ : θ ∈ secZ Xo c w) {e e' : HeightOneSpectrum (𝓞 c.F) →₀ ℝ}
    (he : ∀ (la : HeightOneSpectrum (𝓞 c.F)) (q : ℕ), e la + (vLa la (q : c.F) : ℝ) * a q ≤ e' la)
    (hk : ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e₀ : ℕ), OverLa la T.V io e₀ →
      ∀ y : IntFr Xo c T io, y.IsAlg → (∃ (G' : WTZ E), ∃ f ∈ cuspOn U Z G', evI y f ≠ 0) → ∀ φ : ℝ, HasPhi y φ →
        ((8 / 2500 * φ / e₀ - 8 * e la : ℝ) : EReal) ≤ nval T.V e₀ (evI y θ))
    {la : HeightOneSpectrum (𝓞 c.F)} {v : Rul Xo c → EReal} (hv : v ∈ (recVals Xo c).1 la) {G' : WTZ E} {f : Rul Xo c}
    (hf : f ∈ cuspOn U Z G') (hf0 : v f ≠ ⊤) :
    ∃ B : ℝ, depthOn U Z G v ≤ (B : EReal) ∧ ((8 * B - 8 * e' la : ℝ) : EReal) ≤ v θ := by
  obtain ⟨⟨_, T, io, e₀, ho, y, hy, η, hη, rfl⟩, rfl⟩ := hv
  obtain ⟨T', i, e₁, y', φ, -, ho', hy', hφ, -, hv⟩ := exists_ext_hasPhi ho y hy
  obtain ⟨q, hq, hla⟩ := exists_prime_mem la
  have hf1 : evI y' f ≠ 0 := fun h => hf0 (by
    show nval T.V e₀ (evI y f) = ⊤
    rw [← (hv f hf.1.1.1).2, h, nval_zero])
  letI := (i.comp io).toAlgebra
  have hZ : LiesOn Z y'.1 := by
    by_contra h
    exact hf1 (hf.2 _ _ ((liesOff_iff Z y'.1).2 h))
  refine ⟨_, le_trans (le_of_eq ?_) (depthOn_le hU hq.ne_zero (ha q hq) hla ho' hy' hφ hZ), ?_⟩
  · exact iInf_congr fun g => iInf_congr fun _ => (hv g g.2.1.1.1).2.symm
  · refine le_trans (EReal.coe_le_coe_iff.2 ?_) ((hk la T' _ e₁ ho' y' hy' ⟨G', f, hf, hf1⟩ φ hφ).trans_eq (hv θ hθ.1).2)
    have := he la q
    have e2 : 8 / 2500 * φ / e₁ = 8 * (1 / 2500 * φ / e₁) := by ring
    linarith

theorem mult_of (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) {x : ℝ} {D : D7} {V : (c.F →+* ℂ) → HSp D}
    {dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r} {u u' : AllWt.Weight Dw} {S : Finset ℕ} {a : ℕ → ℝ} {s cc : ℝ}
    (hS : PrimeSum S a s) (ha : ∀ q : ℕ, q.Prime → refExp_vp U (1 / 2500) (wtOf Dw u 0) q ≤ (a q : EReal)) {Z : Comp Xo c}
    (hZ : ∃ (θ : Rul Xo c) (e : HeightOneSpectrum (𝓞 c.F) →₀ ℝ) (t : (c.F →+* ℂ) → ℝ), Carries U Z u u' θ ∧
      (∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e₀ : ℕ), OverLa la T.V io e₀ →
        ∀ y : IntFr Xo c T io, y.IsAlg → (∃ (G' : WTZ E), ∃ f ∈ cuspOn U Z G', evI y f ≠ 0) → ∀ φ : ℝ, HasPhi y φ →
          ((8 / 2500 * φ / e₀ - 8 * e la : ℝ) : EReal) ≤ nval T.V e₀ (evI y θ)) ∧
      InfBd U x V dict Z (wtOf Dw u 0) (wtOf Dw ((8 : ℤ) • (u - u')) 0) 8 θ t ∧ cost e t ≤ cc) :
    Mult U x V dict Z u u' (cc + s) := by
  obtain ⟨θ, e, t, hC, hk, hI, hco⟩ := hZ
  obtain ⟨e', he', he⟩ := exists_spread hS e t
  have key := fun la v hv G' f hf hf0 => exists_bound hU ha hC.1 he hk (la := la) (v := v) hv (G' := G') (f := f) hf hf0
  refine ⟨fun la v hv G' f hf hf0 => ?_, θ, e', t, hC, fun la v hv ⟨w, _, hw⟩ => ?_, hI, by linarith⟩
  · obtain ⟨B, hB, -⟩ := key la v hv G' f hf hf0
    by_contra hn
    push Not at hn
    exact EReal.coe_ne_top B (top_le_iff.1 ((le_iInf₂ fun w hw => (hn w hw).ge).trans hB))
  · obtain ⟨B, hB, hB'⟩ := key la v hv _ w w.2 hw
    calc _ ≤ ((8 : ℕ) : EReal) * (B : EReal) := mul_le_mul_of_nonneg_left hB (by exact_mod_cast Nat.zero_le 8)
      _ = ((8 * B - 8 * e' la : ℝ) : EReal) + ((((8 : ℕ) : ℝ) * e' la : ℝ) : EReal) := by
        rw [← EReal.coe_add, ← EReal.coe_natCast, ← EReal.coe_mul]; congr 1; push_cast; ring
      _ ≤ _ := add_le_add_left hB' _

theorem budget_add {T a b C₁ C₂ u : ℝ} (h₁ : T * b ≤ C₁ * u) (h₂ : T * a ≤ C₂ * u) : T * (a + b) ≤ (C₁ + C₂) * u := by
  linarith

end GlobalTheory.CovMult

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefFibreTwistExists
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjSpace

namespace GlobalTheory.AmpleTwistNef

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}

theorem nefFib_of_cls_eq {L M : HermLB p} (h : cls L.B L.isLB = cls M.B M.isLB) (hL : ArInt.NefFib L) :
    ArInt.NefFib M := by
  intro Z i _ _ κ _ _ _ hd
  have e : cls (L.B.pull i) (pull_isLB L.isLB i) = cls (M.B.pull i) (pull_isLB M.isLB i) := by
    rw [cls_pull L.isLB i, cls_pull M.isLB i, h]
  rw [← topSelf_congr κ (pull_isLB L.isLB i) (pull_isLB M.isLB i) ((cls_eq_iff _ _).1 e)]
  exact hL Z i κ hd

end GlobalTheory.AmpleTwistNef

namespace GlobalTheory.AmpleTwistNef

open GlobalTheory.ArInt

end GlobalTheory.AmpleTwistNef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecCarriedOver
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem gs_eq_map_gs {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)) :
    gs f y U a = (f.stalkMap y).hom (gs (𝟙 X) (f y) U a) := by
  rw [gs_eq f y U h, gs_eq (𝟙 X) (f y) U h]
  have := congrArg (fun q => q.hom a) (f.germ_stalkMap U y h)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  exact this.symm

def IsSecOver {X : Scheme.{0}} (L : LB X) (W : X.Opens) (s : ∀ k, Γ(X, W ⊓ L.U k)) : Prop :=
  ∀ (z : X) (k k' : L.ι), z ∈ W → z ∈ L.U k → z ∈ L.U k' →
    gs (𝟙 X) z (W ⊓ L.U k) (s k) =
      (gm (𝟙 X) z (L.U k ⊓ L.U k') (L.g k k') : X.presheaf.stalk z) * gs (𝟙 X) z (W ⊓ L.U k') (s k')

def SecCarriedOver {X : Scheme.{0}} (L : LB X) (W : X.Opens) (s : ∀ k, Γ(X, W ⊓ L.U k)) (f : X ⟶ X)
    (w : LB.Iso L (L.pull f)) : Prop :=
  ∀ (z : X) (j k : L.ι), z ∈ W → f z ∈ W → z ∈ L.U k → f z ∈ L.U j →
    gs f z (W ⊓ L.U j) (s j) = (gw w (𝟙 X) z j k : X.presheaf.stalk z) * gs (𝟙 X) z (W ⊓ L.U k) (s k)

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartExpOn
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumMult

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

def ChartExpOn (U : UnifPre I D A G) (e k : ℕ) (i' : Fin 1 → U.LG.L.ι) (W : (thickObj R I e G).left.Opens)
    (g : Γ((thickObj R I e G).left, W)) (f : ∀ α : D.toPre.X, D.toPre.SecB k α) : Prop :=
  ∃ S : Finset D.toPre.X,
    (∀ α ∉ S, ∀ j : Fin 4 → D.toPre.P.L.ι, ((U.gt e).pG.left.app _).hom ((f α).f j) = 0) ∧
    ∀ (p : (PUnit.{1} → D.toPre.P.L.ι) × (PUnit.{1} → U.LG.L.ι))
      (jf jt : D.toPre.X → Fin 4 → D.toPre.P.L.ι),
      i' 0 = p.2 PUnit.unit →
      CohAll D.toPre.P.L
        (Sum.elim (fun _ : PUnit.{1} => (U.gt e).pG.left)
          (Sum.elim (fun a : S × Fin 4 => (U.gt e).pG.left ≫ D.toPre.famφB a.1.1 a.2)
            (fun a : S × Fin 4 => D.toPre.Oφ (U.gt e).pG a.1.1 a.2)))
        (Sum.elim (fun _ => p.1 PUnit.unit)
          (Sum.elim (fun a : S × Fin 4 => jf a.1.1 a.2) (fun a : S × Fin 4 => jt a.1.1 a.2))) →
      (res ((inf_le_left.trans inf_le_left).trans inf_le_left :
          U.expW e p i' S jf jt ⊓ W ≤ (LB.div (D.toPre.P.L.pull (U.gt e).pG.left)
            (U.LG.L.pull (fstG I e G).left)).U p) ((U.w e).s p)).val ^ k *
        ((thickObj R I e G).left.presheaf.map (homOfLE (inf_le_right :
          U.expW e p i' S jf jt ⊓ W ≤ W)).op).hom g =
      ∑ α ∈ S.attach,
        ((thickObj R I e G).left.presheaf.map
            (homOfLE (inf_le_left.trans (U.expW_le_f e p i' jf jt α.2))).op).hom
            (((U.gt e).pG.left.app _).hom ((f α.1).f (jf α.1))) *
          (res (inf_le_left.trans (U.expWeight_le_chart_weight e p i' jf jt α.2)) (((U.gt e).t α.1).s (jt α.1))).val

end GlobalTheory.MumMult
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondenceUniquePoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondenceUniquePoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

namespace GlobalTheory.Mum.TensTor

theorem gtRelV_unique : ∀ (F : Type) [Field F] (N N' : NumD F) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F), TensFacts W φ e wv → ∀ (v' u' : N'.Gt) (vs : Fin r → N.Gt), GtRelV W φ e wv v' vs → GtRelV W φ e wv u' vs → v' = u' := by
  intro F _ N N' r W φ e wv hT v' u' vs hv hu
  obtain ⟨-, hφ, -, -, -, hw, -⟩ := hT
  obtain ⟨hv1, hv2⟩ := hv
  obtain ⟨hu1, hu2⟩ := hu
  have hb : v'.b = u'.b := hφ.1 (funext fun j => (hv1 j).trans (hu1 j).symm)
  refine NumD.Gt.ext hb (funext fun χ' => ?_)
  have h1 := hv2 χ'
  have h2 := hu2 χ'
  rw [← hb] at h2
  have hne : wv (N'.c χ') * wv v'.b ≠ 0 := mul_ne_zero (hw _) (hw _)
  apply Units.ext
  apply mul_right_cancel₀ hne
  rw [← _root_.mul_assoc, ← _root_.mul_assoc, h1, h2]

end GlobalTheory.Mum.TensTor
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondenceUniquePointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorTorusValueCorrespondence_unique_point : ∀ (F : Type) [Field F] (N N' : NumD F) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F), TensFacts W φ e wv → ∀ (v' u' : N'.Gt) (vs : Fin r → N.Gt), GtRelV W φ e wv v' vs → GtRelV W φ e wv u' vs → v' = u' := by
  first | exact @GlobalTheory.Mum.TensTor.gtRelV_unique | exact GlobalTheory.Mum.TensTor.gtRelV_unique | (intros; apply GlobalTheory.Mum.TensTor.gtRelV_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkOfInjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum

def stalkOf {W : Type} [CommRing W] (z : Sp W) : W →+* (Sp W).presheaf.stalk z :=
  ((Sp W).presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom

theorem stalkOf_injective {W : Type} [CommRing W] [IsDomain W] (z : Sp W) : Function.Injective (stalkOf z) :=
  (germ_injective_of_isIntegral (Sp W) (U := ⊤) z trivial).comp
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of W)).inv).1

abbrev unitW {W : Type} [CommRing W] (G : Over (Sp W)) [GrpObj G] : Sp W ⟶ G.left := eSec G

abbrev idW (W : Type) [CommRing W] : Sp W ⟶ (𝟙_ (Over (Sp W))).left := 𝟙 (Sp W)

end GlobalTheory.Mum
end
end

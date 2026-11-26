module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.IwasawaUnitaryAdelic.IUAIwa
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieAlgebraOfExpLocal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExpansionEqZeroIffCoeffsMem

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalExpProductDecomposition
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalExpProductDecomposition
open Matrix Topology Filter

noncomputable section

namespace GlobalTheory.CompanionTheory.ClosedSubgroup

section Banach

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [FiniteDimensional ℝ A]

theorem exists_proj_sup {E : Type*} [AddCommGroup E] [Module ℝ E] (𝔨 𝔟 : Submodule ℝ E) :
    ∃ p q : E →ₗ[ℝ] E, (∀ Z, p Z ∈ 𝔨) ∧ (∀ Z, q Z ∈ 𝔟) ∧
      ∀ Z, Z - p Z - q Z ∈ 𝔨 ⊔ 𝔟 → Z - p Z - q Z = 0 := by
  let f : (𝔨 × 𝔟) →ₗ[ℝ] E := 𝔨.subtype.coprod 𝔟.subtype
  have hr : LinearMap.range f = 𝔨 ⊔ 𝔟 := by
    simp [f, LinearMap.range_coprod]
  obtain ⟨s, hs⟩ := f.rangeRestrict.exists_rightInverse_of_surjective (LinearMap.range_rangeRestrict f)
  obtain ⟨P, hP⟩ := (LinearMap.range f).subtype.exists_leftInverse_of_injective (by simp)
  have hsum : ∀ Z, ((s (P Z)).1 : E) + ((s (P Z)).2 : E) = (P Z : E) := by
    intro Z
    have h2 := LinearMap.congr_fun hs (P Z)
    have h3 := congrArg Subtype.val h2
    simpa [f] using h3
  refine ⟨𝔨.subtype ∘ₗ LinearMap.fst ℝ 𝔨 𝔟 ∘ₗ s ∘ₗ P, 𝔟.subtype ∘ₗ LinearMap.snd ℝ 𝔨 𝔟 ∘ₗ s ∘ₗ P,
    fun Z => (s (P Z)).1.2, fun Z => (s (P Z)).2.2, fun Z hZ => ?_⟩
  have hid : ∀ W (hW : W ∈ LinearMap.range f), P W = ⟨W, hW⟩ := fun W hW =>
    LinearMap.congr_fun hP ⟨W, hW⟩
  have hval : Z - ((s (P Z)).1 : E) - ((s (P Z)).2 : E) = Z - (P Z : E) := by
    rw [sub_sub, hsum]
  change Z - ((s (P Z)).1 : E) - ((s (P Z)).2 : E) = 0
  change Z - ((s (P Z)).1 : E) - ((s (P Z)).2 : E) ∈ 𝔨 ⊔ 𝔟 at hZ
  rw [hval] at hZ ⊢
  rw [← hr] at hZ
  have h1 := hid _ hZ
  have h2 : P (Z - (P Z : E)) = P Z - P (P Z : E) := map_sub _ _ _
  have h3 : P (P Z : E) = P Z := hid _ (P Z).2
  rw [h3, sub_self] at h2
  have h4 := congrArg Subtype.val (h1.symm.trans h2)
  simpa using h4

theorem eventually_exp_mul_exp {G : Set A} (hmul : ∀ g ∈ G, ∀ h ∈ G, g * h ∈ G)
    {𝔤 𝔨 𝔟 : Submodule ℝ A} (h𝔤 : ∀ X, X ∈ 𝔤 ↔ ∀ t : ℝ, NormedSpace.exp (t • X) ∈ G)
    {V : Set A} (hV : V ∈ 𝓝 (0 : A)) (hVG : ∀ X ∈ V, NormedSpace.exp X ∈ G → X ∈ 𝔤)
    (hk : 𝔨 ≤ 𝔤) (hb : 𝔟 ≤ 𝔤) (hg : 𝔤 ≤ 𝔨 ⊔ 𝔟) :
    ∀ᶠ g in 𝓝 (1 : A), g ∈ G → ∃ X ∈ 𝔨, ∃ Y ∈ 𝔟, g = NormedSpace.exp X * NormedSpace.exp Y := by
  haveI : CompleteSpace A := FiniteDimensional.complete ℝ A
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  obtain ⟨p₀, q₀, hpk, hqb, hr0⟩ := exists_proj_sup 𝔨 𝔟
  let p : A →L[ℝ] A := LinearMap.toContinuousLinearMap p₀
  let q : A →L[ℝ] A := LinearMap.toContinuousLinearMap q₀
  let r : A →L[ℝ] A := ContinuousLinearMap.id ℝ A - p - q
  have hr : ∀ Z, r Z = Z - p Z - q Z := fun Z => rfl
  let Φ : A → A := fun Z =>
    NormedSpace.exp (p Z) * NormedSpace.exp (q Z) * NormedSpace.exp (r Z)
  have hE : HasStrictFDerivAt (NormedSpace.exp : A → A) (1 : A →L[ℝ] A) 0 :=
    hasStrictFDerivAt_exp_zero
  have hEl : ∀ l : A →L[ℝ] A, HasStrictFDerivAt (fun Z => NormedSpace.exp (l Z)) l (0 : A) := by
    intro l
    have h2 : HasStrictFDerivAt (NormedSpace.exp : A → A) (1 : A →L[ℝ] A) (l 0) := by
      simpa using hE
    exact (h2.comp (0 : A) l.hasStrictFDerivAt).congr_fderiv (ContinuousLinearMap.ext fun _ => rfl)
  have hΦ : HasStrictFDerivAt Φ ((ContinuousLinearEquiv.refl ℝ A : A ≃L[ℝ] A) : A →L[ℝ] A) 0 := by
    have h2 : HasStrictFDerivAt Φ _ 0 := ((hEl p).mul' (hEl q)).mul' (hEl r)
    refine h2.congr_fderiv (ContinuousLinearMap.ext fun Z => ?_)
    simp [hr]
    abel
  have hΦ0 : Φ 0 = 1 := by simp [Φ]
  have hmap := hΦ.map_nhds_eq_of_equiv
  have hW' : r ⁻¹' V ∈ 𝓝 (0 : A) := by
    refine r.continuous.continuousAt.preimage_mem_nhds ?_
    simpa using hV
  have himg : Φ '' (r ⁻¹' V) ∈ 𝓝 (1 : A) := by
    rw [← hΦ0, ← hmap]
    exact image_mem_map hW'
  have hneg : ∀ X ∈ 𝔤, NormedSpace.exp (-X) ∈ G := by
    intro X hX
    simpa using (h𝔤 X).1 hX (-1)
  have hcancel : ∀ X : A, NormedSpace.exp (-X) * NormedSpace.exp X = 1 := by
    intro X
    rw [← NormedSpace.exp_add_of_commute (Commute.neg_left (Commute.refl X)), neg_add_cancel,
      NormedSpace.exp_zero]
  filter_upwards [himg]
  rintro g ⟨Z, hZ, rfl⟩ hgG
  have hpg : p Z ∈ 𝔤 := hk (hpk Z)
  have hqg : q Z ∈ 𝔤 := hb (hqb Z)
  have hrG : NormedSpace.exp (r Z) ∈ G := by
    have h2 := hmul _ (hneg _ hqg) _ (hmul _ (hneg _ hpg) _ hgG)
    have h3 : NormedSpace.exp (-(q Z)) * (NormedSpace.exp (-(p Z)) * Φ Z) = NormedSpace.exp (r Z) := by
      simp only [Φ]
      rw [← mul_assoc (NormedSpace.exp (-(p Z))), ← mul_assoc (NormedSpace.exp (-(p Z))), hcancel,
        one_mul, ← mul_assoc, hcancel, one_mul]
    rwa [h3] at h2
  have hr𝔤 : r Z ∈ 𝔨 ⊔ 𝔟 := hg (hVG _ hZ hrG)
  have hrz : r Z = 0 := hr0 Z hr𝔤
  refine ⟨p Z, hpk Z, q Z, hqb Z, ?_⟩
  simp [Φ, hrz]

end Banach

theorem eventually_exp_mul_exp_of_isLinRed {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hG : GlobalTheory.LinRed.IsLinRed G) (𝔤 𝔨 𝔟 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (h𝔤 : ∀ X, X ∈ 𝔤 ↔ ∀ t : ℝ, NormedSpace.exp (t • X) ∈ G)
    (hV : ∃ V ∈ 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ), ∀ X ∈ V, NormedSpace.exp X ∈ G → X ∈ 𝔤)
    (hk : 𝔨 ≤ 𝔤) (hb : 𝔟 ≤ 𝔤) (hg : 𝔤 ≤ 𝔨 ⊔ 𝔟) :
    ∀ᶠ g in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), g ∈ G →
      ∃ X ∈ 𝔨, ∃ Y ∈ 𝔟, g = NormedSpace.exp X * NormedSpace.exp Y := by
  obtain ⟨V, hV, hVG⟩ := hV
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.instL2OpNormedRing
  letI : NormedSpace ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.instL2OpNormedSpace
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.instL2OpNormedAlgebra
  letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    { (inferInstance : Algebra ℝ (Matrix (Fin n) (Fin n) ℂ)) with
      norm_smul_le := fun t X => by
        have : t • X = (t : ℂ) • X := by ext a b; simp
        rw [this, norm_smul]
        simp }
  exact eventually_exp_mul_exp hG.mul_mem h𝔤 hV hVG hk hb hg

end GlobalTheory.CompanionTheory.ClosedSubgroup
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalExpProductDecompositionStatement
open Matrix Topology Filter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_exp_product_decomposition : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)}, GlobalTheory.LinRed.IsLinRed G → ∀ 𝔤 𝔨 𝔟 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ), (∀ X, X ∈ 𝔤 ↔ ∀ t : ℝ, NormedSpace.exp (t • X) ∈ G) → (∃ V ∈ 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ), ∀ X ∈ V, NormedSpace.exp X ∈ G → X ∈ 𝔤) → 𝔨 ≤ 𝔤 → 𝔟 ≤ 𝔤 → 𝔤 ≤ 𝔨 ⊔ 𝔟 → ∀ᶠ g in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), g ∈ G → ∃ X ∈ 𝔨, ∃ Y ∈ 𝔟, g = NormedSpace.exp X * NormedSpace.exp Y := by
  first | exact @GlobalTheory.CompanionTheory.ClosedSubgroup.eventually_exp_mul_exp_of_isLinRed | exact GlobalTheory.CompanionTheory.ClosedSubgroup.eventually_exp_mul_exp_of_isLinRed | (intros; apply GlobalTheory.CompanionTheory.ClosedSubgroup.eventually_exp_mul_exp_of_isLinRed <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CartanLocalToGlobal
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CartanLocalToGlobal
open Matrix Topology Filter

namespace GlobalTheory.CompanionTheory.LinRedFactor

open GlobalTheory.LinRed

variable {n : ℕ}

theorem isCompact_unitary_fin :
    IsCompact (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) := by
  have hc : IsCompact (Set.pi Set.univ fun _ : Fin n =>
      Set.pi Set.univ fun _ : Fin n => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine IsCompact.of_isClosed_subset (t := _) hc ?_ ?_
  · have : (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) =
        {A | A * Aᴴ = 1} := by
      ext A; exact Matrix.mem_unitaryGroup_iff
    rw [this]
    exact isClosed_eq (continuous_id.matrix_mul continuous_id.matrix_conjTranspose)
      continuous_const
  · intro A hA i _ j _
    simpa using entry_norm_bound_of_unitary hA i j

theorem unitary_mul_star {U : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) : U * Uᴴ = 1 :=
  Matrix.mem_unitaryGroup_iff.1 hU

theorem star_mul_unitary {U : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) : Uᴴ * U = 1 :=
  Matrix.mem_unitaryGroup_iff'.1 hU

theorem conj_mul_conj {U : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (s t : Matrix (Fin n) (Fin n) ℂ) :
    (Uᴴ * s * U) * (Uᴴ * t * U) = Uᴴ * (s * t) * U := by
  calc (Uᴴ * s * U) * (Uᴴ * t * U) = Uᴴ * s * (U * Uᴴ) * t * U := by
        simp only [Matrix.mul_assoc]
    _ = Uᴴ * (s * t) * U := by
        rw [unitary_mul_star hU]; simp only [Matrix.mul_one, Matrix.mul_assoc]

theorem tri_mul {U s t : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hs : (Uᴴ * s * U).BlockTriangular id) (ht : (Uᴴ * t * U).BlockTriangular id) :
    (Uᴴ * (s * t) * U).BlockTriangular id := by
  rw [← conj_mul_conj hU]
  exact hs.mul ht

theorem isClosed_tri (U : Matrix (Fin n) (Fin n) ℂ) :
    IsClosed {s : Matrix (Fin n) (Fin n) ℂ | (Uᴴ * s * U).BlockTriangular id} := by
  simp only [Matrix.BlockTriangular, Set.setOf_forall]
  refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => ?_
  exact isClosed_eq
    (((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_elem i j)
    continuous_const

theorem isCompact_maxCpt {G : Set (Matrix (Fin n) (Fin n) ℂ)} (hG : IsLinRed G) :
    IsCompact (maxCpt G) := by
  refine isCompact_unitary_fin.of_isClosed_subset ?_ Set.inter_subset_right
  refine isClosed_of_closure_subset fun x hx => ?_
  have hxU : x ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) :=
    closure_minimal Set.inter_subset_right isCompact_unitary_fin.isClosed hx
  exact ⟨hG.closed x (IsUnit.of_mul_eq_one _ (unitary_mul_star hxU))
    (closure_mono Set.inter_subset_left hx), hxU⟩

def Good (G : Set (Matrix (Fin n) (Fin n) ℂ)) (U g : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ k ∈ maxCpt G, ∃ s ∈ G, g = k * s ∧ (Uᴴ * s * U).BlockTriangular id

theorem good_nhds {G : Set (Matrix (Fin n) (Fin n) ℂ)} (hG : IsLinRed G)
    {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (h : ∀ᶠ g in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), g ∈ G → Good G U g)
    {g₀ : Matrix (Fin n) (Fin n) ℂ} (h₀ : Good G U g₀) :
    ∀ᶠ g in 𝓝 g₀, g ∈ G → Good G U g := by
  obtain ⟨k₀, hk₀, s₀, hs₀, rfl, ht₀⟩ := h₀
  have hkk : k₀ * k₀ᴴ = 1 := unitary_mul_star hk₀.2
  have hkk' : k₀ᴴ * k₀ = 1 := star_mul_unitary hk₀.2
  have hsu : IsUnit s₀ := hG.isUnit s₀ hs₀
  have hss : s₀ * s₀⁻¹ = 1 := Matrix.mul_nonsing_inv s₀ ((Matrix.isUnit_iff_isUnit_det s₀).1 hsu)
  have hss' : s₀⁻¹ * s₀ = 1 := Matrix.nonsing_inv_mul s₀ ((Matrix.isUnit_iff_isUnit_det s₀).1 hsu)
  have hφ : Continuous fun g : Matrix (Fin n) (Fin n) ℂ => k₀ᴴ * g * s₀⁻¹ :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have e : k₀ᴴ * (k₀ * s₀) * s₀⁻¹ = 1 := by
    rw [← Matrix.mul_assoc, hkk', Matrix.one_mul, hss]
  have ht : Tendsto (fun g : Matrix (Fin n) (Fin n) ℂ => k₀ᴴ * g * s₀⁻¹) (𝓝 (k₀ * s₀)) (𝓝 1) := by
    have := hφ.tendsto (k₀ * s₀)
    rwa [e] at this
  filter_upwards [ht.eventually h] with g hg hgG
  obtain ⟨k₁, hk₁, s₁, hs₁, e₁, t₁⟩ :=
    hg (hG.mul_mem _ (hG.mul_mem _ (hG.star_mem _ hk₀.1) _ hgG) _ (hG.inv_mem _ hs₀))
  refine ⟨k₀ * k₁, ⟨hG.mul_mem _ hk₀.1 _ hk₁.1, mul_mem hk₀.2 hk₁.2⟩, s₁ * s₀,
    hG.mul_mem _ hs₁ _ hs₀, ?_, tri_mul hU t₁ ht₀⟩
  calc g = k₀ * (k₀ᴴ * g * s₀⁻¹) * s₀ := by
        calc g = (k₀ * k₀ᴴ) * g * (s₀⁻¹ * s₀) := by
              rw [hkk, hss', Matrix.one_mul, Matrix.mul_one]
          _ = k₀ * (k₀ᴴ * g * s₀⁻¹) * s₀ := by simp only [Matrix.mul_assoc]
    _ = k₀ * k₁ * (s₁ * s₀) := by
        rw [e₁]; simp only [Matrix.mul_assoc]

theorem isClosed_factor {G : Set (Matrix (Fin n) (Fin n) ℂ)} (hG : IsLinRed G)
    (U : Matrix (Fin n) (Fin n) ℂ) :
    IsClosed {g : Matrix (Fin n) (Fin n) ℂ |
      ∃ k ∈ maxCpt G, (Uᴴ * (kᴴ * g) * U).BlockTriangular id} := by
  haveI : CompactSpace (maxCpt G) := isCompact_iff_compactSpace.1 (isCompact_maxCpt hG)
  have hC : IsClosed {p : maxCpt G × Matrix (Fin n) (Fin n) ℂ |
      (Uᴴ * ((p.1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * p.2) * U).BlockTriangular id} :=
    (isClosed_tri U).preimage
      ((continuous_subtype_val.comp continuous_fst).matrix_conjTranspose.matrix_mul continuous_snd)
  have := isClosedMap_snd_of_compactSpace _ hC
  convert this using 1
  ext g
  constructor
  · rintro ⟨k, hk, t⟩
    exact ⟨(⟨k, hk⟩, g), t, rfl⟩
  · rintro ⟨⟨k, g'⟩, t, rfl⟩
    exact ⟨k.1, k.2, t⟩

theorem good_iff {G : Set (Matrix (Fin n) (Fin n) ℂ)} (hG : IsLinRed G)
    {U g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ G) :
    Good G U g ↔ ∃ k ∈ maxCpt G, (Uᴴ * (kᴴ * g) * U).BlockTriangular id := by
  constructor
  · rintro ⟨k, hk, s, _, rfl, t⟩
    refine ⟨k, hk, ?_⟩
    rwa [← Matrix.mul_assoc kᴴ, star_mul_unitary hk.2, Matrix.one_mul]
  · rintro ⟨k, hk, t⟩
    refine ⟨k, hk, kᴴ * g, hG.mul_mem _ (hG.star_mem _ hk.1) _ hg, ?_, t⟩
    rw [← Matrix.mul_assoc, unitary_mul_star hk.2, Matrix.one_mul]

theorem factor_of_local : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)}, GlobalTheory.LinRed.IsLinRed G →
    ∀ U ∈ Matrix.unitaryGroup (Fin n) ℂ,
    (∀ᶠ g in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), g ∈ G →
      ∃ k ∈ GlobalTheory.LinRed.maxCpt G, ∃ s ∈ G, g = k * s ∧ (Uᴴ * s * U).BlockTriangular id) →
    ∀ g ∈ G, ∃ k ∈ GlobalTheory.LinRed.maxCpt G, ∃ s ∈ G, g = k * s ∧ (Uᴴ * s * U).BlockTriangular id := by
  intro n G hG U hU h g hg
  haveI : PreconnectedSpace G := isPreconnected_iff_preconnectedSpace.1 hG.connected
  have hclosed : IsClosed {x : G | Good G U x.1} := by
    have e : {x : G | Good G U x.1} = Subtype.val ⁻¹' {g : Matrix (Fin n) (Fin n) ℂ |
        ∃ k ∈ maxCpt G, (Uᴴ * (kᴴ * g) * U).BlockTriangular id} := by
      ext x
      exact good_iff hG x.2
    rw [e]
    exact (isClosed_factor hG U).preimage continuous_subtype_val
  have hopen : IsOpen {x : G | Good G U x.1} := by
    rw [isOpen_iff_eventually]
    intro x hx
    have := (continuous_subtype_val.tendsto x).eventually (good_nhds hG hU h hx)
    filter_upwards [this] with y hy using hy y.2
  have hone : Good G U 1 := by
    refine ⟨1, ⟨hG.one_mem, one_mem _⟩, 1, hG.one_mem, by simp, ?_⟩
    rw [Matrix.mul_one, star_mul_unitary hU]
    exact Matrix.blockTriangular_one
  have huniv := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨⟨1, hG.one_mem⟩, hone⟩
  have hmem : (⟨g, hg⟩ : G) ∈ {x : G | Good G U x.1} := huniv ▸ Set.mem_univ _
  exact hmem

end GlobalTheory.CompanionTheory.LinRedFactor
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CartanLocalToGlobalStatement
open Matrix Topology Filter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartan_local_to_global : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)}, GlobalTheory.LinRed.IsLinRed G → ∀ U ∈ Matrix.unitaryGroup (Fin n) ℂ, (∀ᶠ g in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), g ∈ G → ∃ k ∈ GlobalTheory.LinRed.maxCpt G, ∃ s ∈ G, g = k * s ∧ (Uᴴ * s * U).BlockTriangular id) → ∀ g ∈ G, ∃ k ∈ GlobalTheory.LinRed.maxCpt G, ∃ s ∈ G, g = k * s ∧ (Uᴴ * s * U).BlockTriangular id := by
  first | exact @GlobalTheory.CompanionTheory.LinRedFactor.factor_of_local | exact GlobalTheory.CompanionTheory.LinRedFactor.factor_of_local | (intros; apply GlobalTheory.CompanionTheory.LinRedFactor.factor_of_local <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CartanDecompositionLieAlgebra
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CartanDecompositionLieAlgebra
open Matrix Topology Filter

namespace GlobalTheory.CompanionTheory.IwasawaGen

theorem skew_add_upper {n : ℕ} (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (h : Fin n → ℝ)
    (hanti : Antitone h)
    (hf : ∀ (f : ℝ → ℝ), ∀ X ∈ 𝔤, (Matrix.of fun i j => (f (h i - h j) : ℂ) * X i j) ∈ 𝔤)
    (hstar : ∀ X ∈ 𝔤, Xᴴ ∈ 𝔤)
    (hreg : ∀ Y ∈ 𝔤, Yᴴ = Y → Matrix.diagonal (fun i => (h i : ℂ)) * Y =
      Y * Matrix.diagonal (fun i => (h i : ℂ)) → Y.IsDiag) :
    ∀ X ∈ 𝔤, ∃ A ∈ 𝔤, ∃ B ∈ 𝔤, X = A + B ∧ Aᴴ = -A ∧ B.BlockTriangular id := by
  intro X hX
  obtain ⟨P, hP, P_ent⟩ : ∃ P ∈ 𝔤, ∀ i j, P i j = if h j < h i then X i j else 0 := by
    refine ⟨_, hf (fun t => if 0 < t then 1 else 0) X hX, fun i j => ?_⟩
    by_cases hij : h j < h i
    · simp [hij]
    · simp [hij]
  obtain ⟨Z, hZ, Z_ent⟩ : ∃ Z ∈ 𝔤, ∀ i j, Z i j = if h i = h j then X i j else 0 := by
    refine ⟨_, hf (fun t => if t = 0 then 1 else 0) X hX, fun i j => ?_⟩
    by_cases hij : h i = h j
    · simp [hij]
    · simp [hij, sub_eq_zero]
  obtain ⟨M, hM, M_ent⟩ : ∃ M ∈ 𝔤, ∀ i j, M i j = if h i < h j then X i j else 0 := by
    refine ⟨_, hf (fun t => if t < 0 then 1 else 0) X hX, fun i j => ?_⟩
    by_cases hij : h i < h j
    · simp [hij]
    · simp [hij]
  have hsum : X = P + Z + M := by
    ext i j
    simp only [Matrix.add_apply, P_ent, Z_ent, M_ent]
    rcases lt_trichotomy (h i) (h j) with hij | hij | hij
    · simp [hij, hij.ne, not_lt.2 hij.le]
    · simp [hij]
    · simp [hij, hij.ne', not_lt.2 hij.le]
  set Y : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℝ) • (Z + Zᴴ) with hYdef
  have hY : Y ∈ 𝔤 := 𝔤.smul_mem _ (𝔤.add_mem hZ (hstar Z hZ))
  have Y_herm : Yᴴ = Y := by
    ext i j
    simp [hYdef, Matrix.conjTranspose_apply, add_comm]
  have Y_ent : ∀ i j, h i ≠ h j → Y i j = 0 := by
    intro i j hij
    simp [hYdef, Matrix.conjTranspose_apply, Z_ent, hij, hij.symm]
  have Y_comm : Matrix.diagonal (fun i => (h i : ℂ)) * Y =
      Y * Matrix.diagonal (fun i => (h i : ℂ)) := by
    ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hij : h i = h j
    · rw [hij, mul_comm]
    · rw [Y_ent i j hij]; simp
  have Y_diag : Y.IsDiag := hreg Y hY Y_herm Y_comm
  refine ⟨(1 / 2 : ℝ) • (Z - Zᴴ) + M - Mᴴ, ?_, P + Y + Mᴴ, ?_, ?_, ?_, ?_⟩
  · exact 𝔤.sub_mem (𝔤.add_mem (𝔤.smul_mem _ (𝔤.sub_mem hZ (hstar Z hZ))) hM) (hstar M hM)
  · exact 𝔤.add_mem (𝔤.add_mem hP hY) (hstar M hM)
  · have hZsplit : Z = (1 / 2 : ℝ) • (Z - Zᴴ) + Y := by
      rw [hYdef, ← smul_add]
      have : Z - Zᴴ + (Z + Zᴴ) = (2 : ℝ) • Z := by
        rw [two_smul]; abel
      rw [this, smul_smul]; norm_num
    calc X = P + Z + M := hsum
      _ = P + ((1 / 2 : ℝ) • (Z - Zᴴ) + Y) + M := by rw [← hZsplit]
      _ = (1 / 2 : ℝ) • (Z - Zᴴ) + M - Mᴴ + (P + Y + Mᴴ) := by abel
  · simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_conjTranspose, star_trivial]
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply]
    simp only [smul_eq_mul, Complex.real_smul, smul_sub]
    ring
  · intro i j hji
    have hji' : j < i := hji
    have hle : h i ≤ h j := hanti hji'.le
    have h1 : P i j = 0 := by
      rw [P_ent, if_neg (not_lt.2 hle)]
    have h2 : Y i j = 0 := Y_diag hji'.ne'
    have h3 : Mᴴ i j = 0 := by
      rw [Matrix.conjTranspose_apply, M_ent, if_neg (not_lt.2 hle)]; simp
    simp only [Matrix.add_apply, h1, h2, h3, add_zero]

end GlobalTheory.CompanionTheory.IwasawaGen
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CartanDecompositionLieAlgebraStatement
open Matrix Topology Filter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_skewHermitian_add_blockTriangular : ∀ {n : ℕ} (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (h : Fin n → ℝ), Antitone h → (∀ (f : ℝ → ℝ), ∀ X ∈ 𝔤, (Matrix.of fun i j => (f (h i - h j) : ℂ) * X i j) ∈ 𝔤) → (∀ X ∈ 𝔤, Xᴴ ∈ 𝔤) → (∀ Y ∈ 𝔤, Yᴴ = Y → Matrix.diagonal (fun i => (h i : ℂ)) * Y = Y * Matrix.diagonal (fun i => (h i : ℂ)) → Y.IsDiag) → ∀ X ∈ 𝔤, ∃ A ∈ 𝔤, ∃ B ∈ 𝔤, X = A + B ∧ Aᴴ = -A ∧ B.BlockTriangular id := by
  first | exact @GlobalTheory.CompanionTheory.IwasawaGen.skew_add_upper | exact GlobalTheory.CompanionTheory.IwasawaGen.skew_add_upper | (intros; apply GlobalTheory.CompanionTheory.IwasawaGen.skew_add_upper <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralizerRegularCommutes
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralizerRegularCommutes
open Matrix Topology Filter

namespace GlobalTheory.CompanionTheory.MatrixComm

theorem commute_diagonal_of_dominated {n : ℕ} (d e : Fin n → ℂ)
    (Z : Matrix (Fin n) (Fin n) ℂ) (hZ : Matrix.diagonal d * Z = Z * Matrix.diagonal d)
    (hde : ∀ i j, d i = d j → e i = e j) :
    Z * Matrix.diagonal e = Matrix.diagonal e * Z := by
  ext i j
  have hij := congrFun (congrFun hZ i) j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at hij
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hz : Z i j = 0
  · simp [hz]
  · have hd : d i = d j := by
      have : Z i j * d i = Z i j * d j := by rw [mul_comm (Z i j) (d i)]; exact hij
      exact mul_left_cancel₀ hz this
    rw [hde i j hd, mul_comm]

theorem commute_of_dominated_diag {n : ℕ} (U H A Y : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hH : (Uᴴ * H * U).IsDiag) (hA : (Uᴴ * A * U).IsDiag)
    (hdom : ∀ i j, (Uᴴ * H * U) i i = (Uᴴ * H * U) j j → (Uᴴ * A * U) i i = (Uᴴ * A * U) j j)
    (hHY : H * Y = Y * H) : Y * A = A * Y := by
  have h2 : U * Uᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp hU
    simpa [Matrix.star_eq_conjTranspose] using this
  have conj_mul : ∀ P Q : Matrix (Fin n) (Fin n) ℂ,
      (Uᴴ * P * U) * (Uᴴ * Q * U) = Uᴴ * (P * Q) * U := by
    intro P Q
    calc (Uᴴ * P * U) * (Uᴴ * Q * U) = Uᴴ * P * (U * Uᴴ) * Q * U := by
          simp only [Matrix.mul_assoc]
      _ = Uᴴ * (P * Q) * U := by
          rw [h2]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  have back : ∀ P : Matrix (Fin n) (Fin n) ℂ, U * (Uᴴ * P * U) * Uᴴ = P := by
    intro P
    calc U * (Uᴴ * P * U) * Uᴴ = (U * Uᴴ) * P * (U * Uᴴ) := by
          simp only [Matrix.mul_assoc]
      _ = P := by rw [h2]; simp
  have hcomm : (Uᴴ * H * U) * (Uᴴ * Y * U) = (Uᴴ * Y * U) * (Uᴴ * H * U) := by
    rw [conj_mul, conj_mul, hHY]
  have hdH : Matrix.diagonal (fun i => (Uᴴ * H * U) i i) = Uᴴ * H * U := hH.diagonal_diag
  have hdA : Matrix.diagonal (fun i => (Uᴴ * A * U) i i) = Uᴴ * A * U := hA.diagonal_diag
  have key := commute_diagonal_of_dominated (fun i => (Uᴴ * H * U) i i)
    (fun i => (Uᴴ * A * U) i i) (Uᴴ * Y * U) (by rw [hdH]; exact hcomm) hdom
  rw [hdA, conj_mul, conj_mul] at key
  have := congrArg (fun M => U * M * Uᴴ) key
  simpa only [back] using this

end GlobalTheory.CompanionTheory.MatrixComm
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralizerRegularCommutesStatement
open Matrix Topology Filter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralizer_regular_commutes : ∀ {n : ℕ} (U H A Y : Matrix (Fin n) (Fin n) ℂ), U ∈ Matrix.unitaryGroup (Fin n) ℂ → (Uᴴ * H * U).IsDiag → (Uᴴ * A * U).IsDiag → (∀ i j, (Uᴴ * H * U) i i = (Uᴴ * H * U) j j → (Uᴴ * A * U) i i = (Uᴴ * A * U) j j) → H * Y = Y * H → Y * A = A * Y := by
  first | exact @GlobalTheory.CompanionTheory.MatrixComm.commute_of_dominated_diag | exact GlobalTheory.CompanionTheory.MatrixComm.commute_of_dominated_diag | (intros; apply GlobalTheory.CompanionTheory.MatrixComm.commute_of_dominated_diag <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExpBlockTriangular
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExpBlockTriangular
open Matrix Topology Filter

namespace GlobalTheory.CompanionTheory.Unitary.ExpUpper


open scoped Matrix.Norms.L2Operator in
theorem blockTriangular_exp {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : T.BlockTriangular id) : (NormedSpace.exp T).BlockTriangular id := by
  have hmem : ∀ k : ℕ, ((k.factorial : ℂ)⁻¹ • T ^ k) ∈ Matrix.blockTriangularSubalgebra ℂ ℂ id := fun k =>
    Subalgebra.smul_mem _ (Subalgebra.pow_mem _ ((Matrix.mem_blockTriangularSubalgebra).mpr hT) k) _

  refine (isClosed_setOfPred_blockTriangular (b := id)).mem_of_tendsto
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (x := T)) (Filter.Eventually.of_forall fun s => ?_)
  exact (Matrix.mem_blockTriangularSubalgebra).mp (Subalgebra.sum_mem _ fun k _ => hmem k)

theorem blockTriangular_conj_exp {n : ℕ} (U Y : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (h : (Uᴴ * Y * U).BlockTriangular id) :
    (Uᴴ * NormedSpace.exp Y * U).BlockTriangular id := by
  have hUU : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hUU' : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have hunit : IsUnit U := ⟨⟨U, Uᴴ, hUU', hUU⟩, rfl⟩
  have hinv : U⁻¹ = Uᴴ := Matrix.inv_eq_left_inv hUU
  rw [← hinv, ← Matrix.exp_conj' U Y hunit]
  exact GlobalTheory.CompanionTheory.Unitary.ExpUpper.blockTriangular_exp _ (hinv ▸ h)

end GlobalTheory.CompanionTheory.Unitary.ExpUpper
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExpBlockTriangularStatement
open Matrix Topology Filter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exp_block_triangular : ∀ {n : ℕ} (U Y : Matrix (Fin n) (Fin n) ℂ), U ∈ Matrix.unitaryGroup (Fin n) ℂ → (Uᴴ * Y * U).BlockTriangular id → (Uᴴ * NormedSpace.exp Y * U).BlockTriangular id := by
  first | exact @GlobalTheory.CompanionTheory.Unitary.ExpUpper.blockTriangular_conj_exp | exact GlobalTheory.CompanionTheory.Unitary.ExpUpper.blockTriangular_conj_exp | (intros; apply GlobalTheory.CompanionTheory.Unitary.ExpUpper.blockTriangular_conj_exp <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRegularElementAbelian
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRegularElementAbelian
open Matrix Topology Filter

namespace GlobalTheory.CompanionTheory.IwaGen

theorem exists_regular_point : ∀ {n : ℕ} (𝔞 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (U : Matrix (Fin n) (Fin n) ℂ), ∃ H ∈ 𝔞, ∀ i j, (Uᴴ * H * U) i i = (Uᴴ * H * U) j j →
      ∀ A ∈ 𝔞, (Uᴴ * A * U) i i = (Uᴴ * A * U) j j := by
  classical
  intro n 𝔞 U
  let L : Fin n × Fin n → (↥𝔞 →ₗ[ℝ] ℂ) := fun p =>
    { toFun := fun A => (Uᴴ * (A : Matrix (Fin n) (Fin n) ℂ) * U) p.1 p.1
        - (Uᴴ * (A : Matrix (Fin n) (Fin n) ℂ) * U) p.2 p.2
      map_add' := by
        intro A B
        simp only [Submodule.coe_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
        ring
      map_smul' := by
        intro c A
        simp only [Submodule.coe_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply,
          RingHom.id_apply, smul_sub] }
  have hL : ∀ (p : Fin n × Fin n) (A : ↥𝔞), L p A =
      (Uᴴ * (A : Matrix (Fin n) (Fin n) ℂ) * U) p.1 p.1
        - (Uᴴ * (A : Matrix (Fin n) (Fin n) ℂ) * U) p.2 p.2 := fun _ _ => rfl
  let s : Finset (Submodule ℝ ↥𝔞) :=
    (Finset.univ.image fun p => LinearMap.ker (L p)).erase ⊤
  have hs : (⊤ : Submodule ℝ ↥𝔞) ∉ s := Finset.notMem_erase _ _
  obtain ⟨H, hH⟩ := (Set.ne_univ_iff_exists_notMem _).1
    (Subspace.biUnion_ne_univ_of_top_notMem hs)
  refine ⟨H, H.2, fun i j hij A hA => ?_⟩
  have hker : H ∈ LinearMap.ker (L (i, j)) := by
    rw [LinearMap.mem_ker, hL]
    exact sub_eq_zero.2 hij
  have htop : LinearMap.ker (L (i, j)) = ⊤ := by
    by_contra hne
    apply hH
    refine Set.mem_biUnion (x := LinearMap.ker (L (i, j))) ?_ hker
    exact Finset.mem_coe.2 (Finset.mem_erase.2
      ⟨hne, Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩⟩)
  have hA' : (⟨A, hA⟩ : ↥𝔞) ∈ LinearMap.ker (L (i, j)) := by
    rw [htop]
    exact Submodule.mem_top
  rw [LinearMap.mem_ker, hL] at hA'
  exact sub_eq_zero.1 hA'

end GlobalTheory.CompanionTheory.IwaGen
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRegularElementAbelianStatement
open Matrix Topology Filter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_regular_element_abelian : ∀ {n : ℕ} (𝔞 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (U : Matrix (Fin n) (Fin n) ℂ), ∃ H ∈ 𝔞, ∀ i j, (Uᴴ * H * U) i i = (Uᴴ * H * U) j j → ∀ A ∈ 𝔞, (Uᴴ * A * U) i i = (Uᴴ * A * U) j j := by
  first | exact @GlobalTheory.CompanionTheory.IwaGen.exists_regular_point | exact GlobalTheory.CompanionTheory.IwaGen.exists_regular_point | (intros; apply GlobalTheory.CompanionTheory.IwaGen.exists_regular_point <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieAlgebraFunctionCalculus
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieAlgebraFunctionCalculus
open Matrix Topology Filter

namespace GlobalTheory.CompanionTheory.AdProj

noncomputable def entryMul {n : ℕ} (h : Fin n → ℝ) (g : ℝ → ℝ)
    (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => (g (h i - h j) : ℂ) * X i j

theorem diagonal_commutator {n : ℕ} (h : Fin n → ℝ) (X : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.diagonal (fun i => (h i : ℂ)) * X - X * Matrix.diagonal (fun i => (h i : ℂ))
      = entryMul h (fun t => t) X := by
  ext i j
  simp only [entryMul, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply]
  push_cast
  ring

theorem entryMul_pow_mem {n : ℕ} (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (h : Fin n → ℝ)
    (hD : Matrix.diagonal (fun i => (h i : ℂ)) ∈ 𝔤)
    (hbr : ∀ X ∈ 𝔤, ∀ Y ∈ 𝔤, X * Y - Y * X ∈ 𝔤)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ 𝔤) (k : ℕ) :
    entryMul h (fun t => t ^ k) X ∈ 𝔤 := by
  induction k with
  | zero =>
    have h0 : entryMul h (fun t => t ^ 0) X = X := by
      ext i j
      simp [entryMul]
    rw [h0]
    exact hX
  | succ k ih =>
    have hs : entryMul h (fun t => t ^ (k + 1)) X =
        Matrix.diagonal (fun i => (h i : ℂ)) * entryMul h (fun t => t ^ k) X -
          entryMul h (fun t => t ^ k) X * Matrix.diagonal (fun i => (h i : ℂ)) := by
      rw [diagonal_commutator]
      ext i j
      simp only [entryMul, Matrix.of_apply]
      push_cast
      ring
    rw [hs]
    exact hbr _ hD _ ih

theorem entryMul_poly_mem {n : ℕ} (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (h : Fin n → ℝ)
    (hD : Matrix.diagonal (fun i => (h i : ℂ)) ∈ 𝔤)
    (hbr : ∀ X ∈ 𝔤, ∀ Y ∈ 𝔤, X * Y - Y * X ∈ 𝔤)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ 𝔤) (p : Polynomial ℝ) :
    entryMul h (fun t => p.eval t) X ∈ 𝔤 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have hs : entryMul h (fun t => (p + q).eval t) X =
        entryMul h (fun t => p.eval t) X + entryMul h (fun t => q.eval t) X := by
      ext i j
      simp only [entryMul, Matrix.of_apply, Matrix.add_apply, Polynomial.eval_add]
      push_cast
      ring
    rw [hs]
    exact 𝔤.add_mem hp hq
  | monomial m a =>
    have hs : entryMul h (fun t => (Polynomial.monomial m a).eval t) X =
        a • entryMul h (fun t => t ^ m) X := by
      ext i j
      simp only [entryMul, Matrix.of_apply, Matrix.smul_apply, Polynomial.eval_monomial,
        Complex.real_smul]
      push_cast
      ring
    rw [hs]
    exact 𝔤.smul_mem a (entryMul_pow_mem 𝔤 h hD hbr hX m)

theorem mem_of_entrywise {n : ℕ} (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (h : Fin n → ℝ) :
    Matrix.diagonal (fun i => (h i : ℂ)) ∈ 𝔤 → (∀ X ∈ 𝔤, ∀ Y ∈ 𝔤, X * Y - Y * X ∈ 𝔤) →
      ∀ (f : ℝ → ℝ), ∀ X ∈ 𝔤, (Matrix.of fun i j => (f (h i - h j) : ℂ) * X i j) ∈ 𝔤 := by
  intro hD hbr f X hX
  obtain ⟨S, hS⟩ : ∃ S : Finset ℝ, ∀ i j, h i - h j ∈ S :=
    ⟨Finset.univ.image (fun q : Fin n × Fin n => h q.1 - h q.2),
      fun i j => Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩⟩
  have key : ∀ x ∈ S, (Lagrange.interpolate S id f).eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := id) (s := S) (r := f) Function.injective_id.injOn hx
  obtain ⟨p, hp⟩ : ∃ p : Polynomial ℝ, ∀ i j, p.eval (h i - h j) = f (h i - h j) :=
    ⟨Lagrange.interpolate S id f, fun i j => key _ (hS i j)⟩
  have heq : (Matrix.of fun i j => (f (h i - h j) : ℂ) * X i j) = entryMul h (fun t => p.eval t) X := by
    ext i j
    simp only [entryMul, Matrix.of_apply, hp]
  rw [heq]
  exact entryMul_poly_mem 𝔤 h hD hbr hX p

end GlobalTheory.CompanionTheory.AdProj
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieAlgebraFunctionCalculusStatement
open Matrix Topology Filter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_algebra_function_calculus : ∀ {n : ℕ} (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (h : Fin n → ℝ), Matrix.diagonal (fun i => (h i : ℂ)) ∈ 𝔤 → (∀ X ∈ 𝔤, ∀ Y ∈ 𝔤, X * Y - Y * X ∈ 𝔤) → ∀ (f : ℝ → ℝ), ∀ X ∈ 𝔤, (Matrix.of fun i j => (f (h i - h j) : ℂ) * X i j) ∈ 𝔤 := by
  first | exact @GlobalTheory.CompanionTheory.AdProj.mem_of_entrywise | exact GlobalTheory.CompanionTheory.AdProj.mem_of_entrywise | (intros; apply GlobalTheory.CompanionTheory.AdProj.mem_of_entrywise <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AntitoneDiagonalConjugate
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AntitoneDiagonalConjugate
open Matrix Topology Filter

namespace GlobalTheory.CompanionTheory.FrameSort

theorem exists_antitone_reorder : ∀ {n : ℕ} (U₀ : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ), U₀ ∈ Matrix.unitaryGroup (Fin n) ℂ → ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∃ h : Fin n → ℝ, Antitone h ∧ U * Matrix.diagonal (fun i => (h i : ℂ)) * Uᴴ = U₀ * Matrix.diagonal (fun i => (d i : ℂ)) * U₀ᴴ ∧ ∀ Z : Matrix (Fin n) (Fin n) ℂ, (U₀ᴴ * Z * U₀).IsDiag → (Uᴴ * Z * U).IsDiag := by
  intro n U₀ d hU
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin n), Antitone (d ∘ σ) := by
    refine ⟨Tuple.sort (fun i => - d i), ?_⟩
    intro a b hab
    have := Tuple.monotone_sort (fun i => - d i) hab
    simpa using this
  have hH : (U₀.submatrix id σ)ᴴ = U₀ᴴ.submatrix σ id := by
    ext i j; simp
  have hconj : ∀ Z : Matrix (Fin n) (Fin n) ℂ,
      (U₀.submatrix id σ)ᴴ * Z * U₀.submatrix id σ = (U₀ᴴ * Z * U₀).submatrix σ σ := by
    intro Z
    rw [hH]
    ext i j
    simp [Matrix.mul_apply]
  refine ⟨U₀.submatrix id σ, ?_, d ∘ σ, hσ, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    have h1 := hconj 1
    rw [Matrix.mul_one] at h1
    rw [h1, Matrix.mul_one]
    have h2 : U₀ᴴ * U₀ = 1 := by
      have := Matrix.mem_unitaryGroup_iff'.mp hU
      simpa [Matrix.star_eq_conjTranspose] using this
    rw [h2]
    simp
  · rw [hH]
    ext a b
    rw [Matrix.mul_apply, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.submatrix_apply, id, Function.comp]
    exact Equiv.sum_comp σ (fun i => U₀ a i * (d i : ℂ) * U₀ᴴ i b)
  · intro Z hZ
    rw [hconj Z]
    intro i j hij
    simpa using hZ (fun e => hij (σ.injective e))

end GlobalTheory.CompanionTheory.FrameSort
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AntitoneDiagonalConjugateStatement
open Matrix Topology Filter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.antitone_diagonal_conjugate : ∀ {n : ℕ} (U₀ : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ), U₀ ∈ Matrix.unitaryGroup (Fin n) ℂ → ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∃ h : Fin n → ℝ, Antitone h ∧ U * Matrix.diagonal (fun i => (h i : ℂ)) * Uᴴ = U₀ * Matrix.diagonal (fun i => (d i : ℂ)) * U₀ᴴ ∧ ∀ Z : Matrix (Fin n) (Fin n) ℂ, (U₀ᴴ * Z * U₀).IsDiag → (Uᴴ * Z * U).IsDiag := by
  first | exact @GlobalTheory.CompanionTheory.FrameSort.exists_antitone_reorder | exact GlobalTheory.CompanionTheory.FrameSort.exists_antitone_reorder | (intros; apply GlobalTheory.CompanionTheory.FrameSort.exists_antitone_reorder <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMaximalAbelianHermitian
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMaximalAbelianHermitian
open Matrix Topology Filter

namespace GlobalTheory.CompanionTheory.HermitianCommuting

theorem exists_maximal_commuting_hermitian_subspace {n : ℕ}
    (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    ∃ 𝔞 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ), 𝔞 ≤ 𝔤 ∧ (∀ A ∈ 𝔞, Aᴴ = A) ∧
      (∀ A ∈ 𝔞, ∀ B ∈ 𝔞, A * B = B * A) ∧
      ∀ Y ∈ 𝔤, Yᴴ = Y → (∀ A ∈ 𝔞, Y * A = A * Y) → Y ∈ 𝔞 := by
  let S : Set (Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :=
    {a | a ≤ 𝔤 ∧ (∀ A ∈ a, Aᴴ = A) ∧ ∀ A ∈ a, ∀ B ∈ a, A * B = B * A}
  have hS : S.Nonempty := by
    refine ⟨⊥, bot_le, ?_, ?_⟩
    · intro A hA
      rw [Submodule.mem_bot] at hA
      simp [hA]
    · intro A hA B hB
      rw [Submodule.mem_bot] at hA hB
      simp [hA, hB]
  obtain ⟨a, ha, hmax⟩ :=
    (wellFounded_gt (α := Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))).has_min S hS
  refine ⟨a, ha.1, ha.2.1, ha.2.2, ?_⟩
  intro Y hY hYh hYc
  have hmem : a ⊔ Submodule.span ℝ {Y} ∈ S := by
    refine ⟨sup_le ha.1 ((Submodule.span_singleton_le_iff_mem _ _).2 hY), ?_, ?_⟩
    · intro A hA
      obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hA
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
      rw [conjTranspose_add, ha.2.1 x hx, conjTranspose_smul, hYh]
      simp
    · intro A hA B hB
      obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hA
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
      obtain ⟨x', hx', y', hy', rfl⟩ := Submodule.mem_sup.1 hB
      obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.1 hy'
      have h1 := ha.2.2 x hx x' hx'
      have h2 := hYc x hx
      have h3 := hYc x' hx'
      simp only [add_mul, mul_add, smul_add, smul_mul_assoc, mul_smul_comm, smul_smul, h1, h2, h3]
      rw [mul_comm d c]
      abel
  have hne : a ⊔ Submodule.span ℝ {Y} = a := by
    by_contra h
    exact hmax _ hmem (lt_of_le_of_ne le_sup_left (Ne.symm h))
  have hYmem : Y ∈ a ⊔ Submodule.span ℝ {Y} :=
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self Y)
  rwa [hne] at hYmem

end GlobalTheory.CompanionTheory.HermitianCommuting
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMaximalAbelianHermitianStatement
open Matrix Topology Filter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_maximal_abelian_hermitian : ∀ {n : ℕ} (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)), ∃ 𝔞 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ), 𝔞 ≤ 𝔤 ∧ (∀ A ∈ 𝔞, Aᴴ = A) ∧ (∀ A ∈ 𝔞, ∀ B ∈ 𝔞, A * B = B * A) ∧ ∀ Y ∈ 𝔤, Yᴴ = Y → (∀ A ∈ 𝔞, Y * A = A * Y) → Y ∈ 𝔞 := by
  first | exact @GlobalTheory.CompanionTheory.HermitianCommuting.exists_maximal_commuting_hermitian_subspace | exact GlobalTheory.CompanionTheory.HermitianCommuting.exists_maximal_commuting_hermitian_subspace | (intros; apply GlobalTheory.CompanionTheory.HermitianCommuting.exists_maximal_commuting_hermitian_subspace <;> assumption)
end
end

open Matrix Topology Filter

namespace GlobalTheory.CompanionTheory.IwaGen

theorem exp_mem_unitaryGroup {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) :
    NormedSpace.exp X ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  change (NormedSpace.exp X)ᴴ * NormedSpace.exp X = 1
  rw [← Matrix.exp_conjTranspose, hX]
  exact (Matrix.exp_neg X ▸ Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp X)))

theorem frame {n : ℕ} (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∃ h : Fin n → ℝ, Antitone h ∧
      U * Matrix.diagonal (fun i => (h i : ℂ)) * Uᴴ ∈ 𝔤 ∧
      ∀ Y ∈ 𝔤, Yᴴ = Y → (U * Matrix.diagonal (fun i => (h i : ℂ)) * Uᴴ) * Y = Y * (U * Matrix.diagonal (fun i => (h i : ℂ)) * Uᴴ) →
        (Uᴴ * Y * U).IsDiag := by
  obtain ⟨𝔞, hle, hH, hC, hM⟩ := GlobalTheory.T.exists_maximal_abelian_hermitian 𝔤
  obtain ⟨U₀, hU₀, hD⟩ := GlobalTheory.T.commuting_hermitian_simultaneous_diag (𝔞 : Set (Matrix (Fin n) (Fin n) ℂ)) hH hC
  obtain ⟨H, hHa, hreg⟩ := GlobalTheory.T.exists_regular_element_abelian 𝔞 U₀
  have hU₀' : U₀ * U₀ᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hU₀
  have hU₀'' : U₀ᴴ * U₀ = 1 := Matrix.mem_unitaryGroup_iff'.1 hU₀
  let d : Fin n → ℝ := fun i => ((U₀ᴴ * H * U₀) i i).re
  have hdd : Matrix.diagonal (fun i => (d i : ℂ)) = U₀ᴴ * H * U₀ := by
    ext i j
    by_cases hij : i = j
    · subst hij
      have : star ((U₀ᴴ * H * U₀) i i) = (U₀ᴴ * H * U₀) i i := by
        have h2 : (U₀ᴴ * H * U₀)ᴴ = U₀ᴴ * H * U₀ := by
          simp [Matrix.conjTranspose_mul, hH H hHa, Matrix.mul_assoc]
        exact congrFun (congrFun h2 i) i
      have h3 := Complex.conj_eq_iff_real.1 this
      obtain ⟨r, hr⟩ := h3
      simp [d, hr]
    · simp [Matrix.diagonal_apply_ne _ hij, hD H hHa hij]
  have hHd : U₀ * Matrix.diagonal (fun i => (d i : ℂ)) * U₀ᴴ = H := by
    rw [hdd]
    calc U₀ * (U₀ᴴ * H * U₀) * U₀ᴴ = (U₀ * U₀ᴴ) * H * (U₀ * U₀ᴴ) := by simp only [Matrix.mul_assoc]
      _ = H := by rw [hU₀']; simp
  obtain ⟨U, hU, h, hanti, heq, hdiag⟩ := GlobalTheory.T.antitone_diagonal_conjugate U₀ d hU₀
  refine ⟨U, hU, h, hanti, ?_, ?_⟩
  · rw [heq, hHd]; exact hle hHa
  · intro Y hY hYs hcomm
    rw [heq, hHd] at hcomm
    apply hdiag
    refine hD Y (hM Y hY hYs fun A hA => ?_)
    exact GlobalTheory.T.centralizer_regular_commutes U₀ H A Y hU₀ (hD H hHa) (hD A hA) (fun i j hij => hreg i j hij A hA) hcomm

theorem alg {n : ℕ} (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (hs : ∀ X ∈ 𝔤, Xᴴ ∈ 𝔤)
    (hb : ∀ X ∈ 𝔤, ∀ Y ∈ 𝔤, X * Y - Y * X ∈ 𝔤) :
    ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ X ∈ 𝔤, ∃ A ∈ 𝔤, ∃ B ∈ 𝔤, X = A + B ∧ Aᴴ = -A ∧
      (Uᴴ * B * U).BlockTriangular id := by
  obtain ⟨U, hU, h, hanti, hd, hreg⟩ := frame 𝔤
  have h1 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hU
  have h2 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
  have cj : ∀ Z : Matrix (Fin n) (Fin n) ℂ, U * (Uᴴ * Z * U) * Uᴴ = Z := fun Z => by
    calc U * (Uᴴ * Z * U) * Uᴴ = (U * Uᴴ) * Z * (U * Uᴴ) := by simp only [Matrix.mul_assoc]
      _ = Z := by rw [h1]; simp
  have cj' : ∀ Z : Matrix (Fin n) (Fin n) ℂ, Uᴴ * (U * Z * Uᴴ) * U = Z := fun Z => by
    calc Uᴴ * (U * Z * Uᴴ) * U = (Uᴴ * U) * Z * (Uᴴ * U) := by simp only [Matrix.mul_assoc]
      _ = Z := by rw [h2]; simp
  let φ : (Matrix (Fin n) (Fin n) ℂ) →ₗ[ℝ] (Matrix (Fin n) (Fin n) ℂ) :=
    { toFun := fun Z => U * Z * Uᴴ
      map_add' := fun a b => by simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun r a => by simp }
  let 𝔥 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) := 𝔤.comap φ
  have mem : ∀ Z, Z ∈ 𝔥 ↔ U * Z * Uᴴ ∈ 𝔤 := fun Z => Iff.rfl
  have mem' : ∀ Z ∈ 𝔤, Uᴴ * Z * U ∈ 𝔥 := fun Z hZ => by rw [mem, cj]; exact hZ
  have mulc : ∀ P Q : Matrix (Fin n) (Fin n) ℂ, (U * P * Uᴴ) * (U * Q * Uᴴ) = U * (P * Q) * Uᴴ := fun P Q => by
    calc (U * P * Uᴴ) * (U * Q * Uᴴ) = U * P * (Uᴴ * U) * Q * Uᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h2]; simp [Matrix.mul_assoc]
  have hs' : ∀ Z ∈ 𝔥, Zᴴ ∈ 𝔥 := fun Z hZ => by
    have := hs _ ((mem Z).1 hZ)
    rw [mem]
    simpa [Matrix.conjTranspose_mul, Matrix.mul_assoc] using this
  have hb' : ∀ P ∈ 𝔥, ∀ Q ∈ 𝔥, P * Q - Q * P ∈ 𝔥 := fun P hP Q hQ => by
    have := hb _ ((mem P).1 hP) _ ((mem Q).1 hQ)
    rw [mulc, mulc] at this
    rw [mem, Matrix.mul_sub, Matrix.sub_mul]
    exact this
  have hreg' : ∀ Y ∈ 𝔥, Yᴴ = Y → Matrix.diagonal (fun i => (h i : ℂ)) * Y = Y * Matrix.diagonal (fun i => (h i : ℂ)) → Y.IsDiag := by
    intro Y hY hYs hc
    have := hreg _ ((mem Y).1 hY) (by simp [Matrix.conjTranspose_mul, hYs, Matrix.mul_assoc]) (by rw [mulc, mulc, hc])
    rwa [cj'] at this
  refine ⟨U, hU, fun X hX => ?_⟩
  obtain ⟨A, hA, B, hB, hAB, hAs, hBt⟩ := GlobalTheory.T.exists_skewHermitian_add_blockTriangular 𝔥 h hanti (GlobalTheory.T.lie_algebra_function_calculus 𝔥 h ((mem _).2 hd) hb') hs' hreg' _ (mem' X hX)
  refine ⟨U * A * Uᴴ, (mem _).1 hA, U * B * Uᴴ, (mem _).1 hB, ?_, ?_, ?_⟩
  · rw [← Matrix.add_mul, ← Matrix.mul_add, ← hAB, cj]
  · simp [Matrix.conjTranspose_mul, hAs, Matrix.mul_assoc]
  · rwa [cj']

theorem iwaOn_of_isLinRed : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)}, GlobalTheory.LinRed.IsLinRed G → PositivityTheory.Tls2.Iua.IwaOn G := by
  intro n G hG
  obtain ⟨𝔤, hiff, hV⟩ := GlobalTheory.T.lie_algebra_of_exp_local hG
  obtain ⟨hs, hb⟩ := GlobalTheory.T.lie_algebra_star_closed_bracket hG 𝔤 hiff
  obtain ⟨U, hU, hdec⟩ := alg 𝔤 hs hb
  have hexp : ∀ X ∈ 𝔤, NormedSpace.exp X ∈ G := fun X hX => by
    simpa using (hiff X).1 hX 1
  let 𝔨 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) := 𝔤 ⊓
    { carrier := {X | Xᴴ = -X}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at *
        rw [Matrix.conjTranspose_add, ha, hb, neg_add]
      zero_mem' := by simp
      smul_mem' := fun r a ha => by
        simp only [Set.mem_setOf_eq] at *
        ext i j
        have := congrFun (congrFun ha i) j
        simp only [Matrix.conjTranspose_apply, Matrix.neg_apply] at this
        simp [Matrix.conjTranspose_apply, this] }
  let 𝔟 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) := 𝔤 ⊓
    { carrier := {X | (Uᴴ * X * U).BlockTriangular id}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at *
        rw [Matrix.mul_add, Matrix.add_mul]
        exact ha.add hb
      zero_mem' := by simp [Matrix.BlockTriangular]
      smul_mem' := fun r a ha => by
        simp only [Set.mem_setOf_eq] at *
        intro i j hij
        have := ha hij
        have e : Uᴴ * (r • a) * U = r • (Uᴴ * a * U) := by simp
        rw [e, Matrix.smul_apply, this, smul_zero] }
  have hloc := GlobalTheory.T.local_exp_product_decomposition hG 𝔤 𝔨 𝔟 hiff hV inf_le_left inf_le_left (fun X hX => by
    obtain ⟨A, hA, B, hB, hAB, hAs, hBt⟩ := hdec X hX
    rw [hAB]
    exact Submodule.add_mem_sup ⟨hA, hAs⟩ ⟨hB, hBt⟩)
  obtain h := GlobalTheory.T.cartan_local_to_global hG U hU (by
    filter_upwards [hloc] with g hg hgG
    obtain ⟨X, hX, Y, hY, rfl⟩ := hg hgG
    exact ⟨_, ⟨hexp X hX.1, exp_mem_unitaryGroup X hX.2⟩, _, hexp Y hY.1, rfl, GlobalTheory.T.exp_block_triangular U Y hU hY.2⟩)
  exact ⟨U, hU, h⟩

end GlobalTheory.CompanionTheory.IwaGen

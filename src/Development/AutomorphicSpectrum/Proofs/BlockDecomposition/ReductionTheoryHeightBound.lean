module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryPointsHeightBoundCompact

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryPointsHeightBoundCompactStatement
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GroundTheory.Automorphic GroundTheory.Automorphic.Anisotropic
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal NumberField.AdeleRing
attribute [local instance] tensorTopology finite_of_isQuadraticExtension isModuleTopology_tensor isTopologicalRing_tensor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_points_height_bound_compact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Algebra.IsQuadraticExtension F E] (n : ℕ) (H : Matrix (Fin n) (Fin n) E), IsUnit H.det → ∀ (Y : Set (unitaryPoints F E H 𝔸[F])) (ε : ℝ), 0 < ε → (∀ u ∈ Y, ∀ x : Fin (Fintype.card (Fin n × Fin (Module.finrank F E))) → F, x ≠ 0 → ε ≤ Reduction.height (trHom (ι := Fin n) (Module.finBasis F E) 𝔸[F] (u : GL (Fin n) (𝔸[F] ⊗[F] E))) x) → ∃ Ω : Set (unitaryPoints F E H 𝔸[F]), IsCompact Ω ∧ ∀ u ∈ Y, ∃ θ ∈ (unitaryDiagonal F H).range, θ⁻¹ * u ∈ Ω := by
  exact @GlobalTheory.CompanionTheory.RedCov.MahlerU.mahler_unitary_set
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusSiegelHeightLowerBound
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusSiegelHeightLowerBound
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 1

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.RedCov.FirstLower

section Helpers

open PositivityTheory.ThKEst (rId)
open PositivityTheory.ThKEst.Sieg (rId_add rId_zero' rId_snd)
open GroundTheory.Automorphic.Anisotropic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def rIdele [IsTotallyReal F] (c : ℝ) : GroundTheory.Global.IdeleGroup F where
  val := rId F c
  inv := rId F (-c)
  val_inv := by rw [← rId_add, add_neg_cancel, rId_zero']
  inv_val := by rw [← rId_add, neg_add_cancel, rId_zero']

theorem ideleModule_rIdele [IsTotallyReal F] (c : ℝ) :
    (GroundTheory.Global.IdeleGroup.ideleModule F (rIdele c) : ℝ) = Real.exp ((Module.finrank ℚ F : ℝ) * c) := by
  have hm : ∀ w : InfinitePlace F, w.mult = 1 := fun w => by
    rw [InfinitePlace.mult, ite_eq_left (IsTotallyReal.isReal w)]
  have hinf : ∀ w : InfinitePlace F, ‖(rId F c).1 w‖ ^ w.mult = Real.exp c := fun w => by
    rw [hm, pow_one]
    exact norm_evInf_rId w c
  have hfin : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), ‖(rId F c).2 v‖ = 1 := fun v => by
    rw [rId_snd]
    exact norm_one
  have e : (GroundTheory.Global.IdeleGroup.ideleModule F (rIdele c) : ℝ) =
      (∏ w : InfinitePlace F, ‖(rId F c).1 w‖ ^ w.mult) *
        ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), ‖(rId F c).2 v‖ :=
    GroundTheory.Global.IdeleGroup.ideleModule_eq _
  rw [e, finprod_eq_one_of_forall_eq_one hfin, mul_one, Finset.prod_congr rfl fun w _ => hinf w,
    Finset.prod_const, Finset.card_univ, card_infinitePlace, ← Real.exp_nat_mul]

variable {n r : ℕ}

theorem mulVec_ratV_col {X : Matrix (Fin n) (Fin (r + 1)) E} {M : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)}
    {B : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)} (hB : B.BlockTriangular id)
    (h : M * adMat F X = adMat F X * B) : M *ᵥ ratV F (Xᵀ 0) = B 0 0 • ratV F (Xᵀ 0) := by
  funext i
  have h1 : (M *ᵥ ratV F (Xᵀ 0)) i = (M * adMat F X) i 0 := rfl
  rw [h1, h, Matrix.mul_apply, Finset.sum_eq_single 0]
  · simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_comm _ _
  · intro j _ hj
    rw [hB (show id (0 : Fin (r + 1)) < id j from Fin.pos_of_ne_zero hj), mul_zero]
  · simp

theorem ratV_smul (e : E) (w : Fin n → E) : ratV F (e • w) = inclR (F := F) (AF F) e • ratV F w := by
  funext i
  simp [ratV, map_mul]

theorem resVec_algebraMap_smul [Algebra.IsQuadraticExtension F E] (c : AF F) (ξ : Fin n → AF F ⊗[F] E) :
    resVec (ι := Fin n) (Module.finBasis F E) (AF F) (algebraMap (AF F) (AF F ⊗[F] E) c • ξ) =
      c • resVec (ι := Fin n) (Module.finBasis F E) (AF F) ξ := by
  have e : algebraMap (AF F) (AF F ⊗[F] E) c • ξ = c • ξ := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, ← Algebra.smul_def]
  rw [e]
  conv_lhs => rw [← ofResVec_resVec (Module.finBasis F E) (AF F) ξ, ← ofResVec_smul, resVec_ofResVec]

variable {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin (r + 1)) E}

theorem IsTorus.inv_eq {a : (Fin (r + 1) → ℝ) → GAd σ J} (ha : IsTorus σ J X Y a) (s : Fin (r + 1) → ℝ) :
    (a s)⁻¹ = a (-s) := by
  have h0 : a 0 = 1 := by
    have := ha.add 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  rw [inv_eq_iff_mul_eq_one, ← ha.add, add_neg_cancel, h0]

theorem torus_inv_mulVec {a : (Fin (r + 1) → ℝ) → GAd σ J} (ha : IsTorus σ J X Y a) {p : GAd σ J}
    (hp : p ∈ minPar σ J X) (s : Fin (r + 1) → ℝ) (e : E) :
    (matHom _ σ J (a s)⁻¹).1 *ᵥ ((matHom _ σ J p).1 *ᵥ ratV F (e • Xᵀ 0)) =
      algebraMap (AF F) (AF F ⊗[F] E) (rId F (-s 0)) • ((matHom _ σ J p).1 *ᵥ ratV F (e • Xᵀ 0)) := by
  obtain ⟨B, hB, hpB⟩ := hp
  have h1 := mulVec_ratV_col hB hpB
  have h2 := mulVec_ratV_col (Matrix.blockTriangular_diagonal _) (ha.onX (-s))
  rw [Matrix.diagonal_apply_eq] at h2
  rw [IsTorus.inv_eq ha, ratV_smul, Matrix.mulVec_smul, h1, Matrix.mulVec_smul, Matrix.mulVec_smul, h2]
  funext i
  simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem col_ne_zero (hW : IsWittFrame σ J X Y) : Xᵀ 0 ≠ 0 := by
  intro h0
  have h1 := congrFun (congrFun hW.xy 0) 0
  have hc : ∀ i, X i 0 = 0 := fun i => congrFun h0 i
  simp [cT, Matrix.mul_apply, hc] at h1

end Helpers


open GroundTheory.Automorphic GroundTheory.Automorphic.Anisotropic GlobalTheory.CompanionTheory.RedCov.Bridge in
theorem vecMul_trG_torus {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] {σ : E →ₐ[F] E} {n r : ℕ} {J : Matrix (Fin n) (Fin n) E}
    {X Y : Matrix (Fin n) (Fin (r + 1)) E} {a : (Fin (r + 1) → ℝ) → GAd σ J} (ha : IsTorus σ J X Y a)
    {ω : GAd σ J} (hω : ω⁻¹ ∈ minPar σ J X) (s : Fin (r + 1) → ℝ) (e : E) :
    (Reduction.ratVec (cvec F (e • Xᵀ 0)) ᵥ* (trG σ J ω).1) ᵥ* (trG σ J (a s)).1 =
      ((rIdele (-s 0) : GroundTheory.Global.IdeleGroup F) : AF F) •
        (Reduction.ratVec (cvec F (e • Xᵀ 0)) ᵥ* (trG σ J ω).1) := by
  have step : ∀ (g : GAd σ J) (ξ : Fin n → AF F ⊗[F] E),
      resVec (ι := Fin n) (Module.finBasis F E) (AF F) ξ ᵥ* (trG σ J g).1 =
        resVec (ι := Fin n) (Module.finBasis F E) (AF F) ((matHom _ σ J g⁻¹).1 *ᵥ ξ) := fun g ξ => by
    rw [trG, MonoidHom.comp_apply, map_inv]
    exact resVec_vecMul_trHom _ _ _ _
  rw [ratVec_cvec, step, step, torus_inv_mulVec ha hω, resVec_algebraMap_smul]
  rfl


open GroundTheory.Automorphic GlobalTheory.CompanionTheory.RedCov.Bridge in
theorem exp_le_hgt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsWittFrame σ J X Y → ∀ a, IsTorus σ J X Y a → ∀ (Ω C : Set (GAd σ J)), IsCompact Ω → Ω ⊆ minPar σ J X → IsCompact C → ∃ P : ℝ, 0 < P ∧ ∀ ω ∈ Ω, ∀ s : Fin (r + 1) → ℝ, ∀ κ ∈ C, ∀ e : E, e ≠ 0 → Real.exp (- ((Module.finrank ℚ F : ℝ) * s 0)) ≤ P * hgt σ J (ω * a s * κ) (e • Xᵀ 0) := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW a ha Ω C hΩ hΩP hC
  haveI : Algebra.IsQuadraticExtension F E := ⟨h.2.2.1⟩
  haveI : IsTotallyReal F := h.1
  have hcont : Continuous fun g : GAd σ J => (trG σ J g)⁻¹ := (continuous_trG σ J).inv
  obtain ⟨P₁, hP₁, hb₁⟩ := Reduction.exists_adelicNorm_vecMul_le_mul (hC.image hcont)
  obtain ⟨P₂, hP₂, hb₂⟩ := Reduction.exists_adelicNorm_vecMul_le_mul (hΩ.image hcont)
  refine ⟨P₁ * P₂, mul_pos hP₁ hP₂, fun ω hω s κ hκ e he => ?_⟩
  have hv : e • Xᵀ 0 ≠ 0 := smul_ne_zero he (col_ne_zero hW)
  have hc0 := cvec_ne_zero (F := F) hv
  set y₀ := Reduction.ratVec (cvec F (e • Xᵀ 0)) with hy₀
  have hf₀ : Reduction.HasFiniteContent y₀ := Reduction.hasFiniteContent_ratVec hc0
  set y₁ := y₀ ᵥ* (trG σ J ω).1 with hy₁
  have hf₁ : Reduction.HasFiniteContent y₁ := hf₀.vecMul (trG σ J ω)
  set u := rIdele (F := F) (-s 0) with hu
  have hkey : y₁ ᵥ* (trG σ J (a s)).1 = (u : AF F) • y₁ :=
    vecMul_trG_torus ha (inv_mem_minPar h hJ hW (hΩP hω)) s e
  have hg : hgt σ J (ω * a s * κ) (e • Xᵀ 0) = Reduction.adelicNorm (((u : AF F) • y₁) ᵥ* (trG σ J κ).1) := by
    rw [hgt_eq, Reduction.height, map_mul, map_mul, Units.val_mul, Units.val_mul, ← Matrix.vecMul_vecMul,
      ← Matrix.vecMul_vecMul, ← hy₀, ← hy₁, hkey]
  have hf₂ : Reduction.HasFiniteContent (((u : AF F) • y₁) ᵥ* (trG σ J κ).1) := (hf₁.smul u).vecMul (trG σ J κ)
  have hb3 : Reduction.adelicNorm ((u : AF F) • y₁) ≤ P₁ * hgt σ J (ω * a s * κ) (e • Xᵀ 0) := by
    have := hb₁ _ ⟨κ, hκ, rfl⟩ _ hf₂
    rwa [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one, ← hg] at this
  have hb4 : Reduction.adelicNorm y₀ ≤ P₂ * Reduction.adelicNorm y₁ := by
    have := hb₂ _ ⟨ω, hω, rfl⟩ _ hf₁
    rwa [hy₁, Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one] at this
  have h1 : 1 ≤ Reduction.adelicNorm y₀ := Reduction.one_le_adelicNorm_ratVec hc0
  have hsm : Reduction.adelicNorm ((u : AF F) • y₁) =
      Real.exp (- ((Module.finrank ℚ F : ℝ) * s 0)) * Reduction.adelicNorm y₁ := by
    rw [Reduction.adelicNorm_smul hf₁ u, hu, ideleModule_rIdele, mul_neg]
  have hexp := Real.exp_pos (- ((Module.finrank ℚ F : ℝ) * s 0))
  calc Real.exp (- ((Module.finrank ℚ F : ℝ) * s 0))
      ≤ Real.exp (- ((Module.finrank ℚ F : ℝ) * s 0)) * (P₂ * Reduction.adelicNorm y₁) :=
        le_mul_of_one_le_right hexp.le (h1.trans hb4)
    _ = P₂ * Reduction.adelicNorm ((u : AF F) • y₁) := by rw [hsm]; ring
    _ ≤ P₂ * (P₁ * hgt σ J (ω * a s * κ) (e • Xᵀ 0)) := mul_le_mul_of_nonneg_left hb3 hP₂.le
    _ = P₁ * P₂ * hgt σ J (ω * a s * κ) (e • Xᵀ 0) := by ring

end GlobalTheory.CompanionTheory.RedCov.FirstLower
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusSiegelHeightLowerBoundStatement
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_siegel_height_lower_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsWittFrame σ J X Y → ∀ a, IsTorus σ J X Y a → ∀ (Ω C : Set (GAd σ J)), IsCompact Ω → Ω ⊆ minPar σ J X → IsCompact C → ∃ P : ℝ, 0 < P ∧ ∀ ω ∈ Ω, ∀ s : Fin (r + 1) → ℝ, ∀ κ ∈ C, ∀ e : E, e ≠ 0 → Real.exp (- ((Module.finrank ℚ F : ℝ) * s 0)) ≤ P * hgt σ J (ω * a s * κ) (e • Xᵀ 0) := by
  first | exact @GlobalTheory.CompanionTheory.RedCov.FirstLower.exp_le_hgt | exact GlobalTheory.CompanionTheory.RedCov.FirstLower.exp_le_hgt | (intros; apply GlobalTheory.CompanionTheory.RedCov.FirstLower.exp_le_hgt <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryPointsHeightBoundFinite
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryPointsHeightBoundFinite
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GroundTheory.Automorphic GroundTheory.Automorphic.Anisotropic
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal NumberField.AdeleRing
attribute [local instance] tensorTopology finite_of_isQuadraticExtension isModuleTopology_tensor isTopologicalRing_tensor

set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.RedCov.Mahler

open GlobalTheory.CompanionTheory.RedCov.Bridge

def pointsHomeo {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    GAd (conj F E).toAlgHom J ≃ₜ unitaryPoints F E J 𝔸[F] where
  toFun g := ⟨matHom _ _ J g, (SetLike.ext_iff.1 (CompanionTheory.SWFin.HR_eq J (AF F)) _).1 g.2⟩
  invFun u := ⟨u.1, (SetLike.ext_iff.1 (CompanionTheory.SWFin.HR_eq J (AF F)) _).2 u.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val _
  continuous_invFun := Continuous.subtype_mk continuous_subtype_val _

theorem exists_isCompact_of_le_hgt : (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Algebra.IsQuadraticExtension F E] (n : ℕ) (H : Matrix (Fin n) (Fin n) E), IsUnit H.det → ∀ (Y : Set (unitaryPoints F E H 𝔸[F])) (ε : ℝ), 0 < ε → (∀ u ∈ Y, ∀ x : Fin (Fintype.card (Fin n × Fin (Module.finrank F E))) → F, x ≠ 0 → ε ≤ Reduction.height (trHom (ι := Fin n) (Module.finBasis F E) 𝔸[F] (u : GL (Fin n) (𝔸[F] ⊗[F] E))) x) → ∃ Ω : Set (unitaryPoints F E H 𝔸[F]), IsCompact Ω ∧ ∀ u ∈ Y, ∃ θ ∈ (unitaryDiagonal F H).range, θ⁻¹ * u ∈ Ω) → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ t : ℝ, 0 < t → ∃ C₀ : Set (GAd σ J), IsCompact C₀ ∧ ∀ g : GAd σ J, (∀ v : Fin n → E, v ≠ 0 → t ≤ hgt σ J g v) → ∃ γ ∈ ratPts σ J, γ⁻¹ * g ∈ C₀ := by
  intro hM F E _ _ _ _ _ σ hσ n J hJ t ht
  obtain ⟨hF, hE', h2, hc⟩ := hσ
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain rfl : σ = (conj F E).toAlgHom := AlgHom.ext fun x =>
    τ.injective ((hc τ x).trans (GroundTheory.Heights₂.Heights.FiniteCovolume.embedding_conj τ x).symm)
  have hu : IsUnit J.det := isUnit_iff_ne_zero.2 hJ.2
  let e := pointsHomeo (F := F) (E := E) J
  obtain ⟨Ω, hΩ, hcov⟩ := hM F E n J hu
    (e '' {g | ∀ v : Fin n → E, v ≠ 0 → t ≤ hgt _ J g v}) t ht (by
      rintro _ ⟨g, hg, rfl⟩ x hx
      obtain ⟨v, rfl⟩ := cvec_surjective (F := F) (E := E) (n := n) x
      have hv : v ≠ 0 := by
        rintro rfl
        apply hx
        funext p
        simp [cvec]
      have := hg v hv
      rw [hgt_eq] at this
      exact this)
  refine ⟨e ⁻¹' Ω, e.isCompact_preimage.2 hΩ, fun g hg => ?_⟩
  obtain ⟨θ, hθ, hθΩ⟩ := hcov (e g) ⟨g, hg, rfl⟩
  rw [← CompanionTheory.SWFin.HFin_eq, Subgroup.mem_subgroupOf] at hθ
  refine ⟨e.symm θ, ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.2 hθ
  · exact hθΩ

end GlobalTheory.CompanionTheory.RedCov.Mahler
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryPointsHeightBoundFiniteStatement
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GroundTheory.Automorphic GroundTheory.Automorphic.Anisotropic
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal NumberField.AdeleRing
attribute [local instance] tensorTopology finite_of_isQuadraticExtension isModuleTopology_tensor isTopologicalRing_tensor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_points_height_bound_finite : (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Algebra.IsQuadraticExtension F E] (n : ℕ) (H : Matrix (Fin n) (Fin n) E), IsUnit H.det → ∀ (Y : Set (unitaryPoints F E H 𝔸[F])) (ε : ℝ), 0 < ε → (∀ u ∈ Y, ∀ x : Fin (Fintype.card (Fin n × Fin (Module.finrank F E))) → F, x ≠ 0 → ε ≤ Reduction.height (trHom (ι := Fin n) (Module.finBasis F E) 𝔸[F] (u : GL (Fin n) (𝔸[F] ⊗[F] E))) x) → ∃ Ω : Set (unitaryPoints F E H 𝔸[F]), IsCompact Ω ∧ ∀ u ∈ Y, ∃ θ ∈ (unitaryDiagonal F H).range, θ⁻¹ * u ∈ Ω) → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ t : ℝ, 0 < t → ∃ C₀ : Set (GAd σ J), IsCompact C₀ ∧ ∀ g : GAd σ J, (∀ v : Fin n → E, v ≠ 0 → t ≤ hgt σ J g v) → ∃ γ ∈ ratPts σ J, γ⁻¹ * g ∈ C₀ := by
  first | exact @GlobalTheory.CompanionTheory.RedCov.Mahler.exists_isCompact_of_le_hgt | exact GlobalTheory.CompanionTheory.RedCov.Mahler.exists_isCompact_of_le_hgt | (intros; apply GlobalTheory.CompanionTheory.RedCov.Mahler.exists_isCompact_of_le_hgt <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmallHeightVectorIsotropic
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmallHeightVectorIsotropic
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 1

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal NumberField.AdeleRing
open GroundTheory.Automorphic GroundTheory.Automorphic.Anisotropic

namespace GlobalTheory.CompanionTheory.RedCov.Bridge

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem hermValue_inclR (v : Fin n → E) :
    hermValue F J F (fun i => inclR (F := F) F (v i)) =
      inclR (F := F) F (hE (conj F E).toAlgHom J v v) := by
  have hc : ∀ e : E, conjBase F E F (inclR (F := F) F e) = inclR (F := F) F (conj F E e) := fun e => rfl
  have hb : baseMatrix F J F = J.map (inclR (F := F) F) := rfl
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hermValue, hc, hb, hE, Formalism.UG.hform, dotProduct, mulVec, map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Matrix.map_apply, mul_assoc]

theorem ofResVec_cvec (v : Fin n → E) :
    ofResVec (ι := Fin n) (Module.finBasis F E) F (cvec F v) = fun i => inclR (F := F) F (v i) := by
  apply resVec_injective (ι := Fin n) (Module.finBasis F E) F
  rw [resVec_ofResVec]
  funext p
  simp only [cvec, resVec, Function.comp_apply, coordsVec, coords, inclR]
  simp [Algebra.TensorProduct.basis_repr_tmul]

theorem hermCoords_cvec_ne_zero {v : Fin n → E} (h : hE (conj F E).toAlgHom J v v ≠ 0) :
    hermCoords J (Module.finBasis F E) F (cvec F v) ≠ 0 := by
  intro h0
  apply h
  have h1 : hermValue F J F (ofResVec (ι := Fin n) (Module.finBasis F E) F (cvec F v)) = 0 := by
    apply (coords (Module.finBasis F E) F).injective
    rw [map_zero]
    exact h0
  rw [ofResVec_cvec, hermValue_inclR] at h1
  exact Algebra.TensorProduct.includeRight_injective (algebraMap F F).injective (h1.trans (map_zero _).symm)

theorem matHom_mem_unitaryPoints (g : GAd (conj F E).toAlgHom J) :
    matHom (AF F) (conj F E).toAlgHom J g ∈ unitaryPoints F E J (AF F) := by
  rw [← CompanionTheory.SWFin.HR_eq]
  exact g.2

theorem exists_pos_isotropic_of_hgt_lt :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (g : GAd (conj F E).toAlgHom J) (v : Fin n → E), v ≠ 0 →
      hgt (conj F E).toAlgHom J g v < ε → hE (conj F E).toAlgHom J v v = 0 := by
  obtain ⟨C, hC, hCb⟩ := exists_adelicNorm_aeval_le (K := F) (d := 2) two_pos
    (hermPoly J (Module.finBasis F E))
    (fun v t y k => by
      rw [aeval_hermPoly, aeval_hermPoly, hermCoords_smul]
      rfl)
    (fun w t y k => by
      rw [aeval_hermPoly, aeval_hermPoly, hermCoords_smul]
      rfl)
  refine ⟨min 1 C⁻¹, lt_min one_pos (inv_pos.2 hC), fun g v hv hlt => ?_⟩
  by_contra hne
  rw [hgt_eq] at hlt
  have hx : cvec F v ≠ 0 := cvec_ne_zero hv
  have hz := hermCoords_cvec_ne_zero J hne
  have hy := Reduction.hasFiniteContent_height (trG (conj F E).toAlgHom J g) hx
  have he : (fun k => MvPolynomial.aeval
      (Reduction.ratVec (cvec F v) ᵥ* ((trG (conj F E).toAlgHom J g : GL _ (AF F)) : Matrix _ _ (AF F)))
      (hermPoly J (Module.finBasis F E) k)) =
      Reduction.ratVec (hermCoords J (Module.finBasis F E) F (cvec F v)) := by
    funext k
    rw [aeval_hermPoly]
    exact congrFun (hermCoords_vecMul_trHom J (Module.finBasis F E) (cvec F v)
      ⟨_, matHom_mem_unitaryPoints J g⟩) k
  have hfz := Reduction.hasFiniteContent_ratVec hz
  rw [← he] at hfz
  have h1 := Reduction.one_le_adelicNorm_ratVec hz
  rw [← he] at h1
  have h2 : 1 ≤ C * Reduction.height (trG (conj F E).toAlgHom J g) (cvec F v) ^ 2 :=
    h1.trans (hCb _ hy hfz)
  have h0 := Reduction.height_nonneg (trG (conj F E).toAlgHom J g) (cvec F v)
  set t := Reduction.height (trG (conj F E).toAlgHom J g) (cvec F v)
  have ht1 : t < 1 := hlt.trans_le (min_le_left _ _)
  have htC : t < C⁻¹ := hlt.trans_le (min_le_right _ _)
  have h3 : C * t < 1 := by
    have := mul_lt_mul_of_pos_left htC hC
    rwa [mul_inv_cancel₀ hC.ne'] at this
  have h4 : C * t ^ 2 ≤ C * t := by
    nlinarith [mul_nonneg (mul_nonneg hC.le h0) (sub_nonneg.2 ht1.le)]
  linarith

end GlobalTheory.CompanionTheory.RedCov.Bridge

namespace GlobalTheory.CompanionTheory.RedCov

theorem isotropic_of_hgt_lt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∃ ε : ℝ, 0 < ε ∧ ∀ (g : GAd σ J) (v : Fin n → E), v ≠ 0 → hgt σ J g v < ε → hE σ J v v = 0 := by
  intro F E _ _ _ _ _ σ h n J _
  haveI : Algebra.IsQuadraticExtension F E := ⟨h.2.2.1⟩
  haveI : IsTotallyReal F := h.1
  haveI : IsTotallyComplex E := h.2.1
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain rfl : σ = (conj F E).toAlgHom := AlgHom.ext fun x =>
    τ.injective ((h.2.2.2 τ x).trans (GroundTheory.Heights₂.Heights.FiniteCovolume.embedding_conj τ x).symm)
  exact Bridge.exists_pos_isotropic_of_hgt_lt J

end GlobalTheory.CompanionTheory.RedCov

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmallHeightVectorIsotropicStatement
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_height_vector_isotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∃ ε : ℝ, 0 < ε ∧ ∀ (g : GAd σ J) (v : Fin n → E), v ≠ 0 → hgt σ J g v < ε → hE σ J v v = 0 := by
  first | exact @GlobalTheory.CompanionTheory.RedCov.isotropic_of_hgt_lt | exact GlobalTheory.CompanionTheory.RedCov.isotropic_of_hgt_lt | (intros; apply GlobalTheory.CompanionTheory.RedCov.isotropic_of_hgt_lt <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReductionTheoryHeightBound
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 1

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal NumberField.AdeleRing
open GroundTheory.Automorphic GroundTheory.Automorphic.Anisotropic

namespace GlobalTheory.CompanionTheory.RedCov.First

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

omit [NumberField F] [NumberField E] in
theorem form_eq_hE (u v : Fin n → E) :
    toLinearMapₛₗ₂' E (σ : E →+* E) (RingHom.id E) J u v = hE σ J u v := by
  simp only [toLinearMapₛₗ₂'_apply, smul_eq_mul, RingHom.id_apply, RingHom.coe_coe, hE, Formalism.UG.hform]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

omit [NumberField F] [NumberField E] in
theorem hE_mulVec {m : Matrix (Fin n) (Fin n) E} (hm : cT (σ : E →+* E) m * J * m = J) (u : Fin n → E) :
    hE σ J (m *ᵥ u) (m *ᵥ u) = hE σ J u u := by
  have e : Matrix.of (fun a (_ : Fin 1) => (m *ᵥ u) a) = m * Matrix.of (fun a (_ : Fin 1) => u a) := by
    ext i j
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have h1 := gram_apply (σ := σ) (J := J) (s := 1) (r := 1) (Matrix.of fun a _ => (m *ᵥ u) a) (Matrix.of fun a _ => (m *ᵥ u) a) 0 0
  have h2 := gram_apply (σ := σ) (J := J) (s := 1) (r := 1) (Matrix.of fun a _ => u a) (Matrix.of fun a _ => u a) 0 0
  rw [e, pgram_unitary hm] at h1
  rw [h2] at h1
  rw [← form_eq_hE, ← form_eq_hE]
  rw [e] at *
  exact h1.symm

theorem exists_sends {γ : GAd σ J} (hγ : γ ∈ ratPts σ J) {u : Fin n → E} (hu : u ≠ 0) (hi : hE σ J u u = 0) :
    ∃ v : Fin n → E, v ≠ 0 ∧ hE σ J v v = 0 ∧ Sends σ J γ u v := by
  obtain ⟨m, hm, e⟩ := hγ
  refine ⟨m.1 *ᵥ u, ?_, ?_, ?_⟩
  · intro h0
    apply hu
    have := congrArg (fun z => (m⁻¹).1 *ᵥ z) h0
    simpa [Matrix.mulVec_mulVec, ← Units.val_mul] using this
  · rw [hE_mulVec hm, hi]
  · have e1 : (matHom _ σ J γ).1 = m.1.map (inclR (F := F) (AF F)) := by
      rw [matHom_apply]
      exact (congrArg Units.val e).symm
    unfold Sends
    rw [e1]
    funext i
    simp only [ratV]
    exact (RingHom.map_mulVec (inclR (F := F) (AF F)) m.1 u i).symm

omit [NumberField F] [NumberField E] in
theorem first_witt_vector_ne_zero {r : ℕ} {X Y : Matrix (Fin n) (Fin (r + 1)) E} (hW : IsWittFrame σ J X Y) : Xᵀ 0 ≠ 0 := by
  intro h0
  have h1 := gram_apply (σ := σ) (J := J) X Y 0 0
  rw [hW.xy, h0] at h1
  simp at h1

omit [NumberField F] [NumberField E] in
theorem first_witt_vector_isotropic {r : ℕ} {X Y : Matrix (Fin n) (Fin (r + 1)) E} (hW : IsWittFrame σ J X Y) :
    hE σ J (Xᵀ 0) (Xᵀ 0) = 0 := by
  have h1 := gram_apply (σ := σ) (J := J) X X 0 0
  rw [hW.xx, form_eq_hE] at h1
  exact h1.symm

theorem exists_isotropic_le
    (hS : ∃ ε : ℝ, 0 < ε ∧ ∀ (g : GAd σ J) (v : Fin n → E), v ≠ 0 → hgt σ J g v < ε → hE σ J v v = 0)
    (hM : ∀ t : ℝ, 0 < t → ∃ C₀ : Set (GAd σ J), IsCompact C₀ ∧ ∀ g : GAd σ J,
      (∀ v : Fin n → E, v ≠ 0 → t ≤ hgt σ J g v) → ∃ γ ∈ ratPts σ J, γ⁻¹ * g ∈ C₀)
    (hB : ∀ {C : Set (GAd σ J)}, IsCompact C → ∀ {v : Fin n → E}, v ≠ 0 → ∃ B : ℝ, ∀ c ∈ C, hgt σ J c v ≤ B)
    {x : Fin n → E} (hx : x ≠ 0) (hi : hE σ J x x = 0) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ g : GAd σ J, ∃ u : Fin n → E, u ≠ 0 ∧ hE σ J u u = 0 ∧ hgt σ J g u ≤ C₁ := by
  obtain ⟨ε, hε, hS⟩ := hS
  obtain ⟨C₀, hC₀, hC⟩ := hM ε hε
  obtain ⟨B, hB⟩ := hB hC₀ hx
  refine ⟨max ε B, lt_max_of_lt_left hε, fun g => ?_⟩
  by_cases h : ∃ v : Fin n → E, v ≠ 0 ∧ hgt σ J g v < ε
  · obtain ⟨v, hv, hlt⟩ := h
    exact ⟨v, hv, hS g v hv hlt, hlt.le.trans (le_max_left _ _)⟩
  · push_neg at h
    obtain ⟨γ, hγ, hγC⟩ := hC g h
    obtain ⟨v, hv, hvi, hs⟩ := exists_sends hγ hx hi
    refine ⟨v, hv, hvi, ?_⟩
    rw [← hgt_mul hs.inv]
    exact (hB _ hγC).trans (le_max_right _ _)

theorem exp_neg_le_rpow {d : ℝ} (hd : 0 < d) {s D : ℝ} (h : Real.exp (-(d * s)) ≤ D) :
    Real.exp (-s) ≤ D ^ (1 / d) := by
  have e : Real.exp (-s) = Real.exp (-(d * s)) ^ (1 / d) := by
    rw [← Real.exp_mul]
    congr 1
    field_simp
  rw [e]
  exact Real.rpow_le_rpow (Real.exp_pos _).le h (by positivity)

end GlobalTheory.CompanionTheory.RedCov.First


open GlobalTheory.CompanionTheory.RedCov.First in
theorem GlobalTheory.CompanionTheory.RedCov.First.exp_neg_le (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (r : ℕ)
    (X Y : Matrix (Fin n) (Fin (r + 1)) E) (hW : IsWittFrame σ J X Y) (a)
    (ha : PositivityTheory.ThKR.IsTorus σ J X Y a)
    (Ω C : Set (GAd σ J)) (hΩ : IsCompact Ω) (hΩP : Ω ⊆ minParOne σ J X) (hC : IsCompact C) :
    ∃ M : ℝ, 0 < M ∧ ∀ ω ∈ Ω, ∀ s : Fin (r + 1) → ℝ, ∀ κ ∈ C, ∀ e : E, e ≠ 0 →
      NearMin σ J (ω * a s * κ) (e • Xᵀ 0) → Real.exp (- s 0) ≤ M := by
  haveI : Algebra.IsQuadraticExtension F E := ⟨h.2.2.1⟩
  obtain ⟨C₁, hC₁, hu⟩ := exists_isotropic_le (GlobalTheory.T.small_height_vector_isotropic F E σ h n J hJ) ((GlobalTheory.T.unitary_points_height_bound_finite GlobalTheory.T.unitary_points_height_bound_compact) F E σ h n J hJ)
    (fun hC _ hv => GlobalTheory.CompanionTheory.RedCov.Bridge.exists_hgt_le σ J hC hv) (first_witt_vector_ne_zero hW) (first_witt_vector_isotropic hW)
  obtain ⟨P, hP, hlow⟩ := GlobalTheory.T.torus_siegel_height_lower_bound F E σ h n J hJ r X Y hW a ha Ω C hΩ
    (hΩP.trans minParOne_subset) hC
  have hd : (0 : ℝ) < Module.finrank ℚ F := Nat.cast_pos.2 Module.finrank_pos
  refine ⟨(2 * P * C₁) ^ (1 / (Module.finrank ℚ F : ℝ)), Real.rpow_pos_of_pos (by positivity) _, ?_⟩
  intro ω hω s κ hκ e he hN
  obtain ⟨u, hu0, hui, hule⟩ := hu (ω * a s * κ)
  refine exp_neg_le_rpow hd ((hlow ω hω s κ hκ e he).trans ?_)
  calc P * hgt σ J (ω * a s * κ) (e • Xᵀ 0) ≤ P * (2 * hgt σ J (ω * a s * κ) u) :=
        mul_le_mul_of_nonneg_left (hN.2.2 u hu0 hui) hP.le
    _ ≤ P * (2 * C₁) := by gcongr
    _ = 2 * P * C₁ := by ring
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReductionTheoryHeightBoundStatement
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_theory_height_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsWittFrame σ J X Y → ∀ a, IsTorus σ J X Y a → ∀ (Ω C : Set (GAd σ J)), IsCompact Ω → Ω ⊆ minParOne σ J X → IsCompact C → ∃ M : ℝ, 0 < M ∧ ∀ ω ∈ Ω, ∀ s : Fin (r + 1) → ℝ, ∀ κ ∈ C, ∀ e : E, e ≠ 0 → NearMin σ J (ω * a s * κ) (e • Xᵀ 0) → Real.exp (- s 0) ≤ M := by
  first | exact @GlobalTheory.CompanionTheory.RedCov.First.exp_neg_le | exact GlobalTheory.CompanionTheory.RedCov.First.exp_neg_le | (intros; apply GlobalTheory.CompanionTheory.RedCov.First.exp_neg_le <;> assumption)
end

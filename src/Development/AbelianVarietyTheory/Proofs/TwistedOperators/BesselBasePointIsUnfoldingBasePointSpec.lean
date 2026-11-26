module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurableLevelIndicatorCoefficientTestFunction

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselGroupActsBasePointUnitriangular
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittDecompositionProjectionZeroMulEEqZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.Asc.FBL

variable {D : D7} {σ : ℕ}

def x0Mat (B : BesL D σ) : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E :=
  Matrix.of fun k => Fin.snoc (α := fun _ => D.host.E) (B.d.e k) ((B.d.i₀ *ᵥ vecB B.o B.ζ) k)

theorem rat_x0Mat (B : BesL D σ) : rat (x0Mat B) = xLast B.d (vecB B.o B.ζ) := by
  refine Matrix.ext fun k j => ?_
  refine Fin.lastCases ?_ (fun b => ?_) j
  set_option synthInstance.maxHeartbeats 100000 in
    · simp [x0Mat, xLast, rat, HypDec.j0, ratV, Matrix.mulVec, dotProduct, map_sum, map_mul]
  · simp [x0Mat, xLast, rat, HypDec.jX]

def besselBasePointLevelNorm (B : BesL D σ) : D.host.E := star (vecB B.o B.ζ) ⬝ᵥ B.V₀.gram *ᵥ vecB B.o B.ζ

theorem besselBasePointLevelNorm_eq_gram_form (B : BesL D σ) : besselBasePointLevelNorm B = star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ := by
  rw [besselBasePointLevelNorm, vecB, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    B.o.isoB]

theorem besselBasePointLevelNorm_ne_zero (B : BesL D σ) : besselBasePointLevelNorm B ≠ 0 := by
  rw [besselBasePointLevelNorm_eq_gram_form]; exact B.line.2

def besselBasePointLeftInverse (B : BesL D σ) : Matrix (Fin (σ + 1)) (Fin B.V.rank) D.host.E :=
  Matrix.of (Fin.snoc (α := fun _ => Fin B.V.rank → D.host.E) (fun a => B.d.qX a)
    ((besselBasePointLevelNorm B)⁻¹ • (star (vecB B.o B.ζ) ᵥ* (B.V₀.gram * B.d.q0))))

theorem besselLevelDatum_qX_dot_e_eq_one (B : BesL D σ) : B.d.qX * B.d.e = 1 :=
  rat_injective (by rw [rat_mul, rat_one]; exact B.d.pX_jX)

theorem wittDecomposition_projectionX_mul_anisotropicInclusion_eq_zero (B : BesL D σ) : B.d.qX * B.d.i₀ = 0 :=
  rat_injective (by rw [rat_mul, rat_zero]; exact B.d.pX_j0)

theorem wittDecomposition_projectionZero_mul_e_eq_zero (B : BesL D σ) : B.d.q0 * B.d.e = 0 :=
  rat_injective (by rw [rat_mul, rat_zero]; exact B.d.p0_jX)

theorem wittDecomposition_projectionZero_mul_anisotropicInclusion_eq_one (B : BesL D σ) : B.d.q0 * B.d.i₀ = 1 :=
  rat_injective (by rw [rat_mul, rat_one]; exact B.d.p0_j0)

theorem besselBasePointLeftInverse_mul_snocMatrix (B : BesL D σ) : besselBasePointLeftInverse B * x0Mat B = 1 := by
  refine Matrix.ext fun i j => ?_
  refine Fin.lastCases ?_ (fun a => ?_) i <;> refine Fin.lastCases ?_ (fun b => ?_) j
  · have h : ((besselBasePointLevelNorm B)⁻¹ • (star (vecB B.o B.ζ) ᵥ* (B.V₀.gram * B.d.q0))) ⬝ᵥ (B.d.i₀ *ᵥ vecB B.o B.ζ) = 1 := by
      rw [smul_dotProduct, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.mul_assoc, wittDecomposition_projectionZero_mul_anisotropicInclusion_eq_one, Matrix.mul_one,
        ← Matrix.dotProduct_mulVec, smul_eq_mul]
      exact inv_mul_cancel₀ (besselBasePointLevelNorm_ne_zero B)
    rw [Matrix.mul_apply, Matrix.one_apply_eq]
    simp only [besselBasePointLeftInverse, x0Mat, Matrix.of_apply, Fin.snoc_last]
    exact h
  · have h : ((besselBasePointLevelNorm B)⁻¹ • (star (vecB B.o B.ζ) ᵥ* (B.V₀.gram * B.d.q0))) ᵥ* B.d.e = 0 := by
      rw [Matrix.smul_vecMul, Matrix.vecMul_vecMul, Matrix.mul_assoc, wittDecomposition_projectionZero_mul_e_eq_zero, Matrix.mul_zero, Matrix.vecMul_zero, smul_zero]
    rw [Matrix.mul_apply, Matrix.one_apply_ne (Fin.castSucc_ne_last b).symm]
    simp only [besselBasePointLeftInverse, x0Mat, Matrix.of_apply, Fin.snoc_last, Fin.snoc_castSucc]
    exact congrFun h b
  · have h : B.d.qX *ᵥ (B.d.i₀ *ᵥ vecB B.o B.ζ) = 0 := by
      rw [Matrix.mulVec_mulVec, wittDecomposition_projectionX_mul_anisotropicInclusion_eq_zero, Matrix.zero_mulVec]
    rw [Matrix.mul_apply, Matrix.one_apply_ne (Fin.castSucc_ne_last a)]
    simp only [besselBasePointLeftInverse, x0Mat, Matrix.of_apply, Fin.snoc_last, Fin.snoc_castSucc]
    exact congrFun h a
  · rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Fin.castSucc_inj]
    rw [← Matrix.one_apply (α := D.host.E) (i := a) (j := b), ← besselLevelDatum_qX_dot_e_eq_one B, Matrix.mul_apply]
    simp only [besselBasePointLeftInverse, x0Mat, Matrix.of_apply, Fin.snoc_castSucc]

theorem xLast_rat_leftInv : ∀ (D : D7) (σ : ℕ) (B : BesL D σ),
    (∃ P ∈ ratMx D (σ + 1) B.V.rank, P ⬝ xLast B.d (vecB B.o B.ζ) = 1) ∧ xLast B.d (vecB B.o B.ζ) ∈ ratMx D B.V.rank (σ + 1) := fun _ _ B =>
  ⟨⟨rat (besselBasePointLeftInverse B), rat_mem _, by rw [← rat_x0Mat, ← rat_mul, besselBasePointLeftInverse_mul_snocMatrix, rat_one]⟩, rat_x0Mat B ▸ rat_mem _⟩

end GlobalTheory.Asc.FBL
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselGroupActsBasePointUnitriangular
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.Asc.FBL

variable {D : D7} {σ : ℕ}

def actUni (B : BesL D σ) : Subgroup (GA D B.V) where
  carrier := {g | ∃ u ∈ UX D (σ + 1), mt B.V g ⬝ xLast B.d (vecB B.o B.ζ) = xLast B.d (vecB B.o B.ζ) ⬝ u.1}
  one_mem' := ⟨1, one_mem _, by rw [mt_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]⟩
  mul_mem' := by
    rintro a b ⟨u, hu, ha⟩ ⟨u', hu', hb⟩
    refine ⟨u * u', mul_mem hu hu', ?_⟩
    rw [mt_mul, Matrix.mul_assoc, hb, ← Matrix.mul_assoc, ha, Units.val_mul, Matrix.mul_assoc]
  inv_mem' := by
    rintro a ⟨u, hu, ha⟩
    refine ⟨u⁻¹, inv_mem hu, ?_⟩
    have h1 : mt B.V a⁻¹ ⬝ (xLast B.d (vecB B.o B.ζ) ⬝ u.1) ⬝ (u⁻¹).1 = xLast B.d (vecB B.o B.ζ) ⬝ (u⁻¹).1 := by
      rw [← ha, ← Matrix.mul_assoc, ← mt_mul, inv_mul_cancel, mt_one, Matrix.one_mul]
    rw [← h1, Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

theorem mem_actUni_iff (B : BesL D σ) (g : GA D B.V) : g ∈ actUni B ↔ ∃ u ∈ UX D σ, ∃ v : Fin σ → AE D,
    mt B.V g ⬝ B.d.jX = B.d.jX ⬝ u.1 ∧
      mt B.V g *ᵥ (B.d.j0 *ᵥ ratV (vecB B.o B.ζ)) = B.d.j0 *ᵥ ratV (vecB B.o B.ζ) + B.d.jX *ᵥ v :=
  FB.snocCols_uni_iff (AE D) B.V.rank σ B.d.jX _ (mt B.V g)

theorem flagN_le_actUni (B : BesL D σ) : flagN B.d ≤ actUni B := by
  intro n hn
  obtain ⟨u, hu, b, c, rfl⟩ := ((flag_jacobi_structure D B.V B.V₀ σ B.d).1 n).1 hn
  rw [mem_actUni_iff]
  have hm : mt B.V (B.d.levi u * (B.d.nB b * B.d.nC c)) ⬝ B.d.j0 = B.d.j0 + B.d.jX ⬝ (u.1 ⬝ b) := by
    rw [mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, B.d.nC_j0, B.d.nB_j0, Matrix.mul_add, B.d.wittDecomp_levi_inclAnisotropic,
      ← Matrix.mul_assoc, B.d.levi_jX, Matrix.mul_assoc]
  refine ⟨u, hu, (u.1 ⬝ b) *ᵥ ratV (vecB B.o B.ζ), ?_, ?_⟩
  · rw [mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, B.d.nC_jX, B.d.nB_jX, B.d.levi_jX]
  · rw [Matrix.mulVec_mulVec, hm, Matrix.add_mulVec, Matrix.mulVec_mulVec]

theorem embA_mem_actUni (B : BesL D σ) (h : GA D B.A) : embA B.d B.o h ∈ actUni B := by
  rw [mem_actUni_iff]
  refine ⟨1, one_mem _, 0, ?_, ?_⟩
  · rw [embA_apply, B.d.wittDecomp_anisotropicEmbedding_inclX, Units.val_one, Matrix.mul_one]
  · rw [Matrix.mulVec_zero, add_zero, Matrix.mulVec_mulVec, embA_apply, B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mulVec_mulVec,
      vecB, FB.ratV_mulVec_rat]
    change B.d.j0 *ᵥ (mt B.V₀ (B.o.emb (h, 1)) *ᵥ (B.o.jB *ᵥ ratV B.ζ)) = B.d.j0 *ᵥ (B.o.jB *ᵥ ratV B.ζ)
    congr 1
    rw [Matrix.mulVec_mulVec, B.o.emb_jB, mt_one, Matrix.mul_one]

theorem besGrp_le_actUni (B : BesL D σ) : besGrp B.d B.o ≤ actUni B :=
  sup_le (flagN_le_actUni B) (by rintro _ ⟨h, rfl⟩; exact embA_mem_actUni B h)

theorem mem_besGrp_of_actUni (B : BesL D σ) (g : GA D B.V) (hg : g ∈ actUni B) : g ∈ besGrp B.d B.o := by
  obtain ⟨u, hu, v, hX, h0⟩ := (mem_actUni_iff B g).1 hg
  have hst : B.d.levi u⁻¹ * g ∈ stabX B.d := by
    show mt B.V (B.d.levi u⁻¹ * g) ⬝ B.d.jX = B.d.jX
    rw [mt_mul, Matrix.mul_assoc, hX, ← Matrix.mul_assoc, B.d.levi_jX, Matrix.mul_assoc, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.mul_one]
  obtain ⟨n, hn, k, hk⟩ := ((flag_jacobi_structure D B.V B.V₀ σ B.d).2.2.1 _).1 hst
  obtain ⟨b, c, rfl⟩ := ((flag_jacobi_structure D B.V B.V₀ σ B.d).2.1 n).1 hn
  have hp : B.d.p0 ⬝ mt B.V (B.d.levi u⁻¹ * g) ⬝ B.d.j0 = mt B.V₀ k := by
    rw [hk, mt_mul, mt_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, B.d.wittDecomp_projAnisotropic_unipotentMixed, Matrix.sub_mul, B.d.wittDecomp_projAnisotropic_unipotentSkew,
      Matrix.mul_assoc _ B.d.pY, B.d.pY_nC, Matrix.sub_mul, B.d.wittDecomp_projAnisotropic_anisotropicEmbedding, Matrix.mul_assoc _ B.d.pY, B.d.wittDecomp_projY_anisotropicEmbedding,
      Matrix.sub_mul, Matrix.mul_assoc, B.d.p0_j0, Matrix.mul_one, Matrix.mul_assoc _ B.d.pY, B.d.pY_j0,
      Matrix.mul_zero, sub_zero]
  have hz : mt B.V₀ k *ᵥ ratV (B.o.iB *ᵥ B.ζ) = ratV (B.o.iB *ᵥ B.ζ) := by
    have e1 : B.d.p0 ⬝ mt B.V (B.d.levi u⁻¹ * g) = B.d.p0 ⬝ mt B.V g := by
      rw [mt_mul, ← Matrix.mul_assoc, B.d.wittDecomp_projAnisotropic_levi]
    rw [← hp, e1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    change B.d.p0 *ᵥ (mt B.V g *ᵥ (B.d.j0 *ᵥ ratV (vecB B.o B.ζ))) = _
    rw [h0, Matrix.mulVec_add, Matrix.mulVec_mulVec, B.d.p0_j0, Matrix.one_mulVec, Matrix.mulVec_mulVec, B.d.p0_jX,
      Matrix.zero_mulVec, add_zero]
    rfl
  obtain ⟨h, rfl⟩ := FB.fix_lineVec_emb D B.V₀ B.A B.L B.o B.ζ B.line k hz
  have hg' : g = (B.d.levi u * (B.d.nB b * B.d.nC c)) * embA B.d B.o h := by
    rw [embA_apply, mul_assoc, ← hk, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  rw [hg']
  exact mul_mem (Subgroup.mem_sup_left (((flag_jacobi_structure D B.V B.V₀ σ B.d).1 _).2 ⟨u, hu, b, c, rfl⟩))
    (Subgroup.mem_sup_right ⟨h, rfl⟩)

theorem besGrp_act_xLast : ∀ (D : D7) (σ : ℕ) (B : BesL D σ), (∀ g : GA D B.V, g ∈ besGrp B.d B.o ↔ ∃ u ∈ UX D (σ + 1), mt B.V g ⬝ xLast B.d (vecB B.o B.ζ) = xLast B.d (vecB B.o B.ζ) ⬝ u.1) ∧ (∀ a a' : Mx D (σ + 1) (σ + 1), xLast B.d (vecB B.o B.ζ) ⬝ a = xLast B.d (vecB B.o B.ζ) ⬝ a' → a = a') ∧ ∀ g ∈ GQ B.V, ∀ u : UX D (σ + 1), mt B.V g ⬝ xLast B.d (vecB B.o B.ζ) = xLast B.d (vecB B.o B.ζ) ⬝ u.1.1 → u ∈ UXQ D (σ + 1) := by
  intro D σ B
  obtain ⟨⟨P, hP, hPx⟩, hx⟩ := xLast_rat_leftInv D σ B
  refine ⟨fun g => ⟨fun hg => besGrp_le_actUni B hg, fun hg => mem_besGrp_of_actUni B g hg⟩, ?_, ?_⟩
  · intro a a' h
    rw [← Matrix.one_mul a, ← Matrix.one_mul a', ← hPx, Matrix.mul_assoc, Matrix.mul_assoc, h]
  · intro g hg u hgu
    have hinv : mt B.V g⁻¹ ⬝ xLast B.d (vecB B.o B.ζ) = xLast B.d (vecB B.o B.ζ) ⬝ (u.1⁻¹).1 := by
      have h1 : mt B.V g⁻¹ ⬝ (xLast B.d (vecB B.o B.ζ) ⬝ u.1.1) ⬝ (u.1⁻¹).1 = xLast B.d (vecB B.o B.ζ) ⬝ (u.1⁻¹).1 := by
        rw [← hgu, ← Matrix.mul_assoc, ← mt_mul, inv_mul_cancel, mt_one, Matrix.one_mul]
      rw [← h1, Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    refine ⟨?_, ?_⟩
    · have e : u.1.1 = P ⬝ mt B.V g ⬝ xLast B.d (vecB B.o B.ζ) := by
        rw [Matrix.mul_assoc, hgu, ← Matrix.mul_assoc, hPx, Matrix.one_mul]
      rw [e]; exact ratMx_mul (ratMx_mul hP ((mem_GQ_iff _ _).1 hg)) hx
    · have e : (u.1⁻¹).1 = P ⬝ mt B.V g⁻¹ ⬝ xLast B.d (vecB B.o B.ζ) := by
        rw [Matrix.mul_assoc, hinv, ← Matrix.mul_assoc, hPx, Matrix.one_mul]
      rw [e]; exact ratMx_mul (ratMx_mul hP ((mem_GQ_iff _ _).1 (inv_mem hg))) hx

end GlobalTheory.Asc.FBL

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselGroupActsBasePointUnitriangularStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselGroup_acts_basePoint_unitriangular : ∀ (D : D7) (σ : ℕ) (B : BesL D σ), (∀ g : GA D B.V, g ∈ besGrp B.d B.o ↔ ∃ u ∈ UX D (σ + 1), mt B.V g ⬝ xLast B.d (vecB B.o B.ζ) = xLast B.d (vecB B.o B.ζ) ⬝ u.1) ∧ (∀ a a' : Mx D (σ + 1) (σ + 1), xLast B.d (vecB B.o B.ζ) ⬝ a = xLast B.d (vecB B.o B.ζ) ⬝ a' → a = a') ∧ ∀ g ∈ GQ B.V, ∀ u : UX D (σ + 1), mt B.V g ⬝ xLast B.d (vecB B.o B.ζ) = xLast B.d (vecB B.o B.ζ) ⬝ u.1.1 → u ∈ UXQ D (σ + 1) := by
  first | exact @GlobalTheory.Asc.FBL.besGrp_act_xLast | exact GlobalTheory.Asc.FBL.besGrp_act_xLast | (intros; apply GlobalTheory.Asc.FBL.besGrp_act_xLast <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselBasePointIsUnfoldingBasePointSpec
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.Asc.FBL

variable {D : D7} {σ : ℕ}

def zlQ (B : BesL D σ) : Matrix (Fin B.L.rank) (Fin (σ + 1)) D.host.E := vecMulVec B.ζ (GlobalTheory.Unf.FB.eLast D (σ + 1))

theorem rat_zlQ (B : BesL D σ) : (rat (zlQ B) : Mx D B.L.rank (σ + 1)) = zEll B.L (σ + 1) B.ζ := by
  rw [zEll, ← GlobalTheory.Unf.FB.ratV_eLast]
  funext i j
  simp [rat, zlQ, vecMulVec_apply, ratV]

theorem gramQ_zlQ_mulVec_last (B : BesL D σ) (a : Fin (σ + 1) → D.host.E) :
    (gramQ B.L (zlQ B) *ᵥ a) (Fin.last σ) = (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ) * a (Fin.last σ) := by
  simp only [gramQ, zlQ, Matrix.mulVec, dotProduct, Matrix.mul_apply, conjTranspose_apply, vecMulVec_apply,
    GlobalTheory.Unf.FB.eLast, Pi.star_apply, Fin.val_last]
  simp only [if_true, mul_one, star_one]
  rw [Finset.sum_eq_single (Fin.last σ)]
  · simp only [Fin.val_last, if_true, mul_one]
  · intro b _ hb
    have hb' : ¬ (b.1 + 1 = σ + 1) := fun h => hb (Fin.ext (by simp only [Fin.val_last]; omega))
    simp only [hb', if_false, mul_zero, Finset.sum_const_zero, zero_mul]
  · simp

theorem basePoint_spec : ∀ (D : D7) (σ : ℕ) (B : BesL D σ), ∃ x₀ : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E, (rat x₀ : Mx D B.V.rank (σ + 1)) = xLast B.d (vecB B.o B.ζ) ∧ IsBase B.V x₀ ∧ Rgrp B.V (rat x₀ : Mx D B.V.rank (σ + 1)) = besGrp B.d B.o ∧ (∀ a : Fin (σ + 1) → D.host.E, gramQ B.V x₀ *ᵥ a = 0 → a (Fin.last σ) = 0) ∧ ∀ (S S₀ : HSp D) (d : HypDec S S₀ (σ + 1)) (c : skewA D (σ + 1)), d.qS B.V c (xLast B.d (vecB B.o B.ζ)) = d.qS B.L c (zEll B.L (σ + 1) B.ζ) := by
  intro D σ B
  obtain ⟨x, ⟨hli, hg⟩, hx⟩ := GlobalTheory.T.exists_rational_fullRank_besselBasePoint D σ B
  rw [← rat_zlQ] at hg
  have hG : gramQ B.V x = gramQ B.L (zlQ B) := GlobalTheory.Unf.FB.gramQ_eq_of_gramSkew x (zlQ B) hg
  have hA : adj (xLast B.d (vecB B.o B.ζ)) ⬝ (gA B.V ⬝ xLast B.d (vecB B.o B.ζ)) =
      adj (zEll B.L (σ + 1) B.ζ) ⬝ (gA B.L ⬝ zEll B.L (σ + 1) B.ζ) := by
    rw [← hx, ← rat_zlQ, ← GlobalTheory.Unf.FB.rat_gramQ, ← GlobalTheory.Unf.FB.rat_gramQ, hG]
  refine ⟨x, hx, ⟨hli, fun u hu => ?_⟩, ?_, fun a ha => ?_, fun S S₀ d c => ?_⟩
  · rw [GlobalTheory.Unf.FB.rat_gramQ, hx, hA]
    have hz : zEll B.L (σ + 1) B.ζ ⬝ u.1 = zEll B.L (σ + 1) B.ζ := zEll_mul B.L B.ζ hu
    calc adj u.1 ⬝ (adj (zEll B.L (σ + 1) B.ζ) ⬝ (gA B.L ⬝ zEll B.L (σ + 1) B.ζ) ⬝ u.1)
          = adj (zEll B.L (σ + 1) B.ζ ⬝ u.1) ⬝ (gA B.L ⬝ (zEll B.L (σ + 1) B.ζ ⬝ u.1)) := by
          rw [adj_mul]; simp only [Matrix.mul_assoc]
      _ = adj (zEll B.L (σ + 1) B.ζ) ⬝ (gA B.L ⬝ zEll B.L (σ + 1) B.ζ) := by rw [hz]
  · ext g
    rw [hx]
    exact ((GlobalTheory.T.besselGroup_acts_basePoint_unitriangular D σ B).1 g).symm
  · have h1 := congrFun ha (Fin.last σ)
    rw [hG, gramQ_zlQ_mulVec_last, Pi.zero_apply] at h1
    exact (mul_eq_zero.1 h1).resolve_left B.line.2
  · rw [HypDec.qS, HypDec.qS, HypDec.symplOH_extX_extY, HypDec.symplOH_extX_extY, GlobalTheory.Unf.FB.pairS_mul,
      GlobalTheory.Unf.FB.pairS_mul, hA]

end GlobalTheory.Asc.FBL
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselBasePointIsUnfoldingBasePointSpecStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselBasePoint_isUnfoldingBasePoint_spec : ∀ (D : D7) (σ : ℕ) (B : BesL D σ), ∃ x₀ : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E, (rat x₀ : Mx D B.V.rank (σ + 1)) = xLast B.d (vecB B.o B.ζ) ∧ IsBase B.V x₀ ∧ Rgrp B.V (rat x₀ : Mx D B.V.rank (σ + 1)) = besGrp B.d B.o ∧ (∀ a : Fin (σ + 1) → D.host.E, gramQ B.V x₀ *ᵥ a = 0 → a (Fin.last σ) = 0) ∧ ∀ (S S₀ : HSp D) (d : HypDec S S₀ (σ + 1)) (c : skewA D (σ + 1)), d.qS B.V c (xLast B.d (vecB B.o B.ζ)) = d.qS B.L c (zEll B.L (σ + 1) B.ζ) := by
  first | exact @GlobalTheory.Asc.FBL.basePoint_spec | exact GlobalTheory.Asc.FBL.basePoint_spec | (intros; apply GlobalTheory.Asc.FBL.basePoint_spec <;> assumption)
end

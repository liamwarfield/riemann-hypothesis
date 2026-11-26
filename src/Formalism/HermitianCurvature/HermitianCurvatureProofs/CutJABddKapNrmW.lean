module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsNormBoundThreeFamilies
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStable
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegralNormLeDecay

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddKapNrmW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem kap_Dw_emb (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    PI.UnitaryGroupMassFormula.GsFr.Dw k r * B2.embWb k r μ = B2.embWb k r μ * PI.UnitaryGroupMassFormula.GsFr.Dw k r := by
  ext i j
  simp only [PI.UnitaryGroupMassFormula.GsFr.Dw, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hi : TwoByOneBlock.mid k r i <;> by_cases hj : TwoByOneBlock.mid k r j
  · have hi' : (r ≤ i.val ∧ i.val ≤ r + k) := hi
    have hj' : (r ≤ j.val ∧ j.val ≤ r + k) := hj
    simp [hi', hj']
  · have hi' : (r ≤ i.val ∧ i.val ≤ r + k) := hi
    have hj' : ¬(r ≤ j.val ∧ j.val ≤ r + k) := hj
    have hij : i ≠ j := fun h => hj (h ▸ hi)
    rw [TwoByOneBlock.emb_out_col μ i j hj]
    simp [hi', hj', hij]
  · have hi' : ¬(r ≤ i.val ∧ i.val ≤ r + k) := hi
    have hj' : (r ≤ j.val ∧ j.val ≤ r + k) := hj
    have hij : i ≠ j := fun h => hi (h ▸ hj)
    rw [TwoByOneBlock.emb_out_row μ i j hi]
    simp [hi', hj', hij]
  · have hi' : ¬(r ≤ i.val ∧ i.val ≤ r + k) := hi
    have hj' : ¬(r ≤ j.val ∧ j.val ≤ r + k) := hj
    simp [hi', hj']

theorem wbP_mulVec {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {h : B.Mat k r}
    (hh : h ∈ UWset k r z) (v : Fin (2 * r + k + 1) → ℂ) :
    SSn.wbP k r (h *ᵥ v) = h *ᵥ SSn.wbP k r v := by
  obtain ⟨η, -, -, rfl⟩ := (TwoByOneBlock.UWset_iff hz h).1 hh
  have e : ∀ w, SSn.wbP k r w = PI.UnitaryGroupMassFormula.GsFr.Dw k r *ᵥ w := fun w => by
    rw [PI.UnitaryGroupMassFormula.GsFr.Dw_mulVec]; rfl
  rw [e, e, Matrix.mulVec_mulVec, kap_Dw_emb, ← Matrix.mulVec_mulVec]

theorem kap_prWv_mulVec {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {h : B.Mat k r}
    (hh : h ∈ UWset k r z) (v : Fin (2 * r + k + 1) → ℂ) :
    SSn.prWv k r z (h *ᵥ v) = h *ᵥ SSn.prWv k r z v := by
  have hz' : h *ᵥ z = z := hh.2.2
  have hherm : herm (Hpk k r) (h *ᵥ SSn.wbP k r v) z = herm (Hpk k r) (SSn.wbP k r v) z := by
    conv_lhs => rw [← hz']
    exact Formalism.FourierDecayAlt.P.Qx2.herm_uh hh.1 _ _
  unfold SSn.prWv
  rw [wbP_mulVec hz hh, Matrix.mulVec_add, Matrix.mulVec_smul, hz', hherm]

theorem kap_nrmW_mulVec {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {h : B.Mat k r}
    (hh : h ∈ UWset k r z) (a : Fin (2 * r + k + 1) → ℂ) :
    PRho.nrmW k r z (h *ᵥ a) = PRho.nrmW k r z a := by
  unfold PRho.nrmW
  rw [kap_prWv_mulVec hz hh, Formalism.FourierDecayAlt.P.Qx2.herm_uh hh.1]

theorem kap_mulVec_contDiff {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun a : Fin n → ℂ => M *ᵥ a) := by
  have h := ((LinearMap.toContinuousLinearMap (Matrix.mulVecLin M)).contDiff
    (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).restrict_scalars ℝ
  convert h using 1
  funext a
  rfl

theorem kap_herm_contDiff {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : Fin n → ℂ => herm H u u) := by
  have hconj : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (starRingEnd ℂ) := Complex.conjCLE.contDiff
  have e : (fun u : Fin n → ℂ => herm H u u) = fun u => ∑ i, starRingEnd ℂ (u i) * (H *ᵥ u) i := by
    funext u; simp [herm, dotProduct, Complex.star_def]
  rw [e]
  refine ContDiff.sum fun i _ => ?_
  exact (hconj.comp (contDiff_apply ℝ (fun _ => ℂ) i)).mul ((contDiff_apply ℝ (fun _ => ℂ) i).comp (kap_mulVec_contDiff H))

theorem kap_nrmW_contDiff (z : Fin (2 * r + k + 1) → ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun a => PRho.nrmW k r z a) := by
  have e : (fun a => PRho.nrmW k r z a) =
      fun a => (herm (Hpk k r) (PI.UnitaryGroupMassFormula.GsFr.Pm k r z *ᵥ a) (PI.UnitaryGroupMassFormula.GsFr.Pm k r z *ᵥ a)).re := by
    funext a; unfold PRho.nrmW; rw [PI.UnitaryGroupMassFormula.GsFr.Pm_mulVec]; rfl
  rw [e]
  exact Complex.reCLM.contDiff.comp ((kap_herm_contDiff (Hpk k r)).comp (kap_mulVec_contDiff _))

theorem weighted_norm_facts_hold : NrmWFacts := fun k r z hz _ =>
  ⟨kap_nrmW_contDiff z, fun _ hh a => kap_nrmW_mulVec hz hh a⟩

end

end Formalism.FourierDecayAlt.P.CutMP.JA
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGDegLift
theorem Formalism.FourierDecayAlt.P.degree_of_lift_pairing : Formalism.FourierDecayAlt.KB.DegLift :=
  Formalism.FourierDecayAlt.P.PBG.degLift_of_parts Formalism.FourierDecayAlt.P.left_fubini_normalized_tower Formalism.FourierDecayAlt.P.PBG.right_average_smooth_comm
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaVGrpCut
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.TVG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def RightRuleEv : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ)
    (D : Set (Q.Mx k r)) (f : Q.Mx k r → E), inWb k r z' → IsOpen D → Q.SmoothLev k r 0 D f →
    Q.RightEq k r z' 0 D f → ∀ g ∈ Q.Glev k r 0 ∩ D, ∀ a b : Fin r, b.val < a.val →
      Q.EH k r (esI k r a) (esI k r b) f g = (if a.val = b.val + 1 then (1 : ℂ) else 0) • f g

def LeftRuleCellv : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ)
    (D : Set (Q.Mx k r)) (f : Q.Mx k r → E), inWb k r z → IsOpen D →
    (∀ g ∈ Q.Glev k r 0 ∩ D, ∀ n ∈ Q.Nlev k r 0, n * g ∈ D) → Q.SmoothLev k r 0 D f → Q.LeftEq k r z 0 D f →
    ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), Q.wCell k r (Fin.last r) c * g ∈ D → ∀ a b : Fin r, b.val < a.val →
      Q.EH k r (esI k r b) (esI k r a) f (Q.wCell k r (Fin.last r) c * g) =
        (if a.val = b.val + 1 then star (c a) / star (c b) else 0) • f (Q.wCell k r (Fin.last r) c * g)

def TorusCellv : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (D : Set (Q.Mx k r)) (f : Q.Mx k r → E),
    IsOpen D → Q.SmoothLev k r 0 D f → ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r),
    Q.wCell k r (Fin.last r) c * g ∈ D → ∀ l : Fin r,
      Q.EH k r (esI k r l) (esI k r l) f (Q.wCell k r (Fin.last r) c * g) =
        -pbOp l (fun c' => f (Q.wCell k r (Fin.last r) c' * g)) c

def MirrorChainExpansion : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (M : Type) [AddCommGroup M] [Module ℂ M] (k r : ℕ)
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (La : A →ₗ[ℂ] M) (ρ : ℂ), GlRel E →
    ∀ (m : ℕ) (hm : m + 2 ≤ r) (u : ℂ),
    (∀ (x : A) (a : Fin r), r - m - 1 < a.val → La (x * E (esI k r a) (esI k r ⟨r - m - 2, by omega⟩)) = 0) →
    (∀ x : A, La (x * E (esI k r ⟨r - m - 1, by omega⟩) (esI k r ⟨r - m - 2, by omega⟩)) = La x) →
    (∀ (x : A) (b : Fin r), r - m - 2 < b.val →
      La (E (esI k r ⟨r - m - 2, by omega⟩) (esI k r b) * x) = (if b.val = r - m - 1 then ρ else 0) • La x) →
    La (qminor E (colsVm k r (m + 2)) (colsVm k r (m + 2)) u) =
      La (qminor E (colsVm k r (m + 1)) (colsVm k r (m + 1)) u *
          Tm E (u - ((m + 1 : ℕ) : ℂ)) (esI k r ⟨r - m - 2, by omega⟩) (esI k r ⟨r - m - 2, by omega⟩)) -
        ρ • La (qminor E (colsVm k r m) (colsVm k r m) u)

end Formalism.FourierDecayAlt.P.CutMP.TVG
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentiableAtOfPuncturedSmooth
open scoped ContDiff ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.LevelPointCoordinates

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def V1 (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] : Submodule ℂ (ℂ → E) where
  carrier := {f | ContDiffOn ℝ ∞ f {τ | τ ≠ 0}}
  zero_mem' := contDiffOn_const
  add_mem' := fun hf hg => hf.add hg
  smul_mem' := fun c f hf => by
    change ContDiffOn ℝ ∞ (fun τ => c • f τ) _
    exact hf.const_smul c

theorem isOpen_ne_zero_complex : IsOpen {τ : ℂ | τ ≠ 0} := isOpen_ne

theorem differentiableAt_of_punctured_smooth {f : ℂ → E} (hf : f ∈ V1 E) {τ : ℂ} (hτ : τ ≠ 0) : DifferentiableAt ℝ f τ :=
  (hf.differentiableOn (by simp)).differentiableAt (isOpen_ne_zero_complex.mem_nhds hτ)

theorem contDiffOn_fderiv_punctured {f : ℂ → E} (hf : f ∈ V1 E) (v : ℂ) : ContDiffOn ℝ ∞ (fun τ => fderiv ℝ f τ v) {τ | τ ≠ 0} :=
  (hf.fderiv_of_isOpen isOpen_ne_zero_complex (by simp)).clm_apply contDiffOn_const

theorem contDiffOn_wirtinger_dz {f : ℂ → E} (hf : f ∈ V1 E) : ContDiffOn ℝ ∞ (PBP.dz f) {τ | τ ≠ 0} := by
  unfold PBP.dz
  exact ((contDiffOn_fderiv_punctured hf 1).sub ((contDiffOn_fderiv_punctured hf Complex.I).const_smul Complex.I)).const_smul _

theorem contDiffOn_wirtinger_dzbar {f : ℂ → E} (hf : f ∈ V1 E) : ContDiffOn ℝ ∞ (PBP.dzb f) {τ | τ ≠ 0} := by
  unfold PBP.dzb
  exact ((contDiffOn_fderiv_punctured hf 1).add ((contDiffOn_fderiv_punctured hf Complex.I).const_smul Complex.I)).const_smul _

theorem dz_add {f g : ℂ → E} (hf : f ∈ V1 E) (hg : g ∈ V1 E) {τ : ℂ} (hτ : τ ≠ 0) :
    PBP.dz (f + g) τ = PBP.dz f τ + PBP.dz g τ := by
  unfold PBP.dz
  rw [fderiv_add (differentiableAt_of_punctured_smooth hf hτ) (differentiableAt_of_punctured_smooth hg hτ)]
  simp only [ContinuousLinearMap.add_apply, smul_add, smul_sub]
  abel

theorem dzb_add {f g : ℂ → E} (hf : f ∈ V1 E) (hg : g ∈ V1 E) {τ : ℂ} (hτ : τ ≠ 0) :
    PBP.dzb (f + g) τ = PBP.dzb f τ + PBP.dzb g τ := by
  unfold PBP.dzb
  rw [fderiv_add (differentiableAt_of_punctured_smooth hf hτ) (differentiableAt_of_punctured_smooth hg hτ)]
  simp only [ContinuousLinearMap.add_apply, smul_add]
  abel

theorem dz_smul {f : ℂ → E} (hf : f ∈ V1 E) (c : ℂ) {τ : ℂ} (hτ : τ ≠ 0) :
    PBP.dz (c • f) τ = c • PBP.dz f τ := by
  unfold PBP.dz
  rw [fderiv_const_smul (differentiableAt_of_punctured_smooth hf hτ)]
  simp only [ContinuousLinearMap.smul_apply, smul_sub, smul_comm c Complex.I, smul_comm c (1 / 2 : ℂ)]

theorem dzb_smul {f : ℂ → E} (hf : f ∈ V1 E) (c : ℂ) {τ : ℂ} (hτ : τ ≠ 0) :
    PBP.dzb (c • f) τ = c • PBP.dzb f τ := by
  unfold PBP.dzb
  rw [fderiv_const_smul (differentiableAt_of_punctured_smooth hf hτ)]
  simp only [ContinuousLinearMap.smul_apply, smul_add, smul_comm c Complex.I, smul_comm c (1 / 2 : ℂ)]

def off0 (f : ℂ → E) : ℂ → E := fun τ => if τ = 0 then 0 else f τ

theorem off_zero_mem_punctured_smooth {f : ℂ → E} (hf : ContDiffOn ℝ ∞ f {τ | τ ≠ 0}) : off0 f ∈ V1 E :=
  hf.congr fun τ hτ => by simp [off0, show τ ≠ 0 from hτ]

theorem cd_id : ContDiffOn ℝ ∞ (fun τ : ℂ => τ) {τ | τ ≠ 0} := contDiffOn_id
theorem cd_conj : ContDiffOn ℝ ∞ (fun τ : ℂ => conj τ) {τ | τ ≠ 0} := Complex.conjCLE.contDiff.contDiffOn
theorem cd_inv : ContDiffOn ℝ ∞ (fun τ : ℂ => τ⁻¹) {τ | τ ≠ 0} := by
  intro τ hτ
  exact (contDiffAt_inv ℂ (show τ ≠ 0 from hτ)).restrict_scalars ℝ |>.contDiffWithinAt
theorem cd_conjinv : ContDiffOn ℝ ∞ (fun τ : ℂ => (conj τ)⁻¹) {τ | τ ≠ 0} := by
  intro τ hτ
  have h1 : ContDiffAt ℝ ∞ (fun τ : ℂ => conj τ) τ := Complex.conjCLE.contDiff.contDiffAt
  have h2 : conj τ ≠ 0 := by simpa using (show τ ≠ 0 from hτ)
  exact (((contDiffAt_inv ℂ h2).restrict_scalars ℝ).comp τ h1).contDiffWithinAt

def opP (κ : ℂ) : Module.End ℂ (V1 E) where
  toFun f := ⟨off0 fun τ => τ • PBP.dz f.1 τ + κ • f.1 τ,
    off_zero_mem_punctured_smooth ((cd_id.smul (contDiffOn_wirtinger_dz f.2)).add (f.2.const_smul κ))⟩
  map_add' f g := by
    ext τ
    by_cases hτ : τ = 0
    · simp [off0, hτ]
    · simp only [off0, hτ, if_false, Submodule.coe_add, Pi.add_apply]
      rw [dz_add f.2 g.2 hτ]
      simp only [smul_add]
      abel
  map_smul' c f := by
    ext τ
    by_cases hτ : τ = 0
    · simp [off0, hτ]
    · simp only [off0, hτ, if_false, SetLike.val_smul, Pi.smul_apply, RingHom.id_apply]
      rw [dz_smul f.2 c hτ]
      simp only [smul_add, smul_comm τ c, smul_comm κ c]

def opPb (κ : ℂ) : Module.End ℂ (V1 E) where
  toFun f := ⟨off0 fun τ => conj τ • PBP.dzb f.1 τ + κ • f.1 τ,
    off_zero_mem_punctured_smooth ((cd_conj.smul (contDiffOn_wirtinger_dzbar f.2)).add (f.2.const_smul κ))⟩
  map_add' f g := by
    ext τ
    by_cases hτ : τ = 0
    · simp [off0, hτ]
    · simp only [off0, hτ, if_false, Submodule.coe_add, Pi.add_apply]
      rw [dzb_add f.2 g.2 hτ]
      simp only [smul_add]
      abel
  map_smul' c f := by
    ext τ
    by_cases hτ : τ = 0
    · simp [off0, hτ]
    · simp only [off0, hτ, if_false, SetLike.val_smul, Pi.smul_apply, RingHom.id_apply]
      rw [dzb_smul f.2 c hτ]
      simp only [smul_add, smul_comm (conj τ) c, smul_comm κ c]

def opM (m : ℂ → ℂ) (hm : ContDiffOn ℝ ∞ m {τ | τ ≠ 0}) : Module.End ℂ (V1 E) where
  toFun f := ⟨fun τ => m τ • f.1 τ, hm.smul f.2⟩
  map_add' f g := by ext τ; simp [smul_add]
  map_smul' c f := by ext τ; simp [smul_comm (m τ) c]

def site1 (κ : ℂ) : Wd.Site (Q.Pr (V1 E)) :=
  ⟨Q.mkP (opP κ) (-(opPb κ)), Q.mkP (opM (fun τ => τ) cd_id) (opM (fun τ => conj τ) cd_conj),
    Q.mkP (opM (fun τ => τ⁻¹) cd_inv) (opM (fun τ => (conj τ)⁻¹) cd_conjinv)⟩

def act1 {S : Type} [Fintype S] [DecidableEq S] (M : Wd.SlopeTestRemainingChoices S (Q.Pr (V1 E))) (x : Wd.Ix S → V1 E) : Wd.Ix S → V1 E :=
  fun a => ∑ b, (M a b).1 (x b)

def oneBT {S : Type} [Fintype S] [DecidableEq S] (κ : ℂ) (w : List (Wd.Letter ℂ S)) (x : Wd.Ix S → V1 E) :
    Wd.Ix S → V1 E :=
  act1 (Wd.bT (site1 κ) w) x

end Formalism.FourierDecayAlt.P.LevelPointCoordinates
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.PositivityBoundOfActual
namespace Formalism.FourierDecayAlt.P.PBASM

open Formalism.FourierDecayAlt NumberField Formalism.QuantumDeterminants
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

theorem psd_of_rep {α ι H : Type} [Fintype ι] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Y : Finset α)
    (U : ι → α → H) (K : α → α → ℂ) (hK : ∀ x y, K x y = ∑ k, inner ℂ (U k y) (U k x)) : TB.PSDOn Y K := by
  unfold TB.PSDOn
  have key : (Matrix.of fun x y : Y => K x y) = ∑ k, (Matrix.gram ℂ (fun x : Y => U k x)).transpose := by
    ext x y
    simp only [Matrix.of_apply, Matrix.sum_apply, Matrix.transpose_apply, Matrix.gram_apply, hK]
  rw [key]
  exact Matrix.posSemidef_sum _ fun k _ => (Matrix.posSemidef_gram ℂ _).transpose

theorem psd_smul {α : Type} (Y : Finset α) (k : α → α → ℂ) (a : ℝ) (ha : 0 ≤ a) (hk : TB.PSDOn Y k) :
    TB.PSDOn Y (fun x y => (a : ℂ) * k x y) := by
  rw [PBA.psd_iff_qf] at hk ⊢
  refine ⟨fun x hx y hy => ?_, fun c => ?_⟩
  · rw [hk.1 x hx y hy, map_mul, Complex.conj_ofReal]
  · have : PBA.qf Y (fun x y => (a : ℂ) * k x y) c = (a : ℂ) * PBA.qf Y k c := by
      unfold PBA.qf
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      ring
    rw [this, Complex.re_ofReal_mul]
    exact mul_nonneg ha (hk.2 c)

section top

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}

theorem rr_top_rep (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) :
    ∃ (ι : Type) (_ : Fintype ι) (U : ι → C.LPt → PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)),
      ∀ x y, p.RR F (P.r + 1) w x y = ∑ k, inner ℂ (U k y) (U k x) := by
  by_cases hw : w = []
  · refine ⟨Unit, inferInstance, fun _ x => if D.IsLocPt x (P.r + 1) then
      B.hsVec (D.vecV p.T.base p.ν' p.m₀ F x) else 0, fun x y => ?_⟩
    simp only [Fintype.univ_unit, Finset.sum_singleton]
    unfold KB.Pl.RR D.RRplace
    by_cases hx : D.IsLocPt x (P.r + 1)
    · by_cases hy : D.IsLocPt y (P.r + 1)
      · rw [dite_eq_left ⟨hx, hy⟩, dite_eq_right (by omega), if_pos rfl, if_pos hw]
        simp only [hx, hy, if_true, B.hsInner]
      · rw [dite_eq_right (fun h => hy h.2)]
        simp [hy]
    · rw [dite_eq_right (fun h => hx h.1)]
      simp [hx]
  · refine ⟨Wd.Ix (Fin w.length) × M.Ty P, inferInstance, fun k x => if D.IsLocPt x (P.r + 1) then
      ((Top.dH P p.l0 (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') w x k.1 k.2 : ℝ) : ℂ) •
        B.hsVec ((p.TP.E k.2).comp (D.vecV p.T.base p.ν' p.m₀ (p.Θ.Θ w k.1 F) x)) else 0, fun x y => ?_⟩
    rw [Fintype.sum_prod_type]
    unfold KB.Pl.RR D.RRplace
    by_cases hx : D.IsLocPt x (P.r + 1)
    · by_cases hy : D.IsLocPt y (P.r + 1)
      · rw [dite_eq_left ⟨hx, hy⟩, dite_eq_right (by omega), if_pos rfl, if_neg hw]
        unfold Top.topOf
        refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun ρ _ => ?_
        simp only [hx, hy, if_true, B.hsInner, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
        push_cast
        ring
      · rw [dite_eq_right (fun h => hy h.2)]
        simp [hy]
    · rw [dite_eq_right (fun h => hx h.1)]
      simp [hx]

end top

section pos

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem gN_psdC (hA : P5.ThmPActualCpt) (hFP : ModuleFormPositivity.FormPosCpt) (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (hF : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (hw : KB.CutWord (D.parOf S v) (S.l + 1) w) (Y : Finset C.LPt) :
    TB.PSDOn Y (KB.gN (PBL.setC S p F) v ε j w) := by
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hv⟩ := hB'
  obtain ⟨hl0, -, -, -, -⟩ := hv v
  have hw' : KB.CutWord (D.parOf S v) (p v).l0 w := by rw [hl0]; exact hw
  have hgpos := PBL.g_pos_of_built hB
  have hu : ∀ h, PBL.CV ((p v).T.bs j) (PBL.uY S p F v ε j hj w Y h) := by
    intro h
    unfold PBL.uY
    split_ifs
    · unfold PBL.uB
      split_ifs with hh
      · exact PBL.cv_smul _ fun e => Formalism.FourierDecayAlt.P.slice_compact_support_coefficient _ _ (D.parOf S v) (p v) (F v ε) j hj w _
          ((PBD.isLocPt_toStd_iff _ _ hgpos h 1 j).2 hh) (hF v ε hε) e
      · exact PBL.cv_zero
    · exact PBL.cv_zero
  set c0 : ℝ := 1 / (PBL.ΓS S j * S.sizeAt v w) with hc0
  have hc0n : 0 ≤ c0 := by
    have := PBL.gam_pos hB j
    have := PBL.sizeAt_nonneg S v w
    positivity
  have hG := PBL.gram_psd (PBL.CV (S := Fin w.length) ((p v).T.bs j))
    (fun x y => (c0 : ℂ) * (p v).form j hj w x y) PBL.cv_zero (fun x y hx hy => PBL.cv_add hx hy)
    (fun c x hx => PBL.cv_smul c hx)
    (fun x₁ x₂ y c h₁ h₂ hy => by simp only [PBL.form_slC (p v) j hj w x₁ x₂ y c h₁ h₂ hy]; ring)
    (fun x y₁ y₂ c hx h₁ h₂ => by simp only [PBL.form_srC (p v) j hj w x y₁ y₂ c hx h₁ h₂]; ring)
    (fun x hx => mul_nonneg (by exact_mod_cast hc0n) (hFP hA _ _ (D.parOf S v) (p v) j hj w hw' x hx))
    Y (PBL.uY S p F v ε j hj w Y) hu
  refine PBL.psd_congr (fun x hx y hy => ?_) hG
  show (c0 : ℂ) * (p v).form j hj w (PBL.uY S p F v ε j hj w Y x) (PBL.uY S p F v ε j hj w Y y) = _
  rw [PBL.uY_mem S p F v ε j hj w Y x hx, PBL.uY_mem S p F v ε j hj w Y y hy, PBL.gN_uB hB F hF v ε hε j hj w x y]

theorem gramLoc_top_psd (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (v : Fin S.f) (ε : ℝ)
    (w : List C.Letter) (Y : Finset C.LPt) :
    TB.PSDOn Y ((PBL.setC S p F).gramLoc v ε (S.G.r + 1) w) := by
  obtain ⟨ι, _, U, hU⟩ := rr_top_rep (p v) (F v ε) w
  set a : C.LPt → ℝ := fun x => √(PBL.nnS S x) / PBL.bS S x * √(1 / PBL.ΓS S (S.G.r + 1)) with ha
  have hΓ := PBL.gam_pos hB (S.G.r + 1)
  refine psd_of_rep Y (fun k x => ((a x : ℝ) : ℂ) • U k (PBL.stdS S x)) _ fun x y => ?_
  rw [PBL.gramLoc_setC hB, hU]
  simp only [inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hs : √(1 / PBL.ΓS S (S.G.r + 1)) * √(1 / PBL.ΓS S (S.G.r + 1)) = 1 / PBL.ΓS S (S.G.r + 1) :=
    Real.mul_self_sqrt (by positivity)
  have e1 : ((√(PBL.nnS S x) * √(PBL.nnS S y) : ℝ) : ℂ) *
      ((1 / (PBL.bS S x * PBL.bS S y * PBL.ΓS S (S.G.r + 1)) : ℝ) : ℂ) = ((a y : ℝ) : ℂ) * ((a x : ℝ) : ℂ) := by
    rw [ha]
    push_cast
    rw [show ((√(1 / PBL.ΓS S (S.G.r + 1)) : ℝ) : ℂ) = ((√(1 / PBL.ΓS S (S.G.r + 1)) : ℝ) : ℂ) from rfl]
    have hs' : ((√(1 / PBL.ΓS S (S.G.r + 1)) : ℝ) : ℂ) * ((√(1 / PBL.ΓS S (S.G.r + 1)) : ℝ) : ℂ) =
        1 / (PBL.ΓS S (S.G.r + 1) : ℂ) := by exact_mod_cast hs
    calc _ = (√(PBL.nnS S x) : ℂ) * (√(PBL.nnS S y) : ℂ) * ((PBL.bS S x : ℂ)⁻¹ * (PBL.bS S y : ℂ)⁻¹) *
          (1 / (PBL.ΓS S (S.G.r + 1) : ℂ)) := by rw [one_div, one_div, mul_inv, mul_inv]; ring
      _ = _ := by rw [← hs']; ring
  rw [← mul_assoc, e1]
  ring

end pos

theorem posB_of (hA : P5.ThmPActualCpt) (hFP : ModuleFormPositivity.FormPosCpt) : PosB := by
  intro Cb
  refine ⟨0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hB F hF v ε hε i hi w Y
  change i ≤ S.G.r + 1 at hi
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGo, -⟩ := hB'
  rcases Nat.lt_or_ge i (S.G.r + 1) with hlt | hge
  · have hj : i ≤ S.G.r := by omega
    have hCI := PBCut.cutInside_of_built hB
    have hw := PBD.cutWord_of_adm S hGo hCI w v
    have hpsd := gN_psdC hA hFP hB F hF v ε hε i hj (w.1 v) hw Y
    have hsa := PBL.sizeAt_pos S hGo v (w.1 v) ⟨w, rfl⟩
    refine PBL.psd_congr (fun x _ y _ => ?_) (psd_smul Y _ _ hsa.le hpsd)
    show (S.sizeAt v (w.1 v) : ℂ) * KB.gN (PBL.setC S p F) v ε i (w.1 v) x y = _
    unfold KB.gN
    have : ((PBL.setC S p F).sizeAt v (w.1 v) : ℂ) = (S.sizeAt v (w.1 v) : ℂ) := rfl
    rw [this]
    have hne : (S.sizeAt v (w.1 v) : ℂ) ≠ 0 := by exact_mod_cast hsa.ne'
    field_simp
  · have hi' : i = S.G.r + 1 := by omega
    subst hi'
    exact gramLoc_top_psd hB F v ε (w.1 v) Y

end

end Formalism.FourierDecayAlt.P.PBASM

namespace Formalism.FourierDecayAlt.P

theorem positivity_bound : P5.ThmPActualCpt → PBASM.PosB := fun hA => PBASM.posB_of hA module_form_pos_compact_support

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHSliceFamJF
open MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH

theorem sliceFamJF_cpt {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (j : ℕ)
    (Bs : B.RealPlaceData P.k (P.r - j) Wp Wq) (F : B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))
    (hF : JFOKCpt (JC.parLev P j) Bs.z Bs.z' F) : KB.CptCoef Bs F := by
  obtain ⟨⟨hCC, ε, hε, hεG⟩, hcpt⟩ := hF
  refine ⟨Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic.ckOn_top_of_all (fun m => (hCC 0 m).choose_spec.1), ?_, ε, hε, hεG⟩
  have hcont : Continuous (fun g : B.Mat P.k (P.r - j) => B.gN g) := by
    unfold B.gN
    fun_prop
  obtain ⟨R, hR⟩ := (hcpt.isCompact.image hcont).bddAbove
  refine ⟨R, fun g _ hg => hR ⟨g, subset_tsupport F hg, rfl⟩⟩

private theorem liftVec_injective_apply {k i r' : ℕ} {v w : Fin (2 * r' + k + 1) → ℂ}
    (h : liftVec k i r' v = liftVec k i r' w) : v = w := by
  funext q
  have hq := congrFun h ⟨q.1 + i, by omega⟩
  simp only [liftVec] at hq
  rw [dite_eq_left ⟨by simp, by simp; omega⟩, dite_eq_left ⟨by simp, by simp; omega⟩] at hq
  simpa using hq

private theorem castM_castM_eq_castM_trans {k a b c : ℕ} (h1 : a = b) (h2 : b = c) (h3 : a = c) (g : B.Mat k a) :
    D.castM h2 (D.castM h1 g) = D.castM h3 g := by
  subst h1 h2
  rfl

theorem slice_family_orbital : SliceFamJF := by
  intro Wp Wq _ _ _ _ _ _ P T _ hN j hj _ _ F hF t ht γ hγ hΩ
  have e : P.r - (j + 1) + 1 = P.r - j := by omega
  have hC := sliceFamJF_cpt P j (T.bs j) F hF
  set c : ℂ := ((‖t‖ ^ (2 * (P.r - j) + P.k) : ℝ) : ℂ) with hc
  let f0 : B.Mat P.k (P.r - (j + 1)) → Wq →L[ℂ] Wp := (B.GV P.k (P.r - (j + 1))).indicator fun g =>
    ∫ xx : U.RC P.k 1 (P.r - (j + 1)) × U.RC P.k 1 (P.r - (j + 1)),
      (psi P.k (P.r - j) (T.bs j).z cStd (rn1 e xx.1) *
          star (psi P.k (P.r - j) (T.bs j).z' cStd (rn1 e xx.2))) •
        F ((rn1 e xx.1)⁻¹ * mc e t g * rn1 e xx.2)
      ∂(U.muRC P.k 1 (P.r - (j + 1))).prod (U.muRC P.k 1 (P.r - (j + 1)))
  have hsf : sliceFam T j hj F t = fun g => c • f0 g := by
    funext g
    simp only [sliceFam, f0, Set.indicator]
    split_ifs
    · rfl
    · rw [smul_zero]
  rw [hsf, JCx2.bc_JF_smul]
  congr 1
  obtain ⟨hW1, hW1', hN1⟩ := hN j (by omega)
  obtain ⟨hW0, hW0', hN0⟩ := hN (j + 1) hj
  refine jfStep P.k (P.r - (j + 1)) (P.r - j) e Wp Wq (T.bs j) (T.bs (j + 1)) ?_ ?_ ?_ ?_
    hW1 hW1' hW0 hW0' hN1 hN0 F f0 t ht hC ?_ γ hγ hΩ
  · apply liftVec_injective_apply (i := j)
    apply castV_inj (h := (by omega : j + (P.r - j) = P.r))
    rw [T.z_lev j (by omega), asm_castV_castV,
      lift_lift_V j (P.r - (j + 1)) (P.r - j) P.r (by omega) (by omega) (by omega), T.z_lev (j + 1) hj]
  · apply liftVec_injective_apply (i := j)
    apply castV_inj (h := (by omega : j + (P.r - j) = P.r))
    rw [T.z'_lev j (by omega), asm_castV_castV,
      lift_lift_V j (P.r - (j + 1)) (P.r - j) P.r (by omega) (by omega) (by omega), T.z'_lev (j + 1) hj]
  · intro y
    rw [T.π_lev (j + 1) hj, T.π_lev j (by omega)]
    congr 1
    simp only [lev1]
    rw [castM_castM_eq_castM_trans _ _ (by omega : 1 + (P.r - (j + 1)) = P.r - j),
      lift_lift_M j (P.r - (j + 1)) (P.r - j) P.r (by omega) (by omega) (by omega)]
  · intro y
    rw [T.π'_lev (j + 1) hj, T.π'_lev j (by omega)]
    congr 1
    simp only [lev1]
    rw [castM_castM_eq_castM_trans _ _ (by omega : 1 + (P.r - (j + 1)) = P.r - j),
      lift_lift_M j (P.r - (j + 1)) (P.r - j) P.r (by omega) (by omega) (by omega)]
  · intro g hg
    simp [f0, Set.indicator, hg]

end Formalism.FourierDecayAlt.P.CutSH
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.GNPsdC
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

section C1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem block0C (hA : P5.ThmPActualCpt) (hPSC : StandardPairingDecay.PStdC) (hVI : KB.VIsoCpt) (hFP : FormPosCpt)
    (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (hF : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (hw : KB.CutWord (D.parOf S v) (S.l + 1) w) (l : ℂ) (Y : Finset C.LPt)
    (hY : ∀ h ∈ Y, D.ptSize h = j) :
    KB.BlockPSD Y Y (KB.gN (setC S p F) v ε j w) (KB.hatB (setC S p F) v ε (j + 1) 1 w l)
      (KB.gN (setC S p F) v ε j w) := by
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hv⟩ := hB'
  obtain ⟨hl0, -, -, -, -⟩ := hv v
  have hw' : KB.CutWord (D.parOf S v) (p v).l0 w := by rw [hl0]; exact hw
  set Dv := CV ((p v).T.bs j) (S := Fin w.length) with hDv
  refine block_iso Dv ((p v).form j hj w) cv_zero (fun x y hx hy => cv_add hx hy) (fun c x hx => cv_smul c hx)
    (fun x₁ x₂ y c h₁ h₂ hy => form_slC (p v) j hj w x₁ x₂ y c h₁ h₂ hy)
    (fun x y₁ y₂ c hx h₁ h₂ => form_srC (p v) j hj w x y₁ y₂ c hx h₁ h₂)
    (fun x hx => hFP hA _ _ (D.parOf S v) (p v) j hj w hw' x hx)
    (KB.waveG ((p v).T.bs j) (sW S j l) w) (fun x hx => (hVI hA _ _ (D.parOf S v) (p v) j hj w hw' (sW S j l) x x hx hx).1)
    (fun x y hx hy => (hVI hA _ _ (D.parOf S v) (p v) j hj w hw' (sW S j l) x y hx hy).2)
    Y (uY S p F v ε j hj w Y) (fun h => uY_cv hB F hF v ε hε j hj w Y h)
    (1 / (ΓS S j * S.sizeAt v w)) ?_ _ _ ?_ ?_
  · have : 0 ≤ ΓS S j * S.sizeAt v w := by
      refine mul_nonneg ?_ (sizeAt_nonneg S v w)
      unfold ΓS
      have hgpos := g_pos_of_built hB
      have hrd := PBD.rd_pos' E
      exact (PBD.gamLev_pos _ _ _ _ (by unfold D.kapG; positivity) (by unfold D.deG; positivity) _).le
    positivity
  · intro h hh h' hh'
    rw [uY_mem S p F v ε j hj w Y h hh, uY_mem S p F v ε j hj w Y h' hh']
    exact gN_uB hB F hF v ε hε j hj w h h'
  · intro h hh h' hh'
    rw [uY_mem S p F v ε j hj w Y h hh, uY_mem S p F v ε j hj w Y h' hh']
    exact hatB_uB_C hPSC hB F hF v ε hε j hj w hw l h h' (hY h hh) (hY h' hh')

theorem gN_psdC (hA : P5.ThmPActualCpt) (hFP : FormPosCpt) (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (hF : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (hw : KB.CutWord (D.parOf S v) (S.l + 1) w) (Y : Finset C.LPt) :
    TB.PSDOn Y (KB.gN (setC S p F) v ε j w) := by
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hv⟩ := hB'
  obtain ⟨hl0, -, -, -, -⟩ := hv v
  have hw' : KB.CutWord (D.parOf S v) (p v).l0 w := by rw [hl0]; exact hw
  set c0 : ℝ := 1 / (ΓS S j * S.sizeAt v w) with hc0
  have hc0n : 0 ≤ c0 := by
    have := gam_pos hB j
    have := sizeAt_nonneg S v w
    positivity
  set Dv := CV ((p v).T.bs j) (S := Fin w.length) with hDv
  have hG := gram_psd Dv (fun x y => (c0 : ℂ) * (p v).form j hj w x y) cv_zero (fun x y hx hy => cv_add hx hy)
    (fun c x hx => cv_smul c hx)
    (fun x₁ x₂ y c h₁ h₂ hy => by simp only [form_slC (p v) j hj w x₁ x₂ y c h₁ h₂ hy]; ring)
    (fun x y₁ y₂ c hx h₁ h₂ => by simp only [form_srC (p v) j hj w x y₁ y₂ c hx h₁ h₂]; ring)
    (fun x hx => mul_nonneg (by exact_mod_cast hc0n) (hFP hA _ _ (D.parOf S v) (p v) j hj w hw' x hx))
    Y (uY S p F v ε j hj w Y) (fun h => uY_cv hB F hF v ε hε j hj w Y h)
  refine psd_congr (fun x hx y hy => ?_) hG
  show (c0 : ℂ) * (p v).form j hj w (uY S p F v ε j hj w Y x) (uY S p F v ε j hj w Y y) = _
  rw [uY_mem S p F v ε j hj w Y x hx, uY_mem S p F v ε j hj w Y y hy, gN_uB hB F hF v ε hε j hj w x y]

end C1

end

end Formalism.FourierDecayAlt.P.PBL
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddSSnFinal
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddSSnAsm
open Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn

open NumberField Formalism.FourierDecayAlt.P.CutMP

theorem sSnAssemble_of (hC : JA.DatumCompose) : SSnAssemble := by
  intro hG hR
  obtain ⟨K1, hK1, hG⟩ := hG
  obtain ⟨K2, hK2, hR⟩ := hR
  refine ⟨max K1 K2, le_max_of_le_left hK1, ?_⟩
  intro Cc Cb hCc hCb E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e hFr hGa hQQ l hl
  obtain ⟨a, a', ι, hD⟩ := hG Cc Cb (le_trans (le_max_left _ _) hCc) (le_trans (le_max_left _ _) hCb)
    E Wp Wq S T f χ ν' m₀ top A₀ hB v
  obtain ⟨Φ, Φa, hΦ⟩ := hR Cc (le_trans (le_max_right _ _) hCc) E Wp Wq S T f χ ν' m₀ top A₀ hB v e hFr hGa hQQ l hl
  have hCb0 : 0 ≤ Cb := le_trans (le_max_of_le_left hK1) hCb
  have hBg : 0 ≤ Cb * ((S.G.r : ℝ) + 1) := mul_nonneg hCb0 (by positivity)
  obtain ⟨c, ca, hadj, hc, hca, he, hea, hb, hba, hcv⟩ :=
    hC E Wp Wq S T v _ a a' ι Φ Φa hBg hD ⟨hΦ.1, hΦ.2.1, hΦ.2.2.1, hΦ.2.2.2.1⟩
  refine ⟨c, ca, hadj, hc, hca, he, hea, hb, hba, ?_⟩
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Formalism.QuantumDeterminants.Tz S.G.k S.G.r (T v).base.z * Formalism.QuantumDeterminants.Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl
  intro q hq ρ π
  have hqD : q ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' := ⟨hq.1, hTT ▸ hq.2⟩
  have hG' := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base hqD
  have hpos : B.gq (T v).base q ∈ B.GPos (T v).base := ⟨hG'.1, hG'.2.2⟩
  obtain ⟨h1, h2, h3⟩ := hD.2.2.2.2.2.2.2 q hq
  rw [hcv _ hpos, h1, h2, h3]
  exact hΦ.2.2.2.2 q hq ρ π

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn
end
end

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn

theorem sSnRealiser_of (hCh : ChainBd) (hG : SSnGeom) (hR : SSnRep) : SSnRealiser :=
  sSnAssemble_of (JA.datumCompose_of (JA.datumBd_of_chain hCh)) hG hR

theorem jABddSSnQQ_of_leaves (hCh : ChainBd) (hG : SSnGeom) (hR : SSnRep) : JABddSSnQQ :=
  jABddSSnQQ_of real_to_bounded_holds (sSnRealiser_of hCh hG hR)

theorem jABddSSnStarQQ_of_leaves (hCh : ChainBd) (hG : SSnGeom) (hR : SSnRep) : JABddSSnStarQQ :=
  jABddSSnStarQQ_of real_to_bounded_holds (sSnRealiser_of hCh hG hR)

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepCoreAsm
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core

noncomputable section

theorem theta_gauge_constancy_holds : ThtGaugeConstOfCore := by
  intro hA hPt hTh hE hPR hGL hDU
  intro Cc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ v e hH hk l hl Bw Bw' hBw hBw'
  obtain ⟨hB, hFr, hGa, hQQ⟩ := hH
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  obtain ⟨X⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v)
    (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' hPl
  obtain ⟨d, hd1, hd2, hd3, hd4⟩ := Formalism.FourierDecayAlt.P.normal_form_actual (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v)
    (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' hPl X
  have hAct : ActHyp (D.parOf S v) (T v).base X d := ⟨hPl, hd1, hd2, hd3, hd4⟩
  obtain ⟨SS, hSS⟩ := hPt (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (T v).base hk X d hAct l hl
  obtain ⟨Pr, hPr⟩ := hPR (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (T v).base hPl hk
  obtain ⟨θ, hθ⟩ := hTh (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (T v).base hk X d hAct l hl SS hSS Pr hPr
    Bw Bw' hBw hBw'
  have hFrB : Gauge.IsFrameB (D.parOf S v) (T v).base e := hFr
  have hGQ : GQQ (D.parOf S v) (T v).base e := hQQ
  have hSSF := hA (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (T v).base hk X d hAct e hFrB hGQ
  refine ⟨θ, fun ζ hζ π ρ hup => ?_⟩
  have hent := hE (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (T v).base hk X d hAct e hFrB hSSF l hl SS hSS ζ hζ π ρ
  rw [if_pos hup] at hent
  obtain ⟨hP1, hH1, -, -⟩ := hDU Cc E Wp Wq S T f χ ν' m₀ top A₀ hB v ζ hζ
  set n0 := SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ with hn0
  have hN0 : PRho.nrmW S.G.k S.G.r (T v).base.z n0 = 1 := by
    unfold PRho.nrmW; rw [hP1, hH1]; simp
  obtain ⟨-, -, hrest⟩ := hPr
  have hpos : 0 < PRho.nrmW S.G.k S.G.r (T v).base.z n0 := by rw [hN0]; norm_num

  have hfix : ∀ τ y, Pr τ n0 (e τ ζ y) = e τ ζ y := by
    intro τ y
    refine ((hrest n0 hpos).2.2.2 τ (e τ ζ y)).2 ?_
    intro Fr hFrm w
    rw [hP1] at hFrm
    exact hGL Cc E Wp Wq S T f χ ν' m₀ top A₀ v e ⟨hB, hFr, hGa, hQQ⟩ hk ζ hζ τ Fr hFrm w y
  have hfixc : ∀ τ, (Pr τ n0).comp (e τ ζ) = e τ ζ := fun τ => by ext y; exact hfix τ y
  have hsa := (hrest n0 hpos).2.1 ρ
  have hfib : e π ζ ∈ NF.Fib S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec (T v).base.π (T v).base.π' ζ :=
    ((hFrB.2 ζ hζ).1 π)
  set B0 : Wq (S.pl v) →L[ℂ] Wp (S.pl v) := tht S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π'
    Bw Bw' n0 (SSn.nu0' S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ)
    (SSn.io0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ) (e π ζ) with hB0
  have key : (Pr ρ n0).comp (SS ζ (e π ζ)) = θ π • (Pr ρ n0).comp B0 :=
    hθ ζ hζ π ρ hup (e π ζ) hfib (hfixc π)

  have hmove : ∀ Y : Wq (S.pl v) →L[ℂ] Wp (S.pl v),
      inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec ((Pr ρ n0).comp Y)) = inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec Y) := by
    intro Y
    have h1 := hsInner_lmul (Pr ρ n0) hsa Y (e ρ ζ)
    simp only [B.hsInner, lmul_apply] at h1
    rw [hfixc ρ] at h1
    exact h1
  have hsm : ∀ (c : ℂ) (A : Wq (S.pl v) →L[ℂ] Wp (S.pl v)), B.hsVec (c • A) = c • B.hsVec A := by
    intro c A
    unfold B.hsVec
    ext i
    simp
  calc θ π * inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec B0)
      = θ π * inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec ((Pr ρ n0).comp B0)) := by rw [hmove]
    _ = inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec (θ π • (Pr ρ n0).comp B0)) := by rw [hsm, inner_smul_right]
    _ = inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec ((Pr ρ n0).comp (SS ζ (e π ζ)))) := by rw [key]
    _ = inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec (SS ζ (e π ζ))) := hmove _
    _ = _ := hent

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core
end

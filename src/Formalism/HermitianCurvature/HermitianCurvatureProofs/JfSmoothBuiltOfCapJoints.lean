module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactZeroHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftGeneratorWordEvaluation
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ModelPlaceBuilt2OfChartEqs

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.RightCapelliAsGenerators
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff Topology

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem crag_list {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Bs : Fin k → Fin (2 * r + k + 1) → ℂ) (w : ℂ) (σ : Equiv.Perm (Fin k)) :
    (List.ofFn fun i : Fin k => fun y : Q.Mx k r → E =>
      (if id (σ i) = id i then (w - ((i : ℕ) : ℂ)) • y else 0) +
        Q.RZ (Hpk k r) (Q.unitB (Hpk k r) Bs (id (σ i)) (id i)) y) =
      (capGens (zgB Bs) σ).map (fun gn => genOpR (E := E) gn w) := by
  unfold capGens
  rw [List.map_ofFn]
  congr 1
  funext i F h
  simp only [Function.comp_apply, genOpR, capGen, zgB, Q.RZ, id, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, one_smul, add_zero, Pi.add_apply]
  split_ifs <;> simp

theorem right_capelli_as_generators : CapRAsGens := by
  intro k r E _ _ Bs w f g
  simp only [Q.capR, Q.qmF, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [crag_list]

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CoefficientInterpolationHolds
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

theorem coefficient_interpolation_holds : CoeffInterp := by
  intro N m _hm
  refine ⟨fun i => ((i : ℕ) : ℝ),
    fun i => (Lagrange.basis (Finset.univ : Finset (Fin (N + 1))) (fun j => ((j : ℕ) : ℂ)) i).coeff m, ?_⟩
  intro q hq
  have hinj : Set.InjOn (fun j : Fin (N + 1) => ((j : ℕ) : ℂ)) ((Finset.univ : Finset (Fin (N + 1))) : Set (Fin (N + 1))) := by
    intro a _ b _ hab
    simp only at hab
    exact Fin.ext (by exact_mod_cast hab)
  have hdeg : q.degree < ((Finset.univ : Finset (Fin (N + 1))).card : WithBot ℕ) := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le hq) (by exact_mod_cast Nat.lt_succ_self N)
  have h := Lagrange.eq_interpolate hinj hdeg
  conv_rhs => rw [h]
  rw [Lagrange.interpolate_apply, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Polynomial.coeff_C_mul]
  simp only [Complex.ofReal_natCast]
  ring

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.NilpotentOfCharPoly
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix Polynomial
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem nilpotent_of_char_poly : NilOfCharpoly := by
  intro n M h
  have hmon := Matrix.charpoly_monic M
  have hdeg : M.charpoly.natDegree = n := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hX : M.charpoly = (X : ℂ[X]) ^ n := by
    ext i
    rw [Polynomial.coeff_X_pow]
    rcases lt_trichotomy i n with hi | hi | hi
    · rw [if_neg (by omega)]
      have := h (n - i) (by omega) (by omega)
      rwa [show n - (n - i) = i by omega] at this
    · rw [if_pos hi]
      have h1 := hmon.coeff_natDegree
      rw [hdeg] at h1
      rw [hi]; exact h1
    · rw [if_neg (by omega)]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  refine ⟨n, ?_⟩
  have := Matrix.aeval_self_charpoly M
  rwa [hX, map_pow, Polynomial.aeval_X] at this

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.NilpotentLieFiniteHolds
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

theorem nilpotent_lie_finite_holds : LieNFin := by
  intro k r
  obtain ⟨b, hbS, hspan, hli⟩ := exists_linearIndependent ℝ (JfS.lieOf (Nset k r))
  have hfin : b.Finite := hli.setFinite
  have : Fintype b := hfin.fintype
  let Xs : Fin (Fintype.card b) → B.Mat k r := fun i => ((Fintype.equivFin b).symm i : B.Mat k r)
  have hrange : Set.range Xs = b := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ((Fintype.equivFin b).symm i).2
    · intro hx
      refine ⟨Fintype.equivFin b ⟨x, hx⟩, ?_⟩
      simp [Xs]
  refine ⟨Fintype.card b, Xs, fun i => hbS ((Fintype.equivFin b).symm i).2, fun X hX => ⟨?_, ?_⟩⟩
  · exact LieSplitPf.lieHpk_of (fun t => (hX t).1)
  · have hmem : X ∈ Submodule.span ℝ (Set.range Xs) := by
      rw [hrange, hspan]
      exact Submodule.subset_span hX
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
    refine ⟨a, ?_⟩
    rw [← ha]
    refine Finset.sum_congr rfl fun i _ => ?_
    ext p q
    simp [Matrix.smul_apply, Complex.real_smul]

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.SymbolOperatorLinearHolds
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem symbol_operator_linear_holds : SOpLin := by
  intro d S T c O hST hS hT
  obtain ⟨o, a⟩ := S
  obtain ⟨o', b⟩ := T
  simp only at hST
  subst hST
  refine ⟨⟨o, fun k w x => c * a k w x + b k w x⟩, rfl, ?_, ?_, ?_⟩
  · intro i w
    exact (contDiffOn_const.mul (hS i w)).add (hT i w)
  · intro u x
    simp only [SOp.app, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun w _ => ?_
    ring
  · intro x ξ
    simp only [SOp.symb, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    ring

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.RightChartHolds
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Matrix Filter
open scoped ContDiff Topology

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

local instance rwcN {d n : ℕ} : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ →L[ℝ] (Fin d → ℝ)) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance rwcS {d n : ℕ} : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ →L[ℝ] (Fin d → ℝ)) :=
  ContinuousLinearMap.toNormedSpace

namespace RightChartMultiplication

variable {d : ℕ}

theorem vfD_contDiffOn {V : (Fin d → ℝ) → (Fin d → ℝ)} {u : (Fin d → ℝ) → ℂ} {O : Set (Fin d → ℝ)}
    (hO : IsOpen O) {m : ℕ} (hu : ContDiffOn ℝ ((m + 1 : ℕ) : WithTop ℕ∞) u O) (hV : ContDiffOn ℝ ∞ V O) :
    ContDiffOn ℝ (m : WithTop ℕ∞) (vfD V u) O := by
  have h1 : ContDiffOn ℝ (m : WithTop ℕ∞) (fun x => fderiv ℝ u x) O :=
    hu.fderiv_of_isOpen hO (by push_cast; exact le_rfl)
  exact h1.clm_apply (hV.of_le (by exact_mod_cast le_top))

theorem vfW_contDiffOn {O : Set (Fin d → ℝ)} (hO : IsOpen O) :
    ∀ (Vs : List ((Fin d → ℝ) → (Fin d → ℝ))) (n : ℕ) (u : (Fin d → ℝ) → ℂ),
      ContDiffOn ℝ (n : WithTop ℕ∞) u O → (∀ V ∈ Vs, ContDiffOn ℝ ∞ V O) → Vs.length ≤ n →
      ContDiffOn ℝ ((n - Vs.length : ℕ) : WithTop ℕ∞) (vfW Vs u) O
  | [], n, u, hu, _, _ => by simpa [vfW] using hu
  | V :: Vs, n, u, hu, hV, hl => by
      simp only [List.length_cons] at hl
      have ih := vfW_contDiffOn hO Vs n u hu (fun W hW => hV W (List.mem_cons_of_mem _ hW)) (by omega)
      have e : n - Vs.length = (n - (Vs.length + 1)) + 1 := by omega
      rw [e] at ih
      simp only [vfW, List.length_cons]
      exact vfD_contDiffOn hO ih (hV V (List.mem_cons_self ..))

theorem glev0 {k r : ℕ} {g : B.Mat k r} (hg : g ∈ B.GV k r) : g ∈ Q.Glev k r 0 :=
  ⟨hg, fun _ ha => absurd ha (Nat.not_lt_zero _)⟩

def mulLC {k r : ℕ} (X : B.Mat k r) : B.Mat k r →L[ℝ] B.Mat k r :=
  LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ X)

theorem lcurve_hasDerivAt {k r : ℕ} (X g : B.Mat k r) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) * g) (X * g) 0 := by
  have h1 := P.B5.curve_hasDerivAt (1 : B.Mat k r) X 0
  have h2 := (mulRightRealCLM g).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  simp only [Function.comp_def, mulRightCLM_apply, Matrix.one_mul, Complex.ofReal_zero, zero_smul,
    NormedSpace.exp_zero] at h2
  exact h2

theorem rcurve_hasDerivAt {k r : ℕ} (X g : B.Mat k r) :
    HasDerivAt (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) (g * X) 0 := by
  have h1 := P.B5.curve_hasDerivAt g X 0
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.mul_one] at h1
  exact h1

theorem step {k r : ℕ} {O : Set (Fin d → ℝ)} {U : Set (B.Mat k r)} {κ : (Fin d → ℝ) → B.Mat k r}
    {Φ : B.Mat k r → (Fin d → ℝ)} (hC : IsChart k r d O U κ Φ) (f : B.Mat k r → ℂ) (h : (Fin d → ℝ) → ℂ)
    (hfh : ∀ y ∈ O, f (κ y) = h y) {x : Fin d → ℝ} (hx : x ∈ O) (hh : DifferentiableAt ℝ h x)
    (c : ℝ → B.Mat k r) (v : B.Mat k r) (hc : HasDerivAt c v 0) (hc0 : c 0 = κ x)
    (hcG : ∀ t, c t ∈ B.GV k r) :
    deriv (fun t => f (c t)) 0 = fderiv ℝ h x (fderiv ℝ Φ (κ x) v) := by
  obtain ⟨hO, hU, hκ, hΦ, hκO, hΦU⟩ := hC
  have hxU : κ x ∈ U := (hκO x hx).2.1
  have hΦd : DifferentiableAt ℝ Φ (κ x) :=
    (hΦ.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hxU)
  have hmem : ∀ᶠ t : ℝ in 𝓝 0, c t ∈ U :=
    hc.continuousAt.preimage_mem_nhds (by rw [hc0]; exact hU.mem_nhds hxU)
  have heq : (fun t => f (c t)) =ᶠ[𝓝 0] fun t => h (Φ (c t)) := by
    filter_upwards [hmem] with t ht
    obtain ⟨h1, h2⟩ := hΦU (c t) ht (hcG t)
    rw [← hfh _ h1, h2]
  rw [heq.deriv_eq]
  have hγ : HasDerivAt (fun t => Φ (c t)) (fderiv ℝ Φ (κ x) v) 0 := by
    have := hΦd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hc hc0.symm
    exact this
  have hγ0 : Φ (c 0) = x := by rw [hc0]; exact (hκO x hx).2.2
  exact (hh.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm).deriv

end RightChartMultiplication

open RightChartMultiplication in
theorem right_chart_holds : RwChart := by
  intro k r z z' d O U κ Φ u hC hOm hu
  have hC' := hC
  obtain ⟨hO, hU, hκ, hΦ, hκO, hΦU⟩ := hC

  have h1 : ∀ n : ℕ, n ≤ 2 * r + k + 1 → ContDiffOn ℝ (n : WithTop ℕ∞) (fun x => u (κ x)) O := by
    intro n hn x hx
    obtain ⟨V, F, hVo, hxV, hF, hFu⟩ := hu (κ x) ⟨glev0 (hκO x hx).1, hOm x hx⟩
    have hxV' : κ x ∈ V := hxV
    have hev : ∀ᶠ y in 𝓝[O] x, κ y ∈ V := (hκ.continuousOn x hx) (hVo.mem_nhds hxV')
    have hFκ : ContDiffWithinAt ℝ (n : WithTop ℕ∞) (fun y => F (κ y)) O x :=
      ((hF.contDiffAt (hVo.mem_nhds hxV')).of_le (by exact_mod_cast hn)).comp_contDiffWithinAt x
        ((hκ x hx).of_le (by exact_mod_cast le_top))
    refine hFκ.congr_of_eventuallyEq ?_ (hFu _ hxV' (glev0 (hκO x hx).1))
    filter_upwards [hev, self_mem_nhdsWithin] with y hyV hyO
    exact hFu _ hyV (glev0 (hκO y hyO).1)

  have hDΦ : ContDiffOn ℝ ∞ (fun g => fderiv ℝ Φ g) U :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen hU).1 hΦ).2
  have hDΦκ : ContDiffOn ℝ ∞ (fun x => fderiv ℝ Φ (κ x)) O :=
    hDΦ.comp hκ (fun x hx => (hκO x hx).2.1)
  have hVR : ∀ X : B.Mat k r, ContDiffOn ℝ ∞ (VR κ Φ X) O := fun X =>
    hDΦκ.clm_apply ((mulRightRealCLM X).contDiff.comp_contDiffOn hκ)
  have hVL : ∀ X : B.Mat k r, ContDiffOn ℝ ∞ (VL κ Φ X) O := fun X =>
    hDΦκ.clm_apply ((mulLC X).contDiff.comp_contDiffOn hκ)
  refine ⟨h1 _ le_rfl, fun X => ⟨hVR X, hVL X⟩, ?_⟩

  have hdiff : ∀ (Vs : List ((Fin d → ℝ) → (Fin d → ℝ))), (∀ V ∈ Vs, ContDiffOn ℝ ∞ V O) →
      Vs.length + 1 ≤ 2 * r + k + 1 → ∀ x ∈ O, DifferentiableAt ℝ (vfW Vs fun y => u (κ y)) x := by
    intro Vs hVs hl x hx
    have hc := vfW_contDiffOn hO Vs (2 * r + k + 1) _ (h1 _ le_rfl) hVs (by omega)
    have hle : (1 : WithTop ℕ∞) ≤ ((2 * r + k + 1 - Vs.length : ℕ) : WithTop ℕ∞) := by
      exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1 - Vs.length)
    exact ((hc.differentiableOn (by
      exact ne_of_gt (lt_of_lt_of_le (by norm_num) hle))).differentiableAt (hO.mem_nhds hx))
  intro Xs hXs hl
  induction Xs with
  | nil => intro x _; exact ⟨rfl, rfl⟩
  | cons X Xs ih =>
    have hX : B.inLie k r X := hXs X (List.mem_cons_self ..)
    have ih' := ih (fun Y hY => hXs Y (List.mem_cons_of_mem _ hY))
      (by simp only [List.length_cons] at hl; omega)
    simp only [List.length_cons] at hl
    intro x hx
    have hxG : κ x ∈ B.GV k r := (hκO x hx).1
    constructor
    · show RdV X (B.Rw Xs u) (κ x) = vfD (VR κ Φ X) (vfW (Xs.map (VR κ Φ)) fun y => u (κ y)) x
      unfold RdV vfD VR
      exact step hC' (B.Rw Xs u) _ (fun y hy => (ih' y hy).1) hx
        (hdiff _ (by simpa using fun Y _ => hVR Y) (by simpa using hl) x hx)
        (fun t : ℝ => κ x * NormedSpace.exp ((t : ℂ) • X)) (κ x * X) (rcurve_hasDerivAt X (κ x))
        (by simp [NormedSpace.exp_zero]) (fun t => P.B5.curve_mem hxG hX t)
    · show Q.LdV X (Xs.foldr Q.LdV u) (κ x) =
        vfD (VL κ Φ X) (vfW (Xs.map (VL κ Φ)) fun y => u (κ y)) x
      unfold Q.LdV vfD VL
      exact step hC' (Xs.foldr Q.LdV u) _ (fun y hy => (ih' y hy).2) hx
        (hdiff _ (by simpa using fun Y _ => hVL Y) (by simpa using hl) x hx)
        (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) * κ x) (X * κ x) (lcurve_hasDerivAt X (κ x))
        (by simp [NormedSpace.exp_zero]) (fun t => Formalism.FourierDecayAlt.P.TwoByOneBlock.UH_mul (P.B5.exp_mem hX t) hxG)

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ChartCovarianceHolds
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity.ChartCovPf

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

def bq (H : B.Mat k r) : B.Mat k r →ₗ[ℝ] B.Mat k r →ₗ[ℝ] B.Mat k r :=
  LinearMap.mk₂ ℝ (fun M N => Mᴴ * H * N)
    (fun M M' N => by simp [Matrix.conjTranspose_add, Matrix.add_mul])
    (fun c M N => by simp [Matrix.conjTranspose_smul])
    (fun M N N' => by simp [Matrix.mul_add])
    (fun c M N => by simp)

def bqL (H : B.Mat k r) : B.Mat k r →L[ℝ] B.Mat k r →L[ℝ] B.Mat k r :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (B.Mat k r →ₗ[ℝ] B.Mat k r) ≃ₗ[ℝ] (B.Mat k r →L[ℝ] B.Mat k r)).toLinearMap ∘ₗ
      bq H)

theorem bqL_apply (H M N : B.Mat k r) : bqL H M N = Mᴴ * H * N := rfl

theorem tangent_eq {d : ℕ} {O : Set (Fin d → ℝ)} {κ : (Fin d → ℝ) → B.Mat k r} (hO : IsOpen O)
    (hκ : ContDiffOn ℝ ∞ κ O) (hG : ∀ y ∈ O, κ y ∈ B.GV k r) {x : Fin d → ℝ} (hx : x ∈ O)
    (v : Fin d → ℝ) :
    (fderiv ℝ κ x v)ᴴ * Hpk k r * κ x + (κ x)ᴴ * Hpk k r * fderiv ℝ κ x v = 0 := by
  have hd : DifferentiableAt ℝ κ x := (hκ.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have hl : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hc := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  have hB := (bqL (Hpk k r)).hasDerivAt_of_bilinear (fun _ => hc) (fun _ => hc)
  have hmem : ∀ᶠ t in nhds (0 : ℝ), x + t • v ∈ O := by
    have hcont : Continuous (fun t : ℝ => x + t • v) := by fun_prop
    exact hcont.continuousAt.preimage_mem_nhds (by simpa using hO.mem_nhds hx)
  have hev : (fun _ : ℝ => Hpk k r) =ᶠ[nhds 0]
      fun t : ℝ => bqL (Hpk k r) ((κ ∘ fun t : ℝ => x + t • v) t) ((κ ∘ fun t : ℝ => x + t • v) t) := by
    filter_upwards [hmem] with t ht
    rw [bqL_apply]
    exact (hG _ ht).symm
  have h2 := hB.congr_of_eventuallyEq hev
  have e := h2.deriv
  rw [deriv_const] at e
  simp only [Function.comp_apply, zero_smul, add_zero] at e
  have e' : (κ x)ᴴ * Hpk k r * fderiv ℝ κ x v + (fderiv ℝ κ x v)ᴴ * Hpk k r * κ x = 0 := e.symm
  exact (add_comm _ _).trans e'

theorem chart_id {d : ℕ} {O : Set (Fin d → ℝ)} {U : Set (B.Mat k r)} {κ : (Fin d → ℝ) → B.Mat k r}
    {Φ : B.Mat k r → (Fin d → ℝ)} (hC : IsChart k r d O U κ Φ) {x : Fin d → ℝ} (hx : x ∈ O) (v : Fin d → ℝ) :
    fderiv ℝ Φ (κ x) (fderiv ℝ κ x v) = v := by
  obtain ⟨hO, hU, hκ, hΦ, hκO, _⟩ := hC
  have hd : DifferentiableAt ℝ κ x := (hκ.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have hdΦ : DifferentiableAt ℝ Φ (κ x) :=
    (hΦ.contDiffAt (hU.mem_nhds (hκO x hx).2.1)).differentiableAt (by simp)
  have h1 := hdΦ.hasFDerivAt.comp x hd.hasFDerivAt
  have hev : (Φ ∘ κ) =ᶠ[nhds x] id := by
    filter_upwards [hO.mem_nhds hx] with y hy
    exact (hκO y hy).2.2
  have h2 : HasFDerivAt (Φ ∘ κ) (ContinuousLinearMap.id ℝ (Fin d → ℝ)) x :=
    (hasFDerivAt_id x).congr_of_eventuallyEq hev
  have := h1.unique h2
  exact congrArg (fun L : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) => L v) this

theorem vr_onto {d : ℕ} {O : Set (Fin d → ℝ)} {U : Set (B.Mat k r)} {κ : (Fin d → ℝ) → B.Mat k r}
    {Φ : B.Mat k r → (Fin d → ℝ)} (hC : IsChart k r d O U κ Φ) {x : Fin d → ℝ} (hx : x ∈ O) (v : Fin d → ℝ) :
    ∃ Y : B.Mat k r, B.inLie k r Y ∧ VR κ Φ Y x = v := by
  have hG : ∀ y ∈ O, κ y ∈ B.GV k r := fun y hy => (hC.2.2.2.2.1 y hy).1
  have hg : (κ x)ᴴ * Hpk k r * κ x = Hpk k r := hG x hx
  have hdet : IsUnit (κ x).det := Formalism.FourierDecayAlt.P.PBG.isUnit_det_of_UH (hG x hx)
  have hT := tangent_eq hC.1 hC.2.2.1 hG hx v
  set g := κ x with hgdef
  set A := fderiv ℝ κ x v with hAdef
  refine ⟨g⁻¹ * A, ?_, ?_⟩
  · have e1 : (g⁻¹)ᴴ * Hpk k r = Hpk k r * g := by
      calc (g⁻¹)ᴴ * Hpk k r = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) := by rw [hg]
        _ = (g * g⁻¹)ᴴ * Hpk k r * g := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
        _ = Hpk k r * g := by rw [Matrix.mul_nonsing_inv g hdet]; simp
    have e2 : Hpk k r * g⁻¹ = gᴴ * Hpk k r := by
      calc Hpk k r * g⁻¹ = gᴴ * Hpk k r * g * g⁻¹ := by rw [hg]
        _ = gᴴ * Hpk k r := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv g hdet, Matrix.mul_one]
    show (g⁻¹ * A)ᴴ * Hpk k r + Hpk k r * (g⁻¹ * A) = 0
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, e1, ← Matrix.mul_assoc (Hpk k r), e2, ← Matrix.mul_assoc]
    exact hT
  · show fderiv ℝ Φ g (g * (g⁻¹ * A)) = v
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv g hdet, Matrix.one_mul]
    exact chart_id hC hx v

def ellL {d : ℕ} (κ : (Fin d → ℝ) → B.Mat k r) (Φ : B.Mat k r → (Fin d → ℝ)) (x ξ : Fin d → ℝ) :
    B.Mat k r →ₗ[ℝ] ℝ where
  toFun X := ξ ⬝ᵥ VR κ Φ X x
  map_add' X Y := by simp only [VR, Matrix.mul_add, map_add (f := _), dotProduct_add]
  map_smul' c X := by simp only [VR, Matrix.mul_smul, map_smul, dotProduct_smul, RingHom.id_apply, smul_eq_mul]

theorem ellL_apply {d : ℕ} (κ : (Fin d → ℝ) → B.Mat k r) (Φ : B.Mat k r → (Fin d → ℝ)) (x ξ : Fin d → ℝ)
    (X : B.Mat k r) : ellL κ Φ x ξ X = ξ ⬝ᵥ VR κ Φ X x := rfl

def cMat (ℓ : B.Mat k r →ₗ[ℝ] ℝ) : B.Mat k r :=
  Matrix.of fun j i => ((ℓ (Matrix.single i j 1) : ℝ) : ℂ) - Complex.I * ((ℓ (Complex.I • Matrix.single i j 1) : ℝ) : ℂ)

theorem ell_single (ℓ : B.Mat k r →ₗ[ℝ] ℝ) (i j : Fin (2 * r + k + 1)) (c : ℂ) :
    ℓ (Matrix.single i j c) = c.re * ℓ (Matrix.single i j 1) + c.im * ℓ (Complex.I • Matrix.single i j 1) := by
  have : (Matrix.single i j c : B.Mat k r) =
      c.re • (Matrix.single i j (1 : ℂ) : B.Mat k r) + c.im • (Complex.I • (Matrix.single i j (1 : ℂ) : B.Mat k r)) := by
    ext p q
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.single_apply]
    split_ifs <;> simp
  rw [this, map_add (f := _), map_smul, map_smul, smul_eq_mul, smul_eq_mul]

theorem re_trace_cMat (ℓ : B.Mat k r →ₗ[ℝ] ℝ) (X : B.Mat k r) : (Matrix.trace (cMat ℓ * X)).re = ℓ X := by
  conv_rhs => rw [Matrix.matrix_eq_sum_single X]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, cMat, Matrix.of_apply, Complex.re_sum, Complex.mul_re,
    Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.mul_im]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [ell_single ℓ i j (X i j)]
  norm_num
  ring

theorem inLie_half (C : B.Mat k r) : B.inLie k r ((1 / 2 : ℂ) • (C - Hpk k r * Cᴴ * Hpk k r)) := by
  have hH : Hpk k r * Hpk k r = 1 := (hpkFacts k r).2.1
  have hH' : ∀ M : B.Mat k r, Hpk k r * (Hpk k r * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hH, Matrix.one_mul]
  have hHc : (Hpk k r)ᴴ = Hpk k r := (hpkFacts k r).1
  have hs : star (1 / 2 : ℂ) = 1 / 2 := by simp
  show ((1 / 2 : ℂ) • (C - Hpk k r * Cᴴ * Hpk k r))ᴴ * Hpk k r +
    Hpk k r * ((1 / 2 : ℂ) • (C - Hpk k r * Cᴴ * Hpk k r)) = 0
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hHc,
    Matrix.conjTranspose_conjTranspose, hs]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, hH, hH',
    Matrix.mul_one]
  rw [← smul_add]
  have : Cᴴ * Hpk k r - Hpk k r * C + (Hpk k r * C - Cᴴ * Hpk k r) = 0 := by abel
  rw [this, smul_zero]

theorem re_trace_half (C X : B.Mat k r) (hX : B.inLie k r X) :
    (Matrix.trace ((1 / 2 : ℂ) • (C - Hpk k r * Cᴴ * Hpk k r) * X)).re = (Matrix.trace (C * X)).re := by
  have hH : Hpk k r * Hpk k r = 1 := (hpkFacts k r).2.1
  have hX' : Hpk k r * (X * Hpk k r) = -Xᴴ := by
    have h : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
    have h2 := congrArg (· * Hpk k r) h
    simp only [Matrix.add_mul, Matrix.mul_assoc, hH, Matrix.mul_one, Matrix.zero_mul] at h2
    exact eq_neg_of_add_eq_zero_right h2
  have e1 : Matrix.trace (Hpk k r * Cᴴ * Hpk k r * X) = -star (Matrix.trace (C * X)) := by
    calc Matrix.trace (Hpk k r * Cᴴ * Hpk k r * X) = Matrix.trace (Hpk k r * (Cᴴ * Hpk k r * X)) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.trace (Cᴴ * (Hpk k r * (X * Hpk k r))) := by
          rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
      _ = -Matrix.trace ((X * C)ᴴ) := by
          rw [hX', Matrix.mul_neg, Matrix.trace_neg, Matrix.conjTranspose_mul]
      _ = -star (Matrix.trace (C * X)) := by rw [Matrix.trace_conjTranspose, Matrix.trace_mul_comm]
  rw [Matrix.smul_mul, Matrix.trace_smul, Matrix.sub_mul, Matrix.trace_sub, e1, smul_eq_mul]
  simp [Complex.mul_re]
  ring

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity.ChartCovPf

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity


open ChartCovPf in
theorem chart_covariance_holds : ChartCov := by
  intro k r d O U κ Φ hC x hx ξ
  refine ⟨(1 / 2 : ℂ) • (cMat (ellL κ Φ x ξ) - Hpk k r * (cMat (ellL κ Φ x ξ))ᴴ * Hpk k r),
    inLie_half _, ?_, ?_⟩
  · intro hξ h0
    obtain ⟨Y, hY, hYv⟩ := vr_onto hC hx ξ
    have e := re_trace_half (cMat (ellL κ Φ x ξ)) Y hY
    rw [h0, Matrix.zero_mul, Matrix.trace_zero, Complex.zero_re, re_trace_cMat, ellL_apply, hYv] at e
    exact hξ (dotProduct_self_eq_zero.1 e.symm)
  · intro X hX
    rw [re_trace_half _ X hX, re_trace_cMat, ellL_apply]

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameExistence
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

theorem frame_existence : FrameEx := fun _ _ _ hz hT => Qx8.frame_exists hz hT

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.VectorToSymbolOperator
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace IdentityZeroOperators

variable {d : ℕ}

def idOp (d : ℕ) : SOp d := ⟨0, fun _ _ _ => 1⟩

def zeroOp (d m : ℕ) : SOp d := ⟨m, fun _ _ _ => 0⟩

lemma idOp_app (u : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) : (idOp d).app u x = u x := by
  change ∑ k : Fin 1, ∑ w : Fin k → Fin d, (1 : ℂ) * pdc (List.ofFn w) u x = u x
  rw [Fin.sum_univ_one]
  change ∑ w : Fin 0 → Fin d, (1 : ℂ) * pdc (List.ofFn w) u x = u x
  simp [pdc]

lemma idOp_symb (x ξ : Fin d → ℝ) : (idOp d).symb x ξ = 1 := by
  change ∑ w : Fin 0 → Fin d, (∏ i : Fin 0, (ξ (w i) : ℂ)) * (1 : ℂ) = 1
  simp

lemma zeroOp_app (m : ℕ) (u : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) : (zeroOp d m).app u x = 0 := by
  simp [SOp.app, zeroOp]

lemma zeroOp_symb (m : ℕ) (x ξ : Fin d → ℝ) : (zeroOp d m).symb x ξ = 0 := by
  simp [SOp.symb, zeroOp]

lemma word (hF : SOpField) (O : Set (Fin d → ℝ)) (hO : IsOpen O) :
    ∀ Vs : List ((Fin d → ℝ) → (Fin d → ℝ)), (∀ V ∈ Vs, ContDiffOn ℝ ∞ V O) →
    ∃ S : SOp d, S.ord = Vs.length ∧ (∀ i w, ContDiffOn ℝ ∞ (S.a i w) O) ∧
      (∀ u : (Fin d → ℝ) → ℂ, ContDiffOn ℝ (Vs.length : WithTop ℕ∞) u O → ∀ x ∈ O,
        S.app u x = vfW Vs u x) ∧
      ∀ x ∈ O, ∀ ξ : Fin d → ℝ, S.symb x ξ = (Vs.map fun V => ((ξ ⬝ᵥ V x : ℝ) : ℂ)).prod := by
  intro Vs
  induction Vs with
  | nil =>
    intro _
    exact ⟨idOp d, rfl, fun _ _ => contDiffOn_const, fun u _ x _ => by simp [idOp_app, vfW],
      fun x _ ξ => by simp [idOp_symb]⟩
  | cons V Vs ih =>
    intro hV
    obtain ⟨S, hSo, hSc, hSa, hSs⟩ := ih (fun W hW => hV W (List.mem_cons_of_mem _ hW))
    obtain ⟨S', hS'o, hS'c, hS'a, hS's⟩ := hF d S V O hO hSc (hV V List.mem_cons_self)
    refine ⟨S', by rw [hS'o, hSo]; rfl, hS'c, ?_, ?_⟩
    · intro u hu x hx
      have hl : (V :: Vs).length = S.ord + 1 := by rw [hSo]; rfl
      rw [hl] at hu
      have hu0 : ContDiffOn ℝ (Vs.length : WithTop ℕ∞) u O :=
        hu.of_le (by rw [hSo]; exact_mod_cast Nat.le_succ _)
      rw [hS'a u hu x hx]
      have he : S.app u =ᶠ[nhds x] vfW Vs u := by
        filter_upwards [hO.mem_nhds hx] with y hy
        exact hSa u hu0 y hy
      simp only [vfW, vfD]
      rw [he.fderiv_eq]
    · intro x hx ξ
      rw [hS's x hx ξ, hSs x hx ξ]
      simp

end IdentityZeroOperators

open IdentityZeroOperators in
theorem vector_to_symbol_operator : VOpToSOpOfSteps := by
  intro hF hL hLin d m P O hO hP
  induction P with
  | nil =>
    exact ⟨zeroOp d m, rfl, fun _ _ => contDiffOn_const, fun u _ x _ => by simp [zeroOp_app, WOp.app],
      fun x _ ξ => by simp [zeroOp_symb, WOp.symb]⟩
  | cons t P ih =>
    obtain ⟨T, hTo, hTc, hTa, hTs⟩ := ih (fun s hs => hP s (List.mem_cons_of_mem _ hs))
    obtain ⟨hlen, hsm⟩ := hP t List.mem_cons_self
    obtain ⟨S, hSo, hSc, hSa, hSs⟩ := word hF O hO t.2 hsm
    obtain ⟨S', hS'o, hS'c, hS'a, hS's⟩ := hL d S m O (by rw [hSo]; exact hlen) hSc
    obtain ⟨R, hRo, hRc, hRa, hRs⟩ := hLin d S' T t.1 O (hS'o.trans hTo.symm) hS'c hTc
    refine ⟨R, hRo.trans hS'o, hRc, ?_, ?_⟩
    · intro u hu x hx
      rw [hRa, hS'a, hSa u (hu.of_le (by exact_mod_cast hlen)) x hx, hTa u hu x hx]
      simp [WOp.app]
    · intro x hx ξ
      rw [hRs, hS's, hSs x hx ξ, hTs x hx ξ, hSo]
      simp only [WOp.symb, List.map_cons, List.sum_cons]
      split_ifs <;> simp

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.SymbolOperatorFieldHolds
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace SymbolOperatorExtension

variable {d : ℕ}

def ext (S : SOp d) (n : ℕ) (w : Fin n → Fin d) : (Fin d → ℝ) → ℂ :=
  if h : n < S.ord + 1 then S.a ⟨n, h⟩ w else fun _ => 0

theorem ext_fin (S : SOp d) (k : Fin (S.ord + 1)) (w : Fin k → Fin d) : ext S k w = S.a k w := by
  unfold ext
  rw [dite_eq_left k.isLt]

theorem ext_last (S : SOp d) (w : Fin S.ord → Fin d) : ext S S.ord w = S.a (Fin.last S.ord) w := by
  unfold ext
  rw [dite_eq_left (Nat.lt_succ_self _)]
  rfl

theorem ext_top (S : SOp d) (w : Fin (S.ord + 1) → Fin d) : ext S (S.ord + 1) w = fun _ => 0 := by
  unfold ext
  rw [dite_eq_right (lt_irrefl _)]

theorem ext_contDiffOn (S : SOp d) {O : Set (Fin d → ℝ)} (hS : ∀ i w, ContDiffOn ℝ ∞ (S.a i w) O) (n : ℕ)
    (w : Fin n → Fin d) : ContDiffOn ℝ ∞ (ext S n w) O := by
  unfold ext
  split_ifs with h
  · exact hS _ _
  · exact contDiffOn_const

theorem app_eq (S : SOp d) (u : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) :
    S.app u x = ∑ n ∈ Finset.range (S.ord + 1), ∑ w : Fin n → Fin d, ext S n w x * pdc (List.ofFn w) u x := by
  rw [← Fin.sum_univ_eq_sum_range (fun n => ∑ w : Fin n → Fin d, ext S n w x * pdc (List.ofFn w) u x)]
  unfold SOp.app
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [ext_fin]

theorem pdc_contDiffOn {O : Set (Fin d → ℝ)} (hO : IsOpen O) {u : (Fin d → ℝ) → ℂ} {m : ℕ}
    (hu : ContDiffOn ℝ (m : WithTop ℕ∞) u O) :
    ∀ (l : List (Fin d)) (k : ℕ), l.length + k ≤ m → ContDiffOn ℝ (k : WithTop ℕ∞) (pdc l u) O
  | [], k, h => hu.of_le (by exact_mod_cast (show k ≤ m by simpa using h))
  | i :: l, k, h => by
    have ih := pdc_contDiffOn hO hu l (k + 1) (by simp at h; omega)
    have h1 : ContDiffOn ℝ (k : WithTop ℕ∞) (fderiv ℝ (pdc l u)) O :=
      ih.fderiv_of_isOpen hO (by push_cast; exact le_rfl)
    show ContDiffOn ℝ (k : WithTop ℕ∞) (fun x => fderiv ℝ (pdc l u) x (Pi.single i 1)) O
    exact h1.clm_apply contDiffOn_const

theorem pdc_diffAt {O : Set (Fin d → ℝ)} (hO : IsOpen O) {u : (Fin d → ℝ) → ℂ} {m : ℕ}
    (hu : ContDiffOn ℝ (m : WithTop ℕ∞) u O) (l : List (Fin d)) (hl : l.length + 1 ≤ m) {x : Fin d → ℝ}
    (hx : x ∈ O) : DifferentiableAt ℝ (pdc l u) x :=
  ((pdc_contDiffOn hO hu l 1 hl).differentiableOn (by norm_num)).differentiableAt (hO.mem_nhds hx)

theorem fderiv_apply_sum (f : (Fin d → ℝ) → ℂ) (x v : Fin d → ℝ) :
    fderiv ℝ f x v = ∑ i, (v i : ℂ) * fderiv ℝ f x (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (Pi.single i (v i) : Fin d → ℝ) = v i • (Pi.single i 1 : Fin d → ℝ) := by
    ext j
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  rw [this, map_smul, Complex.real_smul]

theorem sum_fin_succ_fun {n : ℕ} (g : (Fin (n + 1) → Fin d) → ℂ) :
    ∑ w, g w = ∑ i : Fin d, ∑ w : Fin n → Fin d, g (Fin.cons i w) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Fin d)).sum_comp g, Fintype.sum_prod_type]
  rfl

def cD (S : SOp d) (V : (Fin d → ℝ) → (Fin d → ℝ)) (n : ℕ) (w : Fin n → Fin d) (x : Fin d → ℝ) : ℂ :=
  fderiv ℝ (ext S n w) x (V x)

def cE (S : SOp d) (V : (Fin d → ℝ) → (Fin d → ℝ)) : (n : ℕ) → (Fin n → Fin d) → (Fin d → ℝ) → ℂ
  | 0, _, _ => 0
  | n + 1, w, x => ext S n (Fin.tail w) x * ((V x (w 0) : ℝ) : ℂ)

def fieldOp (S : SOp d) (V : (Fin d → ℝ) → (Fin d → ℝ)) : SOp d :=
  ⟨S.ord + 1, fun k w x => cD S V k w x + cE S V k w x⟩

theorem cD_top (S : SOp d) (V : (Fin d → ℝ) → (Fin d → ℝ)) (w : Fin (S.ord + 1) → Fin d) (x : Fin d → ℝ) :
    cD S V (S.ord + 1) w x = 0 := by
  simp [cD, ext_top]

theorem fieldOp_app (S : SOp d) (V : (Fin d → ℝ) → (Fin d → ℝ)) (u : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) :
    (fieldOp S V).app u x = ∑ n ∈ Finset.range (S.ord + 1 + 1),
      ∑ w : Fin n → Fin d, (cD S V n w x + cE S V n w x) * pdc (List.ofFn w) u x := by
  unfold SOp.app fieldOp
  exact Fin.sum_univ_eq_sum_range
    (fun n => ∑ w : Fin n → Fin d, (cD S V n w x + cE S V n w x) * pdc (List.ofFn w) u x) (S.ord + 1 + 1)

end SymbolOperatorExtension

open SymbolOperatorExtension in
theorem symbol_operator_field_holds : SOpField := by
  intro d S V O hO hS hV
  refine ⟨fieldOp S V, rfl, ?_, ?_, ?_⟩
  · intro k w
    show ContDiffOn ℝ ∞ (fun x => cD S V k w x + cE S V k w x) O
    refine ContDiffOn.add ?_ ?_
    · exact ((ext_contDiffOn S hS k w).fderiv_of_isOpen hO (by simp)).clm_apply hV
    · rcases k with ⟨_ | n, hk⟩
      · exact contDiffOn_const
      · have hv : ContDiffOn ℝ ∞ (fun x => ((V x (w 0) : ℝ) : ℂ)) O := by
          have := Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_pi.mp hV (w 0))
          simpa [Function.comp_def] using this
        exact (ext_contDiffOn S hS n _).mul hv
  · intro u hu x hx
    have hdiff : ∀ n ∈ Finset.range (S.ord + 1), ∀ w : Fin n → Fin d,
        DifferentiableAt ℝ (ext S n w) x ∧ DifferentiableAt ℝ (pdc (List.ofFn w) u) x := by
      intro n hn w
      refine ⟨((ext_contDiffOn S hS n w).differentiableOn (by simp)).differentiableAt (hO.mem_nhds hx),
        pdc_diffAt hO hu _ ?_ hx⟩
      have := Finset.mem_range.mp hn
      simp only [List.length_ofFn]
      omega
    have key : ∀ n ∈ Finset.range (S.ord + 1),
        fderiv ℝ (fun y => ∑ w : Fin n → Fin d, ext S n w y * pdc (List.ofFn w) u y) x (V x) =
          ∑ w : Fin n → Fin d, (cD S V n w x * pdc (List.ofFn w) u x +
            ∑ i, ext S n w x * ((V x i : ℝ) : ℂ) * pdc (i :: List.ofFn w) u x) := by
      intro n hn
      rw [fderiv_fun_sum (A := fun w y => ext S n w y * pdc (List.ofFn w) u y)
        (fun w _ => (hdiff n hn w).1.mul (hdiff n hn w).2), ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [fderiv_fun_mul (hdiff n hn w).1 (hdiff n hn w).2, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, smul_eq_mul,
        fderiv_apply_sum (pdc (List.ofFn w) u), Finset.mul_sum, add_comm]
      congr 1
      · simp only [cD]; ring
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_assoc]
        rfl
    have hR : fderiv ℝ (S.app u) x (V x) = ∑ n ∈ Finset.range (S.ord + 1), ∑ w : Fin n → Fin d,
        (cD S V n w x * pdc (List.ofFn w) u x +
          ∑ i, ext S n w x * ((V x i : ℝ) : ℂ) * pdc (i :: List.ofFn w) u x) := by
      have hSu : S.app u = fun y => ∑ n ∈ Finset.range (S.ord + 1),
          ∑ w : Fin n → Fin d, ext S n w y * pdc (List.ofFn w) u y := funext (app_eq S u)
      rw [hSu, fderiv_fun_sum (A := fun n y => ∑ w : Fin n → Fin d, ext S n w y * pdc (List.ofFn w) u y)
        (fun n hn => DifferentiableAt.fun_sum (A := fun w y => ext S n w y * pdc (List.ofFn w) u y) fun w _ =>
        (hdiff n hn w).1.mul (hdiff n hn w).2), ContinuousLinearMap.sum_apply]
      exact Finset.sum_congr rfl key
    have hsplit : ∀ n, ∑ w : Fin n → Fin d, (cD S V n w x + cE S V n w x) * pdc (List.ofFn w) u x =
        ∑ w : Fin n → Fin d, cD S V n w x * pdc (List.ofFn w) u x +
          ∑ w : Fin n → Fin d, cE S V n w x * pdc (List.ofFn w) u x := by
      intro n
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun w _ => add_mul _ _ _
    have hD : ∑ n ∈ Finset.range (S.ord + 1 + 1), ∑ w : Fin n → Fin d, cD S V n w x * pdc (List.ofFn w) u x =
        ∑ n ∈ Finset.range (S.ord + 1), ∑ w : Fin n → Fin d, cD S V n w x * pdc (List.ofFn w) u x := by
      rw [Finset.sum_range_succ]
      simp [cD_top]
    have hE : ∑ n ∈ Finset.range (S.ord + 1 + 1), ∑ w : Fin n → Fin d, cE S V n w x * pdc (List.ofFn w) u x =
        ∑ n ∈ Finset.range (S.ord + 1), ∑ w : Fin n → Fin d,
          ∑ i, ext S n w x * ((V x i : ℝ) : ℂ) * pdc (i :: List.ofFn w) u x := by
      rw [Finset.sum_range_succ']
      simp only [cE, zero_mul, Finset.sum_const_zero, add_zero]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [sum_fin_succ_fun, Finset.sum_comm]
      refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun i _ => ?_
      simp only [Fin.cons_zero, Fin.tail_cons, List.ofFn_succ, Fin.cons_succ]
    rw [fieldOp_app]
    simp only [hsplit]
    rw [Finset.sum_add_distrib, hD, hE, ← Finset.sum_add_distrib]
    show _ = fderiv ℝ (S.app u) x (V x)
    rw [hR]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_add_distrib]
  · intro x _ ξ
    show ∑ w : Fin (S.ord + 1) → Fin d, (∏ i, (ξ (w i) : ℂ)) * (cD S V (S.ord + 1) w x + cE S V (S.ord + 1) w x) = _
    simp only [cD_top, zero_add, cE]
    rw [sum_fin_succ_fun]
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.tail_cons, Fin.cons_succ]
    unfold SOp.symb
    simp only [dotProduct]
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [ext_last]
    ring

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.SymbolOperatorLiftHolds
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def liftA {d o : ℕ} (a : (k : Fin (o + 1)) → (Fin k → Fin d) → (Fin d → ℝ) → ℂ) (m' : ℕ) :
    (k : Fin (m' + 1)) → (Fin k → Fin d) → (Fin d → ℝ) → ℂ :=
  fun k w x => if h : (k : ℕ) ≤ o then a ⟨k, by omega⟩ w x else 0

theorem symbol_operator_lift_holds : SOpLift := by
  intro d S m' O hle hS
  obtain ⟨o, a⟩ := S
  simp only at hle
  refine ⟨⟨m', liftA a m'⟩, rfl, ?_, ?_, ?_⟩
  · intro i w
    change ContDiffOn ℝ ∞ (liftA a m' i w) O
    by_cases h : (i : ℕ) ≤ o
    · have e : liftA a m' i w = a ⟨i, by omega⟩ w := funext fun x => dif_pos h
      rw [e]
      exact hS (⟨i, Nat.lt_succ_of_le h⟩ : Fin (o + 1)) w
    · have e : liftA a m' i w = fun _ => 0 := funext fun x => dif_neg h
      rw [e]
      exact contDiffOn_const
  · intro u x
    simp only [SOp.app]
    let F : ℕ → ℂ := fun n =>
      if h : n ≤ o then ∑ w : Fin n → Fin d, a ⟨n, by omega⟩ w x * pdc (List.ofFn w) u x else 0
    have h1 : ∑ k : Fin (m' + 1), ∑ w : Fin k → Fin d, liftA a m' k w x * pdc (List.ofFn w) u x =
        ∑ k : Fin (m' + 1), F k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [F, liftA]
      split_ifs with h
      · rfl
      · simp
    have h2 : ∑ k : Fin (o + 1), ∑ w : Fin k → Fin d, a k w x * pdc (List.ofFn w) u x =
        ∑ k : Fin (o + 1), F k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [F]
      rw [dif_pos (by omega)]
    rw [h1, h2, Fin.sum_univ_eq_sum_range F, Fin.sum_univ_eq_sum_range F]
    symm
    apply Finset.sum_subset
    · intro n hn
      simp only [Finset.mem_range] at hn ⊢
      omega
    · intro n hn hn'
      simp only [Finset.mem_range] at hn hn'
      simp only [F]
      rw [dif_neg (by omega)]
  · intro x ξ
    simp only [SOp.symb]
    by_cases h : o = m'
    · subst h
      rw [if_pos rfl]
      refine Finset.sum_congr rfl fun w _ => ?_
      simp only [liftA]
      rw [dif_pos (by simp)]
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun w _ => ?_
      simp only [liftA]
      rw [dif_neg (by simp; omega)]
      simp

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

theorem chartEqs_of_capJoints (hJ : CapWordsOfParts) (hJR : CapRWordsOfParts) (hJL : CapLWordsOfParts) :
    ChartEqs := by
  obtain ⟨h4, h5, h6⟩ := capWords_all_of hJ hJR hJL derivative_local_representative right_exponential_evaluation left_exponential_evaluation capelli_vector_as_generators
    right_capelli_as_generators left_capelli_as_generators exponential_degree_holds exponential_symbol_holds determinant_shift_coefficient coefficient_interpolation_holds
  exact chartEqs_of_J operator_capelli_vector operator_right_capelli operator_left_capelli nilpotent_of_char_poly conjugation_algebraic_holds left_covariance_chart_holds
    chart_covariance_holds right_chart_holds nilpotent_lie_finite_holds h4 h5 h6 compact_zero_holds frame_existence vector_to_symbol_operator
    symbol_operator_field_holds symbol_operator_lift_holds symbol_operator_linear_holds

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

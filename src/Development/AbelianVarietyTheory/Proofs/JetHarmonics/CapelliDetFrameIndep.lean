module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SingleMulVecOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagonalTransferAction
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QminorPolyMap
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WigMapZeroOfContraction
public import Development.AbelianVarietyTheory.Definitions.Jets.SameFns
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SigmaContOn
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsUniqueIsAl
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.OmgEquivariant

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliDetFrameIndep
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory

theorem capelli_det_frame_indep : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mx k r → (V →L[ℂ] V)) (B B' : Fin k → (Fin (2 * r + k + 1) → ℂ)), inWb k r z → 0 < Tz k r z → IsRepW k r z π → IsFrameOf k r [z] B → IsFrameOf k r [z] B' → ∀ w : ℂ, qdet (EB π B) w = qdet (EB π B') w :=
  fun _ _ _ _ _ _ _ _ _ _ hz hT hπ hB hB' w => Formalism.FourierDecayAlt.P.QrCap.capChange hz hT hπ hB hB' w

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.AdjointMemCapSpSubA
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)
namespace GlobalTheory

theorem adjoint_mem_CapSp_subA : ∀ (V₁ : Type) [NormedAddCommGroup V₁] [InnerProductSpace ℂ V₁] [FiniteDimensional ℂ V₁] (V₂ : Type) [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] [FiniteDimensional ℂ V₂] (n r : ℕ) (z : (Fin (2 * r + (n + 1) + 1) → ℂ)) (π₁ : Mx (n + 1) r → (V₁ →L[ℂ] V₁)) (π₂ : Mx (n + 1) r → (V₂ →L[ℂ] V₂)) (B : Fin (n + 1) → (Fin (2 * r + (n + 1) + 1) → ℂ)) (T : V₂ →L[ℂ] V₁) (μ : Fin n → ℂ), IsRepW (n + 1) r z π₁ → IsRepW (n + 1) r z π₂ → (∀ h ∈ UWset (n + 1) r z, ∀ v, ‖π₁ h v‖ = ‖v‖) → (∀ h ∈ UWset (n + 1) r z, ∀ v, ‖π₂ h v‖ = ‖v‖) → IsFrameOf (n + 1) r [z] B → (∀ h ∈ UWset (n + 1) r z, h *ᵥ B (Fin.last n) = B (Fin.last n) → T.comp (π₂ h) = (π₁ h).comp T) → ∀ v ∈ CapSp (subA (EB π₁ B)) μ, ContinuousLinearMap.adjoint T v ∈ CapSp (subA (EB π₂ B)) μ := by
  intro V₁ _ _ _ V₂ _ _ _ n r z π₁ π₂ B T μ h₁ h₂ hu₁ hu₂ hB hT v hv
  have hB' : IsFrameOf (n + 1) r [z, B (Fin.last n)] (fun a : Fin n => B a.castSucc) := by
    refine ⟨fun a => hB.1 _, fun a b => ?_, fun a x hx => ?_⟩
    · rw [hB.2.1]
      simp only [Fin.castSucc_inj]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hx | hx
      · exact hB.2.2 _ x (by simp [hx])
      · rw [hx, hB.2.1, if_neg (Fin.castSucc_lt_last a).ne]
  have hlie := GlobalTheory.intertwiner_EB_of_stabiliser V₂ V₁ (n + 1) r n z (B (Fin.last n)) π₂ π₁ T
    (fun a : Fin n => B a.castSucc) h₂ h₁ hB' (fun h hh he w => by
      have := congrArg (fun S : V₂ →L[ℂ] V₁ => S w) (hT h hh he)
      simpa using this)
  have hlie' : ∀ (a b : Fin n) (w : V₂),
      T (EB π₂ B a.castSucc b.castSucc w) = EB π₁ B a.castSucc b.castSucc (T w) := hlie
  have hadj : ∀ (a b : Fin n) (w : V₁),
      (ContinuousLinearMap.adjoint T).toLinearMap (subA (EB π₁ B) a b w) =
        subA (EB π₂ B) a b ((ContinuousLinearMap.adjoint T).toLinearMap w) := by
    intro a b w
    apply ext_inner_right ℂ
    intro y
    show inner ℂ (ContinuousLinearMap.adjoint T (EB π₁ B a.castSucc b.castSucc w)) y =
      inner ℂ (EB π₂ B a.castSucc b.castSucc (ContinuousLinearMap.adjoint T w)) y
    rw [ContinuousLinearMap.adjoint_inner_left,
      Formalism.FourierDecayAlt.P5.Kfp.EB_adj h₁.1 h₁.2 hu₁ hB, Formalism.FourierDecayAlt.P5.Kfp.EB_adj h₂.1 h₂.2 hu₂ hB,
      ContinuousLinearMap.adjoint_inner_left, hlie']
  rw [mem_CapSp] at hv ⊢
  intro w
  have hq := qminor_intertwine V₂ V₁ n n (subA (EB π₂ B)) (subA (EB π₁ B))
    (ContinuousLinearMap.adjoint T).toLinearMap hadj id id w v
  have hq' : ContinuousLinearMap.adjoint T (qdet (subA (EB π₁ B)) w v) =
      qdet (subA (EB π₂ B)) w (ContinuousLinearMap.adjoint T v) := hq
  rw [← hq', hv w, map_smul]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RadialPairConstantsPointwiseAdjointBounded
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RadialPairConstantsPointwiseAdjointBounded
open scoped ComplexOrder InnerProductSpace

namespace GlobalTheory.HatNF

section abstract

variable {V E ι : Type} [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem ev_symm_of_nonneg (ev : V →ₗ[ℂ] E) (T : Module.End ℂ V) (h : ∀ v, 0 ≤ ⟪ev v, ev (T v)⟫_ℂ) (v w : V) :
    ⟪ev w, ev (T v)⟫_ℂ = ⟪ev (T w), ev v⟫_ℂ := by
  have hd : ∀ u, ⟪ev u, ev (T u)⟫_ℂ = ⟪ev (T u), ev u⟫_ℂ := by
    intro u
    rw [← inner_conj_symm (ev (T u)) (ev u)]
    exact (Complex.conj_eq_iff_im.mpr (Complex.nonneg_iff.mp (h u)).2.symm).symm
  have h1 := hd (v + w)
  have h2 := hd (v + Complex.I • w)
  have h3 := hd v
  have h4 := hd w
  simp only [map_add (f := _), map_smul, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    Complex.conj_I] at h1 h2
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (1 / 2 : ℂ) * h1 + (Complex.I / 2) * h2 - (1 / 2 + Complex.I / 2) * h3
    - (1 / 2 + Complex.I / 2 * (-Complex.I * Complex.I)) * h4
    + (1 / 2 : ℂ) * (⟪ev w, ev (T v)⟫_ℂ - ⟪ev (T w), ev v⟫_ℂ - ⟪ev v, ev (T w)⟫_ℂ + ⟪ev (T v), ev w⟫_ℂ) * hI

variable [Fintype ι] [DecidableEq ι]

theorem ev_symm_single (ev : V →ₗ[ℂ] E) (K : (ι → ℂ) →ₐ[ℂ] Module.End ℂ V)
    (h : ∀ f : ι → ℂ, (∀ i, 0 < f i) → ∀ v, 0 ≤ ⟪ev v, ev (K f v)⟫_ℂ) (i : ι) (v w : V) :
    ⟪ev w, ev (K (Pi.single i 1) v)⟫_ℂ = ⟪ev (K (Pi.single i 1) w), ev v⟫_ℂ := by
  have hp : ∀ j, (0 : ℂ) < ((Pi.single i 1 : ι → ℂ) + 1) j := by
    intro j
    by_cases hj : j = i
    · subst hj
      simpa using add_pos (zero_lt_one' ℂ) (zero_lt_one' ℂ)
    · simp [hj]
  have h1 := ev_symm_of_nonneg ev _ (h _ hp) v w
  simp only [map_add (f := _), map_one, LinearMap.add_apply, Module.End.one_apply, inner_add_left, inner_add_right] at h1
  linear_combination h1

theorem algHom_apply_eq_sum (ev : V →ₗ[ℂ] E) (K : (ι → ℂ) →ₐ[ℂ] Module.End ℂ V) (f : ι → ℂ) (v : V) :
    ev (K f v) = ∑ i, f i • ev (K (Pi.single i 1) v) := by
  have hf : f = ∑ i, f i • (Pi.single i 1 : ι → ℂ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hf]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]

theorem ev_adj (ev : V →ₗ[ℂ] E) (K : (ι → ℂ) →ₐ[ℂ] Module.End ℂ V)
    (h : ∀ f : ι → ℂ, (∀ i, 0 < f i) → ∀ v, 0 ≤ ⟪ev v, ev (K f v)⟫_ℂ) (f : ι → ℂ) (v w : V) :
    ⟪ev w, ev (K f v)⟫_ℂ = ⟪ev (K (fun i => star (f i)) w), ev v⟫_ℂ := by
  rw [algHom_apply_eq_sum, algHom_apply_eq_sum ev K (fun i => star (f i)), inner_sum, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_right, inner_smul_left, ev_symm_single ev K h]
  simp

theorem ev_single_le (ev : V →ₗ[ℂ] E) (K : (ι → ℂ) →ₐ[ℂ] Module.End ℂ V)
    (h : ∀ f : ι → ℂ, (∀ i, 0 < f i) → ∀ v, 0 ≤ ⟪ev v, ev (K f v)⟫_ℂ) (i : ι) (v : V) :
    ‖ev (K (Pi.single i 1) v)‖ ≤ ‖ev v‖ := by
  have hid : K (Pi.single i 1) (K (Pi.single i 1) v) = K (Pi.single i 1) v := by
    rw [← Module.End.mul_apply, ← map_mul, ← Pi.single_mul, mul_one]
  have h1 := ev_symm_single ev K h i v (K (Pi.single i 1) v)
  rw [hid] at h1
  set a := ev (K (Pi.single i 1) v)
  have h2 : ‖a‖ * ‖a‖ ≤ ‖a‖ * ‖ev v‖ := by
    calc ‖a‖ * ‖a‖ = ‖⟪a, a⟫_ℂ‖ := by
          rw [inner_self_eq_norm_sq_to_K]
          simp [sq]
      _ = ‖⟪a, ev v⟫_ℂ‖ := by rw [h1]
      _ ≤ _ := norm_inner_le_norm _ _
  rcases (norm_nonneg a).eq_or_lt with h0 | h0
  · rw [← h0]
    exact norm_nonneg _
  · exact le_of_mul_le_mul_left h2 h0

theorem ev_le (ev : V →ₗ[ℂ] E) (K : (ι → ℂ) →ₐ[ℂ] Module.End ℂ V)
    (h : ∀ f : ι → ℂ, (∀ i, 0 < f i) → ∀ v, 0 ≤ ⟪ev v, ev (K f v)⟫_ℂ) (f : ι → ℂ) (v : V) :
    ‖ev (K f v)‖ ≤ (∑ i, ‖f i‖) * ‖ev v‖ := by
  rw [algHom_apply_eq_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (ev_single_le ev K h i v) (norm_nonneg _)

end abstract

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

theorem kappa_ptAdj_ptB : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ f : M.Ty P → ℂ, PtAdj P Bs (d.κ f) ∧ PtB P Bs (d.κ f) := by
  intro Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 d hD hN f
  classical
  let ev : (Fin P.r → ℂ) × Q.Mx P.k P.r →
      Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' →ₗ[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) := fun x =>
    { toFun := fun Φ => B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let K : (M.Ty P → ℂ) →ₐ[ℂ] Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :=
    (P5.Kfp.fstAlg _).comp d.κ
  have hpos : ∀ x, ∀ g : M.Ty P → ℂ, (∀ i, 0 < g i) → ∀ v, 0 ≤ ⟪ev x v, ev x (K g v)⟫_ℂ := fun x g hg v =>
    P5.kappaFibrePos Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hD.1 X d hN.1 hN.2.1 hN.2.2.1 hN.2.2.2 g hg v x.1 x.2
  refine ⟨fun Φ Ψ x _ => ?_, ∑ i, ‖f i‖, Finset.sum_nonneg fun _ _ => norm_nonneg _, fun Φ x _ => ?_⟩
  · rw [hN.2.2.1.1 f]
    exact ev_adj (ev x) K (hpos x) f Φ Ψ
  · exact ev_le (ev x) K (hpos x) f Φ

end GlobalTheory.HatNF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RadialPairConstantsPointwiseAdjointBoundedStatement
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.radialPairConstants_pointwiseAdjoint_bounded : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ f : M.Ty P → ℂ, PtAdj P Bs (d.κ f) ∧ PtB P Bs (d.κ f) := by
  first | exact @GlobalTheory.HatNF.kappa_ptAdj_ptB | exact GlobalTheory.HatNF.kappa_ptAdj_ptB | (intros; apply GlobalTheory.HatNF.kappa_ptAdj_ptB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsPolyDegStar
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsPolyDegPrW
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

noncomputable section

namespace GlobalTheory.WigSh

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra

theorem isPolyDeg_prW {N : ℕ} (k r d : ℕ) (z : Fin (2 * r + k + 1) → ℂ)
    (v : Matrix (Fin N) (Fin N) ℂ → Fin (2 * r + k + 1) → ℂ) (hv : ∀ i, U.IsPolyDeg d (fun g => v g i))
    (i : Fin (2 * r + k + 1)) : U.IsPolyDeg d (fun g => D.prW k r z (v g) i) := by
  have hb : ∀ j : Fin (2 * r + k + 1),
      U.IsPolyDeg d (fun g => if r ≤ j.val ∧ j.val ≤ r + k then v g j else 0) := by
    intro j
    by_cases h : r ≤ j.val ∧ j.val ≤ r + k
    · simpa only [if_pos h] using hv j
    · simpa only [if_neg h] using pd_const (N := N) 0 d
  unfold D.prW
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
  refine pd_sub (hb i) (pd_mono (show d + 0 + 0 ≤ d by omega)
    (pd_mul (pd_mul ?_ (pd_const _ 0)) (pd_const _ 0)))
  unfold herm
  simp only [dotProduct, mulVec]
  refine pd_sum _ fun a _ => pd_mono (show 0 + d ≤ d by omega) (pd_mul (pd_const _ 0) ?_)
  exact pd_sum _ fun b _ => pd_mono (show 0 + d ≤ d by omega) (pd_mul (pd_const _ 0) (hb b))

theorem omg_isPolyDeg : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (i : Fin (2 * r + k + 1)),
    Formalism.FourierDecayAlt.U.IsPolyDeg (r + 1) (fun g : Mx k r => GlobalTheory.WigSh.omg k r z z' g i) := by
  intro k r z z' i
  unfold omg
  refine isPolyDeg_prW k r (r + 1) z' (fun g => (Hpk k r * gᴴ * Hpk k r) *ᵥ
    ∑ a, star ((Zhat k r z z' g).adjugate (Fin.last r) a) • fvec k r z a) (fun q => ?_) i
  simp only [dotProduct, mulVec]
  refine pd_sum _ fun s _ => pd_mono (show 1 + r ≤ r + 1 by omega) (pd_mul (P.TLC.omp_inv_pd q s) ?_)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact pd_sum _ fun a _ => pd_mono (show r + 0 ≤ r by omega)
    (pd_mul (P.TLC.omp_adj_pd z z' (Fin.last r) a) (pd_const _ 0))

end GlobalTheory.WigSh
end
end

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

noncomputable section

namespace GlobalTheory.WigSh.OmgContr

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra

variable {N : ℕ}

private lemma star_eval_eq_eval₂_starRingEnd {σ : Type*} (x : σ → ℂ) (q : MvPolynomial σ ℂ) :
    star (MvPolynomial.eval x q) = MvPolynomial.eval₂ (starRingEnd ℂ) (fun v => star (x v)) q := by
  induction q using MvPolynomial.induction_on with
  | C c => simp
  | add p₁ p₂ h₁ h₂ => simp [h₁, h₂]
  | mul_X p v hp => simp [hp]

theorem isPolyDeg_star {a : ℕ} {P : Matrix (Fin N) (Fin N) ℂ → ℂ} (h : U.IsPolyDeg a P) :
    U.IsPolyDeg a (fun g => star (P g)) := by
  obtain ⟨q, hq, hP⟩ := h
  refine ⟨MvPolynomial.rename Sum.swap (MvPolynomial.map (starRingEnd ℂ) q), ?_, ?_⟩
  · exact (MvPolynomial.totalDegree_rename_le _ _).trans
      (le_trans (by
        unfold MvPolynomial.totalDegree
        exact Finset.sup_mono (MvPolynomial.support_map_subset _ _)) hq)
  · intro g
    show star (P g) = _
    rw [hP g, MvPolynomial.eval_rename, MvPolynomial.eval_map, star_eval_eq_eval₂_starRingEnd]
    congr 1
    funext v
    cases v <;> simp

theorem isPolyDeg_pow {a : ℕ} {P : Matrix (Fin N) (Fin N) ℂ → ℂ} (h : U.IsPolyDeg a P) (n : ℕ) :
    U.IsPolyDeg (n * a) (fun g => P g ^ n) := by
  obtain ⟨q, hq, hP⟩ := h
  refine ⟨q ^ n, (MvPolynomial.totalDegree_pow q n).trans (Nat.mul_le_mul_left n hq), ?_⟩
  intro g
  simp [hP g]

theorem isPolyDeg_prod {ι : Type*} (s : Finset ι) (d : ι → ℕ) {P : ι → Matrix (Fin N) (Fin N) ℂ → ℂ}
    (h : ∀ i, U.IsPolyDeg (d i) (P i)) : U.IsPolyDeg (∑ i ∈ s, d i) (fun g => ∏ i ∈ s, P i g) := by
  choose q hq hP using h
  refine ⟨∏ i ∈ s, q i, (MvPolynomial.totalDegree_finsetProd s q).trans (Finset.sum_le_sum fun i _ => hq i), ?_⟩
  intro g
  simp [hP]

private lemma isPolyDeg_const (c : ℂ) (a : ℕ) : U.IsPolyDeg (N := N) a (fun _ => c) :=
  ⟨MvPolynomial.C c, by simp, fun g => by simp⟩

private lemma exists_pow_mul_mul_mem_subring {a b : ℕ} {P Q : Matrix (Fin N) (Fin N) ℂ → ℂ} (hP : U.IsPolyDeg a P)
    (hQ : U.IsPolyDeg b Q) : U.IsPolyDeg (a + b) (fun g => P g * Q g) := by
  obtain ⟨p, hp, hPe⟩ := hP
  obtain ⟨q, hq, hQe⟩ := hQ
  exact ⟨p * q, (MvPolynomial.totalDegree_mul p q).trans (Nat.add_le_add hp hq), fun g => by simp [hPe, hQe]⟩

private lemma exists_pow_mul_finset_sum_mem_subring {ι : Type*} (s : Finset ι) {a : ℕ} {P : ι → Matrix (Fin N) (Fin N) ℂ → ℂ}
    (h : ∀ i ∈ s, U.IsPolyDeg a (P i)) : U.IsPolyDeg a (fun g => ∑ i ∈ s, P i g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isPolyDeg_const (N := N) 0 a
  | insert j s hj ih =>
    have hj' := h j (Finset.mem_insert_self j s)
    have hs := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    obtain ⟨p, hp, hPe⟩ := hj'
    obtain ⟨q, hq, hQe⟩ := hs
    refine ⟨p + q, (MvPolynomial.totalDegree_add p q).trans (max_le hp hq), fun g => ?_⟩
    have e := hQe g
    simp only at e
    show ∑ i ∈ insert j s, P i g = _
    rw [Finset.sum_insert hj, MvPolynomial.eval_add, ← hPe g, ← e]

private lemma mono_lemma {a b : ℕ} {P : Matrix (Fin N) (Fin N) ℂ → ℂ} (h : U.IsPolyDeg a P) (hab : a ≤ b) :
    U.IsPolyDeg b P := by
  obtain ⟨q, hq, hP⟩ := h
  exact ⟨q, hq.trans hab, hP⟩

theorem isPolyDeg_eval {σ : Type*} {a d : ℕ} (f : Matrix (Fin N) (Fin N) ℂ → σ → ℂ)
    (hf : ∀ i, U.IsPolyDeg a (fun g => f g i)) (q : MvPolynomial σ ℂ) (hq : q.totalDegree ≤ d) :
    U.IsPolyDeg (d * a) (fun g => MvPolynomial.eval (f g) q) := by
  classical
  have expand : (fun g => MvPolynomial.eval (f g) q) =
      fun g => ∑ m ∈ q.support, q.coeff m * ∏ i ∈ m.support, f g i ^ m i := by
    funext g
    rw [MvPolynomial.eval_eq]
  rw [expand]
  refine exists_pow_mul_finset_sum_mem_subring _ fun m hm => ?_
  have hdeg : (∑ i ∈ m.support, m i) * a ≤ d * a := by
    apply Nat.mul_le_mul_right
    exact (MvPolynomial.le_totalDegree hm).trans hq
  refine mono_lemma ?_ hdeg
  have hprod : U.IsPolyDeg (∑ i ∈ m.support, m i * a) (fun g => ∏ i ∈ m.support, f g i ^ m i) :=
    isPolyDeg_prod m.support (fun i => m i * a) (fun i => isPolyDeg_pow (hf i) (m i))
  rw [Finset.sum_mul]
  simpa using exists_pow_mul_mul_mem_subring (isPolyDeg_const (q.coeff m) 0) hprod

end GlobalTheory.WigSh.OmgContr

namespace GlobalTheory.WigSh

open OmgContr

theorem wigMap_omg : ∀ (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Wq' : Type) [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (π' : Mx k r → (Wq →L[ℂ] Wq)) (π'' : Mx k r → (Wq' →L[ℂ] Wq')) (d : ℕ) (A : (Fin (2 * r + k + 1) → ℂ) → (Wq' →L[ℂ] Wq)), inWb k r z → 0 < Tz k r z → inWb k r z' → 0 < Tz k r z' → GlobalTheory.WigSh.WigMap k r z' π'' π' d A → (∃ (t : ℕ) (c : Fin t → Mx k r → ℂ) (L : Fin t → (Wq' →L[ℂ] Wq)), (∀ i, Formalism.FourierDecayAlt.U.IsPolyDeg (d * (r + 1)) (c i)) ∧ ∀ g, A (GlobalTheory.WigSh.omg k r z z' g) = ∑ i, c i g • L i) ∧ ∀ g ∈ UH (Hpk k r), ∀ p : Formalism.FourierDecayAlt.B.SS k r, Matrix.of p.1.1 ∈ UWset k r z → Matrix.of p.1.2 ∈ Formalism.QuantumDeterminants.Nset k r → Matrix.of p.2.1 ∈ UWset k r z' → Matrix.of p.2.2 ∈ Formalism.QuantumDeterminants.Nset k r → (A (GlobalTheory.WigSh.omg k r z z' (Formalism.FourierDecayAlt.B.sgs p g))).comp (π'' (Matrix.of p.2.1)⁻¹) = (π' (Matrix.of p.2.1)⁻¹).comp (A (GlobalTheory.WigSh.omg k r z z' g)) := by
  intro Wq _ _ Wq' _ _ k r z z' π' π'' d A hz hTz hz' hTz' hA
  obtain ⟨⟨t, q, Lm, hq, hAe⟩, hAeq, -, -⟩ := hA
  refine ⟨⟨t, fun i g => MvPolynomial.eval
      (Sum.elim (GlobalTheory.WigSh.omg k r z z' g) (fun j => star (GlobalTheory.WigSh.omg k r z z' g j))) (q i), Lm, ?_, ?_⟩, ?_⟩
  · intro i
    refine isPolyDeg_eval (N := 2 * r + k + 1)
      (fun g => Sum.elim (GlobalTheory.WigSh.omg k r z z' g) (fun j => star (GlobalTheory.WigSh.omg k r z z' g j))) ?_ (q i) (hq i)
    rintro (j | j)
    · exact GlobalTheory.WigSh.omg_isPolyDeg k r z z' j
    · exact isPolyDeg_star (GlobalTheory.WigSh.omg_isPolyDeg k r z z' j)
  · intro g
    exact hAe _
  · intro g hg p h1 h2 h3 h4
    have hn : (Matrix.of p.1.2)⁻¹ * g ∈ UH (Hpk k r) :=
      Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv h2.1) hg
    have hG : (Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2 ∈ UH (Hpk k r) :=
      Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hn h4.1
    have hs : Formalism.FourierDecayAlt.B.sgs p g =
        (Matrix.of p.1.1)⁻¹ * ((Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2) * Matrix.of p.2.1 := by
      simp only [Formalism.FourierDecayAlt.B.sgs, Matrix.mul_assoc]
    have hom : GlobalTheory.WigSh.omg k r z z' (Formalism.FourierDecayAlt.B.sgs p g) =
        (Matrix.of p.2.1)⁻¹ *ᵥ GlobalTheory.WigSh.omg k r z z' g := by
      rw [hs, GlobalTheory.WigSh.omg_equivariant k r z z' _ _ _ hz hTz hz' hTz' hG h1 h3,
        GlobalTheory.WigSh.omg_mul_N k r z z' _ _ hz hz' hn h4, GlobalTheory.WigSh.OmLeftN.omg_left_N k r z z' g _ hz hz' hg h2]
    rw [hom]
    exact hAeq _ (GlobalTheory.WigSh.OmgEquiv.inv_mem h3) _

end GlobalTheory.WigSh
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MinusHatsTaylorCoeffLeibnizRule
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MinusHatsTaylorCoeffLeibnizRule
namespace GlobalTheory.HatNF.TaylorMinus

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ}

def Dg (L : LevelData A r) (Y : ℂ) (D : ℕ) (Z : ℂ → A) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (d : ι → ℕ) (x : ι → A), (∀ i, d i ≤ D) ∧
    (∀ s : ℂ, Z (Y - s) = ∑ i, s ^ d i • x i) ∧
    ∀ m : ℕ → A, MulRel L m → ∀ q, Z Y * m q = ∑ i, m (q + d i) * x i

variable {L : LevelData A r} {Y : ℂ}

theorem Dg.mono {D E : ℕ} {Z : ℂ → A} (h : Dg L Y D Z) (hDE : D ≤ E) : Dg L Y E Z := by
  obtain ⟨ι, hι, d, x, hd, h1, h2⟩ := h
  exact ⟨ι, hι, d, x, fun i => (hd i).trans hDE, h1, h2⟩

theorem Dg.add {D : ℕ} {Z W : ℂ → A} (h : Dg L Y D Z) (h' : Dg L Y D W) :
    Dg L Y D (fun y => Z y + W y) := by
  obtain ⟨ι, _, d, x, hd, hs, hm⟩ := h
  obtain ⟨κ, _, e, w, he, hs', hm'⟩ := h'
  refine ⟨ι ⊕ κ, inferInstance, Sum.elim d e, Sum.elim x w, ?_, fun s => ?_, fun m hmr q => ?_⟩
  · rintro (i | j)
    exacts [hd i, he j]
  · simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, hs, hs']
  · simp only [add_mul, hm m hmr q, hm' m hmr q, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]

theorem Dg.mul {D E : ℕ} {Z W : ℂ → A} (h : Dg L Y D Z) (h' : Dg L Y E W) :
    Dg L Y (D + E) (fun y => Z y * W y) := by
  obtain ⟨ι, _, d, x, hd, hs, hm⟩ := h
  obtain ⟨κ, _, e, w, he, hs', hm'⟩ := h'
  refine ⟨ι × κ, inferInstance, fun p => d p.1 + e p.2, fun p => x p.1 * w p.2,
    fun p => Nat.add_le_add (hd p.1) (he p.2), fun s => ?_, fun m hmr q => ?_⟩
  · dsimp only
    rw [hs, hs', Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_smul_comm, pow_add]
  · dsimp only
    rw [mul_assoc, hm' m hmr q, Finset.mul_sum, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_assoc, hm m hmr (q + e j), Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc, show q + e j + d i = q + (d i + e j) by omega]

theorem dg_const (f : A) (hf : ∀ m : ℕ → A, MulRel L m → ∀ q, Commute f (m q)) :
    Dg L Y 0 (fun _ => f) := ⟨Unit, inferInstance, fun _ => 0, fun _ => f, fun _ => le_rfl, fun s => by simp,
    fun m hm q => by simp [(hf m hm q).eq]⟩

theorem dg_lin (Z : ℂ → A) (u : A) (h1 : ∀ s, Z (Y - s) = Z Y + s • u)
    (h2 : ∀ m : ℕ → A, MulRel L m → ∀ q, Z Y * m q = m q * Z Y + m (q + 1) * u) : Dg L Y 1 Z := ⟨Fin 2, inferInstance, ![0, 1], ![Z Y, u], by intro i; fin_cases i <;> simp,
    fun s => by simp [Fin.sum_univ_two, h1], fun m hm q => by simp [Fin.sum_univ_two, h2 m hm q]⟩

theorem Dg.out {D : ℕ} {Z : ℂ → A} (h : Dg L Y D Z) :
    ∃ X : ℕ → A, (∀ s : ℂ, Z (Y - s) = ∑ j ∈ Finset.range (D + 1), s ^ j • X j) ∧
      ∀ m : ℕ → A, MulRel L m → ∀ q, Z Y * m q = ∑ j ∈ Finset.range (D + 1), m (q + j) * X j := by
  obtain ⟨ι, _, d, x, hd, h1, h2⟩ := h
  have hmap : ∀ i ∈ (Finset.univ : Finset ι), d i ∈ Finset.range (D + 1) :=
    fun i _ => Finset.mem_range.2 (Nat.lt_succ_of_le (hd i))
  refine ⟨fun j => ∑ i ∈ Finset.univ.filter (fun i => d i = j), x i, fun s => ?_, fun m hm q => ?_⟩
  · rw [h1, ← Finset.sum_fiberwise_of_maps_to hmap]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.1 hi).2]
  · rw [h2 m hm q, ← Finset.sum_fiberwise_of_maps_to hmap]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.1 hi).2]

theorem comm_c {m : ℕ → A} (hm : MulRel L m) (q : ℕ) (l : Fin r) : Commute (L.c l) (m q) := (hm q).1 _ (by simp [LevelData.fns])

theorem comm_cb {m : ℕ → A} (hm : MulRel L m) (q : ℕ) (l : Fin r) : Commute (L.cb l) (m q) := (hm q).1 _ (by simp [LevelData.fns])

theorem comm_cbi {m : ℕ → A} (hm : MulRel L m) (q : ℕ) (l : Fin r) : Commute (L.cbi l) (m q) := (hm q).1 _ (by simp [LevelData.fns])

theorem comm_GG {m : ℕ → A} (hm : MulRel L m) (q : ℕ) : Commute L.GG (m q) := (hm q).1 _ (by simp [LevelData.fns])

theorem comm_zG {m : ℕ → A} (hm : MulRel L m) (q : ℕ) : Commute (L.ζ * L.GGi) (m q) := ((hm q).1 _ (by simp [LevelData.fns])).mul_left ((hm q).1 _ (by simp [LevelData.fns]))

theorem comm_prod {g : Fin r → A} {a : A} (h : ∀ l, Commute (g l) a) : Commute (List.ofFn g).prod a := Commute.list_prod_left _ _ fun x hx => by
    simp only [List.mem_ofFn] at hx
    obtain ⟨l, rfl⟩ := hx
    exact h l

theorem dg_Tvl (l : Fin r) (i j : Fin 2) : Dg L Y 1 (fun y => L.Tvl y l i j) := by
  fin_cases i <;> fin_cases j
  · show Dg L Y 1 (fun y => algebraMap ℂ A y - L.pb l)
    refine dg_lin _ (-1) (fun s => ?_) (fun m hm q => ?_)
    · rw [map_sub, smul_neg, Algebra.smul_def, mul_one]
      abel
    · rw [sub_mul, mul_sub, ((hm q).2.2.1 l), Algebra.commutes, mul_neg, mul_one]
      abel
  · show Dg L Y 1 (fun _ => -L.cb l)
    exact (dg_const _ fun m hm q => (comm_cb hm q l).neg_left).mono zero_le_one
  · show Dg L Y 1 (fun _ => L.cbi l)
    exact (dg_const _ fun m hm q => comm_cbi hm q l).mono zero_le_one
  · show Dg L Y 1 (fun _ => (0 : A))
    exact (dg_const _ fun m hm q => Commute.zero_left _).mono zero_le_one

theorem dg_list (ls : List (Fin r)) (i j : Fin 2) :
    Dg L Y ls.length (fun y => (ls.map (L.Tvl y)).prod i j) := by
  induction ls generalizing i j with
  | nil =>
    simp only [List.map_nil, List.prod_nil, List.length_nil]
    exact dg_const _ fun m hm q => by
      rw [Matrix.one_apply]
      split_ifs <;> simp
  | cons l ls ih =>
    simp only [List.map_cons, List.prod_cons, Matrix.mul_apply, Fin.sum_univ_two, List.length_cons]
    exact (Dg.add ((dg_Tvl l i 0).mul (ih 0 j)) ((dg_Tvl l i 1).mul (ih 1 j))).mono (by omega)

theorem dg_Tvprod (i j : Fin 2) : Dg L Y r (fun y => L.Tvprod y i j) := by
  have h := dg_list (L := L) (Y := Y) (List.ofFn (fun l : Fin r => l)).reverse i j
  rw [List.length_reverse, List.length_ofFn] at h
  have e : (fun y => L.Tvprod y i j) =
      fun y => (((List.ofFn (fun l : Fin r => l)).reverse).map (L.Tvl y)).prod i j := by
    funext y
    simp only [LevelData.Tvprod, List.map_reverse, List.map_ofFn]
    rfl
  rw [e]
  exact h

theorem backwardTaylorDegree_one_mirrorLetter : Dg L Y 1 L.m0 := by
  show Dg L Y 1 (fun y => -L.nabs - algebraMap ℂ A (y - 1 / 2) * (L.ζ * L.GGi))
  refine dg_lin _ (L.ζ * L.GGi) (fun s => ?_) (fun m hm q => ?_)
  · rw [show Y - s - 1 / 2 = (Y - 1 / 2) - s by ring, map_sub, sub_mul, Algebra.smul_def]
    abel
  · have e1 := (hm q).2.2.2.2
    have c1 := (comm_zG hm q).eq
    have c2 := (comm_zG hm (q + 1)).eq
    have c3 := Algebra.commutes (R := ℂ) (Y - 1 / 2) (m q)
    have e0 : (-L.nabs - algebraMap ℂ A (Y - 1 / 2) * (L.ζ * L.GGi)) * m q =
        -(L.nabs * m q) - algebraMap ℂ A (Y - 1 / 2) * (L.ζ * L.GGi * m q) := by noncomm_ring
    rw [e0, e1, c1, ← mul_assoc (algebraMap ℂ A (Y - 1 / 2)) (m q) (L.ζ * L.GGi), c3, c2]
    noncomm_ring

theorem dg_Ahatv : Dg L Y (r + 1) L.Ahatv := by
  have hc : Dg L Y 0 (fun _ => L.Drb) := dg_const _ fun m hm q => comm_prod fun l => comm_cb hm q l
  exact (hc.mul (dg_Tvprod 0 0)).mono (by omega)

theorem backwardTaylorDegree_minusHatR : Dg L Y (r + 1) L.R0v := by
  have hc : Dg L Y 0 (fun _ => L.Dr * L.GG) :=
    dg_const _ fun m hm q => (comm_prod fun l => comm_c hm q l).mul_left (comm_GG hm q)
  have hA : Dg L Y r (fun y => L.Avr y) := dg_Tvprod 0 0
  have hB : Dg L Y (1 + r) (fun y => L.Bvr y) := (dg_Tvprod 1 0).mono (by omega)
  exact (hc.mul ((backwardTaylorDegree_one_mirrorLetter.mul hA).add hB)).mono (by omega)

theorem taylor_minus : ∀ (A : Type) [Ring A] [Algebra ℂ A] (r : ℕ) (L : LevelData A r), ∀ Y : ℂ, ∃ Xa Xr : ℕ → A, (∀ s : ℂ, L.Ahatv (Y - s) = ∑ j ∈ Finset.range (r + 2), s ^ j • Xa j) ∧ (∀ s : ℂ, L.R0v (Y - s) = ∑ j ∈ Finset.range (r + 2), s ^ j • Xr j) ∧ ∀ m : ℕ → A, MulRel L m → ∀ q, L.Ahatv Y * m q = ∑ j ∈ Finset.range (r + 2), m (q + j) * Xa j ∧ L.R0v Y * m q = ∑ j ∈ Finset.range (r + 2), m (q + j) * Xr j := by
  intro A _ _ r L Y
  obtain ⟨Xa, ha1, ha2⟩ := (dg_Ahatv (L := L) (Y := Y)).out
  obtain ⟨Xr, hr1, hr2⟩ := (backwardTaylorDegree_minusHatR (L := L) (Y := Y)).out
  exact ⟨Xa, Xr, ha1, hr1, fun m hm q => ⟨ha2 m hm q, hr2 m hm q⟩⟩

end GlobalTheory.HatNF.TaylorMinus
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MinusHatsTaylorCoeffLeibnizRuleStatement
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minusHats_taylorCoeff_leibniz_rule : ∀ (A : Type) [Ring A] [Algebra ℂ A] (r : ℕ) (L : LevelData A r), ∀ Y : ℂ, ∃ Xa Xr : ℕ → A, (∀ s : ℂ, L.Ahatv (Y - s) = ∑ j ∈ Finset.range (r + 2), s ^ j • Xa j) ∧ (∀ s : ℂ, L.R0v (Y - s) = ∑ j ∈ Finset.range (r + 2), s ^ j • Xr j) ∧ ∀ m : ℕ → A, MulRel L m → ∀ q, L.Ahatv Y * m q = ∑ j ∈ Finset.range (r + 2), m (q + j) * Xa j ∧ L.R0v Y * m q = ∑ j ∈ Finset.range (r + 2), m (q + j) * Xr j := by
  first | exact @GlobalTheory.HatNF.TaylorMinus.taylor_minus | exact GlobalTheory.HatNF.TaylorMinus.taylor_minus | (intros; apply GlobalTheory.HatNF.TaylorMinus.taylor_minus <;> assumption)
end
end

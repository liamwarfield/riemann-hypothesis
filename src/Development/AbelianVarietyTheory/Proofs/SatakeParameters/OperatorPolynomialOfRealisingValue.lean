module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeaklyAttachedGaloisRepresentationBaseChangeRest
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FramePolynomialsWeightRealisedNextLevel
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SecondKernelProjection

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ModelPolynomialOddDegreeOfRealisesFramePoly
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ModelPolynomialOddDegreeOfRealisesFramePoly
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem blk_iff_posJ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (j : ℕ)
    (x : Var (X.Pj j)) (b : Σ v : X.Pl, Fin (X.G.P.n' v)) :
    ((⟨x.1, x.2.1⟩ : Σ v : Fin (X.Pj j).nV, Fin ((X.Pj j).n' v)) = (GlobalTheory.TwV.DelA.posJ X D pos j).symm (pos b)) ↔ blkJ X j x = b := by
  cases j
  · simp only [blkJ, idxJ]
    change _ = pos.symm (pos b) ↔ _
    rw [Equiv.symm_apply_apply]
    exact Iff.rfl
  · simp only [blkJ, idxJ]
    change _ = pos.symm (pos b) ↔ _
    rw [Equiv.symm_apply_apply]
    exact Iff.rfl

theorem oddDeg_of_realises : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → ∀ (Q : MvPolynomial (GL3Theta.FrV D (D.R.N j)) ℂ), Q ∈ WtPol ℂ ν → ∀ (Gc : XR (X.Pj j) ℂ) (G : (X.Pj j).Xsp), Realises X D pos j (rkS X D hN) (wT X D pos j) Q Gc → MvPolynomial.map (algebraMap X.G.Kf Kc) G = MvPolynomial.map ι Gc → OddDeg X j G := by
  intro p _ X D pos Kc _ _ ι j hN ν hν Q hQ Gc G hR hmap m hm b hb
  have hs : G.support = Gc.support := by
    rw [← MvPolynomial.support_map_of_injective G (algebraMap X.G.Kf Kc).injective, hmap,
      MvPolynomial.support_map_of_injective Gc ι.injective]
  rw [hs] at hm
  have hh := GlobalTheory.T.realising_polynomial_blockwise_homogeneous X D pos j (rkS X D hN) (wT X D pos j) ν Q Gc hQ hR m hm (pos b)
  obtain ⟨he, -⟩ := GlobalTheory.T.realPlaceBlockWeightLastEntry_consecutive_levels X D pos j (pos b)
  obtain ⟨-, hsz, -, -, -⟩ := GlobalTheory.T.modelPartition_size_extension_firstLast_rows X D pos j hN ν hν
  have hodd : IsOddPos (pos.symm (pos b)).2 := by rw [Equiv.symm_apply_apply]; exact hb
  rw [if_pos hodd] at he hh
  rw [he, ← hsz] at hh
  have hl : ((∑ x ∈ Finset.univ.filter (fun x => blkJ X j x = b), m x : ℕ) : ℤ) =
      ∑ x : Var (X.Pj j), if (⟨x.1, x.2.1⟩ : Σ v : Fin (X.Pj j).nV, Fin ((X.Pj j).n' v)) = (GlobalTheory.TwV.DelA.posJ X D pos j).symm (pos b)
        then (m x : ℤ) else 0 := by
    rw [Nat.cast_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [blk_iff_posJ]
  have h1 : szT X D pos j (pos b) = szMu X j b.1 b.2 := by unfold szT; rw [Equiv.symm_apply_apply]
  have h2 : cT1 X D pos j (pos b) = cMu X j b.1 b.2 := by unfold cT1; rw [Equiv.symm_apply_apply]
  rw [hl, hh, h1, h2, hN.1]
  ring

end GlobalTheory.TwV.DelA
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ModelPolynomialOddDegreeOfRealisesFramePolyStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modelPolynomial_oddDegree_of_realisesFramePoly : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → ∀ (Q : MvPolynomial (GL3Theta.FrV D (D.R.N j)) ℂ), Q ∈ WtPol ℂ ν → ∀ (Gc : XR (X.Pj j) ℂ) (G : (X.Pj j).Xsp), Realises X D pos j (rkS X D hN) (wT X D pos j) Q Gc → MvPolynomial.map (algebraMap X.G.Kf Kc) G = MvPolynomial.map ι Gc → OddDeg X j G := by
  first | exact @GlobalTheory.TwV.DelA.oddDeg_of_realises | exact GlobalTheory.TwV.DelA.oddDeg_of_realises | (intros; apply GlobalTheory.TwV.DelA.oddDeg_of_realises <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetTwistedFrameOperatorIdentityDenominator
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TransportedPolynomialComplexPointEvaluation
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TransportedPolynomialComplexPointEvaluation
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwV.DelA

open MvPolynomial

theorem transpC_eval_aeval {σ κ : Type} (x : κ → ℂ) (g : σ → MvPolynomial κ ℂ) (Q : MvPolynomial σ ℂ) :
    eval x (aeval g Q) = eval (fun i => eval x (g i)) Q := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _)]
  | mul_X p v hp => rw [map_mul, map_mul, hp, map_mul, aeval_X, eval_X]

theorem transpC_map_eval {σ Kc : Type} [CommRing Kc] (ι : ℂ →+* Kc) (x : σ → ℂ) (R : MvPolynomial σ ℂ) :
    eval (fun i => ι (x i)) (map ι R) = ι (eval x R) := by
  induction R using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _), map_add (f := _)]
  | mul_X p v hp => rw [map_mul, map_mul, hp, map_mul, map_X, eval_X, eval_X, map_mul]

theorem transpC_hom_aeval {σ ι' κ : Type} (φ : MvPolynomial ι' (MvPolynomial κ ℂ) →+* ℂ) (hφ : ∀ c, φ (C (C c)) = c)
    (g : σ → MvPolynomial ι' (MvPolynomial κ ℂ)) (Q : MvPolynomial σ ℂ) :
    φ (aeval g Q) = eval (fun i => φ (g i)) Q := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp [MvPolynomial.algebraMap_apply, hφ]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _)]
  | mul_X p v hp => rw [map_mul, map_mul, hp, map_mul, aeval_X, eval_X]

theorem evFr_scalar_of_wtPol (D : D7) {N : ℕ} (ν : D.what₂.Tau → Fin N → ℕ) (Q : MvPolynomial (GL3Theta.FrV D N) ℂ)
    (hQ : Q ∈ WtPol ℂ ν) (s : D.what₂.Tau → ℂ) (hs : ∀ τ, s τ ≠ 0) (y : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ) :
    GL3Theta.evFr D Q (fun τ => s τ • y τ) = (∏ τ, ∏ r, s τ ^ ν τ r) * GL3Theta.evFr D Q y := by
  have hB : IsBor (fun τ => s τ • (1 : Matrix (Fin N) (Fin N) ℂ)) := fun τ =>
    ⟨fun r c hcr => by simp [Matrix.one_apply_ne hcr.ne'], fun r => by simp [hs τ]⟩
  have h1 : colSub (fun τ => s τ • (1 : Matrix (Fin N) (Fin N) ℂ)) Q = _ := hQ _ hB
  have h2 := congrArg (eval (fun k : GL3Theta.FrV D N => y k.1 k.2.1 k.2.2)) h1
  simp only [colSub, transpC_eval_aeval, smul_eval] at h2
  have h3 : (∏ τ, ∏ r, (s τ • (1 : Matrix (Fin N) (Fin N) ℂ)) r r ^ ν τ r) = ∏ τ, ∏ r, s τ ^ ν τ r := by simp
  rw [h3] at h2
  unfold GL3Theta.evFr
  rw [← h2]
  refine congrArg (fun x => eval x Q) ?_
  funext k
  simp [Matrix.smul_apply, Matrix.one_apply, mul_comm]

theorem transpC_polDY_eval (D : D7) {N N' : ℕ} (hle : N ≤ N') (s : D.what₂.Tau → ℂ) (Q : MvPolynomial (GL3Theta.FrV D N) ℂ)
    (d : D.what₂.Tau → Matrix (Fin N) (Fin N') ℂ) (f' : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ) :
    MvPolynomial.eval₂Hom (MvPolynomial.eval (fun k : GL3Theta.FrV D N' => f' k.1 k.2.1 k.2.2)) (fun k : GL3Theta.Idx D N N' => d k.1 k.2.2 k.2.1)
        (polDY D s Q (N' := N')) =
      GL3Theta.evFr D Q (fun τ => s τ • (d τ * f' τ).submatrix id (Fin.castLE hle)) := by
  unfold polDY
  rw [transpC_hom_aeval _ (fun c => by simp)]
  unfold GL3Theta.evFr
  refine congrArg (fun x => MvPolynomial.eval x Q) ?_
  funext k
  have hk : ((k.2.2 : Fin N) : ℕ) < N' := lt_of_lt_of_le k.2.2.2 hle
  simp [dfr, Matrix.mul_apply, Finset.mul_sum, hk]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mul_assoc, mul_comm (f' k.1 b _)]
  rfl

theorem evD_trDY_polDY : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → ∀ (Q : MvPolynomial (GL3Theta.FrV D (D.R.N j)) ℂ), Q ∈ WtPol ℂ ν → ∀ (s : D.what₂.Tau → ℂ), (∀ τ, s τ ≠ 0) → ∀ (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ) (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ), (∀ τ, (f' τ).det ≠ 0) → evD X D pos ι hN d f' (trDY X Kc j D (eIdx X D pos j hN) (phi0 X D pos ι j) (polDY D s Q (N' := D.R.N (j + 1)))) * ι (∏ τ, (zT X D pos f' τ).det ^ eT X D pos (j + 1) τ) = ι ((∏ τ, (f' τ).det ^ (-(wT X D pos j τ))) * (∏ τ, s τ ^ szT X D pos j τ) * GL3Theta.evFr D Q (dfr X D hN d f')) := by
  intro p _ X D pos Kc _ _ ι j hN ν hν Q hQ s hs d f' hf
  classical
  have h' := rkT X D hN
  obtain ⟨-, hsz, -, hle, -⟩ := GlobalTheory.T.modelPartition_size_extension_firstLast_rows X D pos j hN ν hν
  have hco := (GlobalTheory.T.operatorPolynomial_coeffs_weight_extended_by_zero D (rk_le X D hN) s ν Q hQ).1
  have hreal : ∀ α, Realises X D pos (j + 1) h' (wT X D pos j) (AddMonoidAlgebra.coeff (polDY D s Q (N' := D.R.N (j + 1))) α)
      (phiC X D pos (j + 1) h' (wT X D pos j) (AddMonoidAlgebra.coeff (polDY D s Q (N' := D.R.N (j + 1))) α)) := by
    intro α
    obtain ⟨R, hR⟩ := GlobalTheory.T.frame_polynomials_weight_realised_next_level X D pos j h' (extNu _ ν) hle _ (hco α)
    exact selOf_mem (relPhi X D pos (j + 1) h' (wT X D pos j)) _ (Submodule.mem_map.2 ⟨(_, R), hR, rfl⟩)
  let F : Fr1 D (D.R.N (j + 1)) := ⟨f', fun τ => isUnit_iff_ne_zero.2 (hf τ)⟩
  have hval : ∀ α, (∏ τ, (zT X D pos f' τ).det ^ eT X D pos (j + 1) τ) *
      valZ X D pos (j + 1) h' (phiC X D pos (j + 1) h' (wT X D pos j) (AddMonoidAlgebra.coeff (polDY D s Q (N' := D.R.N (j + 1))) α)) f' =
      (∏ τ, (f' τ).det ^ (-(wT X D pos j τ))) * GL3Theta.evFr D (AddMonoidAlgebra.coeff (polDY D s Q (N' := D.R.N (j + 1))) α) f' := by
    intro α
    have := hreal α F
    rw [ev1_eq_prod_det_pow_mul_valZ] at this
    exact this
  have hD : evD X D pos ι hN d f' (trDY X Kc j D (eIdx X D pos j hN) (phi0 X D pos ι j) (polDY D s Q (N' := D.R.N (j + 1)))) =
      ι (∑ α ∈ (polDY D s Q (N' := D.R.N (j + 1))).support,
        valZ X D pos (j + 1) h' (phiC X D pos (j + 1) h' (wT X D pos j) (AddMonoidAlgebra.coeff (polDY D s Q (N' := D.R.N (j + 1))) α)) f' *
          ∏ k ∈ α.support, d k.1 k.2.2 k.2.1 ^ α k) := by
    unfold trDY
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    unfold evD
    rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial,
      Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
    unfold phi0
    rw [dite_eq_left h', map_mul, map_prod]
    congr 1
    · unfold valZ
      exact transpC_map_eval ι _ _
    · unfold Finsupp.prod
      refine Finset.prod_congr rfl fun k _ => ?_
      simp [eIdx, map_pow]
  have hP : ∑ α ∈ (polDY D s Q (N' := D.R.N (j + 1))).support,
        GL3Theta.evFr D (AddMonoidAlgebra.coeff (polDY D s Q (N' := D.R.N (j + 1))) α) f' * ∏ k ∈ α.support, d k.1 k.2.2 k.2.1 ^ α k =
      (∏ τ, s τ ^ szT X D pos j τ) * GL3Theta.evFr D Q (dfr X D hN d f') := by
    let φ : MvPolynomial (GL3Theta.Idx D (D.R.N j) (D.R.N (j + 1))) (MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ) →+* ℂ :=
      MvPolynomial.eval₂Hom (MvPolynomial.eval (fun k : GL3Theta.FrV D (D.R.N (j + 1)) => f' k.1 k.2.1 k.2.2))
        (fun k => d k.1 k.2.2 k.2.1)
    have e1 : φ (polDY D s Q (N' := D.R.N (j + 1))) = ∑ α ∈ (polDY D s Q (N' := D.R.N (j + 1))).support,
        GL3Theta.evFr D (AddMonoidAlgebra.coeff (polDY D s Q (N' := D.R.N (j + 1))) α) f' * ∏ k ∈ α.support, d k.1 k.2.2 k.2.1 ^ α k := by
      rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq]
      rfl
    have e2 : φ (polDY D s Q (N' := D.R.N (j + 1))) = GL3Theta.evFr D Q (fun τ => s τ • dfr X D hN d f' τ) :=
      transpC_polDY_eval D (rk_le X D hN) s Q d f'
    have e3 : ∀ τ, ∏ r, s τ ^ ν τ r = s τ ^ szT X D pos j τ := by
      intro τ
      rw [hsz τ, Finset.prod_pow_eq_pow_sum, ← Nat.cast_sum, zpow_natCast]
    rw [← e1, e2, evFr_scalar_of_wtPol D ν Q hQ s hs]
    simp only [e3]
  rw [hD, ← map_mul]
  congr 1
  rw [Finset.sum_mul]
  calc _ = ∑ α ∈ (polDY D s Q (N' := D.R.N (j + 1))).support, (∏ τ, (f' τ).det ^ (-(wT X D pos j τ))) *
        (GL3Theta.evFr D (AddMonoidAlgebra.coeff (polDY D s Q (N' := D.R.N (j + 1))) α) f' * ∏ k ∈ α.support, d k.1 k.2.2 k.2.1 ^ α k) := by
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [← mul_assoc, ← hval α]
        ring
    _ = _ := by rw [← Finset.mul_sum, hP, mul_assoc]

end GlobalTheory.TwV.DelA

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TransportedPolynomialComplexPointEvaluationStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transportedPolynomial_complexPoint_evaluation : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → ∀ (Q : MvPolynomial (GL3Theta.FrV D (D.R.N j)) ℂ), Q ∈ WtPol ℂ ν → ∀ (s : D.what₂.Tau → ℂ), (∀ τ, s τ ≠ 0) → ∀ (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ) (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ), (∀ τ, (f' τ).det ≠ 0) → evD X D pos ι hN d f' (trDY X Kc j D (eIdx X D pos j hN) (phi0 X D pos ι j) (polDY D s Q (N' := D.R.N (j + 1)))) * ι (∏ τ, (zT X D pos f' τ).det ^ eT X D pos (j + 1) τ) = ι ((∏ τ, (f' τ).det ^ (-(wT X D pos j τ))) * (∏ τ, s τ ^ szT X D pos j τ) * GL3Theta.evFr D Q (dfr X D hN d f')) := by
  first | exact @GlobalTheory.TwV.DelA.evD_trDY_polDY | exact GlobalTheory.TwV.DelA.evD_trDY_polDY | (intros; apply GlobalTheory.TwV.DelA.evD_trDY_polDY <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorIdentityLeftSideComplexPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SubstitutedValueAtComplexPointOddBlocks
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SubstitutedValueAtComplexPointOddBlocks
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.DelA

theorem adjugate_transpose_rev {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (h : A.det ≠ 0) :
    (A.transpose.submatrix Fin.rev id).adjugate = (sgRev n * A.det) • (A⁻¹.transpose.submatrix id Fin.rev) := by
  have hB : (A.transpose.submatrix Fin.rev id).det = sgRev n * A.det := by
    show (A.transpose.submatrix (Fin.revPerm : Equiv.Perm (Fin n)) id).det = _
    rw [Matrix.det_permute, Matrix.det_transpose, sgRev]
  have hI : (A.transpose.submatrix Fin.rev id)⁻¹ = A⁻¹.transpose.submatrix id Fin.rev := by
    show (A.transpose.submatrix (Fin.revPerm : Equiv.Perm (Fin n)) (Equiv.refl _))⁻¹ = _
    rw [Matrix.inv_submatrix_equiv, Matrix.transpose_nonsing_inv]
    rfl
  have hne : (A.transpose.submatrix Fin.rev id).det ≠ 0 := by
    rw [hB]
    refine mul_ne_zero ?_ h
    unfold sgRev
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n))) with h1 | h1 <;> rw [h1] <;> norm_num
  rw [← hI, ← hB, Matrix.inv_def, smul_smul, Ring.inverse_eq_inv', mul_inv_cancel₀ hne, one_smul]

end GlobalTheory.TwV.DelA

namespace GlobalTheory.TwV.DelA

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)

theorem posJ_blkJ (j : ℕ) (x : Σ v : Fin (X.Fl.Pj j).nV, Fin ((X.Fl.Pj j).n' v) × (Fin ((X.Fl.Pj j).m + 1) × Fin ((X.Fl.Pj j).m + 1))) :
    posJ X D pos j ⟨x.1, x.2.1⟩ = pos (blkJ X j x) := by
  cases j <;> rfl

theorem levelIndex_row_val_eq (j : ℕ) (x : Σ v : Fin (X.Fl.Pj j).nV, Fin ((X.Fl.Pj j).n' v) × (Fin ((X.Fl.Pj j).m + 1) × Fin ((X.Fl.Pj j).m + 1))) :
    ((idxJ X j x).2.2.1 : ℕ) = x.2.2.1 := by
  cases j <;> rfl

theorem levelIndex_col_val_eq (j : ℕ) (x : Σ v : Fin (X.Fl.Pj j).nV, Fin ((X.Fl.Pj j).n' v) × (Fin ((X.Fl.Pj j).m + 1) × Fin ((X.Fl.Pj j).m + 1))) :
    ((idxJ X j x).2.2.2 : ℕ) = x.2.2.2 := by
  cases j <;> rfl

def kOdd {j : ℕ} (hN : RankTie X D j) (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ)
    (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ) (τ : D.what₂.Tau) : ℂ :=
  (zT X D pos f' τ).det ^ ((D.R.N j : ℤ) - 1) * sgRev (D.R.N j) * (dfr X D hN d f' τ).det

theorem evD_ySub (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) {j : ℕ} (hN : RankTie X D j)
    (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ)
    (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ)
    (hf : ∀ τ, (f' τ).det ≠ 0) (hd : ∀ τ, (dfr X D hN d f' τ).det ≠ 0) (v : X.Pl) (s : Fin (X.G.P.n' v))
    (a t : Fin (NN X.G.P.m X.t j)) :
    evD X D pos ι hN d f' (ySub X Kc j v s a t) =
      (if IsOddPos s then ι (kOdd X D pos hN d f' (pos ⟨v, s⟩)) else 1) *
        ι (zT X D pos (dfr X D hN d f') (pos ⟨v, s⟩) (Fin.cast hN.1.symm a) (Fin.cast hN.1.symm t)) := by
  obtain ⟨_, hE, hO⟩ := GlobalTheory.T.operatorMatrices_at_complexPoint X D pos Kc ι j hN d f' hf hd v s
  have hsym : IsOddPos (pos.symm (pos ⟨v, s⟩)).2 ↔ IsOddPos s := by
    have hb : ∀ b : (Σ v : X.Pl, Fin (X.G.P.n' v)), b = ⟨v, s⟩ → (IsOddPos b.2 ↔ IsOddPos s) := by
      rintro _ rfl; exact Iff.rfl
    exact hb _ (Equiv.symm_apply_apply _ _)
  by_cases ho : IsOddPos s
  · rw [if_pos ho, ySub_odd X Kc j v s ho]
    have h1 := RingHom.map_adjugate (evD X D pos ι hN d f') (YtMat X Kc j v s)
    simp only [RingHom.mapMatrix_apply] at h1
    have h2 := congrFun (congrFun h1 a) t
    rw [Matrix.map_apply] at h2
    rw [h2, hO ho, Matrix.adjugate_smul, Fintype.card_fin,
      show (Fin.cast hN.1.symm : Fin (NN X.G.P.m X.t j) → Fin (D.R.N j)) = ⇑(finCongr hN.1.symm) from rfl,
      Matrix.adjugate_submatrix_equiv_self]
    have h3 := RingHom.map_adjugate ι ((dfr X D hN d f' (pos ⟨v, s⟩)).transpose.submatrix Fin.rev id)
    simp only [RingHom.mapMatrix_apply] at h3
    rw [← h3, adjugate_transpose_rev _ (hd _)]
    have hz : zT X D pos (dfr X D hN d f') (pos ⟨v, s⟩) = ((dfr X D hN d f' (pos ⟨v, s⟩))⁻¹).transpose.submatrix id Fin.rev := by
      unfold zT; rw [if_pos (hsym.2 ho)]
    have hpos : 1 ≤ D.R.N j := by have := rkS X D hN; omega
    have he : ((D.R.N j : ℤ) - 1) = ((NN X.G.P.m X.t j - 1 : ℕ) : ℤ) := by
      rw [← hN.1]; push_cast [Nat.cast_sub hpos]; ring
    rw [hz, kOdd, he, zpow_natCast]
    simp only [Matrix.smul_apply, Matrix.submatrix_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_pow, mul_assoc]
  · rw [if_neg ho, one_mul]
    have h0 : ySub X Kc j v s = dyMat X Kc j v s := by unfold ySub; rw [if_neg ho]
    have hz : zT X D pos (dfr X D hN d f') (pos ⟨v, s⟩) = dfr X D hN d f' (pos ⟨v, s⟩) := by
      unfold zT; rw [if_neg (fun h => ho (hsym.1 h))]
    have h2 := congrFun (congrFun (hE ho) a) t
    rw [Matrix.map_apply] at h2
    rw [h0, h2, hz]
    rfl

end GlobalTheory.TwV.DelA

namespace GlobalTheory.TwV.DelA

theorem evD_subD : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (Gc : XR (X.Pj j) ℂ) (G : (X.Pj j).Xsp), MvPolynomial.map (algebraMap X.G.Kf Kc) G = MvPolynomial.map ι Gc → OddDeg X j G → ∀ (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ) (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ), (∀ τ, (f' τ).det ≠ 0) → (∀ τ, (dfr X D hN d f' τ).det ≠ 0) → evD X D pos ι hN d f' (subD X Kc j G) = ι ((∏ τ, if IsOddPos (pos.symm τ).2 then ((zT X D pos f' τ).det ^ ((D.R.N j : ℤ) - 1) * sgRev (D.R.N j) * (dfr X D hN d f' τ).det) ^ ((D.R.N j : ℤ) * cT1 X D pos j τ - szT X D pos j τ) else 1) * valZ X D pos j (rkS X D hN) Gc (dfr X D hN d f')) := by
  intro p _ X D pos Kc _ _ ι j hN Gc G hG hO d f' hf hd
  let g : Var (X.Pj j) → ℂ := fun y => zT X D pos (dfr X D hN d f') (posJ X D pos j ⟨y.1, y.2.1⟩)
    (Fin.cast (rkS X D hN) y.2.2.1) (Fin.cast (rkS X D hN) y.2.2.2)
  let φ : (X.Pj j).Xsp →+* Kc := (evD X D pos ι hN d f').comp (subD X Kc j : (X.Pj j).Xsp →+* DA X Kc j)
  let ψ : (X.Pj j).Xsp →+* Kc := MvPolynomial.eval₂Hom (algebraMap X.G.Kf Kc) (fun y => ι (g y))
  have hR : ι (valZ X D pos j (rkS X D hN) Gc (dfr X D hN d f')) = ψ G := by
    show ι (MvPolynomial.eval g Gc) = MvPolynomial.eval₂ (algebraMap X.G.Kf Kc) (fun y => ι (g y)) G
    rw [MvPolynomial.eval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left, RingHom.comp_id,
      ← MvPolynomial.eval_map, ← hG, MvPolynomial.eval_map]
    rfl
  have hC : ∀ a, φ (MvPolynomial.C a) = ψ (MvPolynomial.C a) := by
    intro a
    show evD X D pos ι hN d f' (subD X Kc j (MvPolynomial.C a)) = MvPolynomial.eval₂ _ _ (MvPolynomial.C a)
    rw [MvPolynomial.eval₂_C, ← MvPolynomial.algebraMap_eq, AlgHom.commutes, MvPolynomial.algebraMap_apply,
      MvPolynomial.algebraMap_apply]
    simp [evD]
  have hX : ∀ x, φ (MvPolynomial.X x) =
      (if IsOddPos (blkJ X j x).2 then ι (kOdd X D pos hN d f' (pos (blkJ X j x))) else 1) * ψ (MvPolynomial.X x) := by
    intro x
    show evD X D pos ι hN d f' (subD X Kc j (MvPolynomial.X x)) = _ * MvPolynomial.eval₂ _ _ (MvPolynomial.X x)
    rw [subD_X, MvPolynomial.eval₂_X, evD_ySub X D pos Kc ι hN d f' hf hd]
    congr 2
    show _ = zT X D pos (dfr X D hN d f') (posJ X D pos j ⟨x.1, x.2.1⟩) _ _
    rw [posJ_blkJ]
    congr 1 <;> ext <;> simp [levelIndex_row_val_eq, levelIndex_col_val_eq]
  have key := ringHom_scale φ ψ
    (fun x => if IsOddPos (blkJ X j x).2 then ι (kOdd X D pos hN d f' (pos (blkJ X j x))) else 1) hC hX
    (ι (∏ τ, if IsOddPos (pos.symm τ).2 then ((zT X D pos f' τ).det ^ ((D.R.N j : ℤ) - 1) * sgRev (D.R.N j) * (dfr X D hN d f' τ).det) ^ ((D.R.N j : ℤ) * cT1 X D pos j τ - szT X D pos j τ) else 1)) G ?_
  · rw [map_mul, hR]
    exact key
  · intro m hm
    let H : (Σ v : X.Pl, Fin (X.G.P.n' v)) → ℂ := fun b =>
      if IsOddPos b.2 then kOdd X D pos hN d f' (pos b) ^ ((D.R.N j : ℤ) * cMu X j b.1 b.2 - szMu X j b.1 b.2) else 1
    have hF : ∀ τ, (if IsOddPos (pos.symm τ).2 then ((zT X D pos f' τ).det ^ ((D.R.N j : ℤ) - 1) * sgRev (D.R.N j) * (dfr X D hN d f' τ).det) ^ ((D.R.N j : ℤ) * cT1 X D pos j τ - szT X D pos j τ) else 1) = H (pos.symm τ) := by
      intro τ
      simp only [H, cT1, szT, Equiv.apply_symm_apply]
      rfl
    rw [Finset.prod_congr rfl (fun τ _ => hF τ), Fintype.prod_equiv pos.symm (fun τ => H (pos.symm τ)) H (fun _ => rfl),
      map_prod, ← Finset.prod_fiberwise Finset.univ (blkJ X j)]
    refine Finset.prod_congr rfl fun b _ => ?_
    have h2 : ∏ x ∈ Finset.univ.filter (fun x => blkJ X j x = b),
        (if IsOddPos (blkJ X j x).2 then ι (kOdd X D pos hN d f' (pos (blkJ X j x))) else 1) ^ m x =
        (if IsOddPos b.2 then ι (kOdd X D pos hN d f' (pos b)) else 1) ^
          (∑ x ∈ Finset.univ.filter (fun x => blkJ X j x = b), m x) := by
      rw [← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_congr rfl fun x hx => ?_
      rw [(Finset.mem_filter.1 hx).2]
    rw [h2]
    by_cases hb : IsOddPos b.2
    · simp only [H]
      rw [if_pos hb, if_pos hb, hN.1, ← hO m hm b hb, zpow_natCast, map_pow]
    · simp only [H]
      rw [if_neg hb, if_neg hb, one_pow, map_one]

end GlobalTheory.TwV.DelA
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SubstitutedValueAtComplexPointOddBlocksStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.substituted_value_at_complex_point_oddBlocks : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (Gc : XR (X.Pj j) ℂ) (G : (X.Pj j).Xsp), MvPolynomial.map (algebraMap X.G.Kf Kc) G = MvPolynomial.map ι Gc → OddDeg X j G → ∀ (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ) (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ), (∀ τ, (f' τ).det ≠ 0) → (∀ τ, (dfr X D hN d f' τ).det ≠ 0) → evD X D pos ι hN d f' (subD X Kc j G) = ι ((∏ τ, if IsOddPos (pos.symm τ).2 then ((zT X D pos f' τ).det ^ ((D.R.N j : ℤ) - 1) * sgRev (D.R.N j) * (dfr X D hN d f' τ).det) ^ ((D.R.N j : ℤ) * cT1 X D pos j τ - szT X D pos j τ) else 1) * valZ X D pos j (rkS X D hN) Gc (dfr X D hN d f')) := by
  first | exact @GlobalTheory.TwV.DelA.evD_subD | exact GlobalTheory.TwV.DelA.evD_subD | (intros; apply GlobalTheory.TwV.DelA.evD_subD <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NumeratorDivDenominatorAtComplexPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NumeratorDivDenominatorAtComplexPoint
noncomputable section

namespace GlobalTheory.TwV.DelA

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem _root_.Formalism.L2.G.Pend Formalism.MainNotions _root_.Formalism.L2.Ker _root_.Formalism.L2.PairingIndexBounds.F _root_.Formalism.L2.KerInert Formalism.UG _root_.Formalism.L2.G.Cmp _root_.Formalism.L2.Forms _root_.Formalism.L2.KerInert.SecondKernelProjection _root_.Formalism.L2.KerInert.QuadraticBaseChangeGL3 _root_.Formalism.L2.KerInert.SecondKernelDifference _root_.Formalism.L2.KerInert.SecondKernelHermitian

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)

theorem pow_toNat_split {K : Type} [Field K] {a : K} (ha : a ≠ 0) (e : ℤ) :
    a ^ e.toNat = a ^ (-e).toNat * a ^ e := by
  have h := Int.toNat_sub_toNat_neg e
  calc a ^ e.toNat = a ^ (-e).toNat * a ^ ((e.toNat : ℤ) - ((-e).toNat : ℤ)) := by
        rw [zpow_sub₀ ha, zpow_natCast, zpow_natCast]
        field_simp
    _ = _ := by rw [h]

theorem zT_det_ne {n : ℕ} (f : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (hf : ∀ τ, (f τ).det ≠ 0) (τ : D.what₂.Tau) :
    (zT X D pos f τ).det ≠ 0 := by
  unfold zT
  split_ifs
  · have h1 : (((f τ)⁻¹).transpose.submatrix id Fin.rev).det
        = ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤˣ) : ℤ) * (((f τ)⁻¹).transpose).det := by
      exact Matrix.det_permute' (Fin.revPerm : Equiv.Perm (Fin n)) (((f τ)⁻¹).transpose)
    rw [h1, Matrix.det_transpose, Matrix.det_nonsing_inv]
    refine mul_ne_zero (by simp) ?_
    rw [Ring.inverse_eq_inv']
    exact inv_ne_zero (hf τ)
  · exact hf τ

theorem det_rev_transpose {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (A.transpose.submatrix Fin.rev id).det = sgRev n * A.det := by
  have : (A.transpose.submatrix Fin.rev id).det = _ := Matrix.det_permute (Fin.revPerm : Equiv.Perm (Fin n)) A.transpose
  rw [this, Matrix.det_transpose, sgRev]

theorem evD_det {Kc : Type} [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) {j : ℕ} (hN : RankTie X D j)
    (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ)
    (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ) {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n (DA X Kc j)) : evD X D pos ι hN d f' M.det = (M.map (evD X D pos ι hN d f')).det :=
  RingHom.map_det _ M

theorem det_map_cast {Kc : Type} [Field Kc] (ι : ℂ →+* Kc) {a b : ℕ} (h : a = b) (B : Matrix (Fin b) (Fin b) ℂ) :
    ((B.map ι).submatrix (Fin.cast h) (Fin.cast h)).det = ι B.det := by
  have : ((B.map ι).submatrix (Fin.cast h) (Fin.cast h)).det = (B.map ι).det :=
    Matrix.det_submatrix_equiv_self (finCongr h) (B.map ι)
  rw [this, RingHom.map_det]
  rfl

theorem evD_numD_denD : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ) (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ), (∀ τ, (f' τ).det ≠ 0) → (∀ τ, (dfr X D hN d f' τ).det ≠ 0) → evD X D pos ι hN d f' (numD X Kc j) = evD X D pos ι hN d f' (denD X Kc j) * ι (∏ τ, if IsOddPos (pos.symm τ).2 then (zT X D pos f' τ).det ^ (cT1 X D pos j τ - szT X D pos j τ) * ((zT X D pos f' τ).det ^ (D.R.N j) * sgRev (D.R.N j) * (dfr X D hN d f' τ).det) ^ (cT1 X D pos j τ - (D.R.N j : ℤ) * cT1 X D pos j τ + szT X D pos j τ) else (dfr X D hN d f' τ).det ^ (X.nuv (pos.symm τ).1 (j + 1) (pos.symm τ).2 (NN X.G.P.m X.t j)).toNat) := by
  intro p _ X D pos Kc _ _ ι j hN d f' hf hd
  classical
  have key := GlobalTheory.T.operatorMatrices_at_complexPoint X D pos Kc ι j hN d f' hf hd
  have e : ∀ G : D.what₂.Tau → ℂ, ∏ τ, G τ = ∏ v, ∏ s, G (pos ⟨v, s⟩) := fun G => by
    rw [← Equiv.prod_comp pos G, Fintype.prod_sigma]
  rw [e, map_prod]
  unfold numD denD
  simp only [map_prod]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  simp only [cT1, szT]
  rw [Equiv.symm_apply_apply]
  obtain ⟨k1, k2, k3⟩ := key v s
  by_cases hs : IsOddPos s
  · simp only [if_pos hs]
    have hY : evD X D pos ι hN d f' (YtMat X Kc j v s).det
        = ι ((zT X D pos f' (pos ⟨v, s⟩)).det ^ D.R.N j * sgRev (D.R.N j) * (dfr X D hN d f' (pos ⟨v, s⟩)).det) := by
      rw [evD_det, k3 hs, Matrix.det_smul, det_map_cast, det_rev_transpose, Fintype.card_fin,
        show NN X.G.P.m X.t j = D.R.N j from hN.1.symm]
      simp only [map_mul, map_pow]
      ring
    have ha : ι (zT X D pos f' (pos ⟨v, s⟩)).det ≠ 0 := (map_ne_zero ι).2 (zT_det_ne X D pos f' hf _)
    have hb : ι ((zT X D pos f' (pos ⟨v, s⟩)).det ^ D.R.N j * sgRev (D.R.N j) * (dfr X D hN d f' (pos ⟨v, s⟩)).det) ≠ 0 := by
      refine (map_ne_zero ι).2 (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (zT_det_ne X D pos f' hf _)) ?_) (hd _))
      simp [sgRev]
    rw [map_mul ι ((zT X D pos f' (pos ⟨v, s⟩)).det ^ _), map_zpow₀, map_zpow₀]
    rw [map_mul (evD X D pos ι hN d f'), map_mul (evD X D pos ι hN d f'), map_pow (evD X D pos ι hN d f'),
      map_pow (evD X D pos ι hN d f'), map_pow (evD X D pos ι hN d f'), map_pow (evD X D pos ι hN d f'), k1, hY,
      pow_toNat_split ha (exY X j v s), pow_toNat_split hb (exT X j v s)]
    have h1 : exY X j v s = cMu X j v s - szMu X j v s := rfl
    have h2 : exT X j v s = cMu X j v s - (D.R.N j : ℤ) * cMu X j v s + szMu X j v s := by
      rw [exT, show NN X.G.P.m X.t j = D.R.N j from hN.1.symm]
    rw [h1, h2]
    ring
  · simp only [if_neg hs]
    rw [map_one, one_mul, map_pow (evD X D pos ι hN d f'), evD_det, k2 hs, det_map_cast, map_pow]

end GlobalTheory.TwV.DelA
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NumeratorDivDenominatorAtComplexPointStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.numerator_div_denominator_at_complex_point : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ) (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ), (∀ τ, (f' τ).det ≠ 0) → (∀ τ, (dfr X D hN d f' τ).det ≠ 0) → evD X D pos ι hN d f' (numD X Kc j) = evD X D pos ι hN d f' (denD X Kc j) * ι (∏ τ, if IsOddPos (pos.symm τ).2 then (zT X D pos f' τ).det ^ (cT1 X D pos j τ - szT X D pos j τ) * ((zT X D pos f' τ).det ^ (D.R.N j) * sgRev (D.R.N j) * (dfr X D hN d f' τ).det) ^ (cT1 X D pos j τ - (D.R.N j : ℤ) * cT1 X D pos j τ + szT X D pos j τ) else (dfr X D hN d f' τ).det ^ (X.nuv (pos.symm τ).1 (j + 1) (pos.symm τ).2 (NN X.G.P.m X.t j)).toNat) := by
  first | exact @GlobalTheory.TwV.DelA.evD_numD_denD | exact GlobalTheory.TwV.DelA.evD_numD_denD | (intros; apply GlobalTheory.TwV.DelA.evD_numD_denD <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorIdentityLeftSideComplexPoint
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwV.DelA

theorem leftSide_odd_grp {M : Type} [CommGroup M] (u e d d' e' : M) (n : ℕ) (c s w : ℤ) (hu : u = e' * d'⁻¹) (he : e * e = 1) :
    (u ^ ((n : ℤ) - 1) * e * d) ^ ((n : ℤ) * c - s) * (u ^ (c - s) * (u ^ n * e * d) ^ (c - (n : ℤ) * c + s)) * u ^ (w - c) * d ^ (-w)
      = (e * e') ^ w * d' ^ (-w) * (e * d⁻¹) ^ (w - c) := by
  subst hu
  apply Additive.ofMul.injective
  have he' : Additive.ofMul e + Additive.ofMul e = 0 := by rw [← ofMul_mul, he]; rfl
  simp only [ofMul_mul, ofMul_zpow, ofMul_pow, ofMul_inv]
  linear_combination (norm := module) (c - w) • he'

theorem leftSide_odd (u e d d' e' : ℂ) (n : ℕ) (c s w : ℤ) (hd : d ≠ 0) (hd' : d' ≠ 0) (he : e * e = 1) (he' : e' * e' = 1)
    (hu : u = e' * d'⁻¹) :
    (u ^ ((n : ℤ) - 1) * e * d) ^ ((n : ℤ) * c - s) * (u ^ (c - s) * (u ^ n * e * d) ^ (c - (n : ℤ) * c + s)) * u ^ (w - c) * d ^ (-w)
      = (e * e') ^ w * d' ^ (-w) * (e * d⁻¹) ^ (w - c) := by
  have he0 : e ≠ 0 := left_ne_zero_of_mul_eq_one he
  have he0' : e' ≠ 0 := left_ne_zero_of_mul_eq_one he'
  have h := leftSide_odd_grp (Units.mk0 e' he0' * (Units.mk0 d' hd')⁻¹) (Units.mk0 e he0) (Units.mk0 d hd) (Units.mk0 d' hd')
    (Units.mk0 e' he0') n c s w rfl (Units.ext (by simpa using he))
  have h2 := congrArg Units.val h
  simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_mk0] at h2
  subst hu
  exact h2

theorem leftSide_sgRev_sq (n : ℕ) : sgRev n * sgRev n = 1 := by
  unfold sgRev
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
  simp

theorem leftSide_det_zT_odd {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) {n : ℕ}
    (f : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (τ : D.what₂.Tau) (h : IsOddPos (pos.symm τ).2) :
    (zT X D pos f τ).det = sgRev n * ((f τ).det)⁻¹ := by
  unfold zT
  rw [if_pos h]
  have := Matrix.det_permute' (Fin.revPerm : Equiv.Perm (Fin n)) ((f τ)⁻¹).transpose
  rw [show (⇑(Fin.revPerm : Equiv.Perm (Fin n))) = Fin.rev from rfl] at this
  rw [this, Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  rfl

theorem leftSide_zT_even {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) {n : ℕ}
    (f : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (τ : D.what₂.Tau) (h : ¬ IsOddPos (pos.symm τ).2) :
    zT X D pos f τ = f τ := by
  unfold zT; rw [if_neg h]

end GlobalTheory.TwV.DelA
end

namespace GlobalTheory.TwV.DelA

theorem leftSide_at_point : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → ∀ (Q : MvPolynomial (GL3Theta.FrV D (D.R.N j)) ℂ), Q ∈ WtPol ℂ ν → ∀ (Gc : XR (X.Pj j) ℂ) (G : (X.Pj j).Xsp), Realises X D pos j (rkS X D hN) (wT X D pos j) Q Gc → MvPolynomial.map (algebraMap X.G.Kf Kc) G = MvPolynomial.map ι Gc → ∀ (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ) (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ), (∀ τ, (f' τ).det ≠ 0) → (∀ τ, (dfr X D hN d f' τ).det ≠ 0) → evD X D pos ι hN d f' (subD X Kc j G * numD X Kc j) * ι (∏ τ, (zT X D pos f' τ).det ^ eT X D pos (j + 1) τ) = evD X D pos ι hN d f' (denD X Kc j) * ι (sgO X D pos j * (∏ τ, (f' τ).det ^ (-(wT X D pos j τ))) * GL3Theta.evFr D Q (dfr X D hN d f')) := by
  intro p _ X D pos Kc _ _ ι j hN ν hν Q hQ Gc G hR hG d f' hf' hdf
  have hodd := GlobalTheory.T.modelPolynomial_oddDegree_of_realisesFramePoly X D pos Kc ι j hN ν hν Q hQ Gc G hR hG
  have hsub := GlobalTheory.T.substituted_value_at_complex_point_oddBlocks X D pos Kc ι j hN Gc G hG hodd d f' hf' hdf
  have hnum := GlobalTheory.T.numerator_div_denominator_at_complex_point X D pos Kc ι j hN d f' hf' hdf
  have hex := GlobalTheory.T.realPlaceBlockWeightLastEntry_consecutive_levels X D pos j
  have hnn := (GlobalTheory.T.modelPartition_size_extension_firstLast_rows X D pos j hN ν hν).2.2.2.2
  have hR' := hR ⟨dfr X D hN d f', fun τ => (hdf τ).isUnit⟩
  have hR2 := (ev1_eq_prod_det_pow_mul_valZ X D pos j (rkS X D hN) Gc ⟨dfr X D hN d f', fun τ => (hdf τ).isUnit⟩).symm.trans hR'
  clear hR'
  simp only at hR2
  rw [map_mul, hsub, hnum]
  have gen : ∀ (x y z : ℂ) (E : Kc), ι x * (E * ι y) * ι z = E * ι (x * y * z) := by
    intro x y z E; simp only [map_mul]; ring
  rw [gen]
  congr 2
  have hW : (∏ τ, (dfr X D hN d f' τ).det ^ (-(wT X D pos j τ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ (hdf τ)
  have key : ∀ A V B P' S W' q Pj Wf : ℂ, Wf ≠ 0 → A * B * P' * Wf = S * W' * Pj → Pj * V = Wf * q →
      A * V * B * P' = S * W' * q := by
    intro A V B P' S W' q Pj Wf hWf hK hP
    apply mul_right_cancel₀ hWf
    linear_combination V * hK + S * W' * hP
  refine key _ _ _ _ _ _ _ _ _ hW ?_ hR2
  unfold sgO
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  obtain ⟨h1, h2⟩ := hex τ
  by_cases ho : IsOddPos (pos.symm τ).2
  · simp only [if_pos ho] at h1 h2 ⊢
    rw [h1, h2, leftSide_det_zT_odd X D pos f' τ ho, leftSide_det_zT_odd X D pos (dfr X D hN d f') τ ho]
    exact leftSide_odd _ _ _ _ _ _ _ _ _ (hdf τ) (hf' τ) (leftSide_sgRev_sq _) (leftSide_sgRev_sq _) rfl
  · simp only [if_neg ho] at h1 h2 ⊢
    rw [h1, h2, leftSide_zT_even X D pos f' τ ho, leftSide_zT_even X D pos (dfr X D hN d f') τ ho, ← zpow_natCast,
      Int.toNat_of_nonneg (hnn τ), zpow_sub₀ (hdf τ)]
    simp only [zpow_neg]
    ring

end GlobalTheory.TwV.DelA
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorIdentityLeftSideComplexPointStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.operatorIdentity_leftSide_complexPoint : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → ∀ (Q : MvPolynomial (GL3Theta.FrV D (D.R.N j)) ℂ), Q ∈ WtPol ℂ ν → ∀ (Gc : XR (X.Pj j) ℂ) (G : (X.Pj j).Xsp), Realises X D pos j (rkS X D hN) (wT X D pos j) Q Gc → MvPolynomial.map (algebraMap X.G.Kf Kc) G = MvPolynomial.map ι Gc → ∀ (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ) (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ), (∀ τ, (f' τ).det ≠ 0) → (∀ τ, (dfr X D hN d f' τ).det ≠ 0) → evD X D pos ι hN d f' (subD X Kc j G * numD X Kc j) * ι (∏ τ, (zT X D pos f' τ).det ^ eT X D pos (j + 1) τ) = evD X D pos ι hN d f' (denD X Kc j) * ι (sgO X D pos j * (∏ τ, (f' τ).det ^ (-(wT X D pos j τ))) * GL3Theta.evFr D Q (dfr X D hN d f')) := by
  first | exact @GlobalTheory.TwV.DelA.leftSide_at_point | exact GlobalTheory.TwV.DelA.leftSide_at_point | (intros; apply GlobalTheory.TwV.DelA.leftSide_at_point <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SymbolFramePolynomialEqZeroOfGenericVanish
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SymbolFramePolynomialEqZeroOfGenericVanish
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.DelA.Dense

theorem eq_zero_of_vanish_off {σ Kc : Type} [Field Kc] (ι : ℂ →+* Kc) (R : MvPolynomial σ Kc)
    (h : MvPolynomial σ ℂ) (x0 : σ → ℂ) (hx0 : MvPolynomial.eval x0 h ≠ 0)
    (hR : ∀ x : σ → ℂ, MvPolynomial.eval x h ≠ 0 → MvPolynomial.eval (ι ∘ x) R = 0) : R = 0 := by
  have hev : ∀ x : σ → ℂ, MvPolynomial.eval (ι ∘ x) (MvPolynomial.map ι h) = ι (MvPolynomial.eval x h) := by
    intro x
    rw [MvPolynomial.eval_map, MvPolynomial.eval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left,
      RingHom.comp_id]
  have hh : MvPolynomial.map ι h ≠ 0 := by
    intro h0
    apply hx0
    apply ι.injective
    rw [← hev, h0, map_zero, map_zero]
  have hinf : ∀ _ : σ, (Set.range ι).Infinite := fun _ => Set.infinite_range_of_injective ι.injective
  have hprod : R * MvPolynomial.map ι h = 0 := by
    refine MvPolynomial.funext_set (fun _ => Set.range ι) hinf (fun y hy => ?_)
    choose x hx using fun i => hy i (Set.mem_univ i)
    have hy' : y = ι ∘ x := funext fun i => (hx i).symm
    rw [hy', map_mul, map_zero, hev]
    by_cases hz : MvPolynomial.eval x h = 0
    · rw [hz, map_zero, mul_zero]
    · rw [hR x hz, zero_mul]
  exact (mul_eq_zero.mp hprod).resolve_right hh

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
  {j : ℕ} (hN : RankTie X D j)

def idxSym (τ : D.what₂.Tau) (a : Fin (D.R.N j)) (b : Fin (D.R.N (j + 1))) : X.ZA j :=
  ⟨(pos.symm τ).1, ((pos.symm τ).2, Fin.cast hN.1 a, Fin.cast hN.2 b)⟩

def dOf (x : X.ZA j → ℂ) (τ : D.what₂.Tau) : Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ :=
  fun a b => x (idxSym X D pos hN τ a b)

theorem dOf_read (x : X.ZA j → ℂ) (z : X.ZA j) :
    dOf X D pos hN x (pos ⟨z.1, z.2.1⟩) (Fin.cast hN.1.symm z.2.2.1) (Fin.cast hN.2.symm z.2.2.2) = x z := by
  obtain ⟨v, s, a, b⟩ := z
  have key : ∀ q : (Σ v : X.Pl, Fin (X.G.P.n' v)), q = ⟨v, s⟩ →
      (⟨q.1, (q.2, a, b)⟩ : X.ZA j) = ⟨v, (s, a, b)⟩ := by
    rintro q rfl; rfl
  simp only [dOf, idxSym, Fin.cast_cast, Fin.cast_eq_self]
  rw [key _ (pos.symm_apply_apply _)]

theorem dOf_surj (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ) :
    dOf X D pos hN (fun z => d (pos ⟨z.1, z.2.1⟩) (Fin.cast hN.1.symm z.2.2.1) (Fin.cast hN.2.symm z.2.2.2)) = d := by
  funext τ a b
  simp [dOf, idxSym]

def hD (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ) : MvPolynomial (X.ZA j) ℂ :=
  ∏ τ, Matrix.det (Matrix.of fun a b : Fin (D.R.N j) => ∑ k : Fin (D.R.N (j + 1)),
    MvPolynomial.X (idxSym X D pos hN τ a k) * MvPolynomial.C (f' τ k (Fin.castLE (rk_le X D hN) b)))

theorem eval_hD (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ) (x : X.ZA j → ℂ) :
    MvPolynomial.eval x (hD X D pos hN f') = ∏ τ, (dfr X D hN (dOf X D pos hN x) f' τ).det := by
  rw [hD, map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp [dfr, Matrix.mul_apply, dOf]

def idxFr (τ : D.what₂.Tau) (a b : Fin (D.R.N (j + 1))) : Formalism.L2.G.Cmp.Var (X.Pj (j + 1)) :=
  ⟨(pos.symm τ).1, ((pos.symm τ).2, Fin.cast (rkT X D hN).symm a, Fin.cast (rkT X D hN).symm b)⟩

def blkOf (w : Formalism.L2.G.Cmp.Var (X.Pj (j + 1)) → ℂ) (τ : D.what₂.Tau) : Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ :=
  fun a b => w (idxFr X D pos hN τ a b)

theorem blkOf_read (w : Formalism.L2.G.Cmp.Var (X.Pj (j + 1)) → ℂ) (y : Formalism.L2.G.Cmp.Var (X.Pj (j + 1))) :
    blkOf X D pos hN w (pos ⟨y.1, y.2.1⟩) (Fin.cast (rkT X D hN) y.2.2.1) (Fin.cast (rkT X D hN) y.2.2.2) = w y := by
  obtain ⟨v, s, a, b⟩ := y
  have key : ∀ q : (Σ v : X.Pl, Fin (X.G.P.n' v)), q = ⟨v, s⟩ →
      (⟨q.1, (q.2, a, b)⟩ : Formalism.L2.G.Cmp.Var (X.Pj (j + 1))) = ⟨v, (s, a, b)⟩ := by
    rintro q rfl; rfl
  simp only [blkOf, idxFr, Fin.cast_cast, Fin.cast_eq_self]
  rw [key _ (pos.symm_apply_apply _)]

def hY : MvPolynomial (Formalism.L2.G.Cmp.Var (X.Pj (j + 1))) ℂ :=
  ∏ τ, Matrix.det (Matrix.of fun a b : Fin (D.R.N (j + 1)) => MvPolynomial.X (idxFr X D pos hN τ a b))

theorem eval_hY (w : Formalism.L2.G.Cmp.Var (X.Pj (j + 1)) → ℂ) :
    MvPolynomial.eval w (hY X D pos hN) = ∏ τ, (blkOf X D pos hN w τ).det := by
  rw [hY, map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp [blkOf]

def fOf {n : ℕ} (g : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (τ : D.what₂.Tau) : Matrix (Fin n) (Fin n) ℂ :=
  if IsOddPos (pos.symm τ).2 then (((g τ).submatrix id Fin.rev).transpose)⁻¹ else g τ

theorem det_rev_ne_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.det ≠ 0) : (M.submatrix id Fin.rev).transpose.det ≠ 0 := by
  rw [Matrix.det_transpose]
  have h := Matrix.det_permute' (Fin.revPerm : Equiv.Perm (Fin n)) M
  rw [show M.submatrix id ⇑(Fin.revPerm : Equiv.Perm (Fin n)) = M.submatrix id Fin.rev from rfl] at h
  rw [h]
  exact mul_ne_zero (Int.cast_ne_zero.mpr (Units.ne_zero _)) hM

theorem zT_fOf {n : ℕ} (g : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (hg : ∀ τ, (g τ).det ≠ 0) :
    zT X D pos (fOf X D pos g) = g := by
  funext τ
  unfold zT fOf
  by_cases ho : IsOddPos (pos.symm τ).2
  · rw [if_pos ho, if_pos ho,
      Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr (det_rev_ne_zero (g τ) (hg τ)))]
    ext a b
    simp
  · rw [if_neg ho, if_neg ho]

theorem det_fOf {n : ℕ} (g : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (hg : ∀ τ, (g τ).det ≠ 0) (τ : D.what₂.Tau) :
    (fOf X D pos g τ).det ≠ 0 := by
  unfold fOf
  by_cases ho : IsOddPos (pos.symm τ).2
  · rw [if_pos ho]
    exact (Matrix.isUnit_nonsing_inv_det _ (isUnit_iff_ne_zero.mpr (det_rev_ne_zero (g τ) (hg τ)))).ne_zero
  · rw [if_neg ho]; exact hg τ

def yv {Kc : Type} [Field Kc] (ι : ℂ →+* Kc) (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ) :
    Formalism.L2.G.Cmp.Var (X.Pj (j + 1)) → Kc := fun y =>
  ι (zT X D pos f' (pos ⟨y.1, y.2.1⟩) (Fin.cast (rkT X D hN) y.2.2.1) (Fin.cast (rkT X D hN) y.2.2.2))

theorem evD_eq_eval {Kc : Type} [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc)
    (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ)
    (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ) (P : DA X Kc j) :
    evD X D pos ι hN d f' P = MvPolynomial.eval
      (fun z : X.ZA j => ι (d (pos ⟨z.1, z.2.1⟩) (Fin.cast hN.1.symm z.2.2.1) (Fin.cast hN.2.symm z.2.2.2)))
      (MvPolynomial.map (MvPolynomial.eval (yv X D pos hN ι f')) P) := by
  rw [MvPolynomial.eval_map]
  rfl

end GlobalTheory.TwV.DelA.Dense


open GlobalTheory.TwV.DelA.Dense in
theorem GlobalTheory.TwV.DelA.eq_zero_of_evD_generic : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (P : DA X Kc j), (∀ (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ) (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ), (∀ τ, (f' τ).det ≠ 0) → (∀ τ, (dfr X D hN d f' τ).det ≠ 0) → evD X D pos ι hN d f' P = 0) → P = 0 := by
  intro p _ X D pos Kc _ _ ι j hN P hP
  have step1 : ∀ f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ, (∀ τ, (f' τ).det ≠ 0) →
      MvPolynomial.map (MvPolynomial.eval (yv X D pos hN ι f')) P = 0 := by
    intro f' hf'
    set E : Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ :=
      (1 : Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ).submatrix (Fin.castLE (rk_le X D hN)) id with hE
    set d0 : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ := fun τ => E * (f' τ)⁻¹ with hd0
    refine eq_zero_of_vanish_off ι _ (hD X D pos hN f')
      (fun z => d0 (pos ⟨z.1, z.2.1⟩) (Fin.cast hN.1.symm z.2.2.1) (Fin.cast hN.2.symm z.2.2.2)) ?_ ?_
    · rw [eval_hD, dOf_surj]
      refine Finset.prod_ne_zero_iff.mpr fun τ _ => ?_
      have : dfr X D hN d0 f' τ = 1 := by
        unfold dfr
        rw [hd0]
        simp only
        rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hf' τ)), Matrix.mul_one, hE,
          Matrix.submatrix_submatrix, Function.comp_id, Function.id_comp]
        exact Matrix.submatrix_one _ (Fin.castLE_injective _)
      rw [this, Matrix.det_one]
      exact one_ne_zero
    · intro x hx
      rw [eval_hD] at hx
      have hdet : ∀ τ, (dfr X D hN (dOf X D pos hN x) f' τ).det ≠ 0 :=
        fun τ => (Finset.prod_ne_zero_iff.mp hx) τ (Finset.mem_univ _)
      have h := hP (dOf X D pos hN x) f' hf' hdet
      rw [evD_eq_eval] at h
      have hxv : (fun z : X.ZA j => ι (dOf X D pos hN x (pos ⟨z.1, z.2.1⟩) (Fin.cast hN.1.symm z.2.2.1)
          (Fin.cast hN.2.symm z.2.2.2))) = ι ∘ x := by
        funext z
        simp only [Function.comp_apply, dOf_read]
      rw [hxv] at h
      exact h
  ext m : 1
  rw [MvPolynomial.coeff_zero]
  refine eq_zero_of_vanish_off ι _ (hY X D pos hN)
    (fun y => if y.2.2.1 = y.2.2.2 then 1 else 0) ?_ ?_
  · rw [eval_hY]
    refine Finset.prod_ne_zero_iff.mpr fun τ _ => ?_
    have : blkOf X D pos hN (fun y => if y.2.2.1 = y.2.2.2 then 1 else 0) τ = 1 := by
      ext a b
      simp [GlobalTheory.TwV.DelA.Dense.blkOf, GlobalTheory.TwV.DelA.Dense.idxFr, Matrix.one_apply]
    rw [this, Matrix.det_one]
    exact one_ne_zero
  · intro w hw
    rw [eval_hY] at hw
    have hg : ∀ τ, (blkOf X D pos hN w τ).det ≠ 0 := fun τ => (Finset.prod_ne_zero_iff.mp hw) τ (Finset.mem_univ _)
    have h1 := step1 (fOf X D pos (blkOf X D pos hN w)) (det_fOf X D pos _ hg)
    have h2 : yv X D pos hN ι (fOf X D pos (blkOf X D pos hN w)) = ι ∘ w := by
      funext y
      simp only [yv, zT_fOf X D pos _ hg, Function.comp_apply, blkOf_read]
    have h3 := congrArg (AddMonoidAlgebra.coeff · m) h1
    rw [MvPolynomial.coeff_map, h2, MvPolynomial.coeff_zero] at h3
    exact h3

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SymbolFramePolynomialEqZeroOfGenericVanishStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symbolFramePolynomial_eq_zero_of_generic_vanish : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (P : DA X Kc j), (∀ (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ) (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ), (∀ τ, (f' τ).det ≠ 0) → (∀ τ, (dfr X D hN d f' τ).det ≠ 0) → evD X D pos ι hN d f' P = 0) → P = 0 := by
  first | exact @GlobalTheory.TwV.DelA.eq_zero_of_evD_generic | exact GlobalTheory.TwV.DelA.eq_zero_of_evD_generic | (intros; apply GlobalTheory.TwV.DelA.eq_zero_of_evD_generic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetTwistedFrameOperatorIdentityDenominator
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem det_zT_ne_zero {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
    {n : ℕ} (f : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (hf : ∀ τ, (f τ).det ≠ 0) (τ : D.what₂.Tau) :
    (zT X D pos f τ).det ≠ 0 := by
  unfold zT
  split_ifs
  · have hu : IsUnit (f τ).det := isUnit_iff_ne_zero.mpr (hf τ)
    have e : ((f τ)⁻¹).transpose.submatrix id Fin.rev = ((f τ)⁻¹).transpose.submatrix id (Fin.revPerm : Equiv.Perm (Fin n)) := rfl
    rw [e, Matrix.det_permute', Matrix.det_transpose]
    refine mul_ne_zero (by simp [Units.ne_zero]) ?_
    intro h0
    have := Matrix.det_nonsing_inv_mul_det (f τ) hu
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  · exact hf τ

theorem opId_denom : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → ∀ (Q : MvPolynomial (GL3Theta.FrV D (D.R.N j)) ℂ), Q ∈ WtPol ℂ ν → ∀ (Gc : XR (X.Pj j) ℂ) (G : (X.Pj j).Xsp), Realises X D pos j (rkS X D hN) (wT X D pos j) Q Gc → MvPolynomial.map (algebraMap X.G.Kf Kc) G = MvPolynomial.map ι Gc → ∀ (s : D.what₂.Tau → ℂ), (∀ τ, s τ ≠ 0) → subD X Kc j G * numD X Kc j = denD X Kc j * (cD X Kc j (ι (cOp X D pos j s)) * trDY X Kc j D (eIdx X D pos j hN) (phi0 X D pos ι j) (polDY D s Q (N' := D.R.N (j + 1)))) := by
  intro p _ X D pos Kc _ _ ι j hN ν hν Q hQ Gc G hR hG s hs
  apply sub_eq_zero.mp
  apply GlobalTheory.T.symbolFramePolynomial_eq_zero_of_generic_vanish X D pos Kc ι j hN
  intro d f' hf hdf
  have hZ : ι (∏ τ, (zT X D pos f' τ).det ^ eT X D pos (j + 1) τ) ≠ 0 := by
    rw [map_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun τ _ => zpow_ne_zero _ (det_zT_ne_zero X D pos f' hf τ)
  have hL := GlobalTheory.T.operatorIdentity_leftSide_complexPoint X D pos Kc ι j hN ν hν Q hQ Gc G hR hG d f' hf hdf
  have hRr := GlobalTheory.T.transportedPolynomial_complexPoint_evaluation X D pos Kc ι j hN ν hν Q hQ s hs d f' hf
  have hc : evD X D pos ι hN d f' (cD X Kc j (ι (cOp X D pos j s))) = ι (cOp X D pos j s) := by
    simp [evD, cD]
  have hS : (∏ τ, s τ ^ (-(szT X D pos j τ))) * ∏ τ, s τ ^ szT X D pos j τ = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun τ _ => by rw [zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ (hs τ))]
  rw [map_sub, sub_eq_zero]
  apply mul_right_cancel₀ hZ
  rw [hL, (evD X D pos ι hN d f').map_mul (denD X Kc j), (evD X D pos ι hN d f').map_mul (cD X Kc j _), hc, mul_assoc ((evD X D pos ι hN d f') (denD X Kc j)), mul_assoc (ι (cOp X D pos j s)), hRr, ← ι.map_mul]
  congr 2
  unfold cOp
  linear_combination (-(sgO X D pos j * (∏ τ, (f' τ).det ^ (-(wT X D pos j τ))) * GL3Theta.evFr D Q (dfr X D hN d f'))) * hS

end GlobalTheory.TwV.DelA
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetTwistedFrameOperatorIdentityDenominatorStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detTwistedFrame_operatorIdentity_denominator : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → ∀ (Q : MvPolynomial (GL3Theta.FrV D (D.R.N j)) ℂ), Q ∈ WtPol ℂ ν → ∀ (Gc : XR (X.Pj j) ℂ) (G : (X.Pj j).Xsp), Realises X D pos j (rkS X D hN) (wT X D pos j) Q Gc → MvPolynomial.map (algebraMap X.G.Kf Kc) G = MvPolynomial.map ι Gc → ∀ (s : D.what₂.Tau → ℂ), (∀ τ, s τ ≠ 0) → subD X Kc j G * numD X Kc j = denD X Kc j * (cD X Kc j (ι (cOp X D pos j s)) * trDY X Kc j D (eIdx X D pos j hN) (phi0 X D pos ι j) (polDY D s Q (N' := D.R.N (j + 1)))) := by
  first | exact @GlobalTheory.TwV.DelA.opId_denom | exact GlobalTheory.TwV.DelA.opId_denom | (intros; apply GlobalTheory.TwV.DelA.opId_denom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorPolynomialOfRealisingValue
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem trDY_smul {p : ℕ} [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (j : ℕ) (D : D7)
    {N N' : ℕ} {ι : ℂ →+* Kc} (e : GL3Theta.Idx D N N' → X.ZA j)
    (Φ₀ : MvPolynomial (GL3Theta.FrV D N') ℂ →ₛₗ[ι] XspC (X.Pj (j + 1)) Kc)
    (R : MvPolynomial (GL3Theta.Idx D N N') (MvPolynomial (GL3Theta.FrV D N') ℂ)) (r : ℂ) :
    trDY X Kc j D e Φ₀ (r • R) = ι r • trDY X Kc j D e Φ₀ R := by
  unfold trDY
  rw [Finset.smul_sum, Finset.sum_subset MvPolynomial.support_smul]
  · refine Finset.sum_congr rfl fun α _ => ?_
    rw [MvPolynomial.coeff_smul, LinearMap.map_smulₛₗ, MvPolynomial.smul_monomial]
  · intro α _ h
    rw [MvPolynomial.notMem_support_iff.1 h, map_zero, MvPolynomial.monomial_zero]

theorem polDY_smul (D : D7) {N N' : ℕ} (s : D.what₂.Tau → ℂ) (Q : MvPolynomial (GL3Theta.FrV D N) ℂ) (r : ℂ) :
    polDY D s (r • Q) (N' := N') = r • polDY D s Q (N' := N') := by
  unfold polDY
  exact map_smul _ r Q

theorem polDel_realises : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → ∀ (Q : MvPolynomial (GL3Theta.FrV D (D.R.N j)) ℂ), Q ∈ WtPol ℂ ν → ∀ (r : ℂ) (Gc : XR (X.Pj j) ℂ) (G : (X.Pj j).Xsp), Realises X D pos j (rkS X D hN) (wT X D pos j) (r • Q) Gc → MvPolynomial.map (algebraMap X.G.Kf Kc) G = MvPolynomial.map ι Gc → ∀ (s : D.what₂.Tau → ℂ), (∀ τ, s τ ≠ 0) → GoodG X Kc j G ∧ OddDeg X j G ∧ ∀ n, AddMonoidAlgebra.coeff (polDel X Kc j G) n = ι (r * cOp X D pos j s) • AddMonoidAlgebra.coeff (trDY X Kc j D (eIdx X D pos j hN) (phi0 X D pos ι j) (polDY D s Q (N' := D.R.N (j + 1)))) n := by
  intro p _ X D pos Kc _ _ ι j hN ν hν Q hQ r Gc G hR hG s hs
  have hQr : r • Q ∈ WtPol ℂ ν := Submodule.smul_mem _ r hQ
  have hop := GlobalTheory.T.detTwistedFrame_operatorIdentity_denominator X D pos Kc ι j hN ν hν (r • Q) hQr Gc G hR hG s hs
  refine ⟨⟨_, hop⟩, GlobalTheory.T.modelPolynomial_oddDegree_of_realisesFramePoly X D pos Kc ι j hN ν hν (r • Q) hQr Gc G hR hG, fun n => ?_⟩
  rw [polDel_eq X Kc j G _ hop, polDY_smul, trDY_smul, Formalism.L2.G.Pend.cD, RingHom.comp_apply,
    MvPolynomial.coeff_C_mul, ← Algebra.smul_def, MvPolynomial.coeff_smul, smul_smul, map_mul, mul_comm]

end GlobalTheory.TwV.DelA
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorPolynomialOfRealisingValueStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.operatorPolynomial_of_realising_value : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → ∀ (Q : MvPolynomial (GL3Theta.FrV D (D.R.N j)) ℂ), Q ∈ WtPol ℂ ν → ∀ (r : ℂ) (Gc : XR (X.Pj j) ℂ) (G : (X.Pj j).Xsp), Realises X D pos j (rkS X D hN) (wT X D pos j) (r • Q) Gc → MvPolynomial.map (algebraMap X.G.Kf Kc) G = MvPolynomial.map ι Gc → ∀ (s : D.what₂.Tau → ℂ), (∀ τ, s τ ≠ 0) → GoodG X Kc j G ∧ OddDeg X j G ∧ ∀ n, AddMonoidAlgebra.coeff (polDel X Kc j G) n = ι (r * cOp X D pos j s) • AddMonoidAlgebra.coeff (trDY X Kc j D (eIdx X D pos j hN) (phi0 X D pos ι j) (polDY D s Q (N' := D.R.N (j + 1)))) n := by
  first | exact @GlobalTheory.TwV.DelA.polDel_realises | exact GlobalTheory.TwV.DelA.polDel_realises | (intros; apply GlobalTheory.TwV.DelA.polDel_realises <;> assumption)
end

module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameTransport.InstIsModTopTens
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HbApply
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSplitPlaceHermitianFrameGLEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSplitPlaceHermitianFrameGLEmbedding
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel ValuativeRel
open scoped Pointwise

noncomputable section
namespace GlobalTheory.FrameCont
open Matrix

theorem gram_det_isUnit {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) :
    IsUnit S.gram.det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  have key : ∀ v : Fin S.rank → E, S.gram *ᵥ v = 0 → v = 0 := by
    intro v hv
    have h0 : ∑ j, v j • S.frame j = 0 := by
      apply S.nondeg.2
      intro x
      rw [← S.frame.sum_repr x]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
        RingHom.id_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun i _ => ?_
      have hi := congrFun hv i
      simp only [Matrix.mulVec, dotProduct, HSpace.gram, Pi.zero_apply] at hi
      calc _ = (starRingEnd E) (S.frame.repr x i) * ∑ j, S.hT (S.frame i) (S.frame j) * v j := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
        _ = 0 := by rw [hi, mul_zero]
    funext j
    exact Fintype.linearIndependent_iff.1 S.frame.linearIndependent v h0 j
  intro a b hab
  have := key (a - b) (by rw [Matrix.mulVec_sub, hab, sub_self])
  exact sub_eq_zero.1 this

theorem continuous_of_parts {A T m : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [TopologicalSpace T] [Fintype m] [DecidableEq m] (σ : A →+* A) (hσ : Continuous σ) (e : A)
    (J : Matrix m m A) (hJ : IsUnit J.det) (M N : T → Matrix m m A)
    (hU : ∀ t, Formalism.UG.cT σ (N t) * J * N t = J) (hNM : ∀ t, N t * M t = 1)
    (hs : ∀ t i j, (e + σ e) * (M t - 1) i j = (M t - 1) i j)
    (hM : Continuous fun t => e • M t) (hN : Continuous fun t => e • N t) : Continuous M := by
  have hc : ∀ t, σ e • M t = J⁻¹ * Formalism.UG.cT σ (e • N t) * J := by
    intro t
    have h1 : J * M t = Formalism.UG.cT σ (N t) * J := by
      calc J * M t = Formalism.UG.cT σ (N t) * J * N t * M t := by rw [hU]
        _ = Formalism.UG.cT σ (N t) * J := by rw [Matrix.mul_assoc _ (N t) (M t), hNM, Matrix.mul_one]
    have h2 : Formalism.UG.cT σ (e • N t) = σ e • Formalism.UG.cT σ (N t) := by
      ext a b; simp [Formalism.UG.cT]
    rw [h2, Matrix.mul_assoc, Matrix.smul_mul, ← h1, Matrix.mul_smul, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hJ, Matrix.one_mul]
  have hC : Continuous fun t => σ e • M t := by
    simp only [hc]
    exact (continuous_const.matrix_mul (hN.matrix_map hσ).matrix_transpose).matrix_mul continuous_const
  have hsum : M = fun t => (1 - (e + σ e) • (1 : Matrix m m A)) + (e • M t + σ e • M t) := by
    funext t
    ext i j
    have h := hs t i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at h ⊢
    linear_combination -h
  rw [hsum]
  exact continuous_const.add (hM.add hC)

theorem continuous_sigR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] (σ : E →ₐ[F] E) : Continuous (sigR R σ) := by
  have h := IsModuleTopology.continuous_of_linearMap (R := R) (LinearMap.baseChange R σ.toLinearMap)
  refine h.congr fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a y => simp [LinearMap.baseChange_tmul, sigR]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem unitary_mt {D : D7} {S : HSp D} (x : GA D S) :
    Formalism.UG.cT (cA D) (mt S x) * S.gram.map (incA D) * mt S x = S.gram.map (incA D) := (PI.FT.toHR x).2

theorem mt_inv_mul {D : D7} {S : HSp D} (x : GA D S) : mt S x⁻¹ * mt S x = 1 := by
  show (matHom S x⁻¹).val * (matHom S x).val = 1
  rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]

theorem gram_map_det_isUnit {D : D7} (S : HSp D) : IsUnit (S.gram.map (incA D)).det := by
  have h0 := (gram_det_isUnit S).map (incA D)
  rw [RingHom.map_det] at h0
  exact h0

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]

theorem e_mul_entry (β : Frame p S n) (g : GL n k) (i j : Fin S.rank) :
    p.e * mt S (β.gl g) i j = p.sec ((β.b * g.val * β.b') i j) := by
  rw [← p.sec_pr, ← β.gl_mat g]; rfl

theorem continuous_e_smul (β : Frame p S n) : Continuous fun g : GL n k => p.e • mt S (β.gl g) := by
  refine continuous_matrix fun i j => ?_
  refine (p.cont_sec.comp (((continuous_const.matrix_mul
    (Units.continuous_val (M := Matrix n n k))).matrix_mul continuous_const).matrix_elem i j)).congr
      fun g => (e_mul_entry β g i j).symm

theorem continuous_mt (β : Frame p S n) : Continuous fun g : GL n k => mt S (β.gl g) := by
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  refine continuous_of_parts (cA D) (continuous_sigR _ _) p.e (S.gram.map (incA D)) (gram_map_det_isUnit S)
    (fun g => mt S (β.gl g)) (fun g => mt S (β.gl g⁻¹)) (fun g => unitary_mt _) (fun g => ?_)
    (fun g => β.gl_supp g) (continuous_e_smul β) ((continuous_e_smul β).comp continuous_inv)
  show mt S (β.gl g⁻¹) * mt S (β.gl g) = 1
  rw [map_inv]
  exact mt_inv_mul _

theorem continuous_gl : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : Frame p S n), Continuous β.gl := by
  intro D k _ _ _ _ p S n _ _ β
  refine (PI.FT.cont_HA_iff (AF D.host.F) (fun g : GL n k => β.gl g)).2 ⟨continuous_mt β, ?_⟩
  have h := (continuous_mt β).comp (continuous_inv (G := GL n k))
  refine h.congr fun g => ?_
  show mt S (β.gl g⁻¹) = PI.FT.mtI (β.gl g)
  rw [map_inv]; rfl

end GlobalTheory.FrameCont
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSplitPlaceHermitianFrameGLEmbeddingStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel ValuativeRel
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_splitPlaceHermitianFrame_GL_embedding : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : Frame p S n), Continuous β.gl := by
  first | exact @GlobalTheory.FrameCont.continuous_gl | exact GlobalTheory.FrameCont.continuous_gl | (intros; apply GlobalTheory.FrameCont.continuous_gl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardCharacterConductorAlmostAll
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer NumberField Filter
open IsDedekindDomain
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.Conductor

theorem exists_denominator (E : Type) [Field E] [NumberField E] :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ x : E, (∀ o : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E (x * o) = n) → ∃ o : 𝓞 E, (o : E) = N • x := by
  classical
  let b := NumberField.integralBasis E
  obtain ⟨N, hN, h⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image b.traceDual)
  refine ⟨N, hN, fun x hx => ?_⟩
  have hi : IsIntegral ℤ (N • x) := by
    rw [← b.traceDual.sum_repr x, Finset.smul_sum]
    refine IsIntegral.sum _ fun i _ => ?_
    obtain ⟨n, hn⟩ := hx (RingOfIntegers.basis E i)
    have e : b.traceDual.repr x i = (n : ℚ) := by
      rw [← hn, Module.Basis.traceDual_repr_apply, Algebra.traceForm_apply]
      simp [b]
    rw [e, Int.cast_smul_eq_zsmul, smul_comm]
    exact (h _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))).zsmul n
  exact ⟨⟨_, hi⟩, rfl⟩

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]

theorem af_ext {a b : Af F} (h : ∀ w, evalV F w a = evalV F w b) : a = b :=
  DFunLike.ext _ _ h

theorem ev_same (v : HeightOneSpectrum (𝓞 F)) : evalV F v (singleV F v 1) = 1 :=
  GlobalTheory.LatVac.evalV_singleV_same F v

theorem ev_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) : evalV F w (singleV F v 1) = 0 :=
  GlobalTheory.LatVac.evalV_singleV_ne F v w h

theorem idem_mul (v : HeightOneSpectrum (𝓞 F)) (z : Af F ⊗[F] E)
    (h : ∀ w, w ≠ v → Algebra.TensorProduct.map (evalV F w) (AlgHom.id F E) z = 0) :
    (singleV F v 1 ⊗ₜ[F] (1 : E)) * z = z := by
  classical
  let b := Module.finBasis F E
  have key : ∀ (w) (z : Af F ⊗[F] E) i,
      (Algebra.TensorProduct.basis (Fv F w) b).repr (Algebra.TensorProduct.map (evalV F w) (AlgHom.id F E) z) i =
        evalV F w ((Algebra.TensorProduct.basis (Af F) b).repr z i) := by
    intro w z i
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [Algebra.TensorProduct.basis_repr_tmul]
    | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]
  have e : (singleV F v 1 ⊗ₜ[F] (1 : E)) * z = singleV F v 1 • z := by
    rw [Algebra.smul_def]; rfl
  rw [e]
  refine (Algebra.TensorProduct.basis (Af F) b).ext_elem fun i => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
  refine af_ext fun w => ?_
  rw [map_mul]
  by_cases hw : w = v
  · subst hw; rw [ev_same, one_mul]
  · rw [ev_ne hw, zero_mul, ← key, h w hw, map_zero, Finsupp.zero_apply]

theorem idem_mul_mem {v : HeightOneSpectrum (𝓞 F)} {α : Af F} (h : evalV F v α ∈ v.adicCompletionIntegers F) :
    singleV F v 1 * α ∈ intAf F := fun w => by
  rw [map_mul]
  by_cases hw : w = v
  · subst hw; rwa [ev_same, one_mul]
  · rw [ev_ne hw, zero_mul]; exact zero_mem _

theorem tmul_denominator {A : Type} [CommRing A] [Algebra F A] (a : A) {N : ℤ} (hN : N ≠ 0) (x : E) :
    (a ⊗ₜ[F] (1 : E)) * (1 ⊗ₜ[F] x) = (a * algebraMap F A (N : F)⁻¹) ⊗ₜ[F] (N • x) := by
  have hN' : (N : F) ≠ 0 := Int.cast_ne_zero.2 hN
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, mul_comm, ← Algebra.smul_def, TensorProduct.smul_tmul,
    ← Int.cast_smul_eq_zsmul F, smul_smul, inv_mul_cancel₀ hN', one_smul]

theorem trace_map {A B : Type} [CommRing A] [Algebra F A] [CommRing B] [Algebra F B] (f : A →ₐ[F] B) (z : A ⊗[F] E) :
    Algebra.trace B (B ⊗[F] E) (Algebra.TensorProduct.map f (AlgHom.id F E) z) = f (Algebra.trace A (A ⊗[F] E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a e =>
    rw [Algebra.TensorProduct.map_tmul, GlobalTheory.LatVac.trace_tmul, GlobalTheory.LatVac.trace_tmul, map_mul, AlgHom.commutes]; rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

end General

variable {D : D7}

theorem trace_parts (s : AE D) : Algebra.trace (AF D.host.F) (AE D) s =
    pairA D.host.F (Algebra.trace (Ainf D.host.F) _ (infPart D s)) (Algebra.trace (Af D.host.F) _ (finPart D s)) :=
  Prod.ext (trace_map (fstA D.host.F) s).symm (trace_map (sndA D.host.F) s).symm

def chi (ψ : AddChar (AF D.host.F) ℂ) (z : Af D.host.F ⊗[D.host.F] D.host.E) : ℂ :=
  ψ (pairA D.host.F 0 (Algebra.trace (Af D.host.F) _ z))

theorem chi_add (ψ : AddChar (AF D.host.F) ℂ) (x y : Af D.host.F ⊗[D.host.F] D.host.E) :
    chi ψ (x + y) = chi ψ x * chi ψ y := by
  rw [chi, map_add (f := _), GlobalTheory.LatVac.pair_add, ψ.map_add_eq_mul]; rfl

theorem chi_zero (ψ : AddChar (AF D.host.F) ℂ) : chi ψ 0 = 1 := by
  rw [chi, map_zero]; exact ψ.map_zero_eq_one

theorem psiE_eq_chi (ψ : AddChar (AF D.host.F) ℂ) {s : AE D} (h : infPart D s = 0) : psiE ψ s = chi ψ (finPart D s) := by
  rw [psiE, trace_parts, h, map_zero]; rfl

theorem chi_rat {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (x : D.host.E) :
    chi ψ (1 ⊗ₜ[D.host.F] x) = 1 ↔ ∃ n : ℤ, Algebra.trace ℚ D.host.E x = n := by
  rw [chi, GlobalTheory.LatVac.trace_tmul, one_mul, GlobalTheory.LatVac.char_rat hψ]

theorem chi_int {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {z : Af D.host.F ⊗[D.host.F] D.host.E}
    (hz : z ∈ intAE D) : chi ψ z = 1 := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, o, rfl⟩ := hw
    rw [chi, GlobalTheory.LatVac.trace_tmul]
    refine GlobalTheory.IntDense.addChar_eq_one_of_integral D.host.F ψ hψ.1.1 _ (fun a => ?_) _ hα
    rw [← smul_eq_mul, ← map_smul, GlobalTheory.LatVac.char_rat hψ]
    have hi : IsIntegral ℤ ((a : D.host.F) • (o : D.host.E)) := by
      rw [Algebra.smul_def]
      exact (a.isIntegral_coe.map (IsScalarTower.toAlgHom ℤ D.host.F D.host.E)).mul o.isIntegral_coe
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 (Algebra.isIntegral_trace (L := ℚ) hi)
    exact ⟨n, hn.symm⟩
  | zero => exact chi_zero ψ
  | add x y _ _ hx hy => rw [chi_add, hx, hy, one_mul]
  | neg x _ hx =>
    have := chi_add ψ x (-x)
    rwa [add_neg_cancel, chi_zero, hx, one_mul, eq_comm] at this

theorem tmul_mem {α : Af D.host.F} (hα : α ∈ intAf D.host.F) (o : 𝓞 D.host.E) :
    α ⊗ₜ[D.host.F] (o : D.host.E) ∈ intAE D :=
  AddSubgroup.subset_closure ⟨α, hα, o, rfl⟩

theorem mul_mem_int {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  induction hx using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, o, rfl⟩ := hw
    induction hy using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨β, hβ, o', rfl⟩ := hw
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact tmul_mem (GlobalTheory.LatVac.mul_mem_intAf hα hβ) (o * o')
    | zero => rw [mul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | neg x _ hx => rw [mul_neg]; exact neg_mem hx
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx

theorem approx (z : Af D.host.F ⊗[D.host.F] D.host.E) :
    ∃ x : D.host.E, ∃ u ∈ intAE D, z = 1 ⊗ₜ[D.host.F] x + u := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, zero_mem _, by simp⟩
  | add x y hx hy =>
    obtain ⟨a, u, hu, rfl⟩ := hx
    obtain ⟨b, u', hu', rfl⟩ := hy
    exact ⟨a + b, u + u', add_mem hu hu', by rw [TensorProduct.tmul_add, add_add_add_comm]⟩
  | tmul a x =>
    obtain ⟨N, hN, h⟩ := exists_integral_multiples ℤ ℚ ({x} : Finset D.host.E)
    have hi : IsIntegral ℤ (N.natAbs • x) := by
      have := h x (Finset.mem_singleton_self x)
      rcases Int.natAbs_eq N with e | e
      · rwa [e, natCast_zsmul] at this
      · rw [e, neg_smul, natCast_zsmul] at this
        simpa using this.neg
    obtain ⟨a0, β, hβ, hab⟩ :=
      (GlobalTheory.AdLat.strong_approximation_mod_nat D.host.F N.natAbs (Int.natAbs_pos.2 hN)).1 a
    refine ⟨a0 • x, _, tmul_mem (α := β) hβ ⟨_, hi⟩, ?_⟩
    rw [hab]
    exact GlobalTheory.LatVac.approx_tmul a0 _ β x

theorem lift_mem (v : Pl D) (o : 𝓞 D.host.E) :
    pairA D.host.F 0 (singleV D.host.F v 1) ⊗ₜ[D.host.F] (o : D.host.E) ∈ intAt D (· = v) := by
  refine ⟨⟨GlobalTheory.LatVac.infPart_pair _ _, ?_⟩, ?_⟩
  · refine (Submodule.mem_iInf _).2 fun w => ?_
    have : compAt D w.1 (pairA D.host.F 0 (singleV D.host.F v 1) ⊗ₜ[D.host.F] (o : D.host.E)) =
        evalV D.host.F w.1 (singleV D.host.F v 1) ⊗ₜ[D.host.F] (o : D.host.E) := rfl
    rw [RingHom.mem_ker, this, ev_ne w.2, TensorProduct.zero_tmul]
  · rw [GlobalTheory.LatVac.finPart_pair]
    have := idem_mul_mem (v := v) (α := 1) (by rw [map_one]; exact one_mem _)
    rw [mul_one] at this
    exact tmul_mem this o

theorem eventually_conductor : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ᶠ v : Pl D in cofinite, ∀ s ∈ idAt D (· = v),
      (∀ o ∈ intAt D (· = v), psiE ψ (s * o) = 1) ↔ s ∈ intAt D (· = v) := by
  intro D ψ hψ
  obtain ⟨N, hN, hden⟩ := exists_denominator D.host.E
  have hev : ∀ᶠ v : Pl D in cofinite,
      evalV D.host.F v (algebraMap D.host.F (Af D.host.F) (N : D.host.F)⁻¹) ∈ v.adicCompletionIntegers D.host.F :=
    (algebraMap D.host.F (Af D.host.F) (N : D.host.F)⁻¹).2
  filter_upwards [hev] with v hv s hs
  have hinf : ∀ o, infPart D (s * o) = 0 := fun o => by
    have : infPart D s = 0 := hs.1
    rw [RingHom.map_mul, this, zero_mul]
  refine ⟨fun h => ⟨hs, ?_⟩, fun h o ho => ?_⟩
  · have hz : (singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * finPart D s = finPart D s :=
      idem_mul v _ fun w hw => (Submodule.mem_iInf _).1 hs.2 ⟨w, hw⟩
    obtain ⟨x, u, hu, e⟩ := approx (finPart D s)
    have hε : singleV D.host.F v 1 ∈ intAf D.host.F := by
      have := idem_mul_mem (v := v) (α := 1) (by rw [map_one]; exact one_mem _)
      rwa [mul_one] at this
    obtain ⟨y, hy⟩ := hden x fun o => by
      have h1 := h _ (lift_mem v o)
      have e1 : singleV D.host.F v 1 ⊗ₜ[D.host.F] (o : D.host.E) =
          (singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * (1 ⊗ₜ[D.host.F] (o : D.host.E)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [psiE_eq_chi ψ (hinf _), RingHom.map_mul, GlobalTheory.LatVac.finPart_pair, e1, ← mul_assoc, mul_comm (finPart D s), hz, e,
        add_mul, chi_add, chi_int hψ (mul_mem_int hu (tmul_mem (GlobalTheory.LatVac.one_mem_intAf _) o)), mul_one,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one] at h1
      exact (chi_rat hψ _).1 h1
    rw [← hz, e, mul_add]
    refine add_mem ?_ (mul_mem_int (tmul_mem hε 1) hu)
    rw [tmul_denominator _ hN, ← hy]
    exact tmul_mem (idem_mul_mem hv) y
  · rw [psiE_eq_chi ψ (hinf _), RingHom.map_mul]
    exact chi_int hψ (mul_mem_int h.2 ho.2)

end GlobalTheory.FinPl.Conductor
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiActionsMatchThroughLinkMap
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiActionsMatchThroughLinkMap
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf.LinkPoint

variable {D : D7}

theorem gram_zEll (T : HSp D) (ρ : ℕ) (z : Fin T.rank → D.host.E) :
    adj (zEll T ρ z) ⬝ (gA T ⬝ zEll T ρ z) =
      incA D (star z ⬝ᵥ T.gram *ᵥ z) • vecMulVec (fun i => cA D (ell D ρ i)) (ell D ρ) := by
  have h1 : adj (zEll T ρ z) = vecMulVec (fun i => cA D (ell D ρ i)) (ratV (star z)) := by
    funext i j
    change cA D (incA D (z j) * ell D ρ i) = cA D (ell D ρ i) * incA D (star (z j))
    rw [map_mul, GlobalTheory.DualPairCheck.cA_incA, mul_comm]
  have h2 : ratV (star z) ⬝ᵥ ratV (T.gram *ᵥ z) = incA D (star z ⬝ᵥ T.gram *ᵥ z) :=
    (RingHom.map_dotProduct (incA D) _ _).symm
  rw [h1, zEll, Matrix.mul_vecMulVec, gA, ← ratV_mulVec, Matrix.vecMulVec_mul_vecMulVec, h2, Matrix.vecMulVec_smul]

variable {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ)

theorem gA_jY : gA W ⬝ d.jY = adj d.pX := by rw [d.pX_eq, adj_mul, adj_adj, adj_gA]

theorem ptT_eq (L : HSp D) (y : Mx D L.rank ρ) (n : GA D W) :
    ptT d L y n = GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L W₀ (y ⬝ (d.pX ⬝ (mt W n ⬝ d.j0))) := by
  rw [ptT, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj, d.incAdj_apply, d.incY_apply, mt_inv, d.p0_eq]
  rw [adj_mul, adj_mul, adj_mul, ← gA_jY, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul]
  simp only [Matrix.mul_assoc]
  rw [gA_giA_cancel]

theorem trace_inverseGram_conj_smul_eq {R : Type} [CommRing R] {m k : ℕ} (s t : R) (G G' : Matrix (Fin m) (Fin m) R) (hG : G' * G = 1)
    (y : Matrix (Fin m) (Fin k) R) (y' : Matrix (Fin k) (Fin m) R) (M : Matrix (Fin k) (Fin k) R) :
    (G' * ((t • (G * y)) * (M * (s • (y' * G))))).trace = (((t * s) • (y' * (G * y))) * M).trace := by
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc G,
    ← Matrix.mul_assoc G', hG, Matrix.one_mul, Matrix.smul_mul, trace_smul, trace_smul, trace_mul_comm,
    Matrix.mul_assoc M, trace_mul_comm M, Matrix.mul_assoc y' G]

theorem hO_jY (L : HSp D) (n : GA D W) (η : Mx D ρ L.rank) : hO L W (d.jY ⬝ η) (mt W n⁻¹ ⬝ (d.jY ⬝ η)) =
    (giA L ⬝ (adj η ⬝ ((d.pX ⬝ (mt W n ⬝ d.jY)) ⬝ η))).trace := by
  rw [hO_eq_trace, mt_inv, d.pX_eq, adj_mul, adj_mul, adj_mul, adj_mul, adj_adj, adj_gA, adj_giA]
  simp only [Matrix.mul_assoc]
  rw [giA_gA_cancel]

theorem cenT_eq (L : HSp D) (y : Mx D L.rank ρ) (n : GA D W) :
    cenT d L y n = trHalf D ((incA D (D.host.xi0 * star D.host.xi0)⁻¹ •
      (adj y ⬝ (gA L ⬝ y)) ⬝ (d.pX ⬝ (mt W n ⬝ d.jY))).trace) := by
  have hs : cA D (incA D (-D.host.xi0⁻¹)) * incA D (-D.host.xi0⁻¹) = incA D (D.host.xi0 * star D.host.xi0)⁻¹ := by
    rw [GlobalTheory.DualPairCheck.cA_incA, ← map_mul, star_neg, star_inv₀, neg_mul_neg, _root_.mul_inv_rev]
  rw [cenT, symplOH_eq, d.incAdj_apply, d.incY_apply, hO_jY, ← hs, adj_smul, adj_mul, adj_adj, adj_gA]
  exact congrArg _ (trace_inverseGram_conj_smul_eq _ _ _ _ (giA_mul_gA L) _ _ _)

theorem neg_cenS_eq (T : HSp D) (x : Mx D T.rank ρ) (n : GA D W) :
    -cenS d T x n = trHalf D (((adj x ⬝ (gA T ⬝ x)) ⬝ (d.pX ⬝ (mt W n ⬝ d.jY))).trace) := by
  rw [cenS, ← symplOH_skew, symplOH_eq, hO_eq_trace, d.extX_apply, adj_mul, ← gA_jY, Matrix.mul_assoc, Matrix.mul_assoc,
    giA_gA_cancel, trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem link_point (D : D7) (ρ σ : ℕ) (B : BesLev D σ) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E) (_ : IsLineVec L' ζ')
    (l : Link B L' ζ') (W W₀ : HSp D) (d : HypDec W W₀ ρ) (n : GA D W) (_ : n ∈ flagN d) :
    l.κ W₀ (ptS d L' (zEll L' ρ ζ') n) = ptT d B.L (yZero B.L ρ B.ζ) n ∧
      cenT d B.L (yZero B.L ρ B.ζ) n = -cenS d L' (zEll L' ρ ζ') n := by
  constructor
  · have h : (rat l.τ : Mx D B.L.rank L'.rank) ⬝ zEll L' ρ ζ' = yZero B.L ρ B.ζ := by
      have h0 : ratV (-B.ζ) = -ratV B.ζ := funext fun i => map_neg (incA D) _
      rw [yZero, zEll, zEll, Matrix.mul_vecMulVec, ← ratV_mulVec, l.map, h0, Matrix.neg_vecMulVec]
    rw [ptT_eq, Link.κ, ptS, d.extX_apply, ← h]
    simp only [Matrix.mul_assoc]
  · have hN : D.host.xi0 * star D.host.xi0 ≠ 0 :=
      mul_ne_zero (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D) (star_ne_zero.2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D))
    rw [cenT_eq, neg_cenS_eq, yZero, adj_neg, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg, gram_zEll, gram_zEll,
      smul_smul, ← map_mul, l.norm, inv_mul_cancel_left₀ hN]

end GlobalTheory.Unf.LinkPoint

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiActionsMatchThroughLinkMapStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacobiActions_match_through_linkMap : ∀ (D : D7) (ρ σ : ℕ) (B : BesLev D σ) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E), IsLineVec L' ζ' → ∀ (l : Link B L' ζ') (W W₀ : HSp D) (d : HypDec W W₀ ρ), ∀ n ∈ flagN d, l.κ W₀ (ptS d L' (zEll L' ρ ζ') n) = ptT d B.L (yZero B.L ρ B.ζ) n ∧ cenT d B.L (yZero B.L ρ B.ζ) n = -cenS d L' (zEll L' ρ ζ') n := by
  first | exact @GlobalTheory.Unf.LinkPoint.link_point | exact GlobalTheory.Unf.LinkPoint.link_point | (intros; apply GlobalTheory.Unf.LinkPoint.link_point <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TendstoUnitaryAdelicPointsAgreeOnGrowingFinset
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TendstoUnitaryAdelicPointsAgreeOnGrowingFinset
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open Filter Topology IsDedekindDomain NumberField
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.AdelicLimit

section Basis

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]


set_option maxHeartbeats 800000 in
theorem repr_map {R R' : Type} [CommRing R] [CommRing R'] [Algebra F R] [Algebra F R'] (α : R →ₐ[F] R')
    (z : R ⊗[F] E) (k : Fin (Module.finrank F E)) :
    (Algebra.TensorProduct.basis R' (Module.finBasis F E)).repr (Algebra.TensorProduct.map α (AlgHom.id F E) z) k =
      α ((Algebra.TensorProduct.basis R (Module.finBasis F E)).repr z k) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.basis_repr_tmul]
    simp [Finsupp.smul_apply, Finsupp.mapRange_apply, map_mul, AlgHom.commutes]
  | add x y hx hy =>
    simp only [map_add (f := _), Finsupp.add_apply, hx, hy]

end Basis

section Fin

variable {F : Type} [Field F] [NumberField F]

theorem tendsto_finAdele (f : Finset (HeightOneSpectrum (𝓞 F)) → FiniteAdeleRing (𝓞 F) F)
    (y g : FiniteAdeleRing (𝓞 F) F) (hin : ∀ T, ∀ v ∈ T, f T v = y v) (hout : ∀ T, ∀ v, v ∉ T → f T v = g v) :
    Tendsto f atTop (𝓝 y) := by
  classical
  let S : Set (HeightOneSpectrum (𝓞 F)) :=
    {v | y v ∈ v.adicCompletionIntegers F ∧ g v ∈ v.adicCompletionIntegers F}
  have hle : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 F))) ≤ Filter.principal S := by
    rw [Filter.le_principal_iff]; exact y.2.and g.2
  let P := RestrictedProduct (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
      (fun w => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) (Filter.principal S)
  let f' : Finset (HeightOneSpectrum (𝓞 F)) → P := fun T => ⟨fun v => f T v, by
    rw [Filter.eventually_principal]
    intro w hw
    show f T w ∈ (w.adicCompletionIntegers F : Set (w.adicCompletion F))
    by_cases h : w ∈ T
    · rw [hin T w h]; exact hw.1
    · rw [hout T w h]; exact hw.2⟩
  let y' : P := ⟨fun v => y v, by rw [Filter.eventually_principal]; exact fun w hw => hw.1⟩
  have hf : Tendsto f' atTop (𝓝 y') := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.tendsto_nhds_iff, tendsto_pi_nhds]
    intro v
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop ({v} : Finset _)] with T hT
    have : v ∈ T := hT (Finset.mem_singleton_self v)
    change y v = f T v
    rw [hin T v this]
  exact ((RestrictedProduct.continuous_inclusion hle).tendsto y').comp hf

end Fin

section Entry

variable {D : D7}

set_option maxHeartbeats 800000 in
theorem repr_infPart (z : AE D) (k : Fin (Module.finrank D.host.F D.host.E)) :
    (Algebra.TensorProduct.basis (Ainf D.host.F) (Module.finBasis D.host.F D.host.E)).repr (infPart D z) k =
      fstA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).repr z k) := by
  change (Algebra.TensorProduct.basis (Ainf D.host.F) (Module.finBasis D.host.F D.host.E)).repr
    (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) z) k = _
  rw [repr_map]

set_option maxHeartbeats 800000 in
theorem repr_compAt (w : Pl D) (z : AE D) (k : Fin (Module.finrank D.host.F D.host.E)) :
    (Algebra.TensorProduct.basis (Fv D.host.F w) (Module.finBasis D.host.F D.host.E)).repr (compAt D w z) k =
      evalV D.host.F w (sndA D.host.F
        ((Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).repr z k)) := by
  change (Algebra.TensorProduct.basis (Fv D.host.F w) (Module.finBasis D.host.F D.host.E)).repr
    (Algebra.TensorProduct.map (evalV D.host.F w) (AlgHom.id D.host.F D.host.E)
      (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) z)) k = _
  rw [repr_map, repr_map]


set_option maxHeartbeats 800000 in
theorem tendsto_entry (a : Finset (Pl D) → AE D) (b c : AE D) (hinf : ∀ T, infPart D (a T) = infPart D b)
    (hin : ∀ T, ∀ w ∈ T, compAt D w (a T) = compAt D w b)
    (hout : ∀ T w, w ∉ T → compAt D w (a T) = compAt D w c) : Tendsto a atTop (𝓝 b) := by
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  set Bs := Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E) with hBs
  have hc : ∀ k, Tendsto (fun T => Bs.repr (a T) k) atTop (𝓝 (Bs.repr b k)) := by
    intro k
    have h1 : ∀ T, (Bs.repr (a T) k).1 = (Bs.repr b k).1 := fun T => by
      have h := congrArg (fun z => (Algebra.TensorProduct.basis (Ainf D.host.F)
        (Module.finBasis D.host.F D.host.E)).repr z k) (hinf T)
      simp only [repr_infPart] at h
      exact h
    have h2 : Tendsto (fun T => (Bs.repr (a T) k).2) atTop (𝓝 (Bs.repr b k).2) := by
      refine tendsto_finAdele _ _ (Bs.repr c k).2 (fun T w hw => ?_) (fun T w hw => ?_)
      · have h := congrArg (fun z => (Algebra.TensorProduct.basis (Fv D.host.F w)
          (Module.finBasis D.host.F D.host.E)).repr z k) (hin T w hw)
        simp only [repr_compAt] at h
        exact h
      · have h := congrArg (fun z => (Algebra.TensorProduct.basis (Fv D.host.F w)
          (Module.finBasis D.host.F D.host.E)).repr z k) (hout T w hw)
        simp only [repr_compAt] at h
        exact h
    have h3 := (tendsto_const_nhds (x := (Bs.repr b k).1)).prodMk_nhds h2
    refine h3.congr fun T => ?_
    exact Prod.ext (h1 T).symm rfl
  have := tendsto_finsetSum (Finset.univ : Finset (Fin (Module.finrank D.host.F D.host.E)))
    (fun k _ => (hc k).smul_const (Bs k))
  simpa only [Bs.sum_repr] using this

theorem map_inv_entries {A R : Type} [CommRing A] [Ring R] {n : ℕ} (φ : A →+* R) (u v : GL (Fin n) A)
    (h : ∀ i j, φ ((u : Matrix (Fin n) (Fin n) A) i j) = φ ((v : Matrix (Fin n) (Fin n) A) i j)) :
    ∀ i j, φ (((u⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) i j) =
      φ (((v⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) i j) := by
  have hM : φ.mapMatrix (u : Matrix (Fin n) (Fin n) A) = φ.mapMatrix (v : Matrix (Fin n) (Fin n) A) :=
    Matrix.ext fun i j => h i j
  have e1 : φ.mapMatrix ((u⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) * φ.mapMatrix (u : Matrix (Fin n) (Fin n) A) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have e2 : φ.mapMatrix (v : Matrix (Fin n) (Fin n) A) * φ.mapMatrix ((v⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  rw [← hM] at e2
  have e := left_inv_eq_right_inv e1 e2
  intro i j
  exact congrArg (fun M => M i j) e

end Entry


set_option maxHeartbeats 800000 in
theorem tendsto_of_agree (D : D7) (S : HSp D) (κ : GA D S) (x : Finset (Pl D) → GA D S)
    (h1 : ∀ Fs i j, infPart D (Formalism.L2.Theta.mt S (x Fs) i j) = infPart D (Formalism.L2.Theta.mt S κ i j))
    (h2 : ∀ Fs, ∀ w ∈ Fs, ∀ i j, GlobalTheory.FinPl.compAt D w (Formalism.L2.Theta.mt S (x Fs) i j) =
      GlobalTheory.FinPl.compAt D w (Formalism.L2.Theta.mt S κ i j))
    (h3 : ∀ Fs w, w ∉ Fs → ∀ i j, GlobalTheory.FinPl.compAt D w (Formalism.L2.Theta.mt S (x Fs) i j) =
      GlobalTheory.FinPl.compAt D w ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j)) :
    Filter.Tendsto x Filter.atTop (nhds κ) := by
  let u : Finset (Pl D) → GL (Fin S.rank) (AE D) := fun T => matHom S (x T)
  have hv : Tendsto (fun T => (u T).val) atTop
      (𝓝 (matHom S κ).val) :=
    tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j =>
      tendsto_entry (fun T => mt S (x T) i j) (mt S κ i j) ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j)
        (fun T => h1 T i j) (fun T w hw => h2 T w hw i j) (fun T w hw => h3 T w hw i j)
  have hi : Tendsto (fun T => ((u T)⁻¹).val) atTop
      (𝓝 ((matHom S κ)⁻¹).val) := by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    refine tendsto_entry _ _ ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j)
      (fun T => map_inv_entries (infPart D) (u T) (matHom S κ) (h1 T) i j)
      (fun T w hw => map_inv_entries (compAt D w) (u T) (matHom S κ) (h2 T w hw) i j)
      (fun T w hw => ?_)
    have h := map_inv_entries (compAt D w) (u T) 1 (fun i j => by rw [Units.val_one]; exact h3 T w hw i j) i j
    simpa using h
  have key : Tendsto u atTop (𝓝 (matHom S κ)) := by
    rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
    exact hv.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp hi)
  exact tendsto_subtype_rng.2 key

end GlobalTheory.AdelicLimit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TendstoUnitaryAdelicPointsAgreeOnGrowingFinsetStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_unitaryAdelicPoints_agree_on_growing_finset : ∀ (D : D7) (S : HSp D) (κ : GA D S) (x : Finset (Pl D) → GA D S), (∀ Fs i j, infPart D (Formalism.L2.Theta.mt S (x Fs) i j) = infPart D (Formalism.L2.Theta.mt S κ i j)) → (∀ Fs, ∀ w ∈ Fs, ∀ i j, GlobalTheory.FinPl.compAt D w (Formalism.L2.Theta.mt S (x Fs) i j) = GlobalTheory.FinPl.compAt D w (Formalism.L2.Theta.mt S κ i j)) → (∀ Fs w, w ∉ Fs → ∀ i j, GlobalTheory.FinPl.compAt D w (Formalism.L2.Theta.mt S (x Fs) i j) = GlobalTheory.FinPl.compAt D w ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j)) → Filter.Tendsto x Filter.atTop (nhds κ) := by
  first | exact @GlobalTheory.AdelicLimit.tendsto_of_agree | exact GlobalTheory.AdelicLimit.tendsto_of_agree | (intros; apply GlobalTheory.AdelicLimit.tendsto_of_agree <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdelicTraceCharacterSplitSectionNeOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdelicTraceCharacterSplitSectionNeOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl ValuativeRel NumberField
open IsDedekindDomain

namespace GlobalTheory.FinPl.CharNontriv

theorem exists_psiV_ne_one (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1))
    (v : HeightOneSpectrum (𝓞 D.host.F)) : ∃ y, ψ (pairA D.host.F 0 (singleV D.host.F v y)) ≠ 1 := by
  have h := hψ.1
  have h' : IsCharAF D.host.F ψ⁻¹ := by
    refine ⟨h.1.comp continuous_neg, fun x => h.2.1 _, fun a => ?_, ?_⟩
    · rw [AddChar.inv_apply, ← map_neg]; exact h.2.2.1 _
    · obtain ⟨x, hx⟩ := h.2.2.2
      exact ⟨-x, by rwa [AddChar.inv_apply, neg_neg]⟩
  obtain ⟨y, hy⟩ := GlobalTheory.StdCharTotReal.psiV_ne_one_of_trace h' (fun a => by
    rw [← GlobalTheory.StdRat.stdChar_fin_rat D ψ hψ, GlobalTheory.StdRat.char_fin_rat ψ h, psiInf, psiInf, AddChar.inv_apply,
      map_neg (algebraMap D.host.F (Ainf D.host.F))]
    refine congrArg ψ (Prod.ext rfl ?_)
    exact neg_zero) v
  refine ⟨y, fun h1 => hy ?_⟩
  rw [psiV, AddChar.inv_apply', h1, inv_one]

theorem algebraMap_injective (D : D7) : Function.Injective (algebraMap (AF D.host.F) (AE D)) :=
  Algebra.TensorProduct.includeLeft_injective (S := D.host.F) (algebraMap D.host.F D.host.E).injective

theorem exists_psiE_sec_ne_one : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∃ a : k, GlobalTheory.MixPer.psiE ψ (p.sec a) ≠ 1 := by
  intro D k _ _ _ _ p ψ hψ
  obtain ⟨y, hy⟩ := exists_psiV_ne_one D ψ hψ p.v
  obtain ⟨ε, ⟨α, rfl, h1, -⟩, he⟩ := p.above
  have ht : Algebra.trace (AF D.host.F) (AE D) p.e = pairA D.host.F 0 α :=
    algebraMap_injective D ((GlobalTheory.FockCompare.SymplVal.trace_AE D p.e).trans he)
  refine ⟨p.pr (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F p.v y))), ?_⟩
  rw [p.sec_pr, GlobalTheory.MixPer.psiE, mul_comm, ← Algebra.smul_def, map_smul, ht, smul_eq_mul]
  have h2 : pairA D.host.F 0 (singleV D.host.F p.v y) * pairA D.host.F 0 α =
      pairA D.host.F 0 (singleV D.host.F p.v y) := by
    refine Prod.ext (zero_mul _) ?_
    show singleV D.host.F p.v y * α = singleV D.host.F p.v y
    have h3 : α p.v = 1 := h1
    rw [GlobalTheory.StdCharTotReal.single_mul, h3, mul_one]
  rwa [h2]

end GlobalTheory.FinPl.CharNontriv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdelicTraceCharacterSplitSectionNeOneStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl ValuativeRel NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelicTraceCharacter_splitSection_ne_one : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∃ a : k, GlobalTheory.MixPer.psiE ψ (p.sec a) ≠ 1 := by
  first | exact @GlobalTheory.FinPl.CharNontriv.exists_psiE_sec_ne_one | exact GlobalTheory.FinPl.CharNontriv.exists_psiE_sec_ne_one | (intros; apply GlobalTheory.FinPl.CharNontriv.exists_psiE_sec_ne_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedCharacterDetLatticeStabilizerEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedCharacterDetLatticeStabilizerEqOne
open GlobalTheory.FinPl GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing Matrix
open scoped Pointwise

namespace GlobalTheory.LatPair.Det

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]

theorem det_mem_of_mem_latStab_std {g : GL n k} (hg : g ∈ latStab (stdLat k n)) : g.val.det ∈ 𝒪[k] := by
  rw [MulAction.mem_stabilizer_iff] at hg
  have t2 : ∀ v : n → k, v ∈ stdLat k n ↔ ∀ i, v i ∈ 𝒪[k] := by
    intro v
    simp only [stdLat, LinearMap.mem_range]
    constructor
    · rintro ⟨y, rfl⟩ i
      exact (y i).2
    · intro h
      exact ⟨fun i => ⟨v i, h i⟩, rfl⟩
  have hent : ∀ i j, (g : Matrix n n k) i j ∈ 𝒪[k] := by
    intro i j
    have hs : Pi.single j (1 : k) ∈ stdLat k n := by
      rw [t2]
      intro i'
      by_cases h : i' = j
      · subst h
        simp only [Pi.single_eq_same]
        exact one_mem _
      · simp only [Pi.single_eq_of_ne h]
        exact zero_mem _
    have h1 : g • Pi.single j (1 : k) ∈ stdLat k n := by
      rw [← hg]
      exact Submodule.smul_mem_pointwise_smul _ _ _ hs
    rw [t2] at h1
    have h2 := h1 i
    change ((g : Matrix n n k) *ᵥ Pi.single j 1) i ∈ 𝒪[k] at h2
    simpa [Matrix.mulVec_single] using h2
  let A : Matrix n n 𝒪[k] := Matrix.of fun i j => ⟨(g : Matrix n n k) i j, hent i j⟩
  have hA : (algebraMap 𝒪[k] k).mapMatrix A = (g : Matrix n n k) := by
    ext i j
    rfl
  rw [← hA, ← RingHom.map_det]
  exact (A.det).2

theorem exists_smul_stdLat_eq (L : Submodule 𝒪[k] (n → k)) [L.IsFullLattice k] : ∃ h : GL n k, h • stdLat k n = L := by
  classical
  letI : Module.Free 𝒪[k] L := Submodule.IsLattice.free k L
  letI : Module.Finite 𝒪[k] L := Submodule.IsLattice.finite k L
  let b := Module.Free.chooseBasis 𝒪[k] L
  let B := b.extendOfIsFullLattice k
  have hc : Fintype.card (Module.Free.ChooseBasisIndex 𝒪[k] L) = Fintype.card n := by
    have := Module.finrank_eq_card_basis B
    simpa using this.symm
  let e := Fintype.equivOfCardEq hc
  let B' := B.reindex e
  let P := (Pi.basisFun k n).toMatrix B'
  let Q := B'.toMatrix (Pi.basisFun k n)
  let h : GL n k := ⟨P, Q, Module.Basis.toMatrix_mul_toMatrix_flip _ _, Module.Basis.toMatrix_mul_toMatrix_flip _ _⟩
  have hB' : ∀ j, B' j = (b (e.symm j) : n → k) := by
    intro j
    simp [B', B]
  have key : ∀ y : n → k, h • y = ∑ j, y j • B' j := by
    intro y
    change P *ᵥ y = _
    ext i
    simp [P, Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply, Finset.sum_apply, mul_comm]
  refine ⟨h, ?_⟩
  ext x
  simp only [HSMul.hSMul, SMul.smul]
  rw [Submodule.mem_map]
  simp only [DistribSMul.toLinearMap_apply]
  change (∃ y ∈ stdLat k n, h • y = x) ↔ x ∈ L
  simp only [key]
  constructor
  · rintro ⟨y, ⟨c, rfl⟩, rfl⟩
    refine L.sum_mem fun j _ => ?_
    rw [hB']
    change algebraMap 𝒪[k] k (c j) • (b (e.symm j) : n → k) ∈ L
    rw [algebraMap_smul]
    exact L.smul_mem (c j) (b (e.symm j)).2
  · intro hx
    let c := b.repr ⟨x, hx⟩
    refine ⟨fun j => (c (e.symm j) : k), ⟨fun j => c (e.symm j), rfl⟩, ?_⟩
    simp_rw [hB']
    have hsum := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at hsum
    rw [Equiv.sum_comp e.symm (fun i => ((c i : 𝒪[k]) : k) • (b i : n → k))]
    rw [← hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact algebraMap_smul k (c i) _

theorem det_mem_of_mem_latStab {L : Submodule 𝒪[k] (n → k)} [L.IsFullLattice k] {g : GL n k} (hg : g ∈ latStab L) :
    ((Matrix.GeneralLinearGroup.det g : kˣ) : k) ∈ 𝒪[k] := by
  obtain ⟨h, rfl⟩ := exists_smul_stdLat_eq L
  have hs : h⁻¹ * g * h ∈ latStab (stdLat k n) := by
    simp only [latStab, MulAction.mem_stabilizer_iff] at hg ⊢
    rw [mul_smul, mul_smul, hg, inv_smul_smul]
  have h1 := det_mem_of_mem_latStab_std hs
  rw [← Matrix.GeneralLinearGroup.val_det_apply] at h1
  have hdet : Matrix.GeneralLinearGroup.det (h⁻¹ * g * h) = Matrix.GeneralLinearGroup.det g := by
    rw [map_mul, map_mul, map_inv, mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]
  rwa [hdet] at h1

theorem valuation_det_of_mem_latStab {L : Submodule 𝒪[k] (n → k)} [L.IsFullLattice k] {g : GL n k} (hg : g ∈ latStab L) :
    valuation k ((Matrix.GeneralLinearGroup.det g : kˣ) : k) = 1 := by
  have h1 := det_mem_of_mem_latStab hg
  have h2 := det_mem_of_mem_latStab (inv_mem hg)
  rw [map_inv, Units.val_inv_eq_inv_val] at h2
  set d : k := ((Matrix.GeneralLinearGroup.det g : kˣ) : k) with hd
  have hd0 : d ≠ 0 := Units.ne_zero _
  have hu : IsUnit (⟨d, h1⟩ : 𝒪[k]) :=
    ⟨⟨⟨d, h1⟩, ⟨d⁻¹, h2⟩, Subtype.ext (mul_inv_cancel₀ hd0), Subtype.ext (inv_mul_cancel₀ hd0)⟩, rfl⟩
  exact ((Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one).1 hu

end

theorem isUnram_det_latStab : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (L : Submodule 𝒪[k] (n → k)), L.IsFullLattice k → ∀ g ∈ latStab L, ∀ μ : kˣ →* ℂˣ, IsUnram μ → μ (Matrix.GeneralLinearGroup.det g) = 1 := by
  intro k _ _ _ _ n _ _ L hL g hg μ hμ
  exact hμ _ (valuation_det_of_mem_latStab hg)

end GlobalTheory.LatPair.Det
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedCharacterDetLatticeStabilizerEqOneStatement
open GlobalTheory.FinPl GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedCharacter_det_latticeStabilizer_eq_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (L : Submodule 𝒪[k] (n → k)), L.IsFullLattice k → ∀ g ∈ latStab L, ∀ μ : kˣ →* ℂˣ, IsUnram μ → μ (Matrix.GeneralLinearGroup.det g) = 1 := by
  exact @_root_.GlobalTheory.LatPair.Det.isUnram_det_latStab
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeDeterminesSphericalHeckeCharacterGL
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeDeterminesSphericalHeckeCharacterGL
noncomputable section

namespace GlobalTheory.ChainOnto.SatHeckeChar

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun

theorem heckeVec_eq_smul_of_isSatVecGL :
    ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (B : Multiset ℂˣ),
      ∀ φ ∈ Hecke ℂ (KGL w (n := n)), ∃ z : ℂ, ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
        (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (x : V),
          IsSatVecGL w ρ x B → heckeVec ρ (KGL w (n := n)) φ x = z • x := by
  intro E _ _ w n B φ hφ
  by_cases hB : B.card = n
  · obtain ⟨α, rfl⟩ : ∃ α : Fin n → ℂˣ, Finset.univ.val.map α = B := by
      obtain ⟨l, rfl⟩ := Quot.exists_rep B
      obtain rfl : l.length = n := hB
      exact ⟨l.get, by rw [Fin.univ_val_map, List.ofFn_get]; rfl⟩
    obtain ⟨x₀, hx₀⟩ := (hasSatGL_psFunGL (w := w) α).exists_vec
    obtain ⟨z, hz, -⟩ := SatCompare.exists_eigenvalue_GL hx₀ hx₀ φ hφ
    refine ⟨z, fun V _ _ ρ x hx => ?_⟩
    obtain ⟨c, e1, e2⟩ := SatCompare.exists_eigenvalue_GL hx₀ hx φ hφ
    have e : z = c := smul_left_injective ℂ hx₀.1 (hz.symm.trans e1)
    rw [e2, e]
  · exact ⟨0, fun V _ _ ρ x hx => absurd hx.2.2.1 hB⟩

end GlobalTheory.ChainOnto.SatHeckeChar

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeDeterminesSphericalHeckeCharacterGLStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.satake_determines_sphericalHeckeCharacter_GL : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (B : Multiset ℂˣ), ∀ φ ∈ Hecke ℂ (KGL w (n := n)), ∃ z : ℂ, ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (x : V), IsSatVecGL w ρ x B → heckeVec ρ (KGL w (n := n)) φ x = z • x := by
  first | exact @GlobalTheory.ChainOnto.SatHeckeChar.heckeVec_eq_smul_of_isSatVecGL | exact GlobalTheory.ChainOnto.SatHeckeChar.heckeVec_eq_smul_of_isSatVecGL | (intros; apply GlobalTheory.ChainOnto.SatHeckeChar.heckeVec_eq_smul_of_isSatVecGL <;> assumption)
end
end

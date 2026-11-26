module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTransportGroupsCuspFormsWeilDataIsometry
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormInfIsometryConjLeConstMul
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormInfIsometryConjLeConstMul
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix Formalism.IndefR.Datum
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Isom

theorem sum_norm_conj_le {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℂ) (A : Matrix (Fin n) (Fin n) ℂ)
    (Q : Matrix (Fin n) (Fin m) ℂ) :
    ∑ i, ∑ j, ‖(P * A * Q) i j‖ ≤
      ((m : ℝ) * m * (∑ i, ∑ k, ‖P i k‖) * (∑ l, ∑ j, ‖Q l j‖)) * ∑ k, ∑ l, ‖A k l‖ := by
  set cP := ∑ i, ∑ k, ‖P i k‖
  set cQ := ∑ l, ∑ j, ‖Q l j‖
  set S := ∑ k, ∑ l, ‖A k l‖
  have hP : ∀ i k, ‖P i k‖ ≤ cP := fun i k =>
    (Finset.single_le_sum (f := fun k => ‖P i k‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ k)).trans
      (Finset.single_le_sum (f := fun i => ∑ k, ‖P i k‖) (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
        (Finset.mem_univ i))
  have hQ : ∀ l j, ‖Q l j‖ ≤ cQ := fun l j =>
    (Finset.single_le_sum (f := fun j => ‖Q l j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun l => ∑ j, ‖Q l j‖) (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
        (Finset.mem_univ l))
  have hcP : 0 ≤ cP := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hcQ : 0 ≤ cQ := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hent : ∀ i j, ‖(P * A * Q) i j‖ ≤ cP * cQ * S := by
    intro i j
    have e : (P * A * Q) i j = ∑ l, ∑ k, P i k * A k l * Q l j := by
      simp only [Matrix.mul_apply, Finset.sum_mul]
    rw [e]
    calc ‖∑ l, ∑ k, P i k * A k l * Q l j‖ ≤ ∑ l, ∑ k, ‖P i k‖ * ‖A k l‖ * ‖Q l j‖ := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => (norm_sum_le _ _).trans (le_of_eq ?_))
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [norm_mul, norm_mul]
      _ ≤ ∑ l, ∑ k, cP * ‖A k l‖ * cQ := by
          refine Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun k _ => ?_
          exact mul_le_mul (mul_le_mul_of_nonneg_right (hP i k) (norm_nonneg _)) (hQ l j) (norm_nonneg _)
            (mul_nonneg hcP (norm_nonneg _))
      _ = cP * cQ * S := by
          rw [Finset.sum_comm]
          simp only [S, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
          ring
  calc ∑ i, ∑ j, ‖(P * A * Q) i j‖ ≤ ∑ _i : Fin m, ∑ _j : Fin m, cP * cQ * S :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hent i j
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

theorem normInf_kap_le : ∀ (D : D7) (V V' : HSp D) (I : GlobalTheory.Mem.Isom.IsoMat V V') (θ : InfF D), IsInfFam θ →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : GA D V, normInf θ V' (I.kap g) ≤ C * normInf θ V g := by
  intro D V V' I θ hθ
  let K : D.what₂.Tau → ℝ := fun τ =>
    (V'.rank : ℝ) * V'.rank * (∑ i, ∑ k, ‖I.pT τ i k‖) * (∑ l, ∑ j, ‖I.qT τ l j‖)
  have hK : ∀ τ, 0 ≤ K τ := fun τ => by positivity
  refine ⟨∑ τ, K τ, Finset.sum_nonneg fun τ _ => hK τ, fun g => ?_⟩
  unfold normInf
  have key : ∀ τ, (∑ i, ∑ j, (‖infMat D.sp.cm.sig V'.gram (θ τ) (I.kap g) i j‖ +
      ‖infMat D.sp.cm.sig V'.gram (θ τ) (I.kap g)⁻¹ i j‖)) ≤
      K τ * ∑ i, ∑ j, (‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖) := by
    intro τ
    rw [← map_inv I.kap g, I.infMat_kap hθ, I.infMat_kap hθ]
    simp only [Finset.sum_add_distrib, mul_add]
    exact add_le_add (sum_norm_conj_le _ _ _) (sum_norm_conj_le _ _ _)
  have hS : ∀ τ, 0 ≤ ∑ i, ∑ j, (‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ +
      ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖) := fun τ => by positivity
  calc _ ≤ ∑ τ, K τ * ∑ i, ∑ j, (‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ +
          ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖) := Finset.sum_le_sum fun τ _ => key τ
    _ ≤ ∑ τ, (∑ σ, K σ) * ∑ i, ∑ j, (‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ +
          ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖) :=
        Finset.sum_le_sum fun τ _ => mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (fun σ _ => hK σ) (Finset.mem_univ τ)) (hS τ)
    _ = _ := by rw [← Finset.mul_sum]

end GlobalTheory.Mem.Isom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormInfIsometryConjLeConstMulStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix Formalism.IndefR.Datum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normInf_isometryConj_le_const_mul : ∀ (D : D7) (V V' : HSp D) (I : GlobalTheory.Mem.Isom.IsoMat V V') (θ : InfF D), IsInfFam θ → ∃ C : ℝ, 0 ≤ C ∧ ∀ g : GA D V, normInf θ V' (I.kap g) ≤ C * normInf θ V g := by
  first | exact @GlobalTheory.Mem.Isom.normInf_kap_le | exact GlobalTheory.Mem.Isom.normInf_kap_le | (intros; apply GlobalTheory.Mem.Isom.normInf_kap_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCuspidalIsometryTransportHermitian
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCuspidalIsometryTransportHermitian
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix Formalism.IndefR.Datum
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Isom.IsoMat

open Formalism.UG (cT cT_mul cT_one)

section Gen

variable {A : Type} [CommRing A] {k n m : ℕ}

theorem conj_right_zero {r : ℕ} {aP : Matrix (Fin m) (Fin n) A} {aQ : Matrix (Fin n) (Fin m) A} (hQP : aQ * aP = 1)
    {x : Matrix (Fin n) (Fin n) A} {c : Matrix (Fin n) (Fin r) A} (h : x * c = 0) : aP * x * aQ * (aP * c) = 0 := by
  calc _ = aP * (x * ((aQ * aP) * c)) := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hQP, Matrix.one_mul, h, Matrix.mul_zero]

theorem conj_left_zero {aP : Matrix (Fin m) (Fin n) A} {aQ : Matrix (Fin n) (Fin m) A} (hQP : aQ * aP = 1)
    {x : Matrix (Fin n) (Fin n) A} {y : Matrix (Fin k) (Fin n) A} (h : y * x = 0) : y * aQ * (aP * x * aQ) = 0 := by
  calc _ = (y * ((aQ * aP) * x)) * aQ := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hQP, Matrix.one_mul, h, Matrix.zero_mul]

theorem conj_mulVec {r : ℕ} (aP : Matrix (Fin m) (Fin n) A) (aQ : Matrix (Fin n) (Fin m) A)
    (x : Matrix (Fin n) (Fin n) A) (c : Matrix (Fin n) (Fin r) A) (v : Fin m → A) (a : Fin r → A)
    (h : x.mulVec (aQ.mulVec v) = c.mulVec a) : (aP * x * aQ).mulVec v = (aP * c).mulVec a := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_mulVec]

theorem conj_sub_one {aP : Matrix (Fin m) (Fin n) A} {aQ : Matrix (Fin n) (Fin m) A} (hPQ : aP * aQ = 1)
    (x : Matrix (Fin n) (Fin n) A) : aP * x * aQ - 1 = aP * (x - 1) * aQ := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hPQ]

end Gen

variable {D : D7} {V V' : HSp D} (I : IsoMat V V')

theorem cT_P_gram : cT (D.sp.cm.sig : D.host.E →+* D.host.E) I.P * V'.gram = V.gram * I.Q := by
  rw [← I.gram, Matrix.mul_assoc _ I.P, I.PQ, Matrix.mul_one]

theorem mat_kap_sub (g : GA D V) :
    (matHom V' (I.kap g)).1 - 1 = HMul.hMul (HMul.hMul I.aP ((matHom V g).1 - 1)) I.aQ :=
  conj_sub_one I.aP_aQ _

theorem kap_mem_NI {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) {x : GA D V} (hx : x ∈ NI V C) :
    I.kap x ∈ NI V' (I.P * C) := by
  have key : NI V C ≤ (NI V' (I.P * C)).comap I.kap.toMonoidHom := by
    refine (Subgroup.closure_le _).2 ?_
    intro g hg
    show I.kap g ∈ NI V' (I.P * C)
    obtain ⟨h1, h2, h3⟩ := hg
    refine Subgroup.subset_closure ?_
    have hm := I.mat_kap_sub g
    have hPC : (I.P * C).map (incA D) = I.aP * C.map (incA D) := Matrix.map_mul
    have hG : cT (D.sp.cm.sig : D.host.E →+* D.host.E) (I.P * C) * V'.gram =
        cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram * I.Q := by
      rw [cT_mul, Matrix.mul_assoc, I.cT_P_gram, Matrix.mul_assoc]
    have hGm : (cT (D.sp.cm.sig : D.host.E →+* D.host.E) (I.P * C) * V'.gram).map (incA D) =
        (cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram).map (incA D) * I.aQ := by
      rw [hG, Matrix.map_mul]; rfl
    refine ⟨?_, ?_, fun x' hx' => ?_⟩
    · show HMul.hMul ((matHom V' (I.kap g)).1 - 1) ((I.P * C).map (incA D)) = 0
      rw [hm, hPC]
      exact conj_right_zero I.aQ_aP h1
    · show HMul.hMul ((cT (D.sp.cm.sig : D.host.E →+* D.host.E) (I.P * C) * V'.gram).map (incA D))
        ((matHom V' (I.kap g)).1 - 1) = 0
      rw [hGm, hm]
      exact conj_left_zero I.aQ_aP h2
    · have hx : (cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram).mulVec (I.Q.mulVec x') = 0 := by
        rw [Matrix.mulVec_mulVec, ← hG]
        exact hx'
      obtain ⟨a, ha⟩ := h3 _ hx
      refine ⟨a, ?_⟩
      have hQx : I.aQ.mulVec (fun i => incA D (x' i)) = fun i => incA D (I.Q.mulVec x' i) :=
        funext fun i => (RingHom.map_mulVec (incA D) I.Q x' i).symm
      show ((matHom V' (I.kap g)).1 - 1).mulVec (fun i => incA D (x' i)) = ((I.P * C).map (incA D)).mulVec a
      rw [hm, hPC]
      refine conj_mulVec _ _ _ _ _ _ ?_
      rw [hQx]
      exact ha
  exact key hx

theorem isIsoFrame_Q {r : ℕ} {C' : Matrix (Fin V'.rank) (Fin r) D.host.E} (h : IsIsoFrame V' C') :
    IsIsoFrame V (I.Q * C') := by
  obtain ⟨hr, hli, hiso⟩ := h
  refine ⟨hr, ?_, ?_⟩
  · have e : (I.Q * C').transpose = (Matrix.mulVecLin I.Q) ∘ C'.transpose := by
      funext i j
      rfl
    rw [e]
    refine hli.map' _ (LinearMap.ker_eq_bot.2 fun a b hab => ?_)
    have := congrArg I.P.mulVec hab
    simpa [Matrix.mulVec_mulVec, I.PQ] using this
  · have hg : cT (D.sp.cm.sig : D.host.E →+* D.host.E) I.Q * V.gram * I.Q = V'.gram := I.symm.gram
    rw [cT_mul]
    calc _ = cT (D.sp.cm.sig : D.host.E →+* D.host.E) C' *
          (cT (D.sp.cm.sig : D.host.E →+* D.host.E) I.Q * V.gram * I.Q) * C' := by
          simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hg]; exact hiso

theorem kap_mem_NI' {r : ℕ} {C' : Matrix (Fin V'.rank) (Fin r) D.host.E} {x : GA D V} (hx : x ∈ NI V (I.Q * C')) :
    I.kap x ∈ NI V' C' := by
  have := I.kap_mem_NI (I.Q * C') hx
  rwa [← Matrix.mul_assoc, I.PQ, Matrix.one_mul] at this

theorem kap_symm_mem_NI {r : ℕ} {C' : Matrix (Fin V'.rank) (Fin r) D.host.E} {y : GA D V'} (hy : y ∈ NI V' C') :
    I.kap.symm y ∈ NI V (I.Q * C') :=
  I.symm.kap_mem_NI C' hy

end GlobalTheory.Mem.Isom.IsoMat


open GlobalTheory.Mem.Isom GlobalTheory.Mem.Isom.IsoMat in
theorem GlobalTheory.Mem.Isom.isCuspFun_tr : ∀ (D : D7) (V V' : HSp D) (I : GlobalTheory.Mem.Isom.IsoMat V V') (φ : GA D V → ℂ),
    IsCuspFun V φ → IsCuspFun V' (I.tr φ) := by
  intro D V V' I φ hφ r C' hC' μ 𝓕 hμ h𝓕 g
  haveI := GlobalTheory.AutFunCounterexample.borel_NI D V (I.Q * C')
  haveI := GlobalTheory.AutFunCounterexample.borel_NI D V' C'
  haveI := GlobalTheory.AutFunCounterexample.topGroup_GA D V
  haveI := GlobalTheory.AutFunCounterexample.topGroup_GA D V'
  let T : NI V (I.Q * C') ≃ₜ* NI V' C' :=
    { toFun := fun x => ⟨I.kap (x : GA D V), I.kap_mem_NI' x.2⟩
      invFun := fun y => ⟨I.kap.symm (y : GA D V'), I.kap_symm_mem_NI y.2⟩
      left_inv := fun x => Subtype.ext (I.kap.symm_apply_apply (x : GA D V))
      right_inv := fun y => Subtype.ext (I.kap.apply_symm_apply (y : GA D V'))
      map_mul' := fun x y => Subtype.ext (map_mul I.kap (x : GA D V) (y : GA D V))
      continuous_toFun := (I.continuous_kap.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (I.continuous_kap_symm.comp continuous_subtype_val).subtype_mk _ }
  let e : NI V (I.Q * C') ≃ᵐ NI V' C' := T.toHomeomorph.toMeasurableEquiv
  have hp : MeasurePreserving e (μ.map e.symm) μ :=
    (MeasurePreserving.symm e.symm ⟨e.symm.measurable, rfl⟩ :)
  have hH : (μ.map e.symm).IsHaarMeasure := T.symm.isHaarMeasure_map μ
  have hF : IsFundamentalDomain (NIQ V (I.Q * C')) (e ⁻¹' 𝓕) (μ.map e.symm) := by
    refine h𝓕.preimage_of_equiv hp.quasiMeasurePreserving
      (e := fun γ => ⟨T.symm γ, I.symm.kap_mem_GQ γ.2⟩) ⟨fun a b hab => ?_, fun b => ?_⟩ fun γ x => ?_
    · exact Subtype.ext (T.symm.injective (congrArg Subtype.val hab))
    · exact ⟨⟨T b.1, I.kap_mem_GQ b.2⟩, Subtype.ext (T.symm_apply_apply _)⟩
    · change T (T.symm γ * x) = γ * T x
      rw [map_mul, T.apply_symm_apply]
  have key := hφ r (I.Q * C') (I.isIsoFrame_Q hC') (μ.map e.symm) (e ⁻¹' 𝓕) hH hF (I.kap.symm g)
  rw [← hp.setIntegral_preimage_emb e.measurableEmbedding (fun n : NI V' C' => I.tr φ ((n : GA D V') * g)) 𝓕]
  refine Eq.trans ?_ key
  congr 1
  funext x
  show φ (I.kap.symm (I.kap (x : GA D V) * g)) = φ ((x : GA D V) * I.kap.symm g)
  rw [map_mul, MulEquiv.symm_apply_apply]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCuspidalIsometryTransportHermitianStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix Formalism.IndefR.Datum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCuspidal_isometryTransport_hermitian : ∀ (D : D7) (V V' : HSp D) (I : GlobalTheory.Mem.Isom.IsoMat V V') (φ : GA D V → ℂ), IsCuspFun V φ → IsCuspFun V' (I.tr φ) := by
  first | exact @GlobalTheory.Mem.Isom.isCuspFun_tr | exact GlobalTheory.Mem.Isom.isCuspFun_tr | (intros; apply GlobalTheory.Mem.Isom.isCuspFun_tr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GelfandOperatorCommutesIsometry
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TracePowEq
namespace GlobalTheory.TracePowEq

open Matrix

theorem trace_pow_eq {A : Type} [Ring A] [Algebra ℂ A] {n m : ℕ}
    (E : Fin n → Fin n → A) (E' : Fin m → Fin m → A)
    (P : Matrix (Fin m) (Fin n) ℂ) (Q : Matrix (Fin n) (Fin m) ℂ)
    (hPQ : P * Q = (1 : Matrix (Fin m) (Fin m) ℂ))
    (hQP : Q * P = (1 : Matrix (Fin n) (Fin n) ℂ))
    (h : ∀ (a b : Fin m), E' a b = ∑ c : Fin n, ∑ d : Fin n, (Q c a * P b d) • E c d) (k : ℕ) :
    ∑ c : Fin m, ((Matrix.of : (Fin m → Fin m → A) → Matrix (Fin m) (Fin m) A) E' ^ k) c c
      = ∑ c : Fin n, ((Matrix.of : (Fin n → Fin n → A) → Matrix (Fin n) (Fin n) A) E ^ k) c c := by

  obtain ⟨S, hS⟩ : ∃ S : Matrix (Fin m) (Fin n) A, S = Qᵀ.map (algebraMap ℂ A) := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : Matrix (Fin n) (Fin m) A, T = Pᵀ.map (algebraMap ℂ A) := ⟨_, rfl⟩
  have hTS : T * S = 1 := by
    rw [hT, hS, ← Matrix.map_mul, ← Matrix.transpose_mul, hQP, Matrix.transpose_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hST : S * T = 1 := by
    rw [hT, hS, ← Matrix.map_mul, ← Matrix.transpose_mul, hPQ, Matrix.transpose_one,
      Matrix.map_one _ (map_zero _) (map_one _)]

  have hE : (Matrix.of E' : Matrix (Fin m) (Fin m) A) = S * Matrix.of E * T := by
    ext a b
    have key : ∀ c d, (Q c a * P b d) • E c d = S a c * E c d * T d b := by
      intro c d
      rw [hS, hT, Matrix.map_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.transpose_apply,
        Algebra.smul_def, map_mul, mul_assoc, Algebra.commutes (P b d) (E c d), ← mul_assoc]
    rw [Matrix.of_apply, h a b]
    simp only [key, Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul]
    exact Finset.sum_comm

  have hpow : ∀ j : ℕ, (S * Matrix.of E * T) ^ j = S * Matrix.of E ^ j * T := by
    intro j
    induction j with
    | zero => rw [pow_zero, pow_zero, Matrix.mul_one, hST]
    | succ j ih =>
      rw [pow_succ, ih, pow_succ]
      calc S * Matrix.of E ^ j * T * (S * Matrix.of E * T)
          = S * Matrix.of E ^ j * (T * S) * Matrix.of E * T := by simp only [Matrix.mul_assoc]
        _ = S * (Matrix.of E ^ j * Matrix.of E) * T := by rw [hTS, Matrix.mul_one, Matrix.mul_assoc S]

  have hcyc : ∀ X : Matrix (Fin n) (Fin m) A, ∑ c, (S * X) c c = ∑ d, (X * S) d d := by
    intro X
    simp only [Matrix.mul_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun c _ => ?_
    rw [hS, Matrix.map_apply, Algebra.commutes]
  rw [hE, hpow, Matrix.mul_assoc, hcyc, Matrix.mul_assoc, hTS, Matrix.mul_one]

end GlobalTheory.TracePowEq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GelfandOperatorCommutesIsometry
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix Formalism.IndefR.Datum
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Isom

theorem trace_pow_rect {A : Type} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A) (E' : Fin m → Fin m → A)
    (P : Matrix (Fin m) (Fin n) ℂ) (Q : Matrix (Fin n) (Fin m) ℂ) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (h : ∀ a b, E' a b = ∑ c, ∑ d, (Q c a * P b d) • E c d) (k : ℕ) :
    ∑ c, (Matrix.of E' ^ k) c c = ∑ c, (Matrix.of E ^ k) c c := by
  first
  | exact @_root_.GlobalTheory.TracePowEq.trace_pow_eq
  | exact _root_.GlobalTheory.TracePowEq.trace_pow_eq
  | (apply _root_.GlobalTheory.TracePowEq.trace_pow_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.TracePowEq.trace_pow_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TracePowEq.trace_pow_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TracePowEq.trace_pow_eq ..)

namespace IsoMat

variable {D : D7} {V V' : HSp D} (I : IsoMat V V') {θ : InfF D}

def trSm (hθ : IsInfFam θ) : GlobalTheory.Mem.AutSpace.SmFun θ V ≃ₗ[ℂ] GlobalTheory.Mem.AutSpace.SmFun θ V' where
  toFun φ := ⟨I.tr φ.1, I.tr_mem_SmFun hθ φ.2⟩
  invFun ψ := ⟨I.symm.tr ψ.1, I.symm.tr_mem_SmFun hθ ψ.2⟩
  left_inv φ := Subtype.ext (funext fun x => congrArg φ.1 (I.kapF_symm x))
  right_inv ψ := Subtype.ext (funext fun x => congrArg ψ.1 (I.symm.kapF_symm x))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def conjSm (hθ : IsInfFam θ) :
    Module.End ℂ (GlobalTheory.Mem.AutSpace.SmFun θ V) →+* Module.End ℂ (GlobalTheory.Mem.AutSpace.SmFun θ V') where
  toFun f := (I.trSm hθ).toLinearMap ∘ₗ f ∘ₗ (I.trSm hθ).symm.toLinearMap
  map_one' := LinearMap.ext fun x => by simp
  map_mul' f g := LinearMap.ext fun x => by simp
  map_zero' := LinearMap.ext fun x => by simp
  map_add' f g := LinearMap.ext fun x => by simp

theorem conjSm_apply (hθ : IsInfFam θ) (f : Module.End ℂ (GlobalTheory.Mem.AutSpace.SmFun θ V)) (x : GlobalTheory.Mem.AutSpace.SmFun θ V) :
    I.conjSm hθ f (I.trSm hθ x) = I.trSm hθ (f x) := by
  show I.trSm hθ (f ((I.trSm hθ).symm (I.trSm hθ x))) = _
  rw [LinearEquiv.symm_apply_apply]

theorem conjSm_smul (hθ : IsInfFam θ) (c : ℂ) (f : Module.End ℂ (GlobalTheory.Mem.AutSpace.SmFun θ V)) :
    I.conjSm hθ (c • f) = c • I.conjSm hθ f := LinearMap.ext fun x => by simp [conjSm]

theorem derEnd_tr (hθ : IsInfFam θ) (τ : D.what₂.Tau) (Z : Matrix (Fin V'.rank) (Fin V'.rank) ℂ) :
    GlobalTheory.Mem.RealTranslate.derEnd hθ τ Z = I.conjSm hθ (GlobalTheory.Mem.RealTranslate.derEnd hθ τ (I.symm.adP τ Z)) := by
  refine LinearMap.ext fun ψ => ?_
  obtain ⟨φ, rfl⟩ := (I.trSm hθ).surjective ψ
  rw [conjSm_apply]
  exact Subtype.ext (I.RderC_tr hθ τ Z φ.1)

theorem symm_adP_single (τ : D.what₂.Tau) (a b : Fin V'.rank) :
    I.symm.adP τ (Matrix.single a b 1) = ∑ c, ∑ d, (I.qT τ c a * I.pT τ b d) • (Matrix.single c d 1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) := by
  rw [matrix_eq_sum_single (I.symm.adP τ _)]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  rw [Matrix.smul_single, smul_eq_mul, mul_one]
  congr 1
  simp [adP, pT, qT, symm, Matrix.mul_apply, Matrix.single, ite_and]

theorem gelf_tr : ∀ (D : D7) (V V' : HSp D) (I : GlobalTheory.Mem.Isom.IsoMat V V') (θ : InfF D), IsInfFam θ →
    ∀ (τ : D.what₂.Tau) (k : ℕ) (φ : GA D V → ℂ), φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V →
      gelf θ V' τ k (I.tr φ) = I.tr (gelf θ V τ k φ) := by
  intro D V V' I θ hθ τ k φ hφ
  let E0 : Fin V.rank → Fin V.rank → Module.End ℂ (GlobalTheory.Mem.AutSpace.SmFun θ V) :=
    fun c d => GlobalTheory.Mem.RealTranslate.derEnd hθ τ (Matrix.single c d 1)
  let E' : Fin V'.rank → Fin V'.rank → Module.End ℂ (GlobalTheory.Mem.AutSpace.SmFun θ V') :=
    fun a b => GlobalTheory.Mem.RealTranslate.derEnd hθ τ (Matrix.single a b 1)
  have key := trace_pow_rect (fun c d => I.conjSm hθ (E0 c d)) E' (I.pT τ) (I.qT τ) (I.pT_qT τ) (I.qT_pT τ)
    (fun a b => by
      simp only [E', E0]
      rw [I.derEnd_tr hθ τ, I.symm_adP_single τ a b]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, LinearMap.map_smul, conjSm_smul]) (k + 1)
  have hm : Matrix.of (fun c d => I.conjSm hθ (E0 c d)) = (I.conjSm hθ).mapMatrix (Matrix.of E0) := by
    ext c d; rfl
  have hs : ∑ c, (((I.conjSm hθ).mapMatrix (Matrix.of E0)) ^ (k + 1)) c c =
      I.conjSm hθ (∑ c, (Matrix.of E0 ^ (k + 1)) c c) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← RingHom.map_pow, map_sum]; rfl
  rw [hm, hs, ← GlobalTheory.SmoothForms.gelfA_eq_sum_pow, ← GlobalTheory.SmoothForms.gelfA_eq_sum_pow] at key
  have e1 := GlobalTheory.Mem.RealTranslate.gelf_eq hθ τ k (I.trSm hθ ⟨φ, hφ⟩)
  have e2 := GlobalTheory.Mem.RealTranslate.gelf_eq hθ τ k (⟨φ, hφ⟩ : GlobalTheory.Mem.AutSpace.SmFun θ V)
  refine e1.trans ?_
  change (GlobalTheory.SmoothForms.gelfA E' k (I.trSm hθ ⟨φ, hφ⟩)).1 = _
  rw [key, conjSm_apply]
  show I.tr _ = I.tr _
  rw [e2]

end IsoMat
end GlobalTheory.Mem.Isom

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GelfandOperatorCommutesIsometryStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix Formalism.IndefR.Datum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfand_operator_commutes_isometry : ∀ (D : D7) (V V' : HSp D) (I : GlobalTheory.Mem.Isom.IsoMat V V') (θ : InfF D), IsInfFam θ → ∀ (τ : D.what₂.Tau) (k : ℕ) (φ : GA D V → ℂ), φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V → gelf θ V' τ k (I.tr φ) = I.tr (gelf θ V τ k φ) := by
  first | exact @GlobalTheory.Mem.Isom.IsoMat.gelf_tr | exact GlobalTheory.Mem.Isom.IsoMat.gelf_tr | (intros; apply GlobalTheory.Mem.Isom.IsoMat.gelf_tr <;> assumption)
end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem Formalism.IndefR.Datum
open scoped InnerProductSpace

namespace GlobalTheory.Mem.Isom

variable {D : D7}

theorem gelf_tr {V V' : HSp D} (I : IsoMat V V') {θ : InfF D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (k : ℕ) {φ : GA D V → ℂ}
    (hφ : φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V) : gelf θ V' τ k (I.tr φ) = I.tr (gelf θ V τ k φ) :=
  GlobalTheory.T.gelfand_operator_commutes_isometry D V V' I θ hθ τ k φ hφ

theorem cusp_tr {V V' : HSp D} (I : IsoMat V V') {φ : GA D V → ℂ} (hφ : IsCuspFun V φ) : IsCuspFun V' (I.tr φ) :=
  GlobalTheory.T.isCuspidal_isometryTransport_hermitian D V V' I φ hφ

theorem haar_tr {V V' : HSp D} (I : IsoMat V V') (S : HSp D) (μ : Measure (WO S V')) (𝓕 : Set (WO S V')) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL V' S) 𝓕 μ) : ∃ (ν : Measure (WO S V)) (𝓖 : Set (WO S V)), ν.IsAddHaarMeasure ∧
      IsAddFundamentalDomain (ratL V S) 𝓖 ν ∧
        ∀ u : WO S V → ENNReal, ∫⁻ w in 𝓕, u ((I.phi S).symm w) ∂μ = ∫⁻ w in 𝓖, u w ∂ν :=
  GlobalTheory.T.exists_haar_fundamentalDomain_isometryTransport D V V' I S μ 𝓕 hμ h𝓕

theorem entries_fix {A : Type} [CommRing A] {m n : ℕ} (c : A) {M : Matrix (Fin n) (Fin n) A} (hM : ∀ i j, c * M i j = M i j)
    (P : Matrix (Fin m) (Fin n) A) (Q : Matrix (Fin n) (Fin m) A) (i j : Fin m) : c * (P * M * Q) i j = (P * M * Q) i j := by
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  conv_rhs => rw [← hM l k]
  ring

theorem entries_fix' {A : Type} [CommRing A] {m n k : ℕ} (c : A) {M : Matrix (Fin n) (Fin k) A} (hM : ∀ i j, c * M i j = M i j)
    (P : Matrix (Fin m) (Fin n) A) (i : Fin m) (j : Fin k) : c * (P * M) i j = (P * M) i j := by
  simp only [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  conv_rhs => rw [← hM l j]
  ring

theorem sub_one_conj {A : Type} [CommRing A] {m n : ℕ} {P : Matrix (Fin m) (Fin n) A} {Q : Matrix (Fin n) (Fin m) A} (PQ : P * Q = 1)
    (M : Matrix (Fin n) (Fin n) A) : P * M * Q - 1 = P * (M - 1) * Q := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, PQ]

theorem det_conj_rect {A : Type} [CommRing A] {m n : ℕ} (h : n = m) {P : Matrix (Fin m) (Fin n) A} {Q : Matrix (Fin n) (Fin m) A}
    (QP : Q * P = 1) (M : Matrix (Fin n) (Fin n) A) : (P * M * Q).det = M.det := by
  subst h
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm (P.det), mul_assoc, ← Matrix.det_mul, mul_eq_one_comm.1 QP, Matrix.det_one, mul_one]

namespace IsoMat
variable {V V' : HSp D} (I : IsoMat V V') {θ : InfF D}

theorem isAutFun_tr {φ : GA D V → ℂ} (h : IsAutFun V φ) : IsAutFun V' (I.tr φ) := by
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  refine ⟨fun γ hγ g => ?_, ?_, h.cont.comp I.continuous_kap_symm⟩
  · unfold tr
    rw [map_mul]
    exact h.left _ (I.symm.kap_mem_GQ hγ) _
  · obtain ⟨U, hU, e⟩ := h.level
    refine ⟨U.comap I.kap.symm.toMonoidHom, hU.preimage I.continuous_kap_symm, fun k hk hf g => ?_⟩
    unfold tr
    rw [map_mul]
    exact e _ hk (I.symm.kap_mem_GfC hf) _

theorem normInf_kap_le (hθ : IsInfFam θ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ g : GA D V, normInf θ V' (I.kap g) ≤ C * normInf θ V g :=
  GlobalTheory.T.normInf_isometryConj_le_const_mul D V V' I θ hθ

theorem foldr_tr (hθ : IsInfFam θ) (φ : GA D V → ℂ) (l : List (D.what₂.Tau × Matrix (Fin V'.rank) (Fin V'.rank) ℂ))
    (hl : ∀ p ∈ l, p.2 ∈ lieAt V' p.1) :
    l.foldr (fun p f => Rder θ V' p.1 p.2 f) (I.tr φ) =
      I.tr ((l.map fun p => (p.1, I.symm.adP p.1 p.2)).foldr (fun p f => Rder θ V p.1 p.2 f) φ) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rw [List.map_cons, List.foldr_cons, List.foldr_cons, ih fun q hq => hl q (List.mem_cons_of_mem _ hq),
      I.Rder_tr hθ (hl p List.mem_cons_self)]

def trLin : (GA D V → ℂ) →ₗ[ℂ] (GA D V' → ℂ) where
  toFun := I.tr
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem isAutFunSm_tr (hθ : IsInfFam θ) {φ : GA D V → ℂ} (hφ : IsAutFunSm θ V φ) : IsAutFunSm θ V' (I.tr φ) := by
  have ha := I.isAutFun_tr hφ.toIsAutFun
  refine { left := ha.left, level := ha.level, cont := ha.cont, smooth := I.tr_mem_SmFun hθ hφ.smooth, zfin := ?_, growth := ?_ }
  · obtain ⟨W, hW, m, s⟩ := hφ.zfin
    refine ⟨(W ⊓ GlobalTheory.Mem.AutSpace.SmFun θ V).map I.trLin, inferInstance, ⟨φ, ⟨m, hφ.smooth⟩, rfl⟩, ?_⟩
    rintro τ k _ ⟨f, hf, rfl⟩
    exact ⟨_, ⟨s τ k f hf.1, (GlobalTheory.Mem.AutSpace.linOnSm_gelf τ k).mem f hf.2⟩, (_root_.GlobalTheory.Mem.Isom.gelf_tr I hθ τ k hf.2).symm⟩
  · obtain ⟨N, hN⟩ := hφ.growth
    obtain ⟨c, hc0, hc⟩ := I.symm.normInf_kap_le hθ
    refine ⟨N, fun l hl x => ?_⟩
    obtain ⟨C, hC⟩ := hN (l.map fun p => (p.1, I.symm.adP p.1 p.2)) (fun p hp => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact I.symm.adP_mem (hl q hq)) (I.kap.symm x)
    refine ⟨|C| * c ^ N, fun g hg => ?_⟩
    rw [I.foldr_tr hθ φ l hl]
    unfold tr
    rw [map_mul, mul_assoc |C|, ← mul_pow]
    exact (hC _ (I.symm.kap_mem_GinfC hg)).trans (mul_le_mul (le_abs_self _)
      (pow_le_pow_left₀ (GlobalTheory.SmoothForms.normInf_nonneg _) (hc g) N) (pow_nonneg (GlobalTheory.SmoothForms.normInf_nonneg _) N)
      (abs_nonneg _))

theorem isThetaFunO_tr (S : HSp D) {ψ : AddChar (AF D.host.F) ℂ} {f : WO S V → ℂ} (hf : IsThetaFunO ψ S V f) :
    IsThetaFunO ψ S V' (I.trW S f) := by
  have hinf : ∀ w : WO S V', w.map (infPart D) = 0 → ((I.phi S).symm w).map (infPart D) = 0 := fun w h => by
    show (HMul.hMul I.aQ w).map (infPart D) = 0
    rw [Matrix.map_mul, h, Matrix.mul_zero]
  have hfin : ∀ w : WO S V', w.map (finPart D) = 0 → ((I.phi S).symm w).map (finPart D) = 0 := fun w h => by
    show (HMul.hMul I.aQ w).map (finPart D) = 0
    rw [Matrix.map_mul, h, Matrix.mul_zero]
  refine ⟨fun γ w => ?_, ?_, hf.cont.comp (I.continuous_phi_symm S), fun k L hL h0 w => ?_⟩
  · obtain ⟨w, rfl⟩ := (I.phi S).surjective w
    have e : ratW V' S γ = I.phi S (ratW V S (I.Q * γ)) := by
      rw [phi_ratW, ← Matrix.mul_assoc, I.PQ, Matrix.one_mul]
    rw [e, ← map_add (f := _), I.symplOH_phi]
    simp only [trW, AddEquiv.symm_apply_apply]
    exact hf.quasi _ _
  · obtain ⟨U, hU, e⟩ := hf.level
    refine ⟨U.map (I.phi S).toAddMonoidHom, ?_, ?_⟩
    · have e : ((U.map (I.phi S).toAddMonoidHom : AddSubgroup (WO S V')) : Set (WO S V')) = (I.phi S).symm ⁻¹' U := by
        ext w
        simp only [AddSubgroup.coe_map, Set.mem_image, Set.mem_preimage, SetLike.mem_coe]
        constructor
        · rintro ⟨u, hu, rfl⟩
          simpa using hu
        · intro hw
          exact ⟨_, hw, by simp⟩
      rw [e]
      exact hU.preimage (I.continuous_phi_symm S)
    · rintro _ ⟨u, hu, rfl⟩ h0
      have h1 : u.map (infPart D) = 0 := by
        have := hinf _ h0
        simpa using this
      show heisO ψ S V' (I.phi S u) (I.trW S f) = I.trW S f
      rw [I.heisO_trW, e u hu h1]
  · have := hf.smooth k ((I.phi S).symm.toAddMonoidHom.comp L) ((I.continuous_phi_symm S).comp hL) (fun t => hfin _ (h0 t))
      ((I.phi S).symm w)
    simpa [trW] using this

end IsoMat

namespace IsoMat
variable {V V' : HSp D} (I : IsoMat V V')

theorem isWeilDatumO_tr (S : HSp D) {ψ : AddChar (AF D.host.F) ℂ} {χ χ' : IdC D} {om : GA D S × GA D V →* Module.End ℂ (WO S V → ℂ)}
    (h : IsWeilDatumO ψ S V χ χ' om) : IsWeilDatumO ψ S V' χ χ' (I.omT S om) := by
  have hT : ∀ f, IsThetaFunO ψ S V' f → IsThetaFunO ψ S V (I.symm.trW S f) := fun f hf => I.symm.isThetaFunO_tr S hf
  refine ⟨h.std, h.hecS, h.hecT, h.resS, I.rank_eq ▸ h.resT, fun p f hf => ?_, fun g k w₀ f hf => ?_, fun γ hγ γ' hγ' f hf => ?_,
    fun f hf w => ?_, fun μ 𝓕 hμ h𝓕 p f hf => ?_, fun e he g k hg hk x y hx hy => ?_⟩
  · exact I.isThetaFunO_tr S (h.om_pres _ _ (hT f hf))
  · rw [omT_apply, omT_apply, ← I.symm.heisO_trW S ψ w₀ f, h.om_heis _ _ _ _ (hT f hf), ← I.heisO_trW, I.actO_phi]
    congr 2
    · exact I.kap.apply_symm_apply k
    · exact (I.phi S).apply_symm_apply w₀
  · rw [omT_apply]
    show om (γ, I.kap.symm γ') (I.symm.trW S f) ((I.phi S).symm 0) = f 0
    have := h.om_aut γ hγ (I.kap.symm γ') (I.symm.kap_mem_GQ hγ') _ (hT f hf)
    rw [map_zero, this]
    show f ((I.phi S) 0) = f 0
    rw [map_zero]
  · exact (h.om_cont _ (hT f hf) ((I.phi S).symm w)).comp
      (continuous_fst.prodMk ((I.continuous_kap_symm).comp continuous_snd))
  · obtain ⟨ν, 𝓖, hν, h𝓖, hu⟩ := haar_tr I S μ 𝓕 hμ h𝓕
    have e1 := hu fun x => ‖om (p.1, I.kap.symm p.2) (I.symm.trW S f) x‖ₑ ^ 2
    have e2 := hu fun x => ‖I.symm.trW S f x‖ₑ ^ 2
    have e3 : ∀ w, I.symm.trW S f ((I.phi S).symm w) = f w := fun w => congrArg f ((I.phi S).apply_symm_apply w)
    simp only [e3] at e2
    rw [omT_apply]
    exact e1.trans ((h.om_unit ν 𝓖 hν h𝓖 _ _ (hT f hf)).trans e2.symm)
  · have e0 : mt V (I.kap.symm k) - 1 = _ := sub_one_conj I.aQ_aP (mt V' k)
    have hsupp : SuppAt e V (I.kap.symm k) := fun i j => by
      unfold SuppAt at hk
      rw [e0]
      exact entries_fix _ hk _ _ i j
    have e1 : (mt V (I.kap.symm k)).det = (mt V' k).det := det_conj_rect I.rank_eq.symm I.aP_aQ (mt V' k)
    have hdet : IsDetAt e V (I.kap.symm k) y := by
      unfold IsDetAt at hy ⊢
      rw [e1]
      exact hy
    obtain ⟨r, hr, H⟩ := h.om_split e he g (I.kap.symm k) hg hsupp x y hx hdet
    refine ⟨r, hr, fun ℓ hℓ f hf => ?_⟩
    have hinv : ∀ u : WO S V, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S V f →
        (ℓ ∘ₗ I.trL S) (heisO ψ S V u f) = (ℓ ∘ₗ I.trL S) f := by
      intro u hu f hf
      show ℓ (I.trW S (heisO ψ S V u f)) = ℓ (I.trW S f)
      rw [← I.heisO_trW]
      exact hℓ _ (fun i j => entries_fix' _ hu I.aP i j) _ (I.isThetaFunO_tr S hf)
    have := H (ℓ ∘ₗ I.trL S) hinv _ (hT f hf)
    have e1 : (ℓ ∘ₗ I.trL S) (I.symm.trW S f) = ℓ f := congrArg ℓ (I.symm.trW_symm_trW S f)
    rw [e1] at this
    exact this

end IsoMat

theorem exists_isom_transport : ∀ (D : D7) (V V' : HSp D) (e : V.V ≃ₗ[D.host.E] V'.V), HSpace.IsIsomEmb V V' e.toLinearMap →
    ∃ κ : GA D V ≃* GA D V', Continuous κ ∧ Continuous κ.symm ∧ (∀ g, κ g ∈ GQ V' ↔ g ∈ GQ V) ∧
      (∀ θ : InfF D, IsInfFam θ → ∀ F, IsCuspForm θ V F → IsCuspForm θ V' fun h => F (κ.symm h)) ∧
      ∀ (ψ : AddChar (AF D.host.F) ℂ) (S : HSp D) (χ χ' : IdC D) om, IsWeilDatumO ψ S V χ χ' om →
        ∃ om', IsWeilDatumO ψ S V' χ χ' om' ∧ ∀ f, IsThetaFunO ψ S V f → ∃ f', IsThetaFunO ψ S V' f' ∧ (f ≠ 0 → f' ≠ 0) ∧
          ∀ g h, thetaKO om' g (κ h) f' = thetaKO om g h f := by
  intro D V V' e he
  let I := IsoMat.ofEquiv e he
  refine ⟨I.kap, I.continuous_kap, I.continuous_kap_symm, fun g => ⟨fun hg => ?_, I.kap_mem_GQ⟩,
    fun θ hθ F hF => ⟨I.isAutFunSm_tr hθ hF.1, cusp_tr I hF.2⟩, fun ψ S χ χ' om hom => ?_⟩
  · have := I.symm.kap_mem_GQ hg
    rwa [← I.kap_symm_apply, I.kap.symm_apply_apply] at this
  · refine ⟨I.omT S om, I.isWeilDatumO_tr S hom, fun f hf => ⟨I.trW S f, I.isThetaFunO_tr S hf, fun hne h0 => hne ?_, fun g h => ?_⟩⟩
    · have := I.trW_symm_trW S f
      rw [h0] at this
      rw [← this]
      rfl
    · show I.trW S (om (g, I.kap.symm (I.kap h)) (I.symm.trW S (I.trW S f))) 0 = om (g, h) f 0
      rw [I.kap.symm_apply_apply, I.trW_symm_trW]
      show om (g, h) f ((I.phi S).symm 0) = om (g, h) f 0
      rw [map_zero]

end GlobalTheory.Mem.Isom
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_transport_groups_cuspForms_weilData_isometry : ∀ (D : D7) (V V' : HSp D) (e : V.V ≃ₗ[D.host.E] V'.V), HSpace.IsIsomEmb V V' e.toLinearMap → ∃ κ : GA D V ≃* GA D V', Continuous κ ∧ Continuous κ.symm ∧ (∀ g, κ g ∈ GQ V' ↔ g ∈ GQ V) ∧ (∀ θ : InfF D, IsInfFam θ → ∀ F, IsCuspForm θ V F → IsCuspForm θ V' fun h => F (κ.symm h)) ∧ ∀ (ψ : AddChar (AF D.host.F) ℂ) (S : HSp D) (χ χ' : IdC D) om, IsWeilDatumO ψ S V χ χ' om → ∃ om', IsWeilDatumO ψ S V' χ χ' om' ∧ ∀ f, IsThetaFunO ψ S V f → ∃ f', IsThetaFunO ψ S V' f' ∧ (f ≠ 0 → f' ≠ 0) ∧ ∀ g h, thetaKO om' g (κ h) f' = thetaKO om g h f := by
  first | exact @GlobalTheory.Mem.Isom.exists_isom_transport | exact GlobalTheory.Mem.Isom.exists_isom_transport | (intros; apply GlobalTheory.Mem.Isom.exists_isom_transport <;> assumption)

module

public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.SelfDualComap
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassInvOfUnitTrivial
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntMat
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComplexHeckeEigenvectorDescendsToCoefficientFiel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DifferentiableSumU
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H NumberField IsDedekindDomain Classical

namespace GlobalTheory.KerFinEntire

section General

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

theorem differentiable_opU (H : Sesq V) {F : V → ℂ} (hF : Differentiable ℂ F) (x : V) :
    Differentiable ℂ (opU H x F) := by
  have h : Differentiable ℂ fun z => H z x := (LinearMap.toContinuousLinearMap (H.flip x)).differentiable
  unfold opU
  fun_prop

theorem differentiable_sumU (H : Sesq V) (α : V → ℂ) (S : Finset V) {F : V → ℂ} (hF : Differentiable ℂ F) :
    Differentiable ℂ (sumU H α S F) := by
  unfold sumU
  exact Differentiable.fun_sum fun x _ => (differentiable_opU H hF x).const_mul _

theorem differentiable_xiL (H : Sesq V) (α : V → ℂ) (vol : ℝ) (SX SA SB : Finset V) (Φ : V → ℂ) {e : V → ℂ}
    (he : Differentiable ℂ e) : Differentiable ℂ (xiL H α vol SX SA SB Φ e) := by
  unfold xiL xiS
  exact Differentiable.fun_sum fun x _ => (differentiable_opU H (differentiable_sumU H _ SB he) x).const_mul _

end General

theorem differentiable_thC {E : Type} [Field E] [NumberField E] [StarRing E] {ι : Type} [Fintype ι] {a b : ℕ}
    (emb : ι → E →+* ℂ) (δ : ℂ) (d : ℕ) (sc : ℝ) (AA0 : Submodule (𝓞 E) E) (SS : Finset (HeightOneSpectrum (𝓞 E)))
    (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (c : ℕ) (Ξ : HomE E a b → ℂ) {θ : VV ι a b → ℂ}
    (hθ : Differentiable ℂ θ) : Differentiable ℂ (thC emb δ d sc AA0 SS N N' c Ξ θ) := by
  unfold thC xiV
  exact differentiable_xiL _ _ _ _ _ _ _ hθ

theorem kerFin_entire : ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ), s.Ok → TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → TaylorLogMetric.IsChi D χ → ∀ (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), TaylorLogMetric.admitted D a b (s.lat N) (s.lat N') → ∀ (SS : Finset (HeightOneSpectrum (𝓞 X.E))) (c : ℕ) (Ξ : HomE X.E a b → ℂ), Differentiable ℂ (thC (X.embC (ambOf s B χ cD : Amb X).σ₀) (ambOf s B χ cD : Amb X).δ (ambOf s B χ cD : Amb X).d (ambOf s B χ cD : Amb X).sc (ambOf s B χ cD : Amb X).AA SS N N' c Ξ ((ambOf s B χ cD : Amb X).e a b N N')) := by
  intro D X s cc δ B χ cD _ hcc hδ hχ a b N N' hA SS c Ξ
  have hE : Differentiable ℂ (B.eNat χ a b (s.lat N) (s.lat N')) :=
    (B.vec_mem_ne hcc hδ (Formalism.L2.Ker.KS.Lat.delta_ne hcc hδ) (B.stdOK hcc hδ) χ hχ a b _ _ hA).1.1
  let T : VCx X.Tau a b →L[ℂ] TaylorLogMetric.VC D a b := ContinuousLinearMap.pi fun τ => ContinuousLinearMap.proj (s.iT.symm τ)
  have he : Differentiable ℂ ((ambOf s B χ cD : Amb X).e a b N N') := hE.comp T.differentiable
  exact differentiable_thC _ _ _ _ _ _ _ _ _ _ he

end GlobalTheory.KerFinEntire
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointEigenvectorsEqZeroOfSumEqZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem joint_eigenvectors_eq_zero_of_sum_eq_zero (ι κ M : Type) [AddCommGroup M] [Module ℂ M]
    (A : ι → Module.End ℂ M) (χ : κ → ι → ℂ) (v : κ → M) (s : Finset κ)
    (heig : ∀ k ∈ s, ∀ i, A i (v k) = χ k i • v k) (hinj : Set.InjOn χ s)
    (hsum : ∑ k ∈ s, v k = 0) : ∀ k ∈ s, v k = 0 := by
  classical
  induction s using Finset.induction_on generalizing v with
  | empty => simp
  | insert a s ha ih =>
    have hsum' : v a + ∑ k ∈ s, v k = 0 := by rwa [Finset.sum_insert ha] at hsum
    have hs : ∀ k ∈ s, v k = 0 := by
      intro k hk
      have hne : χ k ≠ χ a := by
        intro h
        have hka : k = a := hinj (by simp [hk]) (by simp) h
        exact ha (hka ▸ hk)
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
      have hw : (χ k i - χ a i) • v k = 0 := by
        refine ih (fun j => (χ j i - χ a i) • v j) ?_ ?_ ?_ k hk
        · intro j hj i'
          have h1 := heig j (Finset.mem_insert_of_mem hj) i'
          simp only [map_smul, h1]
          rw [smul_comm]
        · exact hinj.mono (by simp)
        · have h2 : A i (v a + ∑ k ∈ s, v k) - χ a i • (v a + ∑ k ∈ s, v k) = 0 := by
            rw [hsum']; simp
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_add (f := _), map_sum, heig a (Finset.mem_insert_self a s) i, smul_add, Finset.smul_sum,
            add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib] at h2
          rw [← h2]
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [heig j (Finset.mem_insert_of_mem hj) i, sub_smul]
      exact (smul_eq_zero.mp hw).resolve_left (sub_ne_zero.mpr hi)
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · simpa [Finset.sum_eq_zero hs] using hsum'
    · exact hs k hk

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualPolyTwistedHeckePolyEqContragredient
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualPolyTwistedHeckePolyEqContragredient
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Hk3.DualHecke

theorem comp_C_mul_X_dualPoly {K : Type} [Field K] (t u : K) (R : K[X]) :
    (Formalism.L2.DIV.dualPoly t R).comp (C u * X) = Formalism.L2.DIV.dualPoly (t * u) R := by
  unfold Formalism.L2.DIV.dualPoly
  rw [mul_comp, C_comp, comp_assoc, mul_comp, C_comp, X_comp, C_mul]
  congr 2
  ring

theorem dualPoly_heckePolyOf_comp : ∀ (K : Type) [Field K] (n q : ℕ) (a b : ℕ → K) (s s' : K), (q : K) ≠ 0 → s ≠ 0 → 0 < n → a 0 = 1 → (∀ j, j ≤ n → b j * a n = a (n - j)) → dualPoly (s * s' * (q : K) ^ (n - 1)) ((Formalism.L2.Col.heckePolyOf n q b).comp (C s * X)) = (Formalism.L2.Col.heckePolyOf n q a).comp (C s' * X) := by
  intro K _ n q a b s s' hq hs hn h0 h
  have han : a n ≠ 0 := by
    intro h1
    have e := h n le_rfl
    rw [Nat.sub_self, h0, h1, mul_zero] at e
    exact zero_ne_one e
  have hbn : b n * a n = 1 := by
    have e := h n le_rfl
    rwa [Nat.sub_self, h0] at e
  have hb0 : b 0 = 1 := by
    have e := h 0 (Nat.zero_le _)
    rw [Nat.sub_zero] at e
    exact mul_right_cancel₀ han (by rw [e, one_mul])
  have hdual : ∀ k ≤ n, b n * a k = b (n - k) := by
    intro k hk
    have e := h (n - k) (Nat.sub_le _ _)
    rw [Nat.sub_sub_self hk] at e
    rw [← e]
    linear_combination b (n - k) * hbn
  have H := GlobalTheory.PartsCompare.heckePolyOf_dual (n := n) (q := q) hq (a := b) (b := a) hb0 hdual
  have hc := GlobalTheory.PartsCompare.dualPoly_comp (inv_ne_zero hs) (s * s' * (q : K) ^ (n - 1))
    (Formalism.L2.Col.heckePolyOf n q b)
  rw [inv_inv] at hc
  rw [hc, H, comp_C_mul_X_dualPoly]
  congr 1
  field_simp

end GlobalTheory.Hk3.DualHecke
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualPolyTwistedHeckePolyEqContragredientStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualPoly_twistedHeckePoly_eq_contragredient : ∀ (K : Type) [Field K] (n q : ℕ) (a b : ℕ → K) (s s' : K), (q : K) ≠ 0 → s ≠ 0 → 0 < n → a 0 = 1 → (∀ j, j ≤ n → b j * a n = a (n - j)) → dualPoly (s * s' * (q : K) ^ (n - 1)) ((Formalism.L2.Col.heckePolyOf n q b).comp (C s * X)) = (Formalism.L2.Col.heckePolyOf n q a).comp (C s' * X) := by
  first | exact @GlobalTheory.Hk3.DualHecke.dualPoly_heckePolyOf_comp | exact GlobalTheory.Hk3.DualHecke.dualPoly_heckePolyOf_comp | (intros; apply GlobalTheory.Hk3.DualHecke.dualPoly_heckePolyOf_comp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugateSpaceJointEigenspacesPairCommISup
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugateSpaceJointEigenspacesPairCommISup
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwEig

theorem map_mul (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (f g : Module.End ℂ E) :
    (Tw.map s (f * g) : Module.End ℂ (Tw s E)) = Tw.map s f * Tw.map s g := LinearMap.ext fun _ => rfl

theorem pow_sub_apply (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (f : Module.End ℂ E)
    (μ : ℂ) (k : ℕ) (y : Tw s E) :
    Tw.out ((((Tw.map s f : Module.End ℂ (Tw s E)) - μ • 1) ^ k) y) = ((f - cj s μ • 1) ^ k) (Tw.out y) := by
  induction k generalizing y with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ih]
    rfl

theorem mem_maxGen (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (f : Module.End ℂ E)
    (μ : ℂ) (y : Tw s E) :
    y ∈ Module.End.maxGenEigenspace (Tw.map s f : Module.End ℂ (Tw s E)) μ ↔ Tw.out y ∈ f.maxGenEigenspace (cj s μ) := by
  rw [Module.End.mem_maxGenEigenspace, Module.End.mem_maxGenEigenspace]
  refine exists_congr fun k => ?_
  rw [← pow_sub_apply]
  rfl

theorem sub_eq_map (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (V : Submodule ℂ E) :
    Tw.sub s V = V.map (Tw.mkL s E) := by
  ext y
  constructor
  · intro hy; exact ⟨Tw.out y, hy, rfl⟩
  · rintro ⟨x, hx, rfl⟩; exact hx

theorem sub_iSup' (s : Bool) {E : Type} {C : Sort*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (Ec : C → Submodule ℂ E) :
    Tw.sub s (⨆ c, Ec c) = ⨆ c, Tw.sub s (Ec c) := by
  simp only [sub_eq_map, Submodule.map_iSup]

theorem eigAt_tw (s : Bool) {E I : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (h : I → Module.End ℂ E)
    (x : I → ℂ) :
    Formalism.L2.Col.eigAt (fun i => (Tw.map s (h i) : Module.End ℂ (Tw s E))) x =
      Tw.sub s (Formalism.L2.Col.eigAt h fun i => cj s (x i)) := by
  ext y
  simp only [Formalism.L2.Col.eigAt, Submodule.mem_iInf, mem_maxGen]
  show _ ↔ Tw.out y ∈ ⨅ i, (h i).maxGenEigenspace (cj s (x i))
  rw [Submodule.mem_iInf]

end GlobalTheory.TwEig

open GlobalTheory.TwEig in
theorem GlobalTheory.TwEig.pairComm_eigSum_sub_iSup : ∀ (s : Bool) {E I : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (h : I → Module.End ℂ E), (Formalism.L2.Col.PairComm h → Formalism.L2.Col.PairComm (fun i => (Tw.map s (h i) : Module.End ℂ (Tw s E)))) ∧ (∀ Q : (I → ℂ) → Prop, Formalism.L2.Col.eigSum (fun i => (Tw.map s (h i) : Module.End ℂ (Tw s E))) Q = Tw.sub s (Formalism.L2.Col.eigSum h fun x => Q fun i => cj s (x i))) ∧ ∀ {C : Type} (Ec : C → Submodule ℂ E), Tw.sub s (⨆ c, Ec c) = ⨆ c, Tw.sub s (Ec c) := by
  intro s E I _ _ h
  refine ⟨fun hc i j => ?_, fun Q => ?_, fun Ec => sub_iSup' s Ec⟩
  · show Tw.map s (h i) * Tw.map s (h j) = Tw.map s (h j) * Tw.map s (h i)
    rw [← map_mul, ← map_mul, (hc i j).eq]
  · simp only [Formalism.L2.Col.eigSum, eigAt_tw]
    rw [sub_iSup']
    let e : (I → ℂ) ≃ (I → ℂ) := ⟨fun x i => cj s (x i), fun x i => cj s (x i),
      fun x => funext fun i => cj_cj s (x i), fun x => funext fun i => cj_cj s (x i)⟩
    rw [← e.iSup_comp]
    refine iSup_congr fun x => ?_
    simp [e, cj_cj]
    exact (sub_iSup' (E := E) s (fun _ : (Q fun i => cj s (x i)) => Formalism.L2.Col.eigAt h x)).symm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugateSpaceJointEigenspacesPairCommISupStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugateSpace_jointEigenspaces_pairComm_iSup : ∀ (s : Bool) {E I : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (h : I → Module.End ℂ E), (Formalism.L2.Col.PairComm h → Formalism.L2.Col.PairComm (fun i => (Tw.map s (h i) : Module.End ℂ (Tw s E)))) ∧ (∀ Q : (I → ℂ) → Prop, Formalism.L2.Col.eigSum (fun i => (Tw.map s (h i) : Module.End ℂ (Tw s E))) Q = Tw.sub s (Formalism.L2.Col.eigSum h fun x => Q fun i => cj s (x i))) ∧ ∀ {C : Type} (Ec : C → Submodule ℂ E), Tw.sub s (⨆ c, Ec c) = ⨆ c, Tw.sub s (Ec c) := by
  first | exact @GlobalTheory.TwEig.pairComm_eigSum_sub_iSup | exact GlobalTheory.TwEig.pairComm_eigSum_sub_iSup | (intros; apply GlobalTheory.TwEig.pairComm_eigSum_sub_iSup <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixLatticeIndexIntegralTranslationInvariance
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixLatticeIndexIntegralTranslationInvariance
noncomputable section

namespace GlobalTheory.Hk3.HoweDuality

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem mulVec_mem_intVec_of_int {a b : ℕ} {M : Matrix (Fin a) (Fin b) L}
    (hM : ∀ i j, M i j ∈ Formalism.UG.intL L) {v : Fin b → L} (hv : v ∈ intVec L b) :
    M.mulVec v ∈ intVec L a := by
  rw [mem_intVec] at hv ⊢
  intro i
  change (∑ j, M i j * v j) ∈ Formalism.UG.intL L
  exact sum_mem fun j _ => mul_mem (hM i j) (hv j)

theorem entry_mem_of_mem_GLint {n : ℕ} {g : GL (Fin n) L} (hg : g ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L))
    (i j : Fin n) : (g : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L := by
  obtain ⟨g0, rfl⟩ := hg
  exact ((g0 : Matrix (Fin n) (Fin n) (Formalism.UG.intL L)) i j).2

theorem latIdx_add_int {a b : ℕ} (x u : Matrix (Fin a) (Fin b) L) (hu : u ∈ intMat L a b) :
    latIdx (x + u) = latIdx x := by
  have hf : (fun v : intVec L b =>
      (QuotientAddGroup.mk (Matrix.mulVec (x + u) (v : Fin b → L)) : (Fin a → L) ⧸ intVec L a)) =
      fun v : intVec L b => (QuotientAddGroup.mk (Matrix.mulVec x (v : Fin b → L)) : (Fin a → L) ⧸ intVec L a) := by
    funext v
    rw [Matrix.add_mulVec, QuotientAddGroup.mk_add,
      (QuotientAddGroup.eq_zero_iff _).2 (mulVec_mem_intVec_of_int ((mem_intMat u).1 hu) v.2), add_zero]
  unfold latIdx
  rw [hf]

def quotMul {a : ℕ} (M : Matrix (Fin a) (Fin a) L) (hM : ∀ i j, M i j ∈ Formalism.UG.intL L) :
    (Fin a → L) ⧸ intVec L a →+ (Fin a → L) ⧸ intVec L a :=
  QuotientAddGroup.map (intVec L a) (intVec L a) (Matrix.mulVecLin M).toAddMonoidHom
    fun _ hv => mulVec_mem_intVec_of_int hM hv

theorem quotMul_mk {a : ℕ} (M : Matrix (Fin a) (Fin a) L) (hM : ∀ i j, M i j ∈ Formalism.UG.intL L) (v : Fin a → L) :
    quotMul M hM (QuotientAddGroup.mk v) = QuotientAddGroup.mk (M.mulVec v) := rfl

theorem latIdx_GLint_mul {a b : ℕ} (x : Matrix (Fin a) (Fin b) L) (h : GL (Fin a) L)
    (hh : h ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.intL L)) :
    latIdx ((h : Matrix (Fin a) (Fin a) L) * x) = latIdx x := by
  have h1 := entry_mem_of_mem_GLint hh
  have h2 := entry_mem_of_mem_GLint (inv_mem hh)
  have hinj : Function.Injective (quotMul (h : Matrix (Fin a) (Fin a) L) h1) := by
    have hl : Function.LeftInverse (quotMul ((h⁻¹ : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) h2)
        (quotMul (h : Matrix (Fin a) (Fin a) L) h1) := by
      intro q
      induction q using QuotientAddGroup.induction_on with
      | H v =>
        rw [quotMul_mk, quotMul_mk, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.one_mulVec]
    exact hl.injective
  have hr : (Set.range fun v : intVec L b =>
      (QuotientAddGroup.mk (Matrix.mulVec ((h : Matrix (Fin a) (Fin a) L) * x) (v : Fin b → L)) :
        (Fin a → L) ⧸ intVec L a)) =
      quotMul (h : Matrix (Fin a) (Fin a) L) h1 '' Set.range fun v : intVec L b =>
        (QuotientAddGroup.mk (Matrix.mulVec x (v : Fin b → L)) : (Fin a → L) ⧸ intVec L a) := by
    rw [← Set.range_comp]
    congr 1
    funext v
    exact congrArg QuotientAddGroup.mk (Matrix.mulVec_mulVec _ _ _).symm
  unfold latIdx
  rw [hr, Nat.card_image_of_injective hinj]

theorem latIdx_invariance : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (a b : ℕ) (x : Matrix (Fin a) (Fin b) L),
    (∀ u ∈ GlobalTheory.Hk3.HoweDuality.intMat L a b, GlobalTheory.Hk3.HoweDuality.latIdx (x + u) = GlobalTheory.Hk3.HoweDuality.latIdx x) ∧
    ∀ h : GL (Fin a) L, h ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.intL L) →
      GlobalTheory.Hk3.HoweDuality.latIdx ((h : Matrix (Fin a) (Fin a) L) * x) = GlobalTheory.Hk3.HoweDuality.latIdx x :=
  fun _ _ _ _ _ x => ⟨fun u hu => latIdx_add_int x u hu, fun h hh => latIdx_GLint_mul x h hh⟩

end GlobalTheory.Hk3.HoweDuality

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixLatticeIndexIntegralTranslationInvarianceStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixLatticeIndex_integral_translation_invariance : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (a b : ℕ) (x : Matrix (Fin a) (Fin b) L),
    (∀ u ∈ GlobalTheory.Hk3.HoweDuality.intMat L a b, GlobalTheory.Hk3.HoweDuality.latIdx (x + u) = GlobalTheory.Hk3.HoweDuality.latIdx x) ∧
    ∀ h : GL (Fin a) L, h ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.intL L) →
      GlobalTheory.Hk3.HoweDuality.latIdx ((h : Matrix (Fin a) (Fin a) L) * x) = GlobalTheory.Hk3.HoweDuality.latIdx x := by
  first | exact @GlobalTheory.Hk3.HoweDuality.latIdx_invariance | exact GlobalTheory.Hk3.HoweDuality.latIdx_invariance | (intros; apply GlobalTheory.Hk3.HoweDuality.latIdx_invariance <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConstantCoeffPadicLogSeriesUnramifiedEqZero
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU GlobalTheory.OnePlace Classical

noncomputable section

namespace GlobalTheory.OnePlaceRead

open MvPowerSeries

variable {p : ℕ} [Fact p.Prime]

theorem constantCoeff_psubst {K κ : Type} [CommRing K] {a : MvPowerSeries κ K} (ha : constantCoeff a = 0)
    {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0) : constantCoeff (PowerSeries.subst a f) = 0 := by
  have h := GlobalTheory.BeProps.coeff_subst_range ha f 0
  simpa [hf] using h

theorem constantCoeff_padicLogSeries_unramified_eq_zero : PowerSeries.constantCoeff (FormalGroupSystem.logF p) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [FormalGroupSystem.logF]

theorem constantCoeff_logF_C : PowerSeries.constantCoeff (Formalism.MainNotions.GL3Theta.logF p) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [Formalism.MainNotions.GL3Theta.logF]

theorem map_expS {ι : Type} {f : MvPowerSeries ι (FormalGroupSystem.K0 p)} (hf : constantCoeff f = 0) :
    MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (FormalGroupSystem.expS p f) =
      product_zeroth_first_parts.expS ℂ_[p] (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) f) := by
  have hf' : constantCoeff (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) f) = 0 := by
    simp [hf]
  ext n
  rw [coeff_map]
  unfold product_zeroth_first_parts.expS
  rw [GlobalTheory.BeProps.coeff_subst_range hf']
  have hd : (n.sum fun _ k => k) = n.degree := by
    simp [Finsupp.sum, Finsupp.degree_apply]
  rw [hd]
  change Formalism.L2.G.Pend.k0ToC p (∑ k ∈ Finset.range (n.degree + 1),
    ((k.factorial : FormalGroupSystem.K0 p))⁻¹ * MvPowerSeries.coeff n (f ^ k)) = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_inv₀, map_natCast, PowerSeries.coeff_exp, ← map_pow, coeff_map]
  simp

theorem subst_bivariateSeries_difference_pair {τ : Type} {Eσ : Type} [Finite Eσ] (be : MvPowerSeries (Fin 2) (FormalGroupSystem.K0 p))
    {η : Eσ → MvPowerSeries τ ℂ_[p]} (hη : ∀ i, constantCoeff (η i) = 0) (i j : Eσ) :
    MvPowerSeries.subst η (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p)
      (sub2 p be (MvPowerSeries.X i) (MvPowerSeries.X j))) =
      GlobalTheory.ThBe0.at2 (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) be) (η i) (η j) := by
  have hs : HasSubst η := hasSubst_of_constantCoeff_zero hη
  have h2 : HasSubst (![MvPowerSeries.X i, MvPowerSeries.X j] : Fin 2 → MvPowerSeries Eσ (FormalGroupSystem.K0 p)) := by
    refine hasSubst_of_constantCoeff_zero fun s => ?_
    fin_cases s <;> simp
  have h2' : HasSubst (fun s => MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p)
      ((![MvPowerSeries.X i, MvPowerSeries.X j] : Fin 2 → MvPowerSeries Eσ (FormalGroupSystem.K0 p)) s)) := by
    refine hasSubst_of_constantCoeff_zero fun s => ?_
    fin_cases s <;> simp
  unfold sub2 GlobalTheory.ThBe0.at2
  rw [map_subst h2, subst_comp_subst_apply h2' hs]
  congr 1
  funext s
  fin_cases s <;> simp [subst_X hs]

theorem read_thOne {n' r0 r1 : ℕ} {κ : Type} (B : OmBasis p n') (be : MvPowerSeries (Fin 2) (FormalGroupSystem.K0 p)) (hbe : BeProp p be)
    (U : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) (FormalGroupSystem.K0 p)) (J : Zidx n' r0 r1 → MvPowerSeries κ ℂ_[p])
    (ξ : Eidx n' r0 r1 ⊕ Eidx n' r0 r1 → MvPowerSeries κ ℂ_[p])
    (hJ : ∀ z, MvPowerSeries.constantCoeff (J z) = 0) (hξ : ∀ i, MvPowerSeries.constantCoeff (ξ i) = 0)
    (h : ∀ i, MvPowerSeries.subst J (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (coordZ B (FormalGroupSystem.K0 p) 1 i)) =
      PowerSeries.subst (ξ i) (Formalism.MainNotions.GL3Theta.logF p)) :
    MvPowerSeries.subst J (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (thOne B be U)) =
      product_zeroth_first_parts.expS ℂ_[p] (-(∑ e : Eidx n' r0 r1, GlobalTheory.ThBe0.at2 (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) be)
        (PowerSeries.subst (ξ (Sum.inl e)) (Formalism.MainNotions.GL3Theta.logF p))
        (PowerSeries.subst (ξ (Sum.inr e)) (Formalism.MainNotions.GL3Theta.logF p)))) *
      MvPowerSeries.subst ξ (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (inParam p U)) := by
  have hJs : HasSubst J := hasSubst_of_constantCoeff_zero hJ
  have hξs : HasSubst ξ := hasSubst_of_constantCoeff_zero hξ
  have ha := hasSubst_coordZ (r0 := r0) (r1 := r1) B
  have ha0 : ∀ i, constantCoeff (coordZ B (FormalGroupSystem.K0 p) 1 i : MvPowerSeries (Zidx n' r0 r1) (FormalGroupSystem.K0 p)) = 0 :=
    fun i => (ha.const_coeff i).eq_zero
  have ham : HasSubst (fun i => MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p)
      (coordZ B (FormalGroupSystem.K0 p) 1 i : MvPowerSeries (Zidx n' r0 r1) (FormalGroupSystem.K0 p))) :=
    hasSubst_of_constantCoeff_zero fun i => by simp [ha0 i]
  have hη0 : ∀ i, constantCoeff (PowerSeries.subst (ξ i) (Formalism.MainNotions.GL3Theta.logF p)) = 0 :=
    fun i => constantCoeff_psubst (hξ i) constantCoeff_logF_C
  have hηs : HasSubst (fun i => PowerSeries.subst (ξ i) (Formalism.MainNotions.GL3Theta.logF p)) :=
    hasSubst_of_constantCoeff_zero hη0

  have hbe0 : constantCoeff be = 0 := by
    by_contra hc
    have := (hbe.ab 0 (by simpa using hc)).1
    simp at this
  have hsub0 : ∀ e : Eidx n' r0 r1, constantCoeff (sub2 p be
      (MvPowerSeries.X (Sum.inl e) : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) (FormalGroupSystem.K0 p))
      (MvPowerSeries.X (Sum.inr e))) = 0 := by
    intro e
    have h2 : ∀ s, constantCoeff ((![MvPowerSeries.X (Sum.inl e), MvPowerSeries.X (Sum.inr e)] :
        Fin 2 → MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) (FormalGroupSystem.K0 p)) s) = 0 := by
      intro s; fin_cases s <;> simp
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h2) h2 hbe0
  set Φ : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) (FormalGroupSystem.K0 p) :=
    ∑ e : Eidx n' r0 r1, sub2 p be (MvPowerSeries.X (Sum.inl e)) (MvPowerSeries.X (Sum.inr e)) with hΦ
  have hΦ0 : constantCoeff (-Φ) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_neg, hΦ, map_sum, Finset.sum_eq_zero fun e _ => hsub0 e, neg_zero]
  have hΦm : constantCoeff (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (-Φ)) = 0 := by
    rw [constantCoeff_map, hΦ0, map_zero]

  have hexp : MvPowerSeries.subst (fun i => PowerSeries.subst (ξ i) (Formalism.MainNotions.GL3Theta.logF p))
      (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (FormalGroupSystem.expS p (-Φ))) =
      product_zeroth_first_parts.expS ℂ_[p] (-(∑ e : Eidx n' r0 r1, GlobalTheory.ThBe0.at2 (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) be)
        (PowerSeries.subst (ξ (Sum.inl e)) (Formalism.MainNotions.GL3Theta.logF p))
        (PowerSeries.subst (ξ (Sum.inr e)) (Formalism.MainNotions.GL3Theta.logF p)))) := by
    rw [map_expS hΦ0]
    unfold product_zeroth_first_parts.expS
    rw [ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.subst_exp _ hη0 hΦm]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← coe_substAlgHom hηs, map_neg, map_neg, hΦ, map_sum, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [coe_substAlgHom hηs]
    exact subst_bivariateSeries_difference_pair be hη0 _ _

  have hL0 : ∀ i : Eidx n' r0 r1 ⊕ Eidx n' r0 r1, constantCoeff (PowerSeries.subst
      (MvPowerSeries.X i : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) (FormalGroupSystem.K0 p)) (FormalGroupSystem.logF p)) = 0 :=
    fun i => constantCoeff_psubst (by simp) constantCoeff_padicLogSeries_unramified_eq_zero
  have hLm : ∀ i : Eidx n' r0 r1 ⊕ Eidx n' r0 r1, MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (PowerSeries.subst
      (MvPowerSeries.X i : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) (FormalGroupSystem.K0 p)) (FormalGroupSystem.logF p)) =
      PowerSeries.subst (MvPowerSeries.X i) (Formalism.MainNotions.GL3Theta.logF p) := by
    intro i
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (by simp)), map_X,
      Formalism.L2.G.Pend.logF_map]
  have hLc : ∀ i : Eidx n' r0 r1 ⊕ Eidx n' r0 r1, constantCoeff (PowerSeries.subst
      (MvPowerSeries.X i : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) ℂ_[p]) (Formalism.MainNotions.GL3Theta.logF p)) = 0 :=
    fun i => constantCoeff_psubst (by simp) constantCoeff_logF_C
  have hcof : MvPowerSeries.subst ξ (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (inParam p U)) =
      MvPowerSeries.subst (fun i => PowerSeries.subst (ξ i) (Formalism.MainNotions.GL3Theta.logF p))
        (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) U) := by
    unfold inParam
    rw [map_subst (hasSubst_of_constantCoeff_zero hL0)]
    simp_rw [hLm]
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hLc) hξs]
    congr 1
    funext i
    rw [GlobalTheory.BeProps.subst_psubst hξs (by simp), subst_X hξs]
  rw [hcof, ← hexp, ← subst_mul hηs, ← map_mul]
  unfold thOne ThZ
  rw [map_subst ha, subst_comp_subst_apply ham hJs]
  simp_rw [h]
  rfl

end GlobalTheory.OnePlaceRead

end
end

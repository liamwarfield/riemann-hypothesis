module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocOpSt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationInvariantFunctionalRestrict
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarScalingMultiplicative

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayInD
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayInC
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayInB
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayInA
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct SchwartzMap
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.AwayPf

variable {D : D7} {n : ℕ}

theorem evalPoly_congr {m : ℕ} (p : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ) (τ : D.what₂.Tau)
    (hp : ∀ v ∈ p.vars, v.1 ≠ τ) (z z' : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) (h : ∀ τ', τ' ≠ τ → z τ' = z' τ') :
    evalPoly p z = evalPoly p z' := by
  unfold evalPoly
  change MvPolynomial.eval₂ (RingHom.id ℂ) _ p = MvPolynomial.eval₂ (RingHom.id ℂ) _ p
  apply MvPolynomial.eval₂_congr
  intro i c hi hc
  have hv : i ∈ p.vars := (MvPolynomial.mem_vars_iff_mem_support i).2 ⟨c, (MvPolynomial.mem_support_iff).2 hc, hi⟩
  have e := h i.1 (hp i hv)
  simp only [e]

theorem gAway_congr (V : HSp D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (τ : D.what₂.Tau) (z z' : D.what₂.Tau → Matrix (Fin V.rank) (Fin n) ℂ) (h : ∀ τ', τ' ≠ τ → z τ' = z' τ') :
    gAway V l s τ z = gAway V l s τ z' := by
  classical
  unfold gAway
  congr 2
  refine Finset.sum_congr rfl (fun τ' hτ' => ?_)
  rw [h τ' (Finset.mem_filter.1 hτ').2]

theorem dep (θ : InfFam D) (V : HSp D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (τ : D.what₂.Tau) {Ψ : Mx D V.rank n → ℂ} (hΨ : Ψ ∈ awayA θ V n l s τ) (x x' : Mx D V.rank n)
    (hx : ∀ τ', τ' ≠ τ → compAt θ τ' x = compAt θ τ' x') (hf : x.map (finPart D) = x'.map (finPart D)) :
    Ψ x = Ψ x' := by
  induction hΨ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨p, g, _, hp, rfl⟩ := hφ
    simp only
    have hf' : (fun i j => finPart D (x i j)) = (fun i j => finPart D (x' i j)) := hf
    rw [evalPoly_congr p τ hp _ _ hx, gAway_congr V l s τ _ _ hx, hf']
  | zero => rfl
  | add a b _ _ ha hb => simp only [Pi.add_apply, ha, hb]
  | smul c a _ ha => simp only [Pi.smul_apply, ha]

end PositivityTheory.Rg.Sw.Glob.AwayPf
end
end

noncomputable section

open scoped Matrix ComplexConjugate SchwartzMap
open Matrix

namespace PositivityTheory.Rg.Sw.Glob.AwayPf

section
variable {T : Type} [Fintype T] [DecidableEq T] {m n : ℕ} (τ : T)

abbrev Bsp (τ : T) (m n : ℕ) : Type := {τ' : T // τ' ≠ τ} → Fin m → Fin n → ℂ

def extF (b : Bsp τ m n) : T → Fin m → Fin n → ℂ := fun τ' => if h : τ' = τ then 0 else b ⟨τ', h⟩

def extL : Bsp τ m n →L[ℝ] (T → Fin m → Fin n → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := extF τ
      map_add' := fun b b' => by
        funext τ' i j
        by_cases h : τ' = τ <;> simp [extF, h]
      map_smul' := fun r b => by
        funext τ' i j
        by_cases h : τ' = τ <;> simp [extF, h] }

def coordL (k : T × Fin m × Fin n) : Bsp τ m n →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) k.2.2).comp
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) k.2.1).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : T => Fin m → Fin n → ℂ) k.1).comp (extL τ)))

theorem tg_eval {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {σ : Type} (v : σ → E → ℂ)
    (hv : ∀ k, (v k).HasTemperateGrowth) (p : MvPolynomial σ ℂ) :
    (fun x => MvPolynomial.eval (fun k => v k x) p).HasTemperateGrowth := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    have := Function.HasTemperateGrowth.const (E := E) a
    convert this using 1
    all_goals first | rfl | (funext x; simp)
  | add p q hp hq =>
    have := hp.add hq
    convert this using 1
    all_goals first | rfl | (funext x; simp)
  | mul_X p k hp =>
    have := hp.mul (hv k)
    convert this using 1
    all_goals first | rfl | (funext x; simp)

def vC (k : T × Fin m × Fin n × Bool) (b : Bsp τ m n) : ℂ :=
  if k.2.2.2 then conj (coordL τ (k.1, k.2.1, k.2.2.1) b) else coordL τ (k.1, k.2.1, k.2.2.1) b

theorem tg_vC (k : T × Fin m × Fin n × Bool) : (vC (m := m) (n := n) τ k).HasTemperateGrowth := by
  by_cases hk : k.2.2.2 = true
  · have e : vC (m := m) (n := n) τ k = ⇑(Complex.conjCLE.toContinuousLinearMap.comp (coordL τ (k.1, k.2.1, k.2.2.1))) := by
      funext b
      simp [vC, hk]
    rw [e]
    exact ContinuousLinearMap.hasTemperateGrowth _
  · have e : vC (m := m) (n := n) τ k = ⇑(coordL τ (k.1, k.2.1, k.2.2.1)) := by
      funext b
      simp [vC, hk]
    rw [e]
    exact ContinuousLinearMap.hasTemperateGrowth _

theorem tg_poly (p : MvPolynomial (T × Fin m × Fin n × Bool) ℂ) :
    (fun b : Bsp τ m n => MvPolynomial.eval (fun k => vC τ k b) p).HasTemperateGrowth :=
  tg_eval _ (tg_vC τ) p

variable (fr : Matrix (Fin m) (Fin m) ℂ)

def eL (hfr : IsUnit fr.det) : (T → Fin m → Fin n → ℂ) ≃ₗ[ℝ] ((Fin m → Fin n → ℂ) × Bsp τ m n) where
  toFun z := (Matrix.of.symm (fr⁻¹ * Matrix.of (z τ)), fun τ' => z τ'.1)
  invFun ab := fun τ' => if h : τ' = τ then Matrix.of.symm (fr * Matrix.of ab.1) else ab.2 ⟨τ', h⟩
  map_add' z w := by
    ext1
    · exact Matrix.mul_add fr⁻¹ (of (z τ)) (of (w τ))
    · rfl
  map_smul' r z := by
    ext1
    · exact Matrix.mul_smul fr⁻¹ r (of (z τ))
    · rfl
  left_inv z := by
    funext τ'
    by_cases h : τ' = τ
    · subst h
      simp
      change (fr * (fr⁻¹ * of (z τ'))).row = (of (z τ')).row
      rw [Matrix.mul_nonsing_inv_cancel_left fr _ hfr]
    · simp [h]
  right_inv ab := by
    ext1
    · simp
      change (fr⁻¹ * (fr * of ab.1)).row = (of ab.1).row
      rw [Matrix.nonsing_inv_mul_cancel_left fr _ hfr]
    · funext τ'
      simp [τ'.2]

end

end PositivityTheory.Rg.Sw.Glob.AwayPf
end
end

noncomputable section

open scoped Matrix ComplexConjugate SchwartzMap ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob.AwayPf

theorem diag_eq {m n : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) (j : Fin n) :
    (Mᴴ * A * M) j j = star (fun a => M a j) ⬝ᵥ (A *ᵥ fun a => M a j) := by
  simp only [Matrix.mul_apply, dotProduct, mulVec, Matrix.conjTranspose_apply, Pi.star_apply, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  ring

theorem tr_re_nonneg {m n : ℕ} {A : Matrix (Fin m) (Fin m) ℂ} (hA : A.PosDef) (M : Matrix (Fin m) (Fin n) ℂ) :
    0 ≤ (trace (Mᴴ * A * M)).re ∧ (M ≠ 0 → 0 < (trace (Mᴴ * A * M)).re) := by
  have hsum : (trace (Mᴴ * A * M)).re = ∑ j, (star (fun a => M a j) ⬝ᵥ (A *ᵥ fun a => M a j)).re := by
    rw [Matrix.trace, Complex.re_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Matrix.diag_apply, diag_eq]
  have hnn : ∀ j, 0 ≤ (star (fun a => M a j) ⬝ᵥ (A *ᵥ fun a => M a j)).re := by
    intro j
    by_cases hv : (fun a => M a j) = 0
    · rw [hv]
      simp
    · exact (hA.re_dotProduct_pos hv).le
  refine ⟨hsum ▸ Finset.sum_nonneg (fun j _ => hnn j), fun hM => ?_⟩
  obtain ⟨j, hj⟩ : ∃ j, (fun a => M a j) ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply hM
    ext a j
    exact congrFun (hc j) a
  rw [hsum]
  exact Finset.sum_pos' (fun j _ => hnn j) ⟨j, Finset.mem_univ _, hA.re_dotProduct_pos hj⟩

theorem tr_re_symm {m n : ℕ} {A : Matrix (Fin m) (Fin m) ℂ} (hA : A.IsHermitian) (M N : Matrix (Fin m) (Fin n) ℂ) :
    (trace (Mᴴ * A * N)).re = (trace (Nᴴ * A * M)).re := by
  have h : (Mᴴ * A * N)ᴴ = Nᴴ * A * M := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hA.eq,
      Matrix.mul_assoc]
  rw [← h, Matrix.trace_conjTranspose]
  simp

theorem tr_im_zero {m n : ℕ} {A : Matrix (Fin m) (Fin m) ℂ} (hA : A.IsHermitian) (M : Matrix (Fin m) (Fin n) ℂ) :
    trace (Mᴴ * A * M) = ((trace (Mᴴ * A * M)).re : ℂ) := by
  have h : star (trace (Mᴴ * A * M)) = trace (Mᴴ * A * M) := by
    rw [← Matrix.trace_conjTranspose]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hA.eq, Matrix.mul_assoc]
  have him : (trace (Mᴴ * A * M)).im = 0 := by
    have := congrArg Complex.im h
    simp at this
    linarith
  apply Complex.ext <;> simp [him]

section
variable {T : Type} [Fintype T] [DecidableEq T] {m n : ℕ} (τ : T)

def qf (A : T → Matrix (Fin m) (Fin m) ℂ) (w : T → ℝ) (b b' : Bsp τ m n) : ℝ :=
  ∑ t : {τ' : T // τ' ≠ τ}, w t.1 * (trace ((of (b t))ᴴ * A t.1 * of (b' t))).re

def Qf (A : T → Matrix (Fin m) (Fin m) ℂ) (w : T → ℝ) : LinearMap.BilinForm ℝ (Bsp τ m n) :=
  LinearMap.mk₂ ℝ (fun b b' => 2 * qf τ A w b b')
    (fun b₁ b₂ b' => by
      simp only [qf, ← mul_add, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl (fun t _ => ?_)
      congr 1
      rw [← Complex.add_re, ← Matrix.trace_add, ← Matrix.add_mul, ← Matrix.add_mul, ← Matrix.conjTranspose_add]
      rfl)
    (fun r b b' => by
      simp only [qf, Finset.mul_sum, smul_eq_mul]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      have : (of ((r • b) t))ᴴ = (r : ℂ) • (of (b t))ᴴ := by
        rw [show of ((r • b) t) = (r : ℂ) • of (b t) from by ext i j; simp [Complex.real_smul]]
        rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal]
      rw [this, Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
      ring)
    (fun b b₁ b₂ => by
      simp only [qf, ← mul_add, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl (fun t _ => ?_)
      congr 1
      rw [← Complex.add_re, ← Matrix.trace_add, ← Matrix.mul_add]
      rfl)
    (fun r b b' => by
      simp only [qf, Finset.mul_sum, smul_eq_mul]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      have : of ((r • b') t) = (r : ℂ) • of (b' t) := by ext i j; simp [Complex.real_smul]
      rw [this, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
      ring)

theorem Qf_apply (A : T → Matrix (Fin m) (Fin m) ℂ) (w : T → ℝ) (b b' : Bsp τ m n) :
    Qf τ A w b b' = 2 * qf τ A w b b' := rfl

theorem Qf_symm (A : T → Matrix (Fin m) (Fin m) ℂ) (hA : ∀ t, t ≠ τ → (A t).IsHermitian) (w : T → ℝ)
    (b b' : Bsp τ m n) : Qf τ A w b b' = Qf τ A w b' b := by
  rw [Qf_apply, Qf_apply]
  congr 1
  unfold qf
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [tr_re_symm (hA t.1 t.2)]

theorem Qf_pos (A : T → Matrix (Fin m) (Fin m) ℂ) (hA : ∀ t, t ≠ τ → (A t).PosDef) (w : T → ℝ)
    (hw : ∀ t, t ≠ τ → 0 < w t) (b : Bsp τ m n) (hb : b ≠ 0) : 0 < Qf τ A w b b := by
  rw [Qf_apply]
  have hnn : ∀ t : {τ' : T // τ' ≠ τ}, 0 ≤ w t.1 * (trace ((of (b t))ᴴ * A t.1 * of (b t))).re :=
    fun t => mul_nonneg (hw t.1 t.2).le (tr_re_nonneg (hA t.1 t.2) _).1
  obtain ⟨t, ht⟩ : ∃ t, b t ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hb (funext hc)
  have hof : of (b t) ≠ 0 := by
    intro h0
    apply ht
    funext i j
    exact congrFun (congrFun h0 i) j
  have hpos : 0 < qf τ A w b b :=
    Finset.sum_pos' (fun t _ => hnn t)
      ⟨t, Finset.mem_univ _, mul_pos (hw t.1 t.2) ((tr_re_nonneg (hA t.1 t.2) _).2 hof)⟩
  linarith

theorem exists_gauss (A : T → Matrix (Fin m) (Fin m) ℂ) (hA : ∀ t, t ≠ τ → (A t).PosDef) (w : T → ℝ)
    (hw : ∀ t, t ≠ τ → 0 < w t) :
    ∃ G : 𝓢(Bsp τ m n, ℂ), ∀ b, G b = Complex.exp (-(Real.pi : ℂ) * ((2 * qf τ A w b b : ℝ) : ℂ)) := by
  obtain ⟨G, hG⟩ := GlobalTheory.ThK.EvAt0.GaussForm.exists_schwartz_gauss_form (Qf τ A w)
    (Qf_symm τ A (fun t ht => (hA t ht).isHermitian) w) (fun b hb => Qf_pos τ A hA w hw b hb)
  refine ⟨G, fun b => ?_⟩
  rw [(hG b).1, Qf_apply]

end

end PositivityTheory.Rg.Sw.Glob.AwayPf
end
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct SchwartzMap ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.AwayPf

variable {D : D7} {n : ℕ}

open Classical in
theorem gen_sch (θ : InfFam D) (V : HSp D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (τ : D.what₂.Tau) (fr : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hfr : IsUnit fr.det)
    (hs : ∀ τ, IsCartanInv (gramAt D V τ) (s τ)) (hl : ∀ τ', l τ' ≠ 0)
    (p : MvPolynomial (D.what₂.Tau × Fin V.rank × Fin n × Bool) ℂ) (hp : ∀ v ∈ p.vars, v.1 ≠ τ)
    (g : (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E))
    (f : (Fin V.rank → Fin n → ℂ) → ℂ) (hf : IsSch f) :
    tens θ τ fr f (fun x => evalPoly p (fun τ => compAt θ τ x) * gAway V l s τ (fun τ => compAt θ τ x) *
      g (fun i j => finPart D (x i j))) ∈ schwartzA θ V.rank n := by
  obtain ⟨S, hS⟩ := hf
  set A : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ := fun t => gramAt D V t * s t with hAdef
  have hA : ∀ t, t ≠ τ → (A t).PosDef := fun t _ => (hs t).2.2
  have hw : ∀ t, t ≠ τ → 0 < |l t| := fun t _ => abs_pos.mpr (hl t)
  obtain ⟨G, hG⟩ := exists_gauss (n := n) τ A hA (fun t => |l t|) hw
  set poly : Bsp τ V.rank n → ℂ := fun b => MvPolynomial.eval (fun k => vC τ k b) p with hpoly
  have hpolyT : poly.HasTemperateGrowth := tg_poly τ p
  set h : 𝓢(Bsp τ V.rank n, ℂ) := SchwartzMap.smulLeftCLM ℂ poly G with hh
  have hhv : ∀ b, h b = poly b * G b := fun b => by
    rw [hh, SchwartzMap.smulLeftCLM_apply_apply hpolyT, smul_eq_mul]
  obtain ⟨Fp, hFp⟩ := GlobalTheory.SchwartzHadamard.exists_schwartz_prod S h
  let e₀ : (D.what₂.Tau → Fin V.rank → Fin n → ℂ) ≃ₗ[ℝ]
      ((Fin V.rank → Fin n → ℂ) × Bsp τ V.rank n) :=
    { toFun := fun z => (Matrix.of.symm (fr⁻¹ * Matrix.of (z τ)), fun t => z t.1)
      invFun := fun ab t => if ht : t = τ then Matrix.of.symm (fr * Matrix.of ab.1) else ab.2 ⟨t, ht⟩
      map_add' := fun z w => by
        ext1
        · exact Matrix.mul_add fr⁻¹ (Matrix.of (z τ)) (Matrix.of (w τ))
        · rfl
      map_smul' := fun r z => by
        ext1
        · exact Matrix.mul_smul fr⁻¹ r (Matrix.of (z τ))
        · rfl
      left_inv := fun z => by
        funext t
        by_cases ht : t = τ
        · subst t
          simp
          change (fr * (fr⁻¹ * Matrix.of (z τ))).row = (Matrix.of (z τ)).row
          rw [Matrix.mul_nonsing_inv_cancel_left fr _ hfr]
        · simp [ht]
      right_inv := fun ab => by
        ext1
        · simp
          change (fr⁻¹ * (fr * Matrix.of ab.1)).row = (Matrix.of ab.1).row
          rw [Matrix.nonsing_inv_mul_cancel_left fr _ hfr]
        · funext t
          simp [t.2] }
  let e := e₀.toContinuousLinearEquiv
  let Fz : 𝓢(D.what₂.Tau → Fin V.rank → Fin n → ℂ, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e Fp
  have hFz : ∀ z, Fz z = S (Matrix.of.symm (fr⁻¹ * Matrix.of (z τ))) * (poly (fun t => z t.1) * G (fun t => z t.1)) := by
    intro z
    simp only [Fz, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, hFp, hhv]
    rfl
  have hpolyz : ∀ z : D.what₂.Tau → Fin V.rank → Fin n → ℂ,
      poly (fun t => z t.1) = evalPoly p (fun t => Matrix.of (z t)) := by
    intro z
    rw [evalPoly_congr p τ hp (fun t => Matrix.of (z t)) (extF τ (fun t => z t.1)) (fun t ht => by simp only [extF, dif_neg ht]; rfl)]
    rfl
  have hGz : ∀ z : D.what₂.Tau → Fin V.rank → Fin n → ℂ,
      G (fun t => z t.1) = gAway V l s τ (fun t => Matrix.of (z t)) := by
    intro z
    rw [hG]
    unfold gAway qf
    congr 1
    rw [Finset.sum_subtype _ (p := fun τ' => τ' ≠ τ) (fun x => by simp)]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [← tr_im_zero (hA t.1 t.2).isHermitian (Matrix.of (z t.1))]
    simp only [hAdef]
    ring
  have key : ∀ z : D.what₂.Tau → Fin V.rank → Fin n → ℂ, Fz z = f (Matrix.of.symm (fr⁻¹ * Matrix.of (z τ))) *
      (evalPoly p (fun t => Matrix.of (z t)) * gAway V l s τ (fun t => Matrix.of (z t))) := by
    intro z
    rw [hFz, hpolyz, hGz, hS]
  refine Submodule.subset_span ⟨Fz, g, hg, ?_⟩
  funext x
  rw [key]
  simp only [tens, mul_assoc]
  rfl

end PositivityTheory.Rg.Sw.Glob.AwayPf
end
end

noncomputable section

open scoped Matrix ComplexConjugate
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

theorem awayIn : AwayIn := by
  intro D n V θ l s τ ε fr hθ hs hfr hl Ψ hΨ
  refine ⟨fun x x' hx hf => AwayPf.dep θ V l s τ hΨ x x' hx hf, fun f hf => ?_⟩
  induction hΨ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨p, g, hg, hp, rfl⟩ := hφ
    exact AwayPf.gen_sch θ V l s τ fr hfr.1 hs hl p hp g hg f hf
  | zero =>
    have : tens θ τ fr f (0 : Mx D V.rank n → ℂ) = 0 := by
      funext x
      simp [tens]
    rw [this]
    exact Submodule.zero_mem _
  | add a b _ _ ha hb =>
    have : tens θ τ fr f (a + b) = tens θ τ fr f a + tens θ τ fr f b := by
      funext x
      simp only [tens, Pi.add_apply, mul_add]
    rw [this]
    exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
    have : tens θ τ fr f (c • a) = c • tens θ τ fr f a := by
      funext x
      simp only [tens, Pi.smul_apply, smul_eq_mul]
      ring
    rw [this]
    exact Submodule.smul_mem _ c ha

end PositivityTheory.Rg.Sw.Glob

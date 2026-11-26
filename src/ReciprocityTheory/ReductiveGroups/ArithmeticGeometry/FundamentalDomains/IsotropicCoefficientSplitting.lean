module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.AdmissibleHermitianColumns

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex Metric
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace Data

variable {r : ℕ} (X : Data E r)

def IsOrtho (x : Frame X.Ψ r) : Prop :=
  ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x τ) = Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)

abbrev Coord : Type := X.Ψ → Fin (r - X.p0) → Fin X.p0 → ℂ

def lowBlock (Z : X.Coord) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a b => (if a = b then 1 else 0) +
    if h : X.p0 ≤ (a : ℕ) ∧ (b : ℕ) < X.p0 then
      Z τ ⟨(a : ℕ) - X.p0, by have := a.isLt; omega⟩ ⟨b, h.2⟩ else 0

def xZ (x : Frame X.Ψ r) (Z : X.Coord) : Frame X.Ψ r :=
  fun τ => (mat x τ * X.lowBlock Z τ : Matrix (Fin r) (Fin r) ℂ)

def opN {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) : ℝ :=
  sSup {t | ∃ v : Fin n → ℂ, v ≠ 0 ∧
    t = Real.sqrt (∑ i, ‖Matrix.mulVec A v i‖ ^ 2) / Real.sqrt (∑ j, ‖v j‖ ^ 2)}

def zN (Z : X.Coord) : ℝ := ⨆ τ : X.Ψ, opN (Matrix.of (Z τ))

end Data

def OrthonormalFlagTranslate : Prop :=
  ∀ (r : ℕ) (X : Data E r),
    (∀ x ∈ X.dom, ∃ b ∈ Bor X.Ψ r, X.IsOrtho (rmul x b)) ∧
    (∀ (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ),
      (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, P (rmul x b) = bchar la b * P x) →
      ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, X.pnorm la P (rmul x b) = X.pnorm la P x) ∧
    ∀ x ∈ X.dom, ∀ x' ∈ X.dom, X.SameFlag x x' → (∀ ξ : Fin r → E,
      X.Jz x = X.Jz x' ∧ X.Uz x ξ = X.Uz x' ξ ∧ X.aproj x ξ = X.aproj x' ξ) ∧ X.maj x = X.maj x'

def OrthonormalChartNormControl : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x : Frame X.Ψ r), x ∈ X.dom → X.IsOrtho x → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / 10 →
    (∀ Z : X.Coord, X.zN Z ≤ ρ →
      X.xZ x Z ∈ X.dom ∧
      (∀ (la : Wt X.Ψ r) (w : ℝ), (∑ τ, X.spread la τ) ≤ w →
        |Real.log (X.nfac la (X.xZ x Z)) - Real.log (X.nfac la x)| ≤ 4 * w * r * X.zN Z ^ 2) ∧
      ∀ τ v, (1 - ρ) / (1 + ρ) * X.maj x τ v ≤ X.maj (X.xZ x Z) τ v ∧
        X.maj (X.xZ x Z) τ v ≤ (1 + ρ) / (1 - ρ) * X.maj x τ v) ∧
    ∀ G : Frame X.Ψ r → ℂ, DifferentiableOn ℂ G X.dom →
      DifferentiableOn ℂ (fun Z : X.Coord => G (X.xZ x Z)) {Z | X.zN Z < ρ}

def NearSupremumTransference : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (ν : X.Ψ → ℝ)
    (c1 w : ℝ) (z0 : Frame X.Ψ r), ShortVectorHypotheses X la P ξ ν c1 w z0 →
    ∀ x' ∈ X.dom, (∀ τ, (1 - d6rh c1 w) / (1 + d6rh c1 w) ≤ X.tt ξ x' τ ∧
      X.tt ξ x' τ ≤ (1 + d6rh c1 w) / (1 - d6rh c1 w)) →
    X.hatN la (X.fj la ξ ν P) x' ≤
      Real.exp 2 * sSup {t | ∃ y ∈ X.FramesOverBasis ξ, t = X.hatN la (X.fj la ξ ν P) y}

def SchwarzLemmaBall : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (γ : V → ℂ) (ρ S : ℝ), 0 < ρ →
    DifferentiableOn ℂ γ (closedBall 0 ρ) → (∀ Z ∈ closedBall (0 : V) ρ, ‖γ Z‖ ≤ Real.exp (9 / 4) * S) →
    S / 2 < ‖γ 0‖ → ‖γ 0‖ ≤ S → ∀ Z ∈ ball (0 : V) (ρ / 21), γ Z ≠ 0

def SplitData {r : ℕ} (X : DataX E r) (ξ : Fin r → E) (La : ℝ) (z : Frame X.Ψ r)
    (lam : Fin (r - 2) → Fin r → E) : Prop :=
  (∀ j, lam j ∈ X.L' ∧ herm X.Gm (lam j) ξ = 0) ∧
  LinearIndependent E (Fin.cons ξ lam : Fin (r - 2 + 1) → Fin r → E) ∧
  (∀ j k : Fin (r - 2), (j : ℕ) < X.p0 - 1 → X.p0 - 1 ≤ (k : ℕ) → herm X.Gm (lam j) (lam k) = 0) ∧
  (∀ j : Fin (r - 2), (j : ℕ) < X.p0 - 1 → (∀ τ : X.Ψ, 0 < (τ.1 (herm X.Gm (lam j) (lam j))).re) ∧
    X.Jz z (X.ucomp z ξ (X.embV (lam j))) = I • X.ucomp z ξ (X.embV (lam j))) ∧
  (∀ j : Fin (r - 2), X.p0 - 1 ≤ (j : ℕ) → (∀ τ : X.Ψ, (τ.1 (herm X.Gm (lam j) (lam j))).re < 0) ∧
    X.Jz z (X.ucomp z ξ (X.embV (lam j))) = -(I • X.ucomp z ξ (X.embV (lam j)))) ∧
  ∀ j (τ : X.Ψ), ‖τ.1 (herm X.Gm (lam j) (lam j))‖ ≤ La ^ 2

def OrthonormalShortVectorBound : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (ν : X.Ψ → ℝ)
    (c1 w : ℝ) (z0 : Frame X.Ψ r), ShortVectorHypotheses X la P ξ ν c1 w z0 →
    ∀ x0 ∈ X.dom, X.IsOrtho x0 → X.SameFlag z0 x0 →
    ∃ (lam : Fin (r - 2) → Fin r → E) (h1 : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (Z1 : X.Coord),
      X.IsUnitaryC h1 ∧
      (∀ s t : X.Ψ → ℂ, X.applyV h1 (X.lineV ξ s + X.Jz z0 (X.lineV ξ t)) =
        X.lineV ξ s + X.Jz z0 (X.lineV ξ t)) ∧
      (∀ u ∈ X.Uz z0 ξ, X.applyV h1 u ∈ X.Uz z0 ξ) ∧
      SplitData X ξ (d6La r X.p0 (fdeg E) (dE E) (flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w) (d6rh c1 w))
        (X.lmulC h1 z0) lam ∧
      X.SameFlag (X.lmulC h1 z0) (X.xZ x0 Z1) ∧ X.zN Z1 ≤ d6rh c1 w / 100

def IsotropicCoefficientSplitting : Prop :=
  ∀ (r : ℕ) (X : Data E r) (ξ : Fin r → E), X.IsIso ξ →
    ∃ f : (Fin r → E) → E, (∀ μ ∈ X.Λp ξ, f μ • ξ ∈ X.Λ) ∧
      (∀ μ ∈ X.Λp ξ, ∀ μ' ∈ X.Λp ξ, f (μ + μ') = f μ + f μ') ∧
      (∀ (α : 𝓞 E), ∀ μ ∈ X.Λp ξ, f ((α : E) • μ) = α * f μ) ∧
      ∀ e : E, e • ξ ∈ X.Λ → f (e • ξ) = e

def NoShortVectorLowerBound : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (ξ : Fin r → E) (ep0 : ℝ), X.IsIso ξ → 0 < ep0 → ∀ z ∈ X.FramesOverBasis ξ,
    (∀ x ∈ X.L', herm X.Gm x ξ = 0 → (∀ e : E, x ≠ e • ξ) →
      ∃ τ : X.Ψ, ep0 ≤ X.maj z τ (X.ucomp z ξ (X.embV x) τ)) →
    ∀ δ : X.Ψ → (Fin r → ℂ) →ₗ[ℂ] ℂ, ∃ μ ∈ X.Λp ξ, ∀ u ∈ X.Uz z ξ, ∀ τ : X.Ψ,
      X.maj z τ ((δ τ (u τ) - (dE E : ℂ) * (-τ.1 X.ξ0) *
          hermC τ.1 X.Gm (u τ) (X.ucomp z ξ (X.embV μ) τ)) • Data.emb τ.1 ξ) ≤
        frameIndexBound r (fdeg E) (dE E) (rdE E) X.NA X.NC ep0 ^ 2 * X.maj z τ (u τ)

def UnitaryUnipotentMove : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (ν : X.Ψ → ℝ)
    (c1 w : ℝ) (z0 : Frame X.Ψ r), ShortVectorHypotheses X la P ξ ν c1 w z0 →
    ∀ x0 ∈ X.dom, X.IsOrtho x0 → X.SameFlag z0 x0 →
    ∀ (lam : Fin (r - 2) → Fin r → E) (h1 : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (Z1 : X.Coord),
      X.IsUnitaryC h1 →
      (∀ s t : X.Ψ → ℂ, X.applyV h1 (X.lineV ξ s + X.Jz z0 (X.lineV ξ t)) =
        X.lineV ξ s + X.Jz z0 (X.lineV ξ t)) →
      (∀ u ∈ X.Uz z0 ξ, X.applyV h1 u ∈ X.Uz z0 ξ) →
      SplitData X ξ (d6La r X.p0 (fdeg E) (dE E) (flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w) (d6rh c1 w))
        (X.lmulC h1 z0) lam →
      X.SameFlag (X.lmulC h1 z0) (X.xZ x0 Z1) → X.zN Z1 ≤ d6rh c1 w / 100 →
      ∀ n' : ℕ, 1000 * frameIndexBound r (fdeg E) (dE E) (rdE E) X.NA X.NC
          (flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w) / d6rh c1 w ≤ n' →
      ∃ (n : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (Z : X.Coord),
        X.IsUnitaryC n ∧ (∀ τ, Matrix.mulVec (n τ) (Data.emb τ.1 ξ) = Data.emb τ.1 ξ) ∧
        (∀ μ ∈ X.Λp ξ, ∃ e : E, e • ξ ∈ X.Λ ∧
          (n' : ℂ) • X.aproj (X.lmulC n (X.lmulC h1 z0)) ξ (X.embV μ) = X.embV (e • ξ)) ∧
        SplitData X ξ (d6La r X.p0 (fdeg E) (dE E) (flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w)
          (d6rh c1 w)) (X.lmulC n (X.lmulC h1 z0)) lam ∧
        X.SameFlag (X.lmulC n (X.lmulC h1 z0)) (X.xZ x0 Z) ∧ X.zN Z < d6rh c1 w / 21

end

end ReciprocityTheory.ChartRestriction.G.FD
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.TransvectionPeriodicity
namespace ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
  ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

lemma emb_kappa (X : Data E r) (τ : X.Ψ) : τ.1 X.κ0 = -(I * X.c τ) := by

  have hre : (τ.1 X.κ0).re = 0 := by
    have h1 : conj (τ.1 X.κ0) = -(τ.1 X.κ0) := by
      have hξ : IsCMField.complexConj E X.ξ0 = -X.ξ0 := X.ξ0_im
      rw [← emb_cc']
      rcases X.κ0_xi with h | h <;> rw [h] <;> simp [cc, hξ, map_mul, map_neg, map_ofNat]
    have := congrArg Complex.re h1
    simp at this
    linarith
  have hz : τ.1 X.κ0 = ((τ.1 X.κ0).im : ℂ) * I := by
    apply Complex.ext <;> simp [hre]
  have hn : ‖τ.1 X.κ0‖ = |(τ.1 X.κ0).im| := by
    conv_lhs => rw [hz]
    simp
  have hnorm : ‖τ.1 X.κ0‖ = X.c τ := by
    unfold Data.c
    rcases X.κ0_xi with h | h <;> rw [h] <;> simp [norm_mul, map_ofNat]
  have him := X.κ0_sign τ
  rw [hn, abs_of_neg him] at hnorm
  rw [hz, ← hnorm]
  push_cast
  ring

lemma transvMat_mul (G : Matrix (Fin r) (Fin r) E) {ξ : Fin r → E} (hξ : herm G ξ ξ = 0)
    (α β : E) : transvMat G ξ α * transvMat G ξ β = transvMat G ξ (α + β) := by
  set w : Fin r → E := fun b => ∑ k, G b k * cc (ξ k) with hw
  have hA : ∀ γ, transvMat G ξ γ = 1 + γ • Matrix.vecMulVec ξ w := by
    intro γ
    ext a b
    simp only [transvMat, Matrix.of_apply, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, smul_eq_mul, hw]
    ring
  have h0 : ∑ j, w j * ξ j = 0 := by
    rw [← hξ]
    unfold herm
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hw, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring

  have hAA : Matrix.vecMulVec ξ w * Matrix.vecMulVec ξ w = 0 := by
    ext a b
    simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.zero_apply]
    calc ∑ j, ξ a * w j * (ξ j * w b) = ξ a * w b * ∑ j, w j * ξ j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := by rw [h0, mul_zero]
  rw [hA, hA, hA, add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, smul_mul_smul_comm, hAA,
    smul_zero, add_zero, add_smul]
  abel

lemma transvMat_zero (G : Matrix (Fin r) (Fin r) E) (ξ : Fin r → E) : transvMat G ξ 0 = 1 := by
  ext a b
  simp [transvMat, Matrix.one_apply]

lemma transvMat_pow (G : Matrix (Fin r) (Fin r) E) {ξ : Fin r → E} (hξ : herm G ξ ξ = 0)
    (α : E) (n : ℕ) : transvMat G ξ α ^ n = transvMat G ξ (n * α) := by
  induction n with
  | zero => simp [transvMat_zero]
  | succ k ih =>
    rw [pow_succ, ih, transvMat_mul G hξ]
    congr 1
    push_cast
    ring

lemma transvMat_map (X : Data E r) (ξ : Fin r → E) (τ : X.Ψ) (α : E) (s : ℂ)
    (hs : τ.1 α = -(I * X.c τ * s)) :
    (transvMat X.Gm ξ α).map τ.1 = X.flowMat ξ τ s := by
  ext a b
  simp only [Matrix.map_apply, transvMat, Data.flowMat, Matrix.of_apply]
  split_ifs <;> simp [map_sum, emb_cc', hs] <;> ring

variable (X : Data E r)

def cR (p : X.Ψ → ℝ) : X.Ψ → ℂ := fun τ => (p τ : ℂ)

lemma flow_real_mem_dom {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (p : X.Ψ → ℝ) (y : Frame X.Ψ r)
    (hy : y ∈ X.dom) : X.flow ξ (cR X p) y ∈ X.dom := by
  have h0 := (flow_mem_dom_iff X hξ y hy 0).1 (by rw [flow_zero]; exact hy)
  have e : (fun τ => (cR X p τ).im) = fun τ => ((0 : X.Ψ → ℂ) τ).im := by
    funext τ
    simp [cR]
  rw [flow_mem_dom_iff X hξ y hy, e]
  exact h0

lemma chi_pow (la : Wt X.Ψ r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) (n : ℕ) :
    X.χ la (γ ^ n) = X.χ la γ ^ n := by
  have h1 : X.χ la 1 = 1 := by
    obtain ⟨N, hN, hfin⟩ := X.χ_fin la
    have hne : X.χ la 1 ≠ 0 := by
      intro h
      have := hfin 1 X.Γ.one_mem
      rw [h, zero_pow hN.ne'] at this
      exact zero_ne_one this
    have hsq := X.χ_mul la 1 X.Γ.one_mem 1 X.Γ.one_mem
    rw [mul_one] at hsq
    exact mul_left_cancel₀ hne (hsq.symm.trans (mul_one _).symm)
  induction n with
  | zero => simp [h1]
  | succ k ih => rw [pow_succ, X.χ_mul la _ (X.Γ.pow_mem hγ k) _ hγ, ih, pow_succ]

lemma sec_periodic_gen (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : X.IsSec la P) {ξ : Fin r → E}
    (hξΛ : ξ ∈ X.Λ) (hξ : herm X.Gm ξ ξ = 0) (a : E) (ha : cc a = a) (hai : IsIntegral ℤ a)
    (y : Frame X.Ψ r) (hy : y ∈ X.dom) :
    P (X.flow ξ (cR X fun τ => ((X.m * X.chiOrd la : ℕ) : ℝ) * (τ.1 a).re) y) = P y := by
  obtain ⟨γ0, hγ0, hγ0m⟩ := X.transv ξ hξΛ hξ a ha hai
  have hγ : γ0 ^ X.chiOrd la ∈ X.Γ := X.Γ.pow_mem hγ0 _
  have hχ : X.χ la (γ0 ^ X.chiOrd la) = 1 := by
    rw [chi_pow X la hγ0]
    exact (X.χ_fin la).choose_spec.2 γ0 hγ0
  have hmat : ((γ0 ^ X.chiOrd la : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) =
      transvMat X.Gm ξ ((X.chiOrd la : E) * ((X.m : E) * a * X.κ0)) := by
    rw [Units.val_pow_eq_pow_val, hγ0m, transvMat_pow X.Gm hξ]

  have hlact : lact (γ0 ^ X.chiOrd la) y =
      X.flow ξ (cR X fun τ => ((X.m * X.chiOrd la : ℕ) : ℝ) * (τ.1 a).re) y := by
    funext τ
    have hta : τ.1 a = ((τ.1 a).re : ℂ) := by
      have h := emb_cc' τ.1 a
      rw [ha] at h
      apply Complex.ext
      · simp
      · have := congrArg Complex.im h
        simp at this
        simp
        linarith
    have hs : τ.1 ((X.chiOrd la : E) * ((X.m : E) * a * X.κ0)) =
        -(I * X.c τ * cR X (fun τ => ((X.m * X.chiOrd la : ℕ) : ℝ) * (τ.1 a).re) τ) := by
      rw [map_mul, map_mul, map_mul, map_natCast, map_natCast, emb_kappa X τ]
      conv_lhs => rw [hta]
      simp only [cR]
      push_cast
      ring
    simp only [lact, Data.flow]
    rw [hmat, transvMat_map X ξ τ _ _ hs]
  rw [← hlact, hP.2.2 _ hγ y hy, hχ, one_mul]

lemma cR_add (p q : X.Ψ → ℝ) : cR X (p + q) = cR X p + cR X q := by
  funext τ
  simp [cR]

lemma cR_zero : cR X 0 = 0 := by
  funext τ
  simp [cR]

lemma sec_periodic (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : X.IsSec la P) {ξ : Fin r → E}
    (hξΛ : ξ ∈ X.Λ) (hξ : herm X.Gm ξ ξ = 0) {p : X.Ψ → ℝ} (hp : p ∈ X.periods la) :
    ∀ y ∈ X.dom, P (X.flow ξ (cR X p) y) = P y := by
  induction hp using AddSubgroup.closure_induction with
  | mem p hp =>
    obtain ⟨a, ha, hai, rfl⟩ := hp
    exact fun y hy => sec_periodic_gen X la P hP hξΛ hξ a ha hai y hy
  | zero =>
    intro y _
    rw [cR_zero, flow_zero]
  | add p q _ _ hp hq =>
    intro y hy
    rw [cR_add, ← flow_flow X hξ, hp _ (flow_real_mem_dom X hξ q y hy), hq y hy]
  | neg p _ hp =>
    intro y hy
    have hz := flow_real_mem_dom X hξ (-p) y hy
    have e : X.flow ξ (cR X p) (X.flow ξ (cR X (-p)) y) = y := by
      rw [flow_flow X hξ, ← cR_add, add_neg_cancel, cR_zero, flow_zero]
    rw [← hp _ hz, e]

end ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ConjugateConjugate
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex Module
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem d4l2_dual_int (t : E) (h : ∀ γ : 𝓞 E, ∃ k : ℤ, Algebra.trace ℚ E (t * γ) = k) :
    IsIntegral ℤ ((NumberField.discr E : E) * t) := by
  classical
  have ht : t ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
    rw [Submodule.mem_traceDual]
    intro a ha
    obtain ⟨γ, rfl⟩ := Submodule.mem_one.1 ha
    obtain ⟨k, hk⟩ := h γ
    refine RingHom.mem_range.2 ⟨k, ?_⟩
    rw [Algebra.traceForm_apply]
    simpa using hk.symm
  have h1 : (1 : E) ∈ (1 : Submodule (𝓞 E) E) := Submodule.mem_one.2 ⟨1, map_one _⟩
  have hb : ∀ i, IsIntegral ℤ (NumberField.integralBasis E i) := fun i => by
    rw [NumberField.integralBasis_apply]
    exact NumberField.RingOfIntegers.isIntegral_coe _
  have key := isIntegral_discr_mul_of_mem_traceDual (A := ℤ) (K := ℚ)
    (1 : Submodule (𝓞 E) E) hb h1 ht
  have e : Algebra.discr ℚ (NumberField.integralBasis E) • (1 : E) * t =
      (NumberField.discr E : E) * t := by
    rw [← NumberField.coe_discr, Algebra.smul_def, mul_one]
    simp
  rwa [e] at key

theorem d4l2_dual_int' (t : E) (h : ∀ γ : 𝓞 E, ∃ k : ℤ, Algebra.trace ℚ E (t * γ) = k) :
    IsIntegral ℤ (((NumberField.discr E).natAbs : E) * t) := by
  have key := d4l2_dual_int t h
  rcases Int.natAbs_eq (NumberField.discr E) with hd | hd
  · have e : ((NumberField.discr E).natAbs : E) = (NumberField.discr E : E) := by
      conv_rhs => rw [hd]
      simp
    rw [e]
    exact key
  · have e : ((NumberField.discr E).natAbs : E) = -(NumberField.discr E : E) := by
      conv_rhs => rw [hd]
      simp
    rw [e, neg_mul]
    exact key.neg

namespace Data

variable {r : ℕ} (X : Data E r)

theorem conjugate_conjugate' (φ : E →+* ℂ) :
    ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ := by
  ext x
  simp only [ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]

theorem conj_mem_iff (φ : E →+* ℂ) : ComplexEmbedding.conjugate φ ∈ X.Ψ ↔ φ ∉ X.Ψ := by
  rw [X.cmType (ComplexEmbedding.conjugate φ), conjugate_conjugate']

theorem sum_emb_split (f : (E →+* ℂ) → ℂ) :
    ∑ φ : E →+* ℂ, f φ = ∑ τ : X.Ψ, (f τ.1 + f (ComplexEmbedding.conjugate τ.1)) := by
  classical
  have h2 : ∑ φ ∈ X.Ψ, f (ComplexEmbedding.conjugate φ) = ∑ φ ∈ X.Ψᶜ, f φ :=
    Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate
      (fun a ha => Finset.mem_compl.2 fun hc => (X.conj_mem_iff a).1 hc ha)
      (fun a ha => (X.conj_mem_iff a).2 (Finset.mem_compl.1 ha))
      (fun a _ => conjugate_conjugate' a) (fun a _ => conjugate_conjugate' a) (fun a _ => rfl)
  have h2' : ∑ x : X.Ψ, f (ComplexEmbedding.conjugate x.1) = ∑ φ ∈ X.Ψᶜ, f φ := by
    rw [← h2]
    exact Finset.sum_coe_sort X.Ψ (fun φ => f (ComplexEmbedding.conjugate φ))
  rw [Finset.sum_add_distrib, h2', Finset.sum_coe_sort X.Ψ f, Finset.sum_add_sum_compl]

theorem trace_eq_Psi (y : E) :
    ((Algebra.trace ℚ E y : ℚ) : ℂ) = ∑ τ : X.Ψ, (τ.1 y + conj (τ.1 y)) := by
  have h1 : ((Algebra.trace ℚ E y : ℚ) : ℂ) = ∑ φ : E →+* ℂ, φ y := by
    have h := trace_eq_sum_embeddings (K := ℚ) (L := E) (E := ℂ) (x := y)
    rw [eq_ratCast] at h
    rw [h]
    exact Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ fun σ => rfl
  rw [h1, X.sum_emb_split (fun φ => φ y)]
  rfl

theorem re_sum_Psi (y : E) : (∑ τ : X.Ψ, τ.1 y).re = (Algebra.trace ℚ E y : ℝ) / 2 := by
  have h := congrArg Complex.re (X.trace_eq_Psi y)
  simp only [Complex.ratCast_re, Complex.re_sum, Complex.add_re, Complex.conj_re] at h
  rw [Complex.re_sum, h, Finset.sum_add_distrib]
  ring

theorem card_Psi : 2 * Fintype.card X.Ψ = finrank ℚ E := by
  have h := X.sum_emb_split (fun _ => (1 : ℂ))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
  rw [← NumberField.Embeddings.card E ℂ]
  have h' : ((Fintype.card (E →+* ℂ) : ℕ) : ℂ) = ((2 * Fintype.card X.Ψ : ℕ) : ℂ) := by
    push_cast
    linear_combination h
  exact (Nat.cast_injective h').symm

theorem exists_emb_eq (z : X.Ψ → ℂ)
    (hz : ∀ γ : 𝓞 E, ∃ q : ℚ, (∑ τ : X.Ψ, z τ * τ.1 (γ : E)).re = q) :
    ∃ ω : E, ∀ τ : X.Ψ, z τ = τ.1 ω := by
  classical
  let P : (X.Ψ → ℂ) → E →ₗ[ℚ] ℝ := fun w =>
    { toFun := fun x => (∑ τ : X.Ψ, w τ * τ.1 x).re
      map_add' := fun x y => by simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun q x => by
        simp only [Rat.smul_def, map_mul, map_ratCast, RingHom.id_apply]
        rw [show ∑ τ : X.Ψ, w τ * ((q : ℂ) * τ.1 x) = (q : ℂ) * ∑ τ : X.Ψ, w τ * τ.1 x by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun τ _ => by ring]
        rw [← Complex.ofReal_ratCast, Complex.re_ofReal_mul] }
  set b := NumberField.integralBasis E with hbdef
  have hnd := traceForm_nondegenerate ℚ E
  set d := (Algebra.traceForm ℚ E).dualBasis hnd b with hddef
  choose q hq using fun i => hz (NumberField.RingOfIntegers.basis E i)
  set ω : E := ∑ i, (2 * q i) • d i with hωdef
  have htr : ∀ j, Algebra.trace ℚ E (ω * b j) = 2 * q j := by
    intro j
    have h : Algebra.traceForm ℚ E ω (b j) = 2 * q j := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hωdef, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hddef,
        LinearMap.BilinForm.apply_dualBasis_left, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]
    simpa [Algebra.traceForm_apply] using h
  have hbj : ∀ j, (b j : E) = ((NumberField.RingOfIntegers.basis E j : 𝓞 E) : E) := fun j => by
    rw [hbdef, NumberField.integralBasis_apply]
  set w : X.Ψ → ℂ := fun τ => z τ - τ.1 ω with hwdef
  have hPb : ∀ j, P w (b j) = 0 := by
    intro j
    show (∑ τ : X.Ψ, (z τ - τ.1 ω) * τ.1 (b j)).re = 0
    simp only [sub_mul, Finset.sum_sub_distrib, Complex.sub_re]
    have e1 : (∑ τ : X.Ψ, z τ * τ.1 (b j)).re = q j := by
      rw [hbj]
      exact hq j
    have e2 : (∑ τ : X.Ψ, τ.1 ω * τ.1 (b j)).re = q j := by
      rw [show ∑ τ : X.Ψ, τ.1 ω * τ.1 (b j) = ∑ τ : X.Ψ, τ.1 (ω * b j) from
        Finset.sum_congr rfl fun τ _ => (map_mul τ.1 ω (b j)).symm]
      rw [X.re_sum_Psi, htr]
      push_cast
      ring
    rw [e1, e2, sub_self]
  have hP0 : P w = 0 := b.ext fun j => by rw [hPb j, LinearMap.zero_apply]
  have hPw : ∀ x : E, (∑ τ : X.Ψ, w τ * τ.1 x).re = 0 := fun x => LinearMap.congr_fun hP0 x
  let W : (E →+* ℂ) → ℂ := fun φ =>
    if h : φ ∈ X.Ψ then w ⟨φ, h⟩ else conj (w ⟨ComplexEmbedding.conjugate φ, (X.conj_mem_iff φ).2 h⟩)
  have hW1 : ∀ τ : X.Ψ, W τ.1 = w τ := fun τ => by
    simp only [W, dif_pos τ.2]
  have hW2 : ∀ τ : X.Ψ, W (ComplexEmbedding.conjugate τ.1) = conj (w τ) := fun τ => by
    have hn : ComplexEmbedding.conjugate τ.1 ∉ X.Ψ := fun hc => (X.conj_mem_iff τ.1).1 hc τ.2
    simp only [W, dif_neg hn]
    exact congrArg (fun σ : X.Ψ => conj (w σ)) (Subtype.ext (conjugate_conjugate' τ.1))
  have hW : ∀ x : E, ∑ φ : E →+* ℂ, W φ * φ x = 0 := by
    intro x
    rw [X.sum_emb_split (fun φ => W φ * φ x)]
    simp only [hW1, hW2, ComplexEmbedding.conjugate_coe_eq, ← map_mul (starRingEnd ℂ),
      Complex.add_conj]
    rw [← Complex.ofReal_sum, ← Finset.mul_sum, ← Complex.re_sum, hPw x, mul_zero,
      Complex.ofReal_zero]
  have hli : LinearIndependent ℂ (fun φ : E →+* ℂ => (φ : E → ℂ)) :=
    (linearIndependent_monoidHom E ℂ).comp (fun φ : E →+* ℂ => (φ : E →* ℂ))
      (fun a a' h => RingHom.ext fun x => congrArg (fun f : E →* ℂ => f x) h)
  have hsumfun : ∑ φ : E →+* ℂ, W φ • (φ : E → ℂ) = 0 := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact hW x
  refine ⟨ω, fun τ => ?_⟩
  have h0 := Fintype.linearIndependent_iff.1 hli W hsumfun τ.1
  rw [hW1] at h0
  exact sub_eq_zero.1 h0

theorem nonempty_Psi : Nonempty X.Ψ := by
  have h := X.card_Psi
  have hpos : 0 < finrank ℚ E := Module.finrank_pos
  rw [← Fintype.card_pos_iff]
  omega

theorem exists_emb_int (z : X.Ψ → ℂ) (g : ℕ) (hg : 0 < g)
    (hz : ∀ γ : 𝓞 E, ∃ k : ℤ, ((2 * g * (NumberField.discr E).natAbs : ℕ) : ℝ) *
      (∑ τ : X.Ψ, z τ * τ.1 (γ : E)).re = k) :
    ∃ ω : E, (∀ τ : X.Ψ, z τ = τ.1 ω) ∧
      IsIntegral ℤ (((g * (NumberField.discr E).natAbs ^ 2 : ℕ) : E) * ω) := by
  have hN : ∀ γ : 𝓞 E, ∃ q : ℚ, (∑ τ : X.Ψ, z τ * τ.1 (γ : E)).re = q := by
    intro γ
    obtain ⟨k, hk⟩ := hz γ
    have hne : ((2 * g * (NumberField.discr E).natAbs : ℕ) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.2 (Nat.mul_ne_zero (Nat.mul_ne_zero two_ne_zero hg.ne')
        (Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero E)))
    refine ⟨(k : ℚ) / ((2 * g * (NumberField.discr E).natAbs : ℕ) : ℚ), ?_⟩
    rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, eq_div_iff hne, mul_comm]
    exact hk
  obtain ⟨ω, hω⟩ := X.exists_emb_eq z hN
  refine ⟨ω, hω, ?_⟩
  have key : ∀ γ : 𝓞 E, ∃ k : ℤ,
      Algebra.trace ℚ E (((g * (NumberField.discr E).natAbs : ℕ) : E) * ω * γ) = k := by
    intro γ
    obtain ⟨k, hk⟩ := hz γ
    refine ⟨k, ?_⟩
    have hs : ∑ τ : X.Ψ, z τ * τ.1 (γ : E) = ∑ τ : X.Ψ, τ.1 (ω * γ) :=
      Finset.sum_congr rfl fun τ _ => by rw [hω τ, map_mul]
    rw [hs, X.re_sum_Psi] at hk
    have htr : Algebra.trace ℚ E (((g * (NumberField.discr E).natAbs : ℕ) : E) * ω * γ) =
        ((g * (NumberField.discr E).natAbs : ℕ) : ℚ) * Algebra.trace ℚ E (ω * γ) := by
      rw [mul_assoc, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]
    rw [htr]
    have h2 : ((((g * (NumberField.discr E).natAbs : ℕ) : ℚ) * Algebra.trace ℚ E (ω * γ) : ℚ) : ℝ) =
        ((k : ℚ) : ℝ) := by
      push_cast at hk ⊢
      linear_combination hk
    exact_mod_cast h2
  have hint := d4l2_dual_int' (((g * (NumberField.discr E).natAbs : ℕ) : E) * ω) key
  have e : (((g * (NumberField.discr E).natAbs ^ 2 : ℕ)) : E) * ω =
      ((NumberField.discr E).natAbs : E) * (((g * (NumberField.discr E).natAbs : ℕ) : E) * ω) := by
    push_cast
    ring
  rw [e]
  exact hint

end Data

end ReciprocityTheory.ChartRestriction.G.FD
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FinrankEqTwoMulHalfDegree
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem finrank_eq_two_mul_half_degree : (Module.finrank ℚ E : ℝ) = 2 * (fdeg E : ℝ) := by
  have hf : fdeg E = Module.finrank ℚ E / 2 := rfl
  rw [hf, NumberField.IsTotallyComplex.finrank (K := E), Nat.mul_div_cancel_left _ two_pos]
  push_cast
  ring

theorem one_le_field_half_degree : 1 ≤ (fdeg E : ℝ) := by
  have h0 : 0 < Module.finrank ℚ E := Module.finrank_pos
  have h0' : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast h0
  have hr : (0 : ℝ) < fdeg E := by
    have := finrank_eq_two_mul_half_degree (E := E)
    linarith
  have hn : 0 < fdeg E := by exact_mod_cast hr
  exact_mod_cast Nat.succ_le_of_lt hn

theorem field_discr_constant_pos : 0 < dE E := by
  unfold dE
  exact abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero (K := E))

theorem rootDiscriminant_eq_rpow : rdE E = dE E ^ (1 / (2 * (fdeg E : ℝ))) := by
  unfold rdE
  rw [finrank_eq_two_mul_half_degree]

namespace Data

variable {r : ℕ} (X : Data E r)

theorem orthogonal_component_apply (z : Frame X.Ψ r) (ξ x : Fin r → E) (τ : X.Ψ) :
    X.ucomp z ξ (X.embV x) τ = Data.emb τ.1 x -
      (X.Hf z τ (Data.emb τ.1 x) (Data.emb τ.1 ξ) / X.Hf z τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) •
        Data.emb τ.1 ξ := rfl

theorem orthogonal_component_ne_zero (z : Frame X.Ψ r) {ξ x : Fin r → E} (hξ : ξ ≠ 0) (hx : ∀ e : E, x ≠ e • ξ)
    (τ : X.Ψ) : X.ucomp z ξ (X.embV x) τ ≠ 0 := by
  intro h
  rw [orthogonal_component_apply] at h

  obtain ⟨c, hb⟩ : ∃ c : ℂ, ∀ b, τ.1 (x b) = c * τ.1 (ξ b) := ⟨_, fun b => by
    have hb := congrFun h b
    simp only [Data.emb, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hb
    exact sub_eq_zero.mp hb⟩
  obtain ⟨a, ha⟩ : ∃ a, ξ a ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hξ (funext hcon)
  have hτa : τ.1 (ξ a) ≠ 0 := (map_ne_zero τ.1).mpr ha

  apply hx (x a / ξ a)
  funext b
  apply τ.1.injective
  rw [Pi.smul_apply, smul_eq_mul, map_mul, map_div₀, hb a, hb b]
  field_simp

end Data

end

end ReciprocityTheory.ChartRestriction.G.FD
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.RealPlaceEmbeddings
namespace ReciprocityTheory.ChartRestriction.G.FD

namespace RealPlaceEmbeddings

open NumberField Module Submodule
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

instance finite_int : Module.Finite ℤ X.Λ := by
  have : Module.Finite (𝓞 E) X.Λ := Module.Finite.iff_fg.mpr X.Λ_fg
  exact Module.Finite.trans (𝓞 E) X.Λ

instance free_int : Module.Free ℤ X.Λ := inferInstance

noncomputable def zb : Basis (Fin (finrank ℤ X.Λ)) ℤ X.Λ := Module.finBasis ℤ X.Λ

theorem smul_mem_spanQ (α : E) {l : Fin r → E} (hl : l ∈ X.Λ) :
    α • l ∈ span ℚ (X.Λ : Set (Fin r → E)) := by
  have hα : α = ∑ k, (integralBasis E).repr α k • integralBasis E k :=
    ((integralBasis E).sum_repr α).symm
  rw [hα, Finset.sum_smul]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [smul_assoc]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  rw [integralBasis_apply]
  exact X.Λ.smul_of_tower_mem (RingOfIntegers.basis E k) hl

theorem spanQ_eq_top {ι : Type} [Fintype ι] (g : Basis ι ℤ X.Λ) :
    span ℚ (Set.range fun i => (g i : Fin r → E)) = ⊤ := by
  set S := span ℚ (Set.range fun i => (g i : Fin r → E)) with hS
  have hΛ : ∀ l ∈ X.Λ, l ∈ S := by
    intro l hl
    have h1 : (⟨l, hl⟩ : X.Λ) = ∑ i, g.repr ⟨l, hl⟩ i • g i := (g.sum_repr ⟨l, hl⟩).symm
    have h2 : l = ∑ i, ((g.repr ⟨l, hl⟩ i : ℤ) : ℚ) • (g i : Fin r → E) := by
      refine (congrArg Subtype.val h1).trans ?_
      rw [Submodule.coe_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Int.cast_smul_eq_zsmul]
      rfl
    rw [h2]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hspanΛ : span ℚ (X.Λ : Set (Fin r → E)) ≤ S := Submodule.span_le.mpr fun l hl => hΛ l hl
  have hE : ∀ α : E, ∀ w ∈ S, α • w ∈ S := by
    intro α w hw
    induction hw using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact hspanΛ (smul_mem_spanQ X α (g i).2)
    | zero => simp
    | add y z _ _ hy hz => rw [smul_add]; exact S.add_mem hy hz
    | smul q y _ hy => rw [smul_comm]; exact S.smul_mem q hy
  refine eq_top_iff.mpr ?_
  rintro v -
  have hv : v ∈ span E (X.Λ : Set (Fin r → E)) := by rw [X.Λ_span]; trivial
  induction hv using Submodule.span_induction with
  | mem y hy => exact hΛ y hy
  | zero => exact S.zero_mem
  | add y z _ _ hy hz => exact S.add_mem hy hz
  | smul α y _ hy => exact hE α y hy

theorem linIndQ {ι : Type} [Fintype ι] (g : Basis ι ℤ X.Λ) :
    LinearIndependent ℚ fun i => (g i : Fin r → E) := by
  have hZ : LinearIndependent ℤ fun i => (g i : Fin r → E) :=
    g.linearIndependent.map' (X.Λ.toAddSubgroup.subtype.toIntLinearMap)
      (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  exact (LinearIndependent.iff_fractionRing ℤ ℚ).mp hZ

noncomputable def qb {ι : Type} [Fintype ι] (g : Basis ι ℤ X.Λ) : Basis ι ℚ (Fin r → E) :=
  Basis.mk (linIndQ X g) (spanQ_eq_top X g).ge

theorem qb_apply {ι : Type} [Fintype ι] (g : Basis ι ℤ X.Λ) (i : ι) : qb X g i = (g i : Fin r → E) := by
  unfold qb
  exact Basis.mk_apply _ _ _

theorem card_qb {ι : Type} [Fintype ι] (g : Basis ι ℤ X.Λ) :
    Fintype.card ι = r * finrank ℚ E := by
  rw [← Module.finrank_eq_card_basis (qb X g), Module.finrank_pi_fintype]
  simp

theorem two_card_Psi : 2 * Fintype.card X.Ψ = finrank ℚ E := by
  classical
  rw [← NumberField.Embeddings.card E ℂ]
  have h1 : (X.Ψᶜ).card = X.Ψ.card := by
    refine Finset.card_bij (fun τ _ => ComplexEmbedding.conjugate τ) ?_ ?_ ?_
    · intro τ hτ
      rw [Finset.mem_compl] at hτ
      exact (X.cmType _).mpr (by rw [TraceIntegralBasis.conj_conj]; exact hτ)
    · intro a _ b _ h
      have := congrArg ComplexEmbedding.conjugate h
      rwa [TraceIntegralBasis.conj_conj, TraceIntegralBasis.conj_conj] at this
    · intro τ hτ
      refine ⟨ComplexEmbedding.conjugate τ, ?_, TraceIntegralBasis.conj_conj τ⟩
      rw [Finset.mem_compl]
      intro h
      exact ((X.cmType _).mp h) (by rw [TraceIntegralBasis.conj_conj]; exact hτ)
  have h2 := Finset.card_add_card_compl X.Ψ
  rw [Fintype.card_coe]
  omega

noncomputable def plc (τ : X.Ψ) : TraceIntegralBasis.CP E :=
  ⟨InfinitePlace.mk τ.1, IsTotallyComplex.isComplex _⟩

open scoped Classical in
noncomputable def Tm : TraceIntegralBasis.VS E →ₗ[ℝ] (X.Ψ → ℂ) where
  toFun z τ := if (plc X τ).1.embedding = τ.1 then z (plc X τ) else conj (z (plc X τ))
  map_add' z z' := by
    funext τ
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c z := by
    funext τ
    simp only [Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp [Complex.real_smul]

open scoped Classical in
theorem Tm_iota (x : E) (τ : X.Ψ) : Tm X (TraceIntegralBasis.iota E x) τ = τ.1 x := by
  simp only [Tm, LinearMap.coe_mk, AddHom.coe_mk, TraceIntegralBasis.iota_apply]
  split_ifs with h
  · rw [h]
  · rcases InfinitePlace.embedding_mk_eq τ.1 with h' | h'
    · exact absurd h' h
    · change conj ((InfinitePlace.mk τ.1).embedding x) = τ.1 x
      rw [h', ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]

open scoped Classical in
theorem Tm_injective : Function.Injective (Tm X) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  ext w
  obtain ⟨τ, hτ⟩ : ∃ τ : X.Ψ, plc X τ = w := by
    by_cases h : w.1.embedding ∈ X.Ψ
    · exact ⟨⟨_, h⟩, Subtype.ext (InfinitePlace.mk_embedding w.1)⟩
    · have h2 : ComplexEmbedding.conjugate w.1.embedding ∈ X.Ψ :=
        (X.cmType _).mpr (by rw [TraceIntegralBasis.conj_conj]; exact h)
      exact ⟨⟨_, h2⟩, Subtype.ext ((InfinitePlace.mk_conjugate_eq _).trans
        (InfinitePlace.mk_embedding w.1))⟩
  have h3 := congrFun hz τ
  simp only [Tm, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at h3
  subst hτ
  split_ifs at h3
  · simpa using h3
  · simpa using h3

theorem finrank_Psi : finrank ℝ (X.Ψ → ℂ) = finrank ℚ E := by
  rw [Module.finrank_pi_fintype]
  simp only [Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← two_card_Psi X]
  ring

theorem span_real_embeddings_eq_top : span ℝ (Set.range fun x : E => fun τ : X.Ψ => τ.1 x) = ⊤ := by
  have hs : span ℝ (Set.range (TraceIntegralBasis.iota E)) = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← (TraceIntegralBasis.bas E).span_eq]
    exact span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨_, (TraceIntegralBasis.bas_apply i).symm⟩)
  have hdim : finrank ℝ (TraceIntegralBasis.VS E) = finrank ℝ (X.Ψ → ℂ) := by
    rw [TraceIntegralBasis.finrank_VS, finrank_Psi]
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp (Tm_injective X)
  rw [eq_top_iff]
  intro z _
  obtain ⟨y, rfl⟩ := hsurj z
  have hy : y ∈ span ℝ (Set.range (TraceIntegralBasis.iota E)) := by rw [hs]; trivial
  have h1 := Submodule.mem_map_of_mem (f := Tm X) hy
  rw [Submodule.map_span] at h1
  refine span_mono ?_ h1
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  exact ⟨x, funext fun τ => (Tm_iota X x τ).symm⟩

noncomputable def Ja (a : Fin r) : (X.Ψ → ℂ) →ₗ[ℝ] (X.Ψ → Fin r → ℂ) where
  toFun z τ b := if b = a then z τ else 0
  map_add' z z' := by
    funext τ b
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c z := by
    funext τ b
    simp only [Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

theorem span_embV {ι : Type} [Fintype ι] (g : Basis ι ℤ X.Λ) :
    span ℝ (Set.range fun i => X.embV (g i : Fin r → E)) = ⊤ := by
  set S := span ℝ (Set.range fun i => X.embV (g i : Fin r → E)) with hS
  have h1 : ∀ v : Fin r → E, X.embV v ∈ S := by
    intro v
    have hv : X.embV v = ∑ i, (((qb X g).repr v i : ℚ) : ℝ) • X.embV (g i : Fin r → E) := by
      conv_lhs => rw [← (qb X g).sum_repr v]
      funext τ a
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Data.embV, Data.emb, qb_apply, Finset.sum_apply, Pi.smul_apply, Rat.smul_def,
        map_sum, map_mul, map_ratCast, Complex.real_smul, Complex.ofReal_ratCast]
    rw [hv]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (subset_span ⟨i, rfl⟩)
  rw [eq_top_iff]
  intro w _
  have hw : w = ∑ a : Fin r, Ja X a (fun τ => w τ a) := by
    funext τ b
    simp [Ja, Finset.sum_apply]
  rw [hw]
  refine Submodule.sum_mem _ fun a _ => ?_
  have hz : (fun τ : X.Ψ => w τ a) ∈ span ℝ (Set.range fun x : E => fun τ : X.Ψ => τ.1 x) := by
    rw [span_real_embeddings_eq_top]; trivial
  have h2 := Submodule.mem_map_of_mem (f := Ja X a) hz
  rw [Submodule.map_span] at h2
  refine (span_le.mpr ?_) h2
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  have h3 : Ja X a (fun τ : X.Ψ => τ.1 x) = X.embV (Pi.single a x) := by
    funext τ b
    simp only [Ja, LinearMap.coe_mk, AddHom.coe_mk, Data.embV, Data.emb, Pi.single_apply]
    split_ifs <;> simp
  rw [h3]
  exact h1 _

theorem linIndR {ι : Type} [Fintype ι] (g : Basis ι ℤ X.Λ) :
    LinearIndependent ℝ fun i => X.embV (g i : Fin r → E) := by
  refine linearIndependent_of_top_le_span_of_card_eq_finrank (span_embV X g).ge ?_
  rw [card_qb X g, Module.finrank_pi_fintype]
  simp only [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [← two_card_Psi X]
  ring

end RealPlaceEmbeddings

end ReciprocityTheory.ChartRestriction.G.FD
end

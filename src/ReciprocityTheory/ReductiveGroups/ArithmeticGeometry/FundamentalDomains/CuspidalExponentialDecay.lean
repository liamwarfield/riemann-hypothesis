module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantFamilyNorms
public import Lemmata.GeneralBFactAltForm.Imports

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def epStar (M f w k0 : ℝ) : ℝ := min 1 (Real.pi / (M * (f * w + 2) * k0 * Real.log 2))

def CuspFormGapCondition : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ), P ∈ X.SS la →
    ∃ c' : ℝ, 0 < c' ∧ P ∈ X.SSgt la c'

def CuspidalExponentialDecay : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (c : ℝ), 0 ≤ c → P ∈ X.SSgt la c →
    ∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm la P x ^ 2 ≤ C * Real.exp (-2 * Real.pi * c / X.firstMinimumSq x)

def MahlerCompactnessCriterion : Prop :=
  ∀ (r : ℕ) (X : Data E r) (ε : ℝ), 0 < ε → ∃ K : Set (Frame X.Ψ r), IsCompact K ∧ K ⊆ X.dom ∧
    ∀ x ∈ X.dom, ε ≤ X.la1 x → ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ K

def MaxBoundStatement : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (M w : ℝ), P ∈ X.SS la →
    0 < M → (∑ τ, X.spread la τ) ≤ w → 0 < w →
    (∀ v ∈ X.L', herm X.Gm v v = 0 → ∀ b : E, cc b = b → IsIntegral ℤ b →
      ∃ γ ∈ X.Γ, X.χ la γ = 1 ∧
        ∀ τ : X.Ψ, (γ : Matrix (Fin r) (Fin r) E).map τ.1 = X.flowMat v τ ((M : ℂ) * τ.1 b)) →
    ∀ z0 ∈ X.dom, (∀ x ∈ X.dom, X.pnorm la P x ≤ 2 * X.pnorm la P z0) → 0 < X.pnorm la P z0 →
    ∀ v ∈ X.L', v ≠ 0 → ∃ τ : X.Ψ, epStar M (fdeg E) w X.k0 ≤ X.maj z0 τ (Data.emb τ.1 v)

end

end ReciprocityTheory.ChartRestriction.G.FD
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowDomainCriterionHolds
namespace ReciprocityTheory.ChartRestriction.G.FD

open Complex ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

private theorem minors_iff {r : ℕ} (X : Data E r) (e : X.Ψ → Fin r → ℂ) (he : X.IsIsoV e)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) (s : X.Ψ → ℂ) (τ : X.Ψ) :
    (∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm (X.flowV e s x) τ i).re) ↔
      0 < 1 + 2 * X.c τ * (s τ).im * mN τ.1 X.Gm (mat x τ) (e τ) X.p0 := by
  have hG := MajorantFamilyNorms.hG_of X τ
  have hdet : (mat x τ).det ≠ 0 := (hx τ).1
  have hsg := MajorantFamilyNorms.hsg_of X hx τ
  have he0 := (he τ).1
  have key : ∀ i : Fin (r + 1), (dmin X.Gm (X.flowV e s x) τ i).re =
      (dmin X.Gm x τ i).re * (1 + 2 * X.c τ * (s τ).im * mN τ.1 X.Gm (mat x τ) (e τ) i) := by
    intro i
    rw [MajorantFamilyNorms.dmin_eq X (X.flowV e s x), MajorantFamilyNorms.dmin_flow X hx e τ he0 s,
      ← MajorantFamilyNorms.dmin_eq X x, Complex.re_mul_ofReal]
  have hpos : ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := (hx τ).2
  have hb := fun (i : ℕ) (hi : i ≤ r) =>
    mN_bounds hG X.p0 X.p0_le (mat x τ) hdet hsg (e τ) he0 i hi
  have hmp := mN_pos hG X.p0 X.p0_le (mat x τ) hdet hsg (e τ) he0 (he τ).2
  constructor
  · intro h
    have h0 := h ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩
    rw [key, ← mul_assoc] at h0
    exact pos_of_mul_pos_right h0 (hpos _).le
  · intro h i
    rw [key, ← mul_assoc]
    refine mul_pos (hpos i) ?_
    obtain ⟨h0, h1⟩ := hb i (Nat.le_of_lt_succ i.isLt)
    rcases le_or_gt 0 (2 * X.c τ * (s τ).im) with hk | hk
    · nlinarith [mul_nonneg hk h0]
    · nlinarith [mul_le_mul_of_nonpos_left h1 hk.le]

theorem flowDomainCriterion_holds : FlowDomainCriterion (E := E) := by
  intro r X e he x hx s
  have hmp : ∀ τ, 0 < mN τ.1 X.Gm (mat x τ) (e τ) X.p0 := fun τ =>
    mN_pos (MajorantFamilyNorms.hG_of X τ) X.p0 X.p0_le (mat x τ) (hx τ).1 (MajorantFamilyNorms.hsg_of X hx τ) (e τ)
      (he τ).1 (he τ).2
  have hm : ∀ τ, 1 + (s τ).im / X.ttV e x τ =
      1 + 2 * X.c τ * (s τ).im * mN τ.1 X.Gm (mat x τ) (e τ) X.p0 := by
    intro τ
    rw [Data.ttV, MajorantFamilyNorms.maj_eq X hx e τ (he τ).1, one_div, div_inv_eq_mul]
    ring
  have hdom : X.flowV e s x ∈ X.dom ↔
      ∀ τ, ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm (X.flowV e s x) τ i).re := by
    constructor
    · intro h τ
      exact (h τ).2
    · intro h τ
      refine ⟨?_, h τ⟩
      show (X.flowMatV (e τ) τ (s τ) * mat x τ).det ≠ 0
      rw [Matrix.det_mul, MajorantFamilyNorms.det_flowMat X (e τ) τ (s τ) (he τ).1, one_mul]
      exact (hx τ).1
  refine ⟨?_, ?_⟩
  · rw [hdom]
    refine forall_congr' fun τ => ?_
    rw [hm τ]
    exact minors_iff X e he hx s τ
  · intro hf τ
    have hpos := (minors_iff X e he hx s τ).1 (hdom.1 hf τ)
    have hc := MajorantFamilyNorms.c_pos X τ
    have hm0 := hmp τ
    simp only [Data.ttV]
    rw [MajorantFamilyNorms.maj_flow X hx e τ (he τ).1 s hpos.ne', MajorantFamilyNorms.maj_eq X hx e τ (he τ).1]
    field_simp

end ReciprocityTheory.ChartRestriction.G.FD
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermitianTraceFormVanishing
namespace ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing

open NumberField ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

@[simp] lemma cc_cc (a : E) : cc (cc a) = a := by simp [cc]
@[simp] lemma cc_mul (a b : E) : cc (a * b) = cc a * cc b := by simp [cc]
@[simp] lemma cc_add (a b : E) : cc (a + b) = cc a + cc b := by simp [cc]
@[simp] lemma cc_sub (a b : E) : cc (a - b) = cc a - cc b := by simp [cc]
@[simp] lemma cc_neg (a : E) : cc (-a) = -cc a := by simp [cc]
@[simp] lemma cc_zero : cc (0 : E) = 0 := by simp [cc]
@[simp] lemma cc_one : cc (1 : E) = 1 := by simp [cc]
@[simp] lemma cc_inv (a : E) : cc a⁻¹ = (cc a)⁻¹ := by simp [cc]
lemma cc_sum {ι : Type*} (s : Finset ι) (f : ι → E) : cc (∑ i ∈ s, f i) = ∑ i ∈ s, cc (f i) := by
  simp [cc]
@[simp] lemma cc_eq_zero (a : E) : cc a = 0 ↔ a = 0 := by simp [cc]
@[simp] lemma cc_intCast (n : ℤ) : cc (n : E) = n := by simp [cc]
@[simp] lemma cc_natCast (n : ℕ) : cc (n : E) = n := by simp [cc]

variable {r : ℕ}

lemma herm_add_left (G : Matrix (Fin r) (Fin r) E) (x x' y : Fin r → E) :
    herm G (x + x') y = herm G x y + herm G x' y := by
  simp [herm, add_mul, Finset.sum_add_distrib]

lemma herm_sub_left (G : Matrix (Fin r) (Fin r) E) (x x' y : Fin r → E) :
    herm G (x - x') y = herm G x y - herm G x' y := by
  simp [herm, sub_mul, Finset.sum_sub_distrib]

lemma herm_smul_left (G : Matrix (Fin r) (Fin r) E) (c : E) (x y : Fin r → E) :
    herm G (c • x) y = c * herm G x y := by
  simp [herm, Finset.mul_sum, mul_assoc]

lemma herm_sub_right (G : Matrix (Fin r) (Fin r) E) (x y y' : Fin r → E) :
    herm G x (y - y') = herm G x y - herm G x y' := by
  simp [herm, mul_sub, Finset.sum_sub_distrib]

lemma herm_smul_right (G : Matrix (Fin r) (Fin r) E) (c : E) (x y : Fin r → E) :
    herm G x (c • y) = cc c * herm G x y := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, cc_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma herm_conj (G : Matrix (Fin r) (Fin r) E) (hG : ∀ a b, cc (G a b) = G b a)
    (x y : Fin r → E) : cc (herm G x y) = herm G y x := by
  simp only [herm, cc_sum, cc_mul, cc_cc, hG]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma cc_single (b c : Fin r) :
    cc ((Pi.single b (1 : E) : Fin r → E) c) = (Pi.single b (1 : E) : Fin r → E) c := by
  by_cases h : c = b
  · subst h; simp
  · simp [h]

lemma herm_single_right (G : Matrix (Fin r) (Fin r) E) (v : Fin r → E) (b : Fin r) :
    herm G v (Pi.single b 1) = (Matrix.vecMul v G) b := by
  simp only [herm, cc_single, Matrix.vecMul, dotProduct]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [Pi.single_apply]

lemma eq_zero_of_herm (G : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0) (v : Fin r → E)
    (hv : ∀ y, herm G v y = 0) : v = 0 := by
  apply Matrix.eq_zero_of_vecMul_eq_zero hG
  funext b
  rw [← herm_single_right]
  simpa using hv _

lemma exists_eq_smul_of_herm (G : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0)
    (hGh : ∀ a b, cc (G a b) = G b a) (ξ μ : Fin r → E) (hξ : ξ ≠ 0)
    (h : ∀ y, herm G y ξ = 0 → herm G μ y = 0) : ∃ e : E, μ = e • ξ := by
  have hk : ∃ k, herm G (Pi.single k 1) ξ ≠ 0 := by
    by_contra hne
    simp only [not_exists, not_not] at hne
    apply hξ
    apply Matrix.eq_zero_of_vecMul_eq_zero hG
    funext b
    rw [← herm_single_right, ← herm_conj G hGh, hne b]
    simp
  obtain ⟨k, hk⟩ := hk
  set y0 : Fin r → E := (herm G (Pi.single k 1) ξ)⁻¹ • Pi.single k 1
  have hy0 : herm G y0 ξ = 1 := by
    simp only [y0, herm_smul_left]; exact inv_mul_cancel₀ hk
  refine ⟨herm G μ y0, ?_⟩
  have hall : ∀ y, herm G (μ - herm G μ y0 • ξ) y = 0 := by
    intro y
    have h1 := h (y - herm G y ξ • y0) (by rw [herm_sub_left, herm_smul_left, hy0]; ring)
    rw [herm_sub_right, herm_smul_right, herm_conj G hGh, sub_eq_zero] at h1
    rw [herm_sub_left, herm_smul_left, h1]
    ring
  have := eq_zero_of_herm G hG _ hall
  exact sub_eq_zero.mp this

lemma eq_zero_of_trace (a : E) (h : ∀ β : 𝓞 E, Algebra.trace ℚ E (cc (β : E) * a) = 0) :
    a = 0 := by
  by_contra ha
  have halg : IsAlgebraic ℤ (cc a⁻¹) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic _)
  obtain ⟨y, hy, hint⟩ := halg.exists_integral_multiple
  let β : 𝓞 E := ⟨y • cc a⁻¹, hint⟩
  have hβ : (β : E) = y • cc a⁻¹ := rfl
  have h1 := h β
  have h2 : cc (y • cc a⁻¹) * a = algebraMap ℚ E (y : ℚ) := by
    rw [zsmul_eq_mul, cc_mul, cc_intCast, cc_cc, mul_assoc, inv_mul_cancel₀ ha, mul_one]
    simp
  rw [hβ, h2, Algebra.trace_algebraMap] at h1
  have hd : (Module.finrank ℚ E : ℚ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := E)).ne'
  rw [nsmul_eq_mul] at h1
  rcases mul_eq_zero.mp h1 with h3 | h3
  · exact hd h3
  · exact hy (by exact_mod_cast h3)

theorem exists_smul_mem {R F X : Type*} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] [AddCommGroup X] [Module F X] [Module R X] [IsScalarTower R F X]
    (S : Submodule R X) {x : X}
    (hx : x ∈ Submodule.span F (S : Set X)) : ∃ d : R, d ≠ 0 ∧ d • x ∈ S := by
  exact Bl.general_b_fact_alt_form.goal1 S hx

end ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicOutsideLine
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex MeasureTheory
open scoped ComplexConjugate ComplexOrder

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def IsIsoPair {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (u : Fin 2 → Fin r → E) : Prop :=
  (∀ i k, herm G (u i) (u k) = 0) ∧ LinearIndependent E u

def IsHermFam {ι : Type} (b : ι → Fin 2 → Fin 2 → ℂ) : Prop := ∀ τ i k, b τ k i = conj (b τ i k)

def dEnat (E : Type) [Field E] [NumberField E] : ℕ := (NumberField.discr E).natAbs

namespace Data

variable {r : ℕ} (X : Data E r)

def zmat (u : Fin 2 → Fin r → E) (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a j => (if a = j then 1 else 0) -
    I * X.c τ * ∑ i, ∑ k, b τ i k * emb τ.1 (u i) a * ∑ l, τ.1 (X.Gm j l) * conj (emb τ.1 (u k) l)

def Zb (u : Fin 2 → Fin r → E) (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (x : Frame X.Ψ r) : Frame X.Ψ r :=
  fun τ => (X.zmat u b τ * mat x τ : Matrix (Fin r) (Fin r) ℂ)

def pairR (χ b : X.Ψ → Fin 2 → Fin 2 → ℂ) : ℝ := (∑ τ, ∑ i, ∑ k, χ τ i k * b τ i k).re

def embH (β : Matrix (Fin 2) (Fin 2) E) : X.Ψ → Fin 2 → Fin 2 → ℂ := fun τ i k => τ.1 (β i k)

def LZ (g : ℕ) : Set (X.Ψ → Fin 2 → Fin 2 → ℂ) :=
  {b | ∃ β : Matrix (Fin 2) (Fin 2) E, (∀ i k, cc (β i k) = β k i) ∧
    (∀ i k, ∃ γ : E, IsIntegral ℤ γ ∧ β i k = ((g * dEnat E : ℕ) : E) / 2 * γ) ∧ b = X.embH β}

def IsFreqZ (g : ℕ) (χ : X.Ψ → Fin 2 → Fin 2 → ℂ) : Prop :=
  ∀ b ∈ X.LZ g, ∃ k : ℤ, 2 * X.pairR χ b = k

def IsLZBasis (g : ℕ) (ω : Fin (4 * Fintype.card X.Ψ) → X.Ψ → Fin 2 → Fin 2 → ℂ) : Prop :=
  (∀ j, ω j ∈ X.LZ g) ∧ (∀ b ∈ X.LZ g, ∃! n : Fin (4 * Fintype.card X.Ψ) → ℤ, b = ∑ j, (n j : ℂ) • ω j) ∧
    LinearIndependent ℝ ω


open scoped Classical in
open Classical in
def fz (u : Fin 2 → Fin r → E) (g : ℕ) (χ : X.Ψ → Fin 2 → Fin 2 → ℂ) (G : Frame X.Ψ r → ℂ)
    (x : Frame X.Ψ r) : ℂ :=
  if IsHermFam χ ∧ X.IsFreqZ g χ then
    if h : ∃ ω, X.IsLZBasis g ω then
      ∫ t in Set.pi Set.univ (fun _ : Fin (4 * Fintype.card X.Ψ) => Set.Icc (0 : ℝ) 1),
        G (X.Zb u (∑ j, (t j : ℂ) • h.choose j) x) *
          cexp (-(4 * Real.pi * I) * X.pairR χ (∑ j, (t j : ℂ) • h.choose j))
    else 0
  else 0

def chiAt (χ : X.Ψ → Fin 2 → Fin 2 → ℂ) (a : X.Ψ → Fin 2 → ℂ) (τ : X.Ψ) : ℂ :=
  ∑ i, ∑ k, χ τ i k * a τ i * conj (a τ k)

def uvec (u : Fin 2 → Fin r → E) (a : X.Ψ → Fin 2 → ℂ) : X.Ψ → Fin r → ℂ :=
  fun τ => ∑ i, a τ i • emb τ.1 (u i)

end Data

def UnipotentVectorGroup : Prop :=
  ∀ (r : ℕ) (X : Data E r) (u : Fin 2 → Fin r → E), IsIsoPair X.Gm u →
    (∀ b b' x, X.Zb u b (X.Zb u b' x) = X.Zb u (b + b') x) ∧
    ∀ b, IsHermFam b →
      X.IsUnitaryC (X.zmat u b) ∧ (∀ τ i, Matrix.mulVec (X.zmat u b τ) (Data.emb τ.1 (u i)) = Data.emb τ.1 (u i)) ∧
      (∀ τ, (X.zmat u b τ).det = 1) ∧
      (∀ x ∈ X.dom, X.Zb u b x ∈ X.dom) ∧ (∀ x x', X.SameFlag x x' → X.SameFlag (X.Zb u b x) (X.Zb u b x')) ∧
      (∀ (la : Wt X.Ψ r) x, x ∈ X.dom → X.nfac la (X.Zb u b x) = X.nfac la x) ∧
      (∀ x τ, x ∈ X.dom → X.maj (X.Zb u b x) τ (Data.emb τ.1 (u 0)) = X.maj x τ (Data.emb τ.1 (u 0))) ∧
      (∀ x ∈ X.FramesOverBasis (u 0), X.Zb u b x ∈ X.FramesOverBasis (u 0)) ∧
      (∀ (a : X.Ψ → Fin 2 → ℂ) (s : X.Ψ → ℂ) x, X.Zb u b (X.flowV (X.uvec u a) s x) =
        X.flowV (X.uvec u a) s (X.Zb u b x))
    ∧ ∀ (a : X.Ψ → Fin 2 → ℂ) (s : X.Ψ → ℝ) x,
      X.flowV (X.uvec u a) (fun τ => (s τ : ℂ)) x =
        X.Zb u (fun τ i k => (s τ : ℂ) * a τ i * conj (a τ k)) x

def UnipotentLatticeLift : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (u : Fin 2 → Fin r → E), IsIsoPair X.Gm u → (∀ i, u i ∈ X.Λ) →
    (∀ b ∈ X.LZ X.g, ∃ γ ∈ X.Γ, (∀ v ∈ X.Λ, ∃ y ∈ X.Λ,
        Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) v - v = (X.g : E) • y) ∧
      ∀ τ, (γ : Matrix (Fin r) (Fin r) E).map τ.1 = X.zmat u b τ) ∧
    (∀ (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ), X.IsSec la P →
      (∀ γ ∈ X.Γ, (∀ v ∈ X.Λ, ∃ y ∈ X.Λ,
        Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) v - v = (X.g : E) • y) → X.χ la γ = 1) →
      ∀ b ∈ X.LZ X.g, ∀ x ∈ X.dom, P (X.Zb u b x) = P x) ∧
    ∀ χ, IsHermFam χ → X.IsFreqZ X.g χ → ∃ β : Matrix (Fin 2) (Fin 2) E,
      (∀ i k, cc (β i k) = β k i) ∧ χ = X.embH β ∧
      ∀ i k, IsIntegral ℤ (((X.g * dEnat E ^ 2 : ℕ) : E) * β i k)

def FourierCoefficientProperties : Prop :=
  ∀ (r : ℕ) (X : Data E r) (u : Fin 2 → Fin r → E) (g : ℕ), IsIsoPair X.Gm u → 0 < g →
    ∀ (la : Wt X.Ψ r) (G : Frame X.Ψ r → ℂ), DifferentiableOn ℂ G X.dom →
    (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, G (rmul x b) = bchar la b * G x) →
    (∀ b ∈ X.LZ g, ∀ x ∈ X.dom, G (X.Zb u b x) = G x) →
    ∀ χ : X.Ψ → Fin 2 → Fin 2 → ℂ,
      (DifferentiableOn ℂ (X.fz u g χ G) X.dom ∧
        (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, X.fz u g χ G (rmul x b) = bchar la b * X.fz u g χ G x) ∧
        ∀ b, IsHermFam b → ∀ x ∈ X.dom,
          X.fz u g χ G (X.Zb u b x) = cexp (4 * Real.pi * I * X.pairR χ b) * X.fz u g χ G x) ∧
      (∀ x ∈ X.dom, ∀ M : ℝ, (∀ b, IsHermFam b → X.pnorm la G (X.Zb u b x) ≤ M) →
        X.pnorm la (X.fz u g χ G) x ≤ M)
    ∧ (∀ x ∈ X.dom, Summable (fun χ : X.Ψ → Fin 2 → Fin 2 → ℂ => ‖X.fz u g χ G x‖) →
        HasSum (fun χ : X.Ψ → Fin 2 → Fin 2 → ℂ => X.fz u g χ G x) (G x))

def FourierCoefficientSupport : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (u : Fin 2 → Fin r → E), IsIsoPair X.Gm u → (∀ i, u i ∈ X.Λ) →
    ∀ (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ), X.IsSec la P →
    (∀ γ ∈ X.Γ, (∀ v ∈ X.Λ, ∃ y ∈ X.Λ,
        Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) v - v = (X.g : E) • y) → X.χ la γ = 1) →
    ∀ (ν : X.Ψ → ℝ) (χ : X.Ψ → Fin 2 → Fin 2 → ℂ), ∀ x ∈ X.dom,
      X.fz u X.g χ (X.fj la (u 0) ν P) x =
        if (∀ τ, χ τ 0 0 = (ν τ : ℂ)) then X.fz u X.g χ P x else 0

def HolomorphicPeriodicityExtension : Prop :=
  ∀ (r : ℕ) (X : Data E r) (e : X.Ψ → Fin r → ℂ), X.IsIsoV e → ∀ G : Frame X.Ψ r → ℂ,
    DifferentiableOn ℂ G X.dom → ∀ (m : X.Ψ → ℂ), ∀ x ∈ X.dom,
    (∀ s : X.Ψ → ℝ, G (X.flowV e (fun τ => (s τ : ℂ)) x) =
      cexp (4 * Real.pi * I * ∑ τ, m τ * s τ) * G x) →
    ∀ s : X.Ψ → ℂ, X.flowV e s x ∈ X.dom →
      G (X.flowV e s x) = cexp (4 * Real.pi * I * ∑ τ, m τ * s τ) * G x

def NonvanishingCoefficientPositivity : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (u : Fin 2 → Fin r → E), IsIsoPair X.Gm u → (∀ i, u i ∈ X.Λ) →
    ∀ (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ), P ∈ X.SS la →
    (∀ γ ∈ X.Γ, (∀ v ∈ X.Λ, ∃ y ∈ X.Λ,
        Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) v - v = (X.g : E) • y) → X.χ la γ = 1) →
    ∀ χ : X.Ψ → Fin 2 → Fin 2 → ℂ, (∃ x ∈ X.dom, X.fz u X.g χ P x ≠ 0) →
      ∀ τ, (Matrix.of (χ τ)).PosDef

def IsotropicFlowSetting {r : ℕ} (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E)
    (ν : X.Ψ → ℝ) (c1 w : ℝ) (z0 : Frame X.Ψ r) (x : Fin r → E) (a : X.Ψ → Fin 2 → ℂ) : Prop :=
  ShortVectorHypotheses X la P ξ ν c1 w z0 ∧ x ∈ X.L' ∧ herm X.Gm x ξ = 0 ∧ herm X.Gm x x = 0 ∧ (∀ e : E, x ≠ e • ξ) ∧
    (∀ τ, X.ucomp z0 ξ (X.embV x) τ ≠ 0) ∧
    ∀ τ, X.uvec ![ξ, (X.NC : E) • x] a τ =
      ((Real.sqrt (X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)))⁻¹ : ℂ) •
        X.ucomp z0 ξ (X.embV x) τ

def CoefficientIndexLowerBound : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (ν : X.Ψ → ℝ)
    (c1 w : ℝ) (z0 : Frame X.Ψ r) (x : Fin r → E) (a : X.Ψ → Fin 2 → ℂ) (ε : ℝ),
    IsotropicFlowSetting X la P ξ ν c1 w z0 x a → 0 < ε →
    (∀ τ, X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ) ≤ ε) →
    ∀ χ : X.Ψ → Fin 2 → Fin 2 → ℂ, (∃ y ∈ X.dom, X.fz ![ξ, (X.NC : E) • x] X.g χ (X.fj la ξ ν P) y ≠ 0) →
      (fdeg E : ℝ) ^ 2 / ((X.g * dE E ^ 2) ^ 2 * (X.NC : ℝ) ^ 2 * c1 * ε) ≤
        2 * ∑ τ, (X.chiAt χ a τ).re

def CoefficientHeightBound : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (ν : X.Ψ → ℝ)
    (c1 w : ℝ) (z0 : Frame X.Ψ r) (x : Fin r → E) (a : X.Ψ → Fin 2 → ℂ),
    IsotropicFlowSetting X la P ξ ν c1 w z0 x a →
    (∀ τ, X.c τ * X.maj z0 τ (Data.emb τ.1 ((X.NC : E) • x)) ≤
      (X.NC : ℝ) ^ 2 * (2 + 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 * (X.NA : ℝ) ^ 2)) →
    ∀ t : ℝ, 1 ≤ t →
      let K2 := 1 + X.g * dE E ^ 2 * ((X.NC : ℝ) ^ 2 * (2 + 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 *
        (X.NA : ℝ) ^ 2)) * (2 * c1 + 1)
      let S := {χ : X.Ψ → Fin 2 → Fin 2 → ℂ | (∃ y ∈ X.dom, X.fz ![ξ, (X.NC : E) • x] X.g χ
        (X.fj la ξ ν P) y ≠ 0) ∧ 2 * ∑ τ, (X.chiAt χ a τ).re ≤ t}
      S.Finite ∧ (S.ncard : ℝ) ≤ (K2 * t) ^ (4 * fdeg E)

def CountingExponentialSum : Prop :=
  ∀ (K N w : ℝ), 1 ≤ K → 1 ≤ N → 0 ≤ w → ∀ (ι : Type) (t : ι → ℝ),
    (∀ j, w + N * Real.log (2 * K * N) + N + 2 < t j) →
    (∀ t0 : ℝ, 1 ≤ t0 → {j | t j ≤ t0}.Finite ∧ ({j | t j ≤ t0}.ncard : ℝ) ≤ (K * t0) ^ N) →
    Summable (fun j => Real.exp (-Real.pi * t j)) ∧
      2 ^ (w / 2) * ∑' j, Real.exp (-Real.pi * t j) < 1 / 2

def IsotropicOutsideLine : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (ξ : Fin r → E), X.IsIso ξ → ∀ z0 ∈ X.FramesOverBasis ξ, ∀ x ∈ X.L',
    herm X.Gm x ξ = 0 → (∀ e : E, x ≠ e • ξ) → (∀ τ, X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ) < 1) →
    herm X.Gm x x = 0 ∧ ∃ α : 𝓞 E,
      let x' := x + ((X.NA : E) * α) • ξ
      x' ∈ X.L' ∧ herm X.Gm x' ξ = 0 ∧ X.ucomp z0 ξ (X.embV x') = X.ucomp z0 ξ (X.embV x) ∧
      (∀ τ, ‖X.Hf z0 τ (Data.emb τ.1 x') (Data.emb τ.1 ξ) / X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)‖ ≤
        2 * (fdeg E : ℝ) ^ 2 * rdE E * X.NA) ∧
      ∀ τ, X.c τ * X.maj z0 τ (Data.emb τ.1 ((X.NC : E) • x')) ≤
        (X.NC : ℝ) ^ 2 * (2 + 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 * (X.NA : ℝ) ^ 2)

end

end ReciprocityTheory.ChartRestriction.G.FD
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowMatMulVec
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section herm

variable {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)

lemma hC_add_left (u u' v : Fin r → ℂ) : hermC τ G (u + u') v = hermC τ G u v + hermC τ G u' v := by
  simp only [hermC, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma hC_sub_left (u u' v : Fin r → ℂ) : hermC τ G (u - u') v = hermC τ G u v - hermC τ G u' v := by
  simp only [hermC, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

lemma hC_smul_left (c : ℂ) (u v : Fin r → ℂ) : hermC τ G (c • u) v = c * hermC τ G u v := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma hC_add_right (u v v' : Fin r → ℂ) : hermC τ G u (v + v') = hermC τ G u v + hermC τ G u v' := by
  simp only [hermC, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]

lemma hC_smul_right (c : ℂ) (u v : Fin r → ℂ) : hermC τ G u (c • v) = conj c * hermC τ G u v := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma hC_sum_left {ι : Type*} (s : Finset ι) (f : ι → Fin r → ℂ) (v : Fin r → ℂ) :
    hermC τ G (∑ i ∈ s, f i) v = ∑ i ∈ s, hermC τ G (f i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hermC]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hC_add_left, ih]

lemma hC_symm (hG : ∀ a b, cc (G a b) = G b a) (u v : Fin r → ℂ) :
    hermC τ G v u = conj (hermC τ G u v) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hermC, map_sum, map_mul, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← emb_cc, hG]
  ring

lemma emb_herm (x y : Fin r → E) : τ (herm G x y) = hermC τ G (Data.emb τ x) (Data.emb τ y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [herm, hermC, Data.emb, map_sum, map_mul, emb_cc]

end herm

namespace Data

variable {r : ℕ} (X : Data E r)

lemma col_mul (A B : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) : col (A * B) a = Matrix.mulVec A (col B a) := by
  funext k; simp [col, Matrix.mul_apply, Matrix.mulVec, dotProduct]

lemma flowMat_mulVec (ξ : Fin r → E) (τ : X.Ψ) (s : ℂ) (v : Fin r → ℂ) :
    Matrix.mulVec (X.flowMat ξ τ s) v =
      v + (-(I * X.c τ * s) * hermC τ.1 X.Gm v (emb τ.1 ξ)) • emb τ.1 ξ := by
  funext a
  simp only [flowMat, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, hermC, emb, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [sub_eq_add_neg]
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => ?_
  ring

lemma mat_flow (ξ : Fin r → E) (s : X.Ψ → ℂ) (x : Frame X.Ψ r) (τ : X.Ψ) :
    mat (X.flow ξ s x) τ = X.flowMat ξ τ (s τ) * mat x τ := rfl

lemma ppos_eq_of (x : Frame X.Ψ r) (τ : X.Ψ) (hA : (X.gramPos x τ).det ≠ 0) (u : Fin r → ℂ)
    (β : Fin X.p0 → ℂ)
    (horth : ∀ b : Fin X.p0, hermC τ.1 X.Gm (u - ∑ a, β a • col (mat x τ) (Fin.castLE X.p0_le a))
      (col (mat x τ) (Fin.castLE X.p0_le b)) = 0) :
    X.ppos x τ u = ∑ a, β a • col (mat x τ) (Fin.castLE X.p0_le a) := by
  set A := X.gramPos x τ with hAdef
  set cf : Fin X.p0 → ℂ := fun b => hermC τ.1 X.Gm u (col (mat x τ) (Fin.castLE X.p0_le b))
  have hc : cf = Matrix.vecMul β A := by
    funext b
    have h := horth b
    rw [hC_sub_left, sub_eq_zero, hC_sum_left] at h
    simp only [cf, h, hC_smul_left, Matrix.vecMul, dotProduct, hAdef, gramPos, gram,
      Matrix.submatrix_apply, Matrix.of_apply]
  have hα : (fun a => ∑ b, cf b * A⁻¹ b a) = β := by
    have : Matrix.vecMul cf A⁻¹ = β := by
      rw [hc, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (Ne.isUnit hA), Matrix.vecMul_one]
    rw [← this]; rfl
  unfold ppos
  rw [← hα]

lemma ppos_orth (x : Frame X.Ψ r) (τ : X.Ψ) (hA : (X.gramPos x τ).det ≠ 0) (u : Fin r → ℂ)
    (b : Fin X.p0) : hermC τ.1 X.Gm (u - X.ppos x τ u) (col (mat x τ) (Fin.castLE X.p0_le b)) = 0 := by
  set A := X.gramPos x τ with hAdef
  set cf : Fin X.p0 → ℂ := fun b => hermC τ.1 X.Gm u (col (mat x τ) (Fin.castLE X.p0_le b))
  have key : Matrix.vecMul (Matrix.vecMul cf A⁻¹) A = cf := by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (Ne.isUnit hA), Matrix.vecMul_one]
  have h2 := congrFun key b
  simp only [Matrix.vecMul, dotProduct] at h2
  rw [hC_sub_left, sub_eq_zero]
  unfold ppos
  rw [hC_sum_left]
  simp only [hC_smul_left]
  rw [show hermC τ.1 X.Gm u (col (mat x τ) (Fin.castLE X.p0_le b)) = cf b from rfl, ← h2]
  rfl

lemma gramPos_det_ne {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) : (X.gramPos x τ).det ≠ 0 := by
  have h := (hx τ).2 ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩
  intro h0
  have : dmin X.Gm x τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ = 0 := h0
  rw [this] at h
  simp at h

end Data

end ReciprocityTheory.ChartRestriction.G.FD
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermitianPairingAlgebra
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField
open scoped nonZeroDivisors

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

namespace HermitianPairingAlgebra

lemma cc_cc (a : E) : cc (cc a) = a := by
  exact IsCMField.complexConj_apply_apply E a

lemma cc_mul (a b : E) : cc (a * b) = cc a * cc b := by
  exact map_mul (IsCMField.complexConj E) a b

lemma cc_add (a b : E) : cc (a + b) = cc a + cc b := by
  exact map_add (IsCMField.complexConj E) a b

lemma cc_sum {ι : Type*} (s : Finset ι) (f : ι → E) : cc (∑ i ∈ s, f i) = ∑ i ∈ s, cc (f i) := by
  exact map_sum (IsCMField.complexConj E) f s

lemma herm_add_left {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (x x' y : Fin r → E) :
    herm G (x + x') y = herm G x y + herm G x' y := by
  simp only [herm, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma herm_smul_left {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (a : E) (x y : Fin r → E) :
    herm G (a • x) y = a * herm G x y := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma herm_sub_left {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (x x' y : Fin r → E) :
    herm G (x - x') y = herm G x y - herm G x' y := by
  simp only [herm, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

lemma herm_symm {r : ℕ} {G : Matrix (Fin r) (Fin r) E} (hG : ∀ a b, cc (G a b) = G b a)
    (x y : Fin r → E) : cc (herm G x y) = herm G y x := by
  simp only [herm, cc_sum, cc_mul, cc_cc, hG]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma smul_mem' {r : ℕ} {M : Submodule (𝓞 E) (Fin r → E)} {a : E} (ha : IsIntegral ℤ a)
    {y : Fin r → E} (hy : y ∈ M) : a • y ∈ M := by
  convert M.smul_mem (⟨a, ha⟩ : 𝓞 E) hy using 1
  rw [← algebraMap_smul E]
  rfl

noncomputable def pairL {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (ξ : Fin r → E) :
    (Fin r → E) →ₗ[𝓞 E] E where
  toFun y := herm G y ξ
  map_add' x y := herm_add_left G x y ξ
  map_smul' a y := by
    simp only [RingHom.id_apply]
    rw [← algebraMap_smul E a y, herm_smul_left, Algebra.smul_def]

lemma pairL_apply {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (ξ y : Fin r → E) :
    pairL G ξ y = herm G y ξ := rfl

end HermitianPairingAlgebra

open HermitianPairingAlgebra in
theorem hermitian_lattice_pairing_duality : PerpQuotientSelfDual (E := E) := by
  intro r X ξ _ x _ hx
  have hsym : ∀ u v, cc (herm X.Gm u v) = herm X.Gm v u := fun u v => herm_symm X.Gm_herm u v
  have hintcc : ∀ a : E, IsIntegral ℤ a → IsIntegral ℤ (cc a) := fun a ha =>
    ha.map (IsCMField.complexConj E).toAlgHom.toRingHom.toIntAlgHom
  suffices hP : ∃ c : E, ∀ y ∈ X.L', IsIntegral ℤ (herm X.Gm y x - c * herm X.Gm y ξ) by
    obtain ⟨c, hc⟩ := hP
    refine ⟨-cc c, X.L'_dual _ fun y hy => ?_⟩
    have h := hintcc _ (hc y hy)
    have e : cc (herm X.Gm y x - c * herm X.Gm y ξ) = herm X.Gm (x + (-cc c) • ξ) y := by
      rw [herm_add_left, herm_smul_left, ← hsym y x, ← hsym y ξ]
      simp only [cc, map_sub, map_mul, map_neg]
      ring
    rwa [e] at h
  by_cases hI : X.L'.map (pairL X.Gm ξ) = ⊥
  · refine ⟨0, fun y hy => ?_⟩
    have hy0 : herm X.Gm y ξ = 0 := by
      have hm : pairL X.Gm ξ y ∈ X.L'.map (pairL X.Gm ξ) := Submodule.mem_map_of_mem hy
      rw [hI, Submodule.mem_bot, pairL_apply] at hm
      exact hm
    rw [zero_mul, sub_zero, ← hsym x y]
    exact hintcc _ (hx y hy hy0)
  · let J : FractionalIdeal (𝓞 E)⁰ E :=
      ⟨X.L'.map (pairL X.Gm ξ), FractionalIdeal.isFractional_of_fg (X.L'_fg.map _)⟩
    have hJc : (J : Submodule (𝓞 E) E) = X.L'.map (pairL X.Gm ξ) := rfl
    have hJ0 : J ≠ 0 := by
      intro h
      apply hI
      rw [← hJc, h, FractionalIdeal.coe_zero]
    have h1 : (1 : E) ∈ (J : Submodule (𝓞 E) E) * ((J⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) := by
      rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ hJ0]
      exact FractionalIdeal.one_mem_one _
    have key := Submodule.mul_induction_on
      (C := fun w => ∃ c : E, ∀ y ∈ X.L', IsIntegral ℤ (w * herm X.Gm y x - c * herm X.Gm y ξ)) h1
      (fun t ht u hu => by
        rw [hJc] at ht
        obtain ⟨yt, hyt, rfl⟩ := Submodule.mem_map.mp ht
        have hu' := (FractionalIdeal.mem_inv_iff hJ0).mp hu
        have hint : ∀ y ∈ X.L', IsIntegral ℤ (u * herm X.Gm y ξ) := fun y hy => by
          have hs : herm X.Gm y ξ ∈ J := by
            rw [← FractionalIdeal.mem_coe, hJc, ← pairL_apply]
            exact Submodule.mem_map_of_mem hy
          obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff _).mp (hu' _ hs)
          rw [← ha]
          exact a.isIntegral_coe
        refine ⟨u * herm X.Gm yt x, fun y hy => ?_⟩
        have hb := hint yt hyt
        have ha := hint y hy
        have hmem : (u * herm X.Gm yt ξ) • y - (u * herm X.Gm y ξ) • yt ∈ X.L' :=
          X.L'.sub_mem (smul_mem' hb hy) (smul_mem' ha hyt)
        have hz : herm X.Gm ((u * herm X.Gm yt ξ) • y - (u * herm X.Gm y ξ) • yt) ξ = 0 := by
          rw [herm_sub_left, herm_smul_left, herm_smul_left]
          ring
        have h2 := hintcc _ (hx _ hmem hz)
        rw [hsym, herm_sub_left, herm_smul_left, herm_smul_left] at h2
        rw [pairL_apply]
        convert h2 using 1
        ring)
      (fun w1 w2 ⟨c1, h1⟩ ⟨c2, h2⟩ => ⟨c1 + c2, fun y hy => by
        have h3 := (h1 y hy).add (h2 y hy)
        have e : (w1 + w2) * herm X.Gm y x - (c1 + c2) * herm X.Gm y ξ =
            (w1 * herm X.Gm y x - c1 * herm X.Gm y ξ) + (w2 * herm X.Gm y x - c2 * herm X.Gm y ξ) := by
          ring
        show IsIntegral ℤ ((w1 + w2) * herm X.Gm y x - (c1 + c2) * herm X.Gm y ξ)
        rw [e]
        exact h3⟩)
    obtain ⟨c, hc⟩ := key
    exact ⟨c, fun y hy => by simpa using hc y hy⟩

end ReciprocityTheory.ChartRestriction.G.FD
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.TraceIntegralBasis
namespace ReciprocityTheory.ChartRestriction.G.FD.TraceIntegralBasis

open NumberField InfinitePlace Module Submodule
open scoped ComplexConjugate Classical

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

abbrev CP := {w : InfinitePlace E // IsComplex w}

abbrev VS := EuclideanSpace ℂ (CP E)

instance isEmpty_real : IsEmpty {w : InfinitePlace E // IsReal w} :=
  ⟨fun w => (not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w.1)) w.2⟩

noncomputable def iota : E →+ VS E where
  toFun x := WithLp.toLp 2 (fun w : CP E => w.1.embedding x)
  map_zero' := by ext w; simp
  map_add' x y := by ext w; simp

variable {E}

lemma iota_apply (x : E) (w : CP E) : iota E x w = w.1.embedding x := rfl

lemma conj_conj (φ : E →+* ℂ) :
    ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ := by
  first
    | exact ComplexEmbedding.conjugate_conjugate φ
    | (ext x; simp [ComplexEmbedding.conjugate_coe_eq])

lemma inner_iota (x y : E) :
    inner ℝ (iota E x) (iota E y) = ∑ w : CP E, (w.1.embedding x * conj (w.1.embedding y)).re := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [iota_apply, iota_apply, Complex.inner]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

lemma norm_sq_iota (x : E) : ‖iota E x‖ ^ 2 = ∑ w : CP E, ‖w.1.embedding x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [iota_apply]

lemma sum_re_eq_trace (u : E) :
    ∑ w : CP E, (w.1.embedding u).re = (1 / 2 : ℝ) * (Algebra.trace ℚ E u : ℝ) := by
  have hall : ∀ w : InfinitePlace E, IsComplex w := fun w =>
    InfinitePlace.not_isReal_iff_isComplex.mp fun hw =>
      IsEmpty.false (⟨w, hw⟩ : {w : InfinitePlace E // IsReal w})
  have hfib : ∀ w : InfinitePlace E,
      ∑ φ ∈ Finset.univ.filter (fun φ : E →+* ℂ => InfinitePlace.mk φ = w), φ u =
        w.embedding u + conj (w.embedding u) := by
    intro w
    have hne : ComplexEmbedding.conjugate w.embedding ≠ w.embedding := by
      intro h
      exact (InfinitePlace.not_isReal_iff_isComplex.mpr (hall w))
        (InfinitePlace.isReal_iff.mpr (ComplexEmbedding.isReal_iff.mpr h))
    have hset : Finset.univ.filter (fun φ : E →+* ℂ => InfinitePlace.mk φ = w) =
        {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
      ext φ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · intro h
        have h' : InfinitePlace.mk φ = InfinitePlace.mk w.embedding := by
          rw [h, InfinitePlace.mk_embedding]
        rcases InfinitePlace.mk_eq_iff.mp h' with h1 | h1
        · exact Or.inl h1
        · right
          rw [← h1, conj_conj]
      · rintro (rfl | rfl)
        · exact InfinitePlace.mk_embedding w
        · rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
    rw [hset, Finset.sum_pair hne.symm, ComplexEmbedding.conjugate_coe_eq]
  have h0 : algebraMap ℚ ℂ (Algebra.trace ℚ E u) = ∑ σ : E →ₐ[ℚ] ℂ, σ u := by
    first
      | exact trace_eq_sum_embeddings ℂ
      | exact trace_eq_sum_embeddings ℂ (x := u)
      | exact trace_eq_sum_embeddings (E := ℂ) (x := u)
      | exact Algebra.trace_eq_sum_embeddings ℂ
  have h1 : ∑ σ : E →ₐ[ℚ] ℂ, σ u = ∑ φ : E →+* ℂ, φ u :=
    (Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) (fun φ : E →+* ℂ => φ u)
      (fun σ : E →ₐ[ℚ] ℂ => σ u)
      (fun _ => rfl)).symm
  have h2 : ∑ φ : E →+* ℂ, φ u =
      ∑ w : InfinitePlace E, (w.embedding u + conj (w.embedding u)) := by
    rw [← Finset.sum_fiberwise Finset.univ (fun φ : E →+* ℂ => InfinitePlace.mk φ) (fun φ => φ u)]
    refine Finset.sum_congr rfl fun w _ => ?_
    first
      | exact hfib w
      | convert hfib w
  have h3 : ((Algebra.trace ℚ E u : ℚ) : ℂ) =
      ∑ w : CP E, (w.1.embedding u + conj (w.1.embedding u)) := by
    rw [← eq_ratCast (algebraMap ℚ ℂ), h0, h1, h2]
    exact (Fintype.sum_equiv (Equiv.subtypeUnivEquiv hall) _ _ (fun _ => rfl)).symm
  have h4 := congrArg Complex.re h3
  rw [Complex.re_sum] at h4
  simp only [Complex.add_re, Complex.conj_re, Complex.ratCast_re] at h4
  rw [h4, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  ring

variable (E)

noncomputable def toVS : mixedEmbedding.mixedSpace E ≃ₗ[ℝ] VS E :=
  LinearEquiv.ofLinearMap
    (f := (WithLp.linearEquiv 2 ℝ (CP E → ℂ)).symm.toLinearMap ∘ₗ LinearMap.snd ℝ _ _)
    (g := LinearMap.inr ℝ _ _ ∘ₗ (WithLp.linearEquiv 2 ℝ (CP E → ℂ)).toLinearMap)
    (by ext z w; simp)
    (by
      apply LinearMap.ext
      intro z
      refine Prod.ext (funext fun w => (IsEmpty.false w).elim) ?_
      simp)

noncomputable def bas : Basis (Free.ChooseBasisIndex ℤ (𝓞 E)) ℝ (VS E) :=
  (mixedEmbedding.latticeBasis E).map (toVS E)

variable {E}

lemma bas_apply (i : Free.ChooseBasisIndex ℤ (𝓞 E)) : bas E i = iota E (integralBasis E i) := by
  rw [bas, Basis.map_apply, mixedEmbedding.latticeBasis_apply]
  first
    | rfl
    | (ext w; simp [toVS, iota, mixedEmbedding])

lemma mem_span_bas {x : VS E} (hx : x ∈ span ℤ (Set.range (bas E))) :
    ∃ α : 𝓞 E, x = iota E (α : E) := by
  obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun ℤ).1 hx
  refine ⟨∑ i, c i • RingOfIntegers.basis E i, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [bas_apply, integralBasis_apply, ← map_zsmul, ← map_sum]

lemma card_CP : Fintype.card (CP E) = fdeg E ∧ finrank ℚ E = 2 * Fintype.card (CP E) := by
  have h := InfinitePlace.card_add_two_mul_card_eq_rank E
  have h0 : nrRealPlaces E = 0 := by
    first
      | exact Fintype.card_eq_zero
      | simp [nrRealPlaces]
  have h1 : nrComplexPlaces E = Fintype.card (CP E) := rfl
  rw [h0, zero_add, h1] at h
  refine ⟨?_, h.symm⟩
  unfold fdeg
  rw [← h]
  omega

lemma finrank_VS : finrank ℝ (VS E) = finrank ℚ E := by
  rw [← (toVS E).finrank_eq]
  first
    | exact mixedEmbedding.finrank E
    | exact mixedEmbedding.finrank

end ReciprocityTheory.ChartRestriction.G.FD.TraceIntegralBasis
end

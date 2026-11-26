module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtData

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpolationModelInequalities
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates
open scoped ContDiff ENNReal

noncomputable section

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
  {E : Type} [Field E] [NumberField E] [IsCMField E]

def BasePotentialExistence {r : ℕ} (X : FD.Data E r) (de : Wt X.Ψ r) (rr a1 : ℝ) : Prop :=
  ∃ ps0 : Frame X.Ψ r → ℝ, IsInvFn X ps0 ∧
    (∀ x0 ∈ X.dom, ContDiffOn ℝ ∞ (fun z => ps0 (cpt X x0 z)) {z | cpt X x0 z ∈ X.dom}) ∧
    (∀ x0 ∈ X.dom, ∀ z, cpt X x0 z ∈ X.dom → ∀ ξ : Fin (nd X) → ℂ,
      -(rr / 2 * leviM X (phla X de) x0 z ξ) ≤ leviM X ps0 x0 z ξ) ∧
    cfwM X ps0 a1

def InterpolationModelInequalities {r : ℕ} (X : FD.Data E r) {N : ℕ} (L eW : Wt X.Ψ r) (w : Fin N → Frame X.Ψ r → ℂ)
    (et : Frame X.Ψ r → ℂ) (c i : ℝ) (ph : Frame X.Ψ r → ℝ) : Prop :=
  (∃ K : ℝ, ∀ x ∈ X.dom, Real.exp (-(2 * c * ph x)) ≤ K * ∑ k, X.pnorm L (w k) x ^ 2) ∧
  ∃ K : ℝ, ∀ x ∈ X.dom, X.pnorm eW et x ^ 2 ≤ K * Real.exp (-(2 * i * ph x))

def IsDominantR {r : ℕ} (X : FD.Data E r) (v : X.Ψ → Fin r → ℝ) : Prop :=
  ∀ τ : X.Ψ, (∀ i j : Fin r, i ≤ j → (j : ℕ) < X.p0 → v τ j ≤ v τ i) ∧
    (∀ i j : Fin r, X.p0 ≤ (i : ℕ) → i ≤ j → v τ j ≤ v τ i) ∧
    (∀ i j : Fin r, (i : ℕ) < X.p0 → X.p0 ≤ (j : ℕ) → v τ i ≤ v τ j)

def CurvNumStatement : Prop :=
  ∀ (r : ℕ) (X : FD.Data E r) (L de Fp : Wt X.Ψ r) (T rr η : ℝ), 0 < η → 0 < rr → 0 ≤ T →
    IsStrictDom X L → IsStrictDom X (2 • L - de) →
    (∀ t ∈ ({0, 2 * T / rr} : Set ℝ), IsDominantR X fun τ a =>
      ((Fp - kapW X - nd X • L) τ a : ℝ) - t * (rr / 2) * (de τ a : ℝ) - 2 * η * (L τ a : ℝ)) →
    (∀ x0 ∈ X.dom, ∀ z, cpt X x0 z ∈ X.dom → ∀ ξ : Fin (nd X) → ℂ, ξ ≠ 0 →
      0 < leviM X (phla X L) x0 z ξ) ∧
    (∀ x0 ∈ X.dom, ∀ z, cpt X x0 z ∈ X.dom → ∀ ξ : Fin (nd X) → ℂ, ξ ≠ 0 →
      0 < leviM X (phla X (2 • L - de)) x0 z ξ) ∧
    ∀ t : ℝ, 0 ≤ t → t * rr ≤ 2 * T → ∀ x0 ∈ X.dom, ∀ z, cpt X x0 z ∈ X.dom → ∀ ξ : Fin (nd X) → ℂ,
      2 * η * leviM X (phla X L) x0 z ξ ≤
        leviM X (phla X (Fp - kapW X - nd X • L)) x0 z ξ - t * (rr / 2) * leviM X (phla X de) x0 z ξ

def de2W {r : ℕ} (X : FD.Data E r) : Wt X.Ψ r := fun _ j => if X.p0 ≤ (j : ℕ) then 1 else -1

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ModeHalfStatementPfC
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

namespace ModeHalfC

open Matrix NumberField Complex ReciprocityTheory.ChartRestriction.G.FD Topology Filter ModeHalfA ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.L2DbarEstimates Module

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem posDef_int_lower {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosDef) :
    ∃ m0 : ℝ, 0 < m0 ∧ ∀ x : Fin N → ℤ, x ≠ 0 →
      m0 ≤ (fun i => (x i : ℝ)) ⬝ᵥ (A *ᵥ fun i => (x i : ℝ)) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    exact ⟨1, one_pos, fun x hx => absurd (Subsingleton.elim x 0) hx⟩
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  let q : (Fin N → ℝ) → ℝ := fun y => y ⬝ᵥ (A *ᵥ y)
  have hqc : Continuous q :=
    continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)
  have hpos : ∀ y : Fin N → ℝ, y ≠ 0 → 0 < q y := by
    intro y hy
    have h0 := hA.dotProduct_mulVec_pos hy
    simpa [q] using h0

  obtain ⟨y0, hy0, hmin⟩ := (isCompact_sphere (0 : Fin N → ℝ) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr zero_le_one) hqc.continuousOn
  have hy0ne : y0 ≠ 0 := by
    intro h
    rw [h, mem_sphere_zero_iff_norm, norm_zero] at hy0
    exact zero_ne_one hy0
  refine ⟨q y0, hpos y0 hy0ne, fun x hx => ?_⟩
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hx (funext hc)
  have hs1 : 1 ≤ ‖(fun i => (x i : ℝ))‖ := by
    have h1 : (1 : ℝ) ≤ |(x i : ℝ)| := by exact_mod_cast Int.one_le_abs hi
    calc (1 : ℝ) ≤ ‖(x i : ℝ)‖ := by rw [Real.norm_eq_abs]; exact h1
      _ ≤ ‖(fun i => (x i : ℝ))‖ := norm_le_pi_norm (fun i => (x i : ℝ)) i
  set xr : Fin N → ℝ := fun i => (x i : ℝ) with hxr
  have hs0 : ‖xr‖ ≠ 0 := (lt_of_lt_of_le one_pos hs1).ne'
  have hy : ‖xr‖⁻¹ • xr ∈ Metric.sphere (0 : Fin N → ℝ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hs0]
  have hq : q xr = ‖xr‖ ^ 2 * q (‖xr‖⁻¹ • xr) := by
    simp only [q, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    field_simp
  have h3 : q y0 ≤ q (‖xr‖⁻¹ • xr) := hmin hy
  have h4 : 0 < q y0 := hpos y0 hy0ne
  have hs2 : 1 ≤ ‖xr‖ ^ 2 := by nlinarith
  show q y0 ≤ q xr
  rw [hq]
  nlinarith

theorem first_minimum_pos (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (hne : ∃ v ∈ X.Λ, v ≠ 0) :
    0 < X.la1 x := by
  obtain ⟨b, hb, h⟩ := ReciprocityTheory.ChartRestriction.G.FD.MajorantNormalForms.exists_normal_frame (X := X) hx
  have horth : IsOrth X (rmul x b) := fun τ => (h τ).1
  have hdet : ∀ τ, (mat (rmul x b) τ).det ≠ 0 := fun τ => (dom_of_orth X horth τ).1
  have hm : ∀ τ v, X.maj x τ v = ∑ a, ‖((mat (rmul x b) τ)⁻¹ *ᵥ v) a‖ ^ 2 :=
    fun τ v => (h τ).2 v
  obtain ⟨m0, hm0, hlow⟩ := posDef_int_lower
    (ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.Am_posDef (X := X) (mat (rmul x b)) hdet
      (ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings.zb (X := X)))

  have hQ : ∀ v ∈ X.Λ, v ≠ 0 → m0 ≤ ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v) := by
    intro v hv hv0
    have e1 : ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v) =
        ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.Qy X (mat (rmul x b)) v := by
      simp only [ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.Qy, hm]
    have hc : (ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings.zb (X := X)).repr ⟨v, hv⟩ ≠ 0 := by
      intro h0
      have h1 := (LinearEquiv.map_eq_zero_iff _).mp h0
      exact hv0 (by simpa using congrArg Subtype.val h1)
    have hx0 : (fun i => (ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings.zb (X := X)).repr ⟨v, hv⟩ i) ≠ 0 := by
      intro h0
      apply hc
      ext i
      exact congrFun h0 i
    have e2 := ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.quad_int (X := X) (mat (rmul x b))
      (ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings.zb (X := X))
      (fun i => (ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings.zb (X := X)).repr ⟨v, hv⟩ i)
    have e3 := ReciprocityTheory.ChartRestriction.G.FD.HermitianLatticeMaps.coe_expand (X := X)
      (ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings.zb (X := X)) ⟨v, hv⟩
    rw [e1]
    calc m0 ≤ _ := hlow _ hx0
      _ = _ := e2
      _ = ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.Qy X (mat (rmul x b)) v := by rw [← e3]
  have hS : m0 ≤ X.firstMinimumSq x := by
    unfold ReciprocityTheory.ChartRestriction.G.FD.Data.firstMinimumSq
    obtain ⟨v, hv, hv0⟩ := hne
    refine le_csInf ⟨_, v, hv, hv0, rfl⟩ ?_
    rintro t ⟨w, hw, hw0, rfl⟩
    exact hQ w hw hw0
  unfold ReciprocityTheory.ChartRestriction.G.FD.Data.la1
  exact Real.sqrt_pos.mpr (lt_of_lt_of_le hm0 hS)

theorem orthonormalize (X : Data E r) {p : Frame X.Ψ r} (hp : p ∈ X.dom) :
    ∃ b ∈ Bor X.Ψ r, IsOrth X (rmul p b) ∧ ∀ τ v, X.maj (rmul p b) τ v = X.maj p τ v := by
  obtain ⟨b, hb, h⟩ := ReciprocityTheory.ChartRestriction.G.FD.MajorantNormalForms.exists_normal_frame (X := X) hp
  have horth : IsOrth X (rmul p b) := fun τ => (h τ).1
  refine ⟨b, hb, horth, fun τ v => ?_⟩
  rw [maj_orth X horth, (h τ).2 v]

theorem maj_nonneg_orth (X : Data E r) {u : Frame X.Ψ r} (hu : IsOrth X u) (τ : X.Ψ) (v : Fin r → ℂ) :
    0 ≤ X.maj u τ v := by
  rw [maj_orth X hu]
  positivity

end ModeHalfC

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.DivStatementPfLE
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.DivStatementPfLB
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter Asymptotics

noncomputable section

variable {n : ℕ}

theorem mulO {f g : V n → ℂ} {a b c : ℕ} (hf : f =O[𝓝 0] fun z => ‖z‖ ^ a)
    (hg : g =O[𝓝 0] fun z => ‖z‖ ^ b) (h : a + b = c) :
    (fun z => f z * g z) =O[𝓝 0] fun z => ‖z‖ ^ c := by
  subst h
  exact (hf.mul hg).congr_right fun z => (pow_add _ _ _).symm

theorem pow_sub_pow {u v : V n → ℂ} (hu : u =O[𝓝 0] fun z => ‖z‖) (hv : v =O[𝓝 0] fun z => ‖z‖)
    (huv : (fun z => u z - v z) =O[𝓝 0] fun z => ‖z‖ ^ 2) (e : ℕ) :
    (fun z => u z ^ e - v z ^ e) =O[𝓝 0] fun z => ‖z‖ ^ (e + 1) := by
  rcases e with _ | e
  · simp only [pow_zero, sub_self]
    exact Asymptotics.isBigO_zero (fun z : V n => ‖z‖ ^ (0 + 1)) (𝓝 (0 : V n))
  · have hs : (fun z : V n => ∑ i ∈ Finset.range (e + 1), u z ^ i * v z ^ (e + 1 - 1 - i)) =O[𝓝 0]
        fun z : V n => ‖z‖ ^ e := by
      have hterm : ∀ i ∈ Finset.range (e + 1), (fun z : V n => u z ^ i * v z ^ (e + 1 - 1 - i)) =O[𝓝 0]
          fun z : V n => ‖z‖ ^ e := by
        intro i hi
        have hi' : i ≤ e := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        refine ((hu.pow i).mul (hv.pow (e + 1 - 1 - i))).congr_right fun z => ?_
        rw [← pow_add]
        congr 1
        omega
      exact (Asymptotics.IsBigO.sum hterm).congr_left fun z => Finset.sum_apply z _ _
    refine ((hs.mul huv).congr_left fun z => ?_).congr_right fun z => ?_
    · exact (Commute.all (u z) (v z)).geom_sum₂_mul (e + 1)
    · ring

theorem prod_pow_O {ι : Type*} (s : Finset ι) (u : ι → V n → ℂ) (e : ι → ℕ)
    (hu : ∀ i, u i =O[𝓝 0] fun z => ‖z‖) :
    (fun z => ∏ i ∈ s, u i z ^ e i) =O[𝓝 0] fun z => ‖z‖ ^ (∑ i ∈ s, e i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.prod_empty, Finset.sum_empty, pow_zero]
    exact Asymptotics.isBigO_const_const (1 : ℂ) one_ne_zero _
  · intro a s ha ih
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    exact mulO ((hu a).pow (e a)) ih rfl

theorem prod_pow_sub {ι : Type*} (s : Finset ι) (u v : ι → V n → ℂ) (e : ι → ℕ)
    (hu : ∀ i, u i =O[𝓝 0] fun z => ‖z‖) (hv : ∀ i, v i =O[𝓝 0] fun z => ‖z‖)
    (huv : ∀ i, (fun z => u i z - v i z) =O[𝓝 0] fun z => ‖z‖ ^ 2) :
    (fun z => ∏ i ∈ s, u i z ^ e i - ∏ i ∈ s, v i z ^ e i) =O[𝓝 0]
      fun z => ‖z‖ ^ (∑ i ∈ s, e i + 1) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.prod_empty, sub_self]
    exact Asymptotics.isBigO_zero (fun z : V n => ‖z‖ ^ (∑ i ∈ (∅ : Finset ι), e i + 1)) (𝓝 (0 : V n))
  · intro a s ha ih
    have hc : e a + (∑ i ∈ s, e i + 1) = ∑ i ∈ insert a s, e i + 1 := by
      have := Finset.sum_insert ha (f := e); omega
    have hc' : (e a + 1) + ∑ i ∈ s, e i = ∑ i ∈ insert a s, e i + 1 := by
      have := Finset.sum_insert ha (f := e); omega
    have h1 := mulO ((hu a).pow (e a)) ih hc
    have h2 := mulO (pow_sub_pow (hu a) (hv a) (huv a) (e a)) (prod_pow_O s v e hv) hc'
    refine (h1.add h2).congr_left fun z => ?_
    simp only [Finset.prod_insert ha]
    ring

theorem taylor2 {g : V n → ℂ} (hg : AnalyticAt ℂ g 0) :
    (fun z => g z - g 0 - fderiv ℂ g 0 z) =O[𝓝 0] fun z => ‖z‖ ^ 2 := by
  obtain ⟨p, hp⟩ := hg
  have h := hp.isBigO_sub_partialSum_pow 2
  rw [hp.hasFDerivAt.fderiv]
  refine h.congr_left fun z => ?_
  have e1 : (p 1 fun _ => z) = p 1 ![z] := by
    congr 1
    funext i
    rw [Subsingleton.elim i 0]
    rfl
  simp [FormalMultilinearSeries.partialSum, Finset.sum_range_succ, hp.coeff_zero, e1]
  try ring

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.DivStatementPfLD
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter Asymptotics

noncomputable section

variable {n : ℕ}

theorem comp_O (L : V n ≃L[ℂ] V n) (k : Fin n) :
    (fun z : V n => (L z) k) =O[𝓝 0] fun z => ‖z‖ := by
  have h1 : (fun z : V n => L z) =O[𝓝 0] fun z => z := (L : V n →L[ℂ] V n).isBigO_id _
  have h2 : (fun z : V n => (L z) k) =O[𝓝 0] fun z => L z := by
    refine IsBigO.of_bound 1 (Filter.Eventually.of_forall fun z => ?_)
    rw [one_mul]
    first
      | exact norm_le_pi_norm (L z) k
      | exact PiLp.norm_apply_le (L z) k
      | simpa using norm_le_pi_norm (L z) k
  exact (h2.trans h1).trans (isBigO_norm_right.mpr (isBigO_refl _ _))

theorem sub_val_O {g : V n → ℂ} (hg : AnalyticAt ℂ g 0) :
    (fun z => g 0 - g z) =O[𝓝 0] fun z => ‖z‖ ^ 1 := by
  have h := hg.differentiableAt.hasFDerivAt.isBigO_sub
  simp only [sub_zero] at h
  have h2 := h.neg_left
  simp only [neg_sub] at h2
  simp only [pow_one]
  exact h2.trans (isBigO_norm_right.mpr (isBigO_refl _ _))

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.DivStatementPfLC
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.DivLC

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
  Asymptotics ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ContDiff ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem nmat_zero' (τ : X.Ψ) : mat (nmat X (0 : V (nd X))) τ = 1 := by
  ext a b
  by_cases h : b < a
  · have hab : a ≠ b := by rintro rfl; exact lt_irrefl _ h
    simp [mat, nmat, h, hab, Matrix.one_apply]
    rfl
  · by_cases hab : a = b
    · subst hab; simp [mat, nmat]
    · simp [mat, nmat, h, hab, Matrix.one_apply]

theorem cpt_zero' (x0 : Frame X.Ψ r) : cpt X x0 0 = x0 := by
  funext τ
  show mat x0 τ * mat (nmat X (0 : V (nd X))) τ = x0 τ
  rw [nmat_zero', mul_one]
  rfl

theorem nmat_zero_mem : nmat X (0 : V (nd X)) ∈ Bor X.Ψ r := by
  simp only [Bor, Set.mem_setOf_eq]
  intro τ
  refine ⟨?_, fun a c hca => ?_⟩
  · rw [nmat_zero']; simp
  · simp [nmat, hca]
    rfl

theorem lact_one' (y : Frame X.Ψ r) : lact (1 : GL (Fin r) E) y = y := by
  funext τ
  simp only [lact, Units.val_one]
  rw [Matrix.map_one _ (map_zero _) (map_one _), one_mul]
  rfl

theorem s_xs_zero {Xa : ArchInM X} (Fl : FlatM X Xa) (j : Fin Fl.δ) (k : Fin (nd X)) :
    Fl.s k (Fl.xs j) = 0 := by
  have he : Fl.xs j = lact (1 : GL (Fin r) E) (rmul (Fl.xs j) (nmat X 0)) := by
    rw [lact_one']
    exact (cpt_zero' X (Fl.xs j)).symm
  exact (Fl.S_eq (Fl.xs j) (Fl.xs_mem j)).mpr ⟨j, 1, X.Γ.one_mem, nmat X 0, nmat_zero_mem X, he⟩ k

theorem anal_loc {P : Frame X.Ψ r → ℂ} (hP : DifferentiableOn ℂ P X.dom) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) : AnalyticAt ℂ (fun z => P (cpt X x z)) 0 := by
  have hc := OntoB.cd_cpt X x
  have hU : IsOpen {z : V (nd X) | cpt X x z ∈ X.dom} :=
    (FourierCoefficientDomain.isOpen_dom X).preimage hc.continuous
  refine DivLA.analyticAt_of_diffOn hU ?_ (by simpa [cpt_zero'] using hx)
  exact hP.comp (hc.differentiable (by simp)).differentiableOn (fun z hz => hz)

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.DivLC
end

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.DivLC

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
  Asymptotics ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ContDiff ENNReal Matrix

noncomputable section

theorem coordL {n : ℕ} (W : V n → ℂ) (S : Fin n → V n → ℂ) (hW : AnalyticAt ℂ W 0) (hW0 : W 0 ≠ 0)
    (hS : ∀ k, AnalyticAt ℂ (S k) 0) (hS0 : ∀ k, S k 0 = 0)
    (hdet : (fderiv ℂ (fun z : V n => (WithLp.toLp 2 fun k => S k z / W z : V n)) 0).det ≠ 0) :
    ∃ L : V n ≃L[ℂ] V n, (∀ k z, (L z) k = fderiv ℂ (fun y => S k y / W y) 0 z) ∧
      (fun z => (WithLp.toLp 2 fun k => S k z / W z : V n) - L z) =o[𝓝 0] fun z => z := by
  classical
  let F : V n → V n := fun z => (WithLp.toLp 2 fun k => S k z / W z : V n)
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)
  have hcomp : ∀ k, DifferentiableAt ℂ (fun y => S k y / W y) 0 :=
    fun k => ((hS k).div hW hW0).differentiableAt
  have hG : DifferentiableAt ℂ (fun z k => S k z / W z) 0 := differentiableAt_pi.2 hcomp
  have hFd : DifferentiableAt ℂ F 0 := e.symm.differentiableAt.comp 0 hG
  have hdet' : LinearMap.det (fderiv ℂ F 0 : V n →ₗ[ℂ] V n) ≠ 0 := hdet
  let L : V n ≃L[ℂ] V n :=
    (LinearMap.equivOfDetNeZero (fderiv ℂ F 0 : V n →ₗ[ℂ] V n) hdet').toContinuousLinearEquiv
  have hL : ∀ z, L z = fderiv ℂ F 0 z := fun z => rfl
  refine ⟨L, fun k z => ?_, ?_⟩
  · rw [hL]
    have h1' := ((PiLp.proj 2 (fun _ : Fin n => ℂ) k).hasFDerivAt (x := F 0)).comp (0 : V n) hFd.hasFDerivAt
    have h1 : HasFDerivAt (fun y => S k y / W y)
        ((PiLp.proj 2 (fun _ : Fin n => ℂ) k).comp (fderiv ℂ F 0)) 0 := h1'
    rw [h1.fderiv]
    rfl
  · have h2 := hFd.hasFDerivAt.isLittleO
    have hF0 : F 0 = 0 := by
      apply PiLp.ext
      intro k
      simp [F, hS0]
    simp only [hF0, sub_zero] at h2
    exact h2

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.DivLC
end

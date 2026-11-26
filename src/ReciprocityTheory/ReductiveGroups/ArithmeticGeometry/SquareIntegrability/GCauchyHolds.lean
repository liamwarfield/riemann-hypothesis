module

public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SSAscent
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitR
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.InvBuild
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColEmpty
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.HfNormLeTwo
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PerFactor
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitO

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Imports
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.CharMain
namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section

namespace ChA

lemma omega_fin {E : Type} [Field E] [NumberField E] [IsCMField E] :
    ∃ ω : Fin (Module.finrank ℚ E) → 𝓞 E, LinearIndependent ℚ (fun j => (ω j : E)) ∧
      ∀ j (τ : E →+* ℂ), ‖τ (ω j : E)‖ ≤ omStar (E := E) := by
  obtain ⟨n, ω, hωB, hspan⟩ := omega_exists' (E := E)
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' (K := ℚ) (fun j => (ω j : E))
  have htop : Submodule.span ℚ (Set.range ((fun j => (ω j : E)) ∘ a)) = ⊤ := by
    rw [hsp, eq_top_iff, ← (NumberField.integralBasis E).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [NumberField.integralBasis_apply]
    exact hspan _
  haveI : Finite κ := Finite.of_injective a ha
  haveI : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = Module.finrank ℚ E := by
    rw [← finrank_span_eq_card hli, htop, finrank_top]
  let e : Fin (Module.finrank ℚ E) ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  exact ⟨fun j => ω (a (e j)), hli.comp e e.injective, fun j τ => hωB _ τ⟩

set_option maxHeartbeats 1000000 in
theorem char_main (hx : Ext.All) : CharStatement := by
  intro E _ _ _ X DF P I hI σ ρ hρ
  classical
  have hNP : Ext.NearestPlane := hx.2.2.2.2.1
  obtain ⟨ω, hω, hωB⟩ := omega_fin (E := E)
  have hf1n : 1 ≤ PT.f E := le_trans (Nat.one_le_pow _ _ P.hm1) P.hmf
  have hF1 : (1 : ℝ) ≤ PT.f E := by exact_mod_cast hf1n
  have hm1 : (1 : ℝ) ≤ P.m := by exact_mod_cast P.hm1
  have hrd := P.hrd
  have hmf : ((P.m : ℝ)) ^ 4 ≤ PT.f E := by exact_mod_cast P.hmf
  have hf2 := P.hf2
  have hdR : (dstar (E := E) P.m : ℝ) = 2 * PT.f E * P.m := by simp [dstar]
  have hd2 : (2 : ℝ) ≤ dstar (E := E) P.m := by rw [hdR]; nlinarith
  have hFd : (PT.f E : ℝ) ≤ dstar (E := E) P.m := by rw [hdR]; nlinarith
  have hΩ2 : omStar (E := E) ^ 2 = 4 * (PT.f E : ℝ) ^ 3 * PT.rd E ^ 2 := by
    rw [omStar, mul_pow, mul_pow, ← Real.rpow_natCast ((PT.f E : ℝ) ^ ((3 : ℝ) / 2)),
      ← Real.rpow_mul (by positivity)]
    norm_num
  have hK0 : (0 : ℝ) < (dstar (E := E) P.m : ℝ) ^ 2 * PT.rd E := by positivity
  have hK : (dstar (E := E) P.m : ℝ) * omStar (E := E) ^ 2 / 4 ≤
      ((dstar (E := E) P.m : ℝ) ^ 2 * PT.rd E) ^ 2 := by
    rw [hΩ2]
    have h3 : (PT.f E : ℝ) ^ 3 ≤ (dstar (E := E) P.m : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) hFd 3
    have h4 : 0 ≤ (dstar (E := E) P.m : ℝ) * PT.rd E ^ 2 := by positivity
    calc (dstar (E := E) P.m : ℝ) * (4 * (PT.f E : ℝ) ^ 3 * PT.rd E ^ 2) / 4
        = ((dstar (E := E) P.m : ℝ) * PT.rd E ^ 2) * (PT.f E : ℝ) ^ 3 := by ring
      _ ≤ ((dstar (E := E) P.m : ℝ) * PT.rd E ^ 2) * (dstar (E := E) P.m : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_left h3 h4
      _ = _ := by ring
  have hD : Module.finrank ℝ (IR I) ≤ dstar (E := E) P.m := by
    obtain ⟨ρ', hρ'm, hρ'⟩ := hI.rank
    rw [hρ', dstar, mul_assoc, mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hρ'm)
  obtain ⟨xb, ub, hxub, hspan, hbnd⟩ := exists_short_real_span hI
  have hex : ∀ W : Submodule ℂ (Vsp X.dim), Module.finrank ℂ W < ρ →
      ∃ y ∈ Xg X.L I, prj σ y ∉ W ∧
        ‖y‖ ^ 2 ≤ PT.rd E ^ 2 * (dstar (E := E) P.m : ℝ) ^ 4 * P.ph / (2 * PT.f E) := by
    intro W hW
    obtain ⟨j, hj⟩ := exists_out (by exact hρ) ub hspan W hW
    exact ⟨ub j, ⟨xb j, (hxub j).1, (hxub j).2⟩, hj, hbnd j⟩
  have hρm : ρ ≤ P.m := rho_le hI ω hω (by exact hρ)
  have hρmR : (ρ : ℝ) ≤ P.m := by exact_mod_cast hρm
  obtain ⟨χ, w, R, μ, ε, hinv⟩ := inv_build hNP X.stable hI.stable hI.iso (sep_X hI) ω hω
    (omStar (E := E)) hωB (dstar (E := E) P.m) hD σ ρ _ _ hK0 hK hex ρ le_rfl
  obtain ⟨hχX, hwW, hort, hdec, hεz, hεn, hRb, hred, hflag, hμB⟩ := hinv
  have hph : 0 ≤ P.ph := by
    rw [Par.ph, PT.ph]; split_ifs
    · positivity
    · exact le_rfl
  have hs2 : Real.sqrt 2 < 1.415 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num

  have hcmp : ∀ s : Fin ρ, 30 ≤ 30 * (ρ : ℝ) ^ 2 ∧
      Real.sqrt 2 * (30 * (ρ : ℝ) ^ 2 + 1) + 1 ≤ 3 / 2 * (30 * (ρ : ℝ) ^ 2) := by
    intro s
    have : (1 : ℝ) ≤ ρ := by exact_mod_cast (show 1 ≤ ρ by have := s.2; omega)
    constructor <;> nlinarith [Real.sqrt_nonneg 2]
  have hχn : ∀ s : Fin ρ, ‖χ s‖ ≤ 3 / 2 * (30 * (ρ : ℝ) ^ 2) * ((dstar (E := E) P.m : ℝ) ^ 2 * PT.rd E) * μ s := by
    intro s
    have h1 := (hRb s s.2).2
    have h2 := (hcmp s).2
    have hμ := (hred s s.2).1
    have h3 : 0 ≤ ((dstar (E := E) P.m : ℝ) ^ 2 * PT.rd E) * μ s := by positivity
    have := mul_le_mul_of_nonneg_right h2 h3
    nlinarith
  refine ⟨fun s => w s, fun s => (hχX s s.2).choose, fun s => χ s, fun s => R s,
    fun s s' => ε s s', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s
    have := Wk_le hI.stable σ χ (s + 1) (fun j hj => hχX j (by omega)) (hwW s s.2)
    exact ⟨(Submodule.mem_inf.mp this).2, (Submodule.mem_inf.mp this).1⟩
  · intro s s'
    show Hf (w s) (w s') = _
    rw [Hf_eq_inner, hort s' s'.2 s s.2]
    by_cases h : s = s'
    · subst h; simp
    · rw [if_neg (fun e => h (Fin.ext e).symm), if_neg h]
  · intro s
    exact (hχX s s.2).choose_spec
  · intro s s' h
    exact hεz s s.2 s' (Fin.lt_def.mp h).le
  · intro s
    have hsum : ∑ s' : Fin ρ, ‖ε s s'‖ ^ 2 = ∑ i ∈ Finset.range s, ‖ε s i‖ ^ 2 := by
      rw [show (∑ s' : Fin ρ, ‖ε s s'‖ ^ 2) = ∑ i ∈ Finset.range ρ, ‖ε s i‖ ^ 2 from
        Fin.sum_univ_eq_sum_range (fun i => ‖ε s i‖ ^ 2) ρ]
      symm
      refine Finset.sum_subset (Finset.range_mono s.2.le) fun i _ hi => ?_
      rw [hεz s s.2 i (by simpa using hi), norm_zero]; norm_num
    have hb := hεn s s.2
    have hA := (hcmp s).1
    have hq : 0 ≤ 1 / (30 * (ρ : ℝ) ^ 2) := by positivity
    constructor
    · show Real.sqrt (∑ s' : Fin ρ, ‖ε s s'‖ ^ 2) ≤ _
      rw [hsum, ← Real.sqrt_sq hq]; exact Real.sqrt_le_sqrt hb
    · show ∑ s' : Fin ρ, ‖ε s s'‖ ≤ _
      have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun s' : Fin ρ => ‖ε s s'‖)
      simp only [Finset.card_univ, Fintype.card_fin] at hcs
      rw [hsum] at hcs
      have h0 : 0 ≤ ∑ s' : Fin ρ, ‖ε s s'‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
      have h1 : (∑ s' : Fin ρ, ‖ε s s'‖) ^ 2 ≤ (Real.sqrt ρ / (30 * (ρ : ℝ) ^ 2)) ^ 2 := by
        rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
        calc _ ≤ (ρ : ℝ) * ∑ i ∈ Finset.range s, ‖ε s i‖ ^ 2 := hcs
          _ ≤ (ρ : ℝ) * (1 / (30 * (ρ : ℝ) ^ 2)) ^ 2 := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
          _ = _ := by ring
      have hb0 : 0 ≤ Real.sqrt ρ / (30 * (ρ : ℝ) ^ 2) := by positivity
      nlinarith
  · intro s v hv
    have hR : (R s : ℂ) ≠ 0 := by
      have h1 := (hRb s s.2).1
      have hμ := (hred s s.2).1
      have hA := (hcmp s).1
      have h2 : 0 < (30 * (ρ : ℝ) ^ 2) * ((dstar (E := E) P.m : ℝ) ^ 2 * PT.rd E) * μ s := mul_pos (mul_pos (by linarith) hK0) (by linarith)
      have : 0 < R s := lt_of_lt_of_le h2 h1
      exact_mod_cast this.ne'
    show Hf v (χ s) / (R s : ℂ) = Hf v (w s) + ∑ s' : Fin ρ, ε s s' * Hf v (w s')
    rw [← Hf_prj_right hv (χ s), hdec s s.2]
    simp only [Hf_eq_inner, inner_smul_left, inner_add_left, sum_inner, Complex.conj_ofReal,
      Complex.conj_conj]
    rw [mul_div_cancel_left₀ _ hR]
    congr 1
    rw [show (∑ s' : Fin ρ, ε s s' * inner ℂ (w s') v) = ∑ i ∈ Finset.range ρ, ε s i * inner ℂ (w i) v from
      Fin.sum_univ_eq_sum_range (fun i => ε s i * inner ℂ (w i) v) ρ]
    refine Finset.sum_subset (Finset.range_mono s.2.le) fun i _ hi => ?_
    rw [hεz s s.2 i (by simpa using hi), zero_mul]
  · intro s
    show ‖χ s‖ ≤ 1.5 * R s ∧ 1 ≤ 2 * Real.pi * R s
    have hRs := (hRb s s.2).1
    have hμ := (hred s s.2).1
    have hA := (hcmp s).1
    have hn := hχn s
    have hK1 : 1 ≤ ((dstar (E := E) P.m : ℝ) ^ 2 * PT.rd E) := by nlinarith
    have h1 : 30 ≤ (30 * (ρ : ℝ) ^ 2) * ((dstar (E := E) P.m : ℝ) ^ 2 * PT.rd E) := by nlinarith
    have hX : 30 ≤ (30 * (ρ : ℝ) ^ 2) * ((dstar (E := E) P.m : ℝ) ^ 2 * PT.rd E) * μ s := by nlinarith
    have e15 : (1.5 : ℝ) = 3 / 2 := by norm_num
    rw [e15]
    constructor
    · nlinarith
    · nlinarith [Real.pi_gt_three]
  · intro s y hy uy hU
    show |2 * inner ℝ (χ s) uy| ≤ M1 (E := E) P.m * ‖uy‖ ^ 2
    have huy : uy ∈ Xg X.L I := ⟨y, hy, hU⟩
    have hA := (hcmp s).1
    have hM : 3 * (30 * (ρ : ℝ) ^ 2) * ((dstar (E := E) P.m : ℝ) ^ 2 * PT.rd E) ≤ M1 (E := E) P.m := by
      rw [M1]
      have h1 : (ρ : ℝ) ^ 2 ≤ (P.m : ℝ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hρmR 2
      have h2 := mul_le_mul_of_nonneg_right h1 hK0.le
      nlinarith
    have hK1 : 1 ≤ ((dstar (E := E) P.m : ℝ) ^ 2 * PT.rd E) := by nlinarith
    have hM1 : 1 ≤ M1 (E := E) P.m := by nlinarith
    have e1 : |2 * inner ℝ (χ s) uy| ≤ 2 * (‖χ s‖ * ‖uy‖) := by
      rw [abs_mul, abs_two]
      exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by norm_num)
    rcases (hred s s.2).2 uy huy with h | h
    · have := mul_le_mul_of_nonneg_right hM1 (sq_nonneg ‖uy‖)
      linarith
    · have hn := hχn s
      have h2 : ‖χ s‖ ≤ 3 / 2 * (30 * (ρ : ℝ) ^ 2) * ((dstar (E := E) P.m : ℝ) ^ 2 * PT.rd E) * ‖uy‖ :=
        le_trans hn (mul_le_mul_of_nonneg_left h (by positivity))
      have h3 := mul_le_mul_of_nonneg_right h2 (norm_nonneg uy)
      have h4 := mul_le_mul_of_nonneg_right hM (sq_nonneg ‖uy‖)
      nlinarith
  · intro s
    show ‖χ s‖ ^ 2 ≤ Cchi (E := E) P.m * P.ph
    have hn := hχn s
    have hμ := (hred s s.2).1
    have hB := hμB s s.2
    have h0 : 0 ≤ 3 / 2 * (30 * (ρ : ℝ) ^ 2) * ((dstar (E := E) P.m : ℝ) ^ 2 * PT.rd E) := by positivity
    have h1 : ‖χ s‖ ^ 2 ≤ (3 / 2 * (30 * (ρ : ℝ) ^ 2) * ((dstar (E := E) P.m : ℝ) ^ 2 * PT.rd E)) ^ 2 * (PT.rd E ^ 2 * (dstar (E := E) P.m : ℝ) ^ 4 * P.ph / (2 * (PT.f E : ℝ))) := by
      calc ‖χ s‖ ^ 2 ≤ (3 / 2 * (30 * (ρ : ℝ) ^ 2) * ((dstar (E := E) P.m : ℝ) ^ 2 * PT.rd E) * μ s) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
        _ = (3 / 2 * (30 * (ρ : ℝ) ^ 2) * ((dstar (E := E) P.m : ℝ) ^ 2 * PT.rd E)) ^ 2 * μ s ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hB (sq_nonneg _)
    have hFpos : (0 : ℝ) < (PT.f E : ℝ) := by linarith
    have hd4 : (dstar (E := E) P.m : ℝ) ^ 4 ≤ 8 * (PT.f E : ℝ) * PT.rd E ^ 3 := by
      rw [hdR]
      have h5 : 16 * (PT.f E : ℝ) ^ 4 * (P.m : ℝ) ^ 4 ≤ 16 * (PT.f E : ℝ) ^ 5 := by
        have := mul_le_mul_of_nonneg_left hmf (by positivity : (0 : ℝ) ≤ 16 * (PT.f E : ℝ) ^ 4)
        nlinarith
      have h6 : (PT.f E : ℝ) ^ 4 ≤ PT.rd E ^ 2 := by
        have := pow_le_pow_left₀ (by positivity) hf2 2
        nlinarith
      have h7 : 16 * (PT.f E : ℝ) ^ 4 ≤ PT.rd E * PT.rd E ^ 2 := by nlinarith
      have h8a := mul_le_mul_of_nonneg_left h7 hFpos.le
      have h8b : 0 ≤ (PT.f E : ℝ) * PT.rd E ^ 3 := by positivity
      have h8 : 16 * (PT.f E : ℝ) ^ 5 ≤ 8 * (PT.f E : ℝ) * PT.rd E ^ 3 := by nlinarith
      nlinarith
    have hρ4 : (ρ : ℝ) ^ 4 ≤ (P.m : ℝ) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hρmR 4
    have hdF : (dstar (E := E) P.m : ℝ) ^ 4 / (PT.f E : ℝ) ≤ 8 * PT.rd E ^ 3 := by rw [div_le_iff₀ hFpos]; linarith
    have hC : 0 ≤ 2025 / 2 * (dstar (E := E) P.m : ℝ) ^ 4 * PT.rd E ^ 4 * P.ph := mul_nonneg (by positivity) hph
    refine h1.trans ?_
    calc _ = (2025 / 2 * (dstar (E := E) P.m : ℝ) ^ 4 * PT.rd E ^ 4 * P.ph) * ((ρ : ℝ) ^ 4 * ((dstar (E := E) P.m : ℝ) ^ 4 / (PT.f E : ℝ))) := by
          field_simp; ring
      _ ≤ (2025 / 2 * (dstar (E := E) P.m : ℝ) ^ 4 * PT.rd E ^ 4 * P.ph) * ((P.m : ℝ) ^ 4 * (8 * PT.rd E ^ 3)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hρ4 hdF (by positivity) (by positivity)) hC
      _ = Cchi (E := E) P.m * P.ph := by rw [Cchi, RR]; ring

end ChA
end
end ReciprocityTheory.ChartRestriction.G.I2
end

namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex

theorem char (hx : Ext.All) : CharStatement :=
  ChA.char_main hx

end ReciprocityTheory.ChartRestriction.G.I2
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ImportsAlt
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitG
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitU
namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex
open scoped InnerProductSpace

noncomputable section

variable {E : Type} [Field E] [NumberField E]

section lin

variable {dim : (E →+* ℂ) → ℕ}

theorem IsU.add' {I : Submodule ℤ (Vsp dim)} {x y u v : Vsp dim} (hu : IsU I x u)
    (hv : IsU I y v) : IsU I (x + y) (u + v) := by
  refine ⟨add_mem hu.1 hv.1, fun a ha => ?_⟩
  have hH : Hf (x + y) a = Hf x a + Hf y a := by
    simp [Hf, add_mul, Finset.sum_add_distrib]
  rw [inner_add_left, hu.2 a ha, hv.2 a ha, hH, Complex.add_im]

theorem IsU.zero' (I : Submodule ℤ (Vsp dim)) : IsU I 0 0 := by
  exact ⟨zero_mem _, fun a _ => by simp [Hf]⟩

theorem IsU.zsmul' {I : Submodule ℤ (Vsp dim)} {x u : Vsp dim} (k : ℤ) (hu : IsU I x u) :
    IsU I (k • x) (k • u) := by
  refine ⟨zsmul_mem hu.1 k, fun a ha => ?_⟩
  have hH : Hf (k • x) a = (k : ℂ) * Hf x a := by
    simp only [Hf]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_assoc]
  rw [← Int.cast_smul_eq_zsmul ℝ k u, real_inner_smul_left, hu.2 a ha, hH]
  simp

end lin

theorem eq_zero_of_im_L (X : PT E) {a : Vsp X.dim} (h : ∀ y ∈ X.L, (Hf y a).im = 0) : a = 0 := by
  have hH : ∀ y, Hf y a = inner ℂ a y := fun y => by
    simp [Hf, PiLp.inner_apply, mul_comm]
  have hf : (Complex.imLm.comp ((innerₛₗ ℂ a).restrictScalars ℝ) : Vsp X.dim →ₗ[ℝ] ℝ) = 0 :=
    X.b.ext fun i => by
      simpa [← hH] using h (X.b i) (Submodule.subset_span ⟨i, rfl⟩)
  have h0 : (inner ℂ a ((Complex.I : ℂ) • a)).im = 0 := by
    have := LinearMap.congr_fun hf ((Complex.I : ℂ) • a)
    first
      | exact this
      | (simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, innerₛₗ_apply,
          LinearMap.zero_apply] at this
         exact this)
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K] at h0
  have h2 : ‖a‖ ^ 2 = 0 := by
    have h3 : (Complex.I * ((‖a‖ : ℂ) ^ 2)).im = ‖a‖ ^ 2 := by
      rw [← Complex.ofReal_pow, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im]
      ring
    rw [← h3]
    exact h0
  simpa using h2

theorem mem_L_of_int (X : PT E) {a : Vsp X.dim} (h : ∀ y ∈ X.L, ∃ k : ℤ, (Hf y a).im = k) :
    a ∈ X.L := by
  have hadd : ∀ y y' : Vsp X.dim, (Hf (y + y') a).im = (Hf y a).im + (Hf y' a).im :=
    fun y y' => by simp [Hf, add_mul, Finset.sum_add_distrib]
  let φ : X.L →+ ℤ :=
    { toFun := fun y => (h (y : Vsp X.dim) y.2).choose
      map_zero' := by
        have e := (h ((0 : X.L) : Vsp X.dim) (0 : X.L).2).choose_spec
        have e' : (((h ((0 : X.L) : Vsp X.dim) (0 : X.L).2).choose : ℤ) : ℝ) = 0 := by
          rw [← e]
          simp [Hf]
        exact_mod_cast e'
      map_add' := fun y y' => by
        have e1 := (h ((y + y' : X.L) : Vsp X.dim) (y + y').2).choose_spec
        have e2 := (h (y : Vsp X.dim) y.2).choose_spec
        have e3 := (h (y' : Vsp X.dim) y'.2).choose_spec
        have e' : (((h ((y + y' : X.L) : Vsp X.dim) (y + y').2).choose : ℤ) : ℝ) =
            (h (y : Vsp X.dim) y.2).choose + (h (y' : Vsp X.dim) y'.2).choose := by
          rw [← e1, ← e2, ← e3, Submodule.coe_add, hadd]
        exact_mod_cast e' }
  obtain ⟨x, hx, hxy⟩ := X.perfect φ
  have key : a + x = 0 := by
    apply eq_zero_of_im_L X
    intro y hy
    have h1 : ((φ ⟨y, hy⟩ : ℤ) : ℝ) = (Hf x y).im := hxy ⟨y, hy⟩
    have hφ : ((φ ⟨y, hy⟩ : ℤ) : ℝ) = (Hf y a).im := (h y hy).choose_spec.symm
    have hc : (Hf y x).im = -(Hf x y).im := by
      have hcj : Hf y x = starRingEnd ℂ (Hf x y) := by simp [Hf, map_sum, mul_comm]
      rw [hcj, Complex.conj_im]
    have hr : Hf y (a + x) = Hf y a + Hf y x := by simp [Hf, mul_add, Finset.sum_add_distrib]
    rw [hr, Complex.add_im, hc, ← h1, hφ]
    ring
  have ha : a = -x := eq_neg_of_add_eq_zero_left key
  rw [ha]
  exact neg_mem hx

theorem exists_short_vectors_realSpan (X : PT E) (I : Submodule ℤ (Vsp X.dim)) (hle : I ≤ X.L)
    (hsat : ∀ x ∈ X.L, x ∈ IR I → x ∈ I) (hla : 0 < X.la1) {ε : ℝ} (hε : 0 < ε) :
    ∃ x u : Fin (Module.finrank ℝ (IR I)) → Vsp X.dim, (∀ j, x j ∈ X.L ∧ IsU I (x j) (u j)) ∧
      LinearIndependent ℝ u ∧ ∀ j, ‖u j‖ ≤ Module.finrank ℝ (IR I) / X.la1 + ε := by
  set K := IR I with hK
  set N := Module.finrank ℝ K with hNdef
  let e : K ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N) := (stdOrthonormalBasis ℝ K).repr
  let M : Submodule ℤ (EuclideanSpace ℝ (Fin N)) :=
    { carrier := {z | ∃ y ∈ X.L, IsU I y ((e.symm z : K) : Vsp X.dim)}
      add_mem' := by
        rintro z z' ⟨y, hy, hu⟩ ⟨y', hy', hu'⟩
        exact ⟨y + y', X.L.add_mem hy hy', by simpa using hu.add' hu'⟩
      zero_mem' := ⟨0, X.L.zero_mem, by simpa using IsU.zero' I⟩
      smul_mem' := by
        rintro k z ⟨y, hy, hu⟩
        exact ⟨k • y, X.L.smul_mem k hy, by simpa using hu.zsmul' k⟩ }
  have hmemM : ∀ y ∈ X.L, ∀ u, IsU I y u → ∃ z ∈ M, ((e.symm z : K) : Vsp X.dim) = u :=
    fun y hy u hu => ⟨e ⟨u, hu.1⟩, ⟨y, hy, by simpa using hu⟩, by simp⟩
  have hinner : ∀ z z' : EuclideanSpace ℝ (Fin N),
      ⟪z, z'⟫_ℝ = ⟪((e.symm z : K) : Vsp X.dim), ((e.symm z' : K) : Vsp X.dim)⟫_ℝ := by
    intro z z'
    rw [← Submodule.coe_inner, LinearIsometryEquiv.inner_map_map]
  have hnormE : ∀ z, ‖((e.symm z : K) : Vsp X.dim)‖ = ‖z‖ := by
    intro z
    rw [← e.symm.norm_map z]
    rfl
  have hdual : ∀ z ∈ PI.dualZ M, ((e.symm z : K) : Vsp X.dim) ∈ I := by
    intro z hz
    apply hsat _ ?_ (e.symm z).2
    apply mem_L_of_int X
    intro y hy
    obtain ⟨u, hu⟩ := exists_isU I y
    obtain ⟨z', hz'M, hz'⟩ := hmemM y hy u hu
    obtain ⟨k, hk⟩ := hz z' hz'M
    refine ⟨k, ?_⟩
    rw [← hu.2 _ (e.symm z).2, ← hk, hinner, hz', real_inner_comm]
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · have : IsEmpty (Fin N) := by rw [hN0]; infer_instance
    exact ⟨fun _ => 0, fun _ => 0, fun j => isEmptyElim j, linearIndependent_empty_type,
      fun j => isEmptyElim j⟩
  obtain ⟨a0, ha0I, ha0⟩ : ∃ a ∈ I, a ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hK0 : K = ⊥ := by
      rw [eq_bot_iff, hK]
      exact Submodule.span_le.2 (fun a ha => by simp [hcon a ha])
    have : N = 0 := by rw [hNdef, hK0]; exact finrank_bot ℝ _
    omega
  have hspan : Submodule.span ℝ (M : Set (EuclideanSpace ℝ (Fin N))) = ⊤ := by
    rw [← Submodule.orthogonal_eq_bot_iff, Submodule.eq_bot_iff]
    intro z hz
    have h0 : ∀ z' ∈ M, ⟪z', z⟫_ℝ = 0 := fun z' hz' =>
      (Submodule.mem_orthogonal _ _).1 hz z' (Submodule.subset_span hz')
    have ha : ((e.symm z : K) : Vsp X.dim) = 0 := by
      apply eq_zero_of_im_L X
      intro y hy
      obtain ⟨u, hu⟩ := exists_isU I y
      obtain ⟨z', hz'M, hz'⟩ := hmemM y hy u hu
      rw [← hu.2 _ (e.symm z).2, ← hz', ← hinner]
      exact h0 z' hz'M
    have : e.symm z = 0 := Subtype.ext ha
    simpa using congrArg e this

  obtain ⟨s, hsI, hsspan, hsli⟩ := exists_linearIndependent ℝ (I : Set (Vsp X.dim))
  have hsfin : s.Finite := hsli.setFinite
  set A := ∑ a ∈ hsfin.toFinset, ‖a‖ + 1 with hA
  have hApos : 0 < A := by
    have : 0 ≤ ∑ a ∈ hsfin.toFinset, ‖a‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    linarith
  have hlow : ∀ z ∈ M, z ≠ 0 → 1 / A ≤ ‖z‖ := by
    intro z hzM hz0
    obtain ⟨y, hy, hu⟩ := hzM
    set u := ((e.symm z : K) : Vsp X.dim)
    have hu0 : u ≠ 0 := by
      intro h0
      apply hz0
      have : e.symm z = 0 := Subtype.ext h0
      simpa using congrArg e this
    obtain ⟨a, has, ha⟩ : ∃ a ∈ s, ⟪u, a⟫_ℝ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have : ∀ w ∈ Submodule.span ℝ s, ⟪u, w⟫_ℝ = 0 := by
        intro w hw
        induction hw using Submodule.span_induction with
        | mem x hx => exact hcon x hx
        | zero => exact inner_zero_right _
        | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
        | smul r x _ hx => rw [real_inner_smul_right, hx, mul_zero]
      have h1 := this u (by rw [hsspan]; exact hu.1)
      exact hu0 (inner_self_eq_zero.1 h1)
    have h1 : 1 ≤ |⟪u, a⟫_ℝ| := by
      rw [hu.2 a (mem_IR (hsI has))]
      rw [hu.2 a (mem_IR (hsI has))] at ha
      exact one_le_abs_im X hy (hle (hsI has)) ha
    have h2 : |⟪u, a⟫_ℝ| ≤ ‖u‖ * ‖a‖ := abs_real_inner_le_norm _ _
    have h3 : ‖a‖ ≤ A := by
      have := Finset.single_le_sum (f := fun a => ‖a‖) (fun _ _ => norm_nonneg _)
        ((Set.Finite.mem_toFinset hsfin).2 has)
      linarith
    rw [← hnormE z, div_le_iff₀ hApos]
    nlinarith [norm_nonneg u]
  have hdisc : DiscreteTopology M := by
    rw [discreteTopology_iff_isOpen_singleton_zero, Metric.isOpen_singleton_iff]
    refine ⟨1 / A, by positivity, fun z hz => ?_⟩
    by_contra hz0
    have h1 := hlow z z.2 (fun h => hz0 (Subtype.ext h))
    rw [dist_zero_right] at hz
    have : ‖(z : EuclideanSpace ℝ (Fin N))‖ = ‖z‖ := rfl
    linarith
  have hT := transference_successive_minima N M hdisc hspan N hNpos le_rfl
  rw [show N + 1 - N = 1 by omega] at hT
  have hsm0 : 0 ≤ PI.succMin M N := Real.sInf_nonneg (fun t ht => ht.1)
  have hdual1 : X.la1 ≤ PI.succMin (PI.dualZ M) 1 := by
    apply le_csInf
    · have hmem : e ⟨a0, mem_IR ha0I⟩ ∈ PI.dualZ M := by
        intro z hz
        obtain ⟨y, hy, hu⟩ := hz
        obtain ⟨k, hk⟩ := X.integral y a0 hy (hle ha0I)
        refine ⟨k, ?_⟩
        rw [hinner, LinearIsometryEquiv.symm_apply_apply, real_inner_comm, hu.2 a0 (mem_IR ha0I), hk]
      refine ⟨‖e ⟨a0, mem_IR ha0I⟩‖, norm_nonneg _, fun _ => e ⟨a0, mem_IR ha0I⟩,
        fun _ => hmem, ?_, fun _ => le_rfl⟩
      rw [linearIndependent_unique_iff]
      intro h0
      apply ha0
      have := congrArg e.symm h0
      simpa using congrArg Subtype.val this
    · rintro t ⟨-, v, hvM, hvli, hvt⟩
      have hv0 := hvli.ne_zero 0
      have ha := hdual (v 0) (hvM 0)
      have hne : ((e.symm (v 0) : K) : Vsp X.dim) ≠ 0 := by
        intro h0
        apply hv0
        have : e.symm (v 0) = 0 := Subtype.ext h0
        simpa using congrArg e this
      calc X.la1 ≤ ‖((e.symm (v 0) : K) : Vsp X.dim)‖ := sq_le_Qy_of_le_firstMinimum X (hle ha) hne
        _ = ‖v 0‖ := hnormE _
        _ ≤ t := hvt 0
  have hlam : PI.succMin M N ≤ N / X.la1 := by
    rw [le_div_iff₀ hla]
    nlinarith

  have hne : {t : ℝ | 0 ≤ t ∧ ∃ v : Fin N → EuclideanSpace ℝ (Fin N),
      (∀ j, v j ∈ M) ∧ LinearIndependent ℝ v ∧ ∀ j, ‖v j‖ ≤ t}.Nonempty := by
    obtain ⟨s', hs'M, hs'span, hs'li⟩ := exists_linearIndependent ℝ (M : Set (EuclideanSpace ℝ (Fin N)))
    have hfin' : s'.Finite := hs'li.setFinite
    have : Fintype s' := hfin'.fintype
    let bs := Module.Basis.mk hs'li (by rw [Subtype.range_coe, hs'span, hspan])
    have hcard : Fintype.card s' = N := by
      rw [← Module.finrank_eq_card_basis bs, finrank_euclideanSpace_fin]
    let eq : Fin N ≃ s' := (Fintype.equivFinOfCardEq hcard).symm
    refine ⟨∑ j, ‖((eq j : s') : EuclideanSpace ℝ (Fin N))‖,
      Finset.sum_nonneg (fun _ _ => norm_nonneg _), fun j => (eq j : EuclideanSpace ℝ (Fin N)),
      fun j => hs'M (eq j).2, hs'li.comp eq eq.injective, fun j => ?_⟩
    exact Finset.single_le_sum (f := fun j => ‖((eq j : s') : EuclideanSpace ℝ (Fin N))‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
  obtain ⟨t, ⟨-, v, hvM, hvli, hvt⟩, htlt⟩ :=
    exists_lt_of_csInf_lt hne (lt_add_of_pos_right (PI.succMin M N) hε)
  choose y hy hyU using hvM
  refine ⟨y, fun j => ((e.symm (v j) : K) : Vsp X.dim), fun j => ⟨hy j, hyU j⟩, ?_, ?_⟩
  · exact (hvli.map' e.symm.toLinearEquiv.toLinearMap (LinearEquiv.ker _)).map' K.subtype
      K.ker_subtype
  · intro j
    rw [hnormE]
    have := hvt j
    have h2 : PI.succMin M N = sInf {t : ℝ | 0 ≤ t ∧ ∃ v : Fin N → EuclideanSpace ℝ (Fin N),
      (∀ j, v j ∈ M) ∧ LinearIndependent ℝ v ∧ ∀ j, ‖v j‖ ≤ t} := rfl
    linarith

end

end ReciprocityTheory.ChartRestriction.G.I2
end

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex
open scoped InnerProductSpace

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem IR_bot {dim : (E →+* ℂ) → ℕ} : IR (⊥ : Submodule ℤ (Vsp dim)) = ⊥ := by
  simp [IR]

theorem split_bot (X : PT E) {DF : ℕ} (P : Par X DF) (h : ¬ X.la1 < P.th) : IsSplit P ⊥ := by
  have hIR : IR (⊥ : Submodule ℤ (Vsp X.dim)) = ⊥ := IR_bot
  have h0 : Module.finrank ℝ (IR (⊥ : Submodule ℤ (Vsp X.dim))) = 0 := by
    rw [hIR]; exact finrank_bot ℝ (Vsp X.dim)
  have h' : ¬ X.la1 < th (E := E) P.q P.R0 := h
  have hph : P.ph = 0 := by
    unfold Par.ph PT.ph
    rw [if_neg h']
  refine
    { le := bot_le
      sat := ?_
      stable := ?_
      iso := ?_
      eps := ?_
      rank := ⟨0, Nat.zero_le _, by rw [h0, mul_zero]⟩
      ne_bot := iff_of_false (fun h'' => h'' rfl) h
      thick := ?_
      sep := ?_
      u1 := ?_
      u2 := ?_ }
  · intro x _ k hk hx
    rw [Submodule.mem_bot] at hx ⊢
    rw [← Int.cast_smul_eq_zsmul ℂ] at hx
    exact (smul_eq_zero.mp hx).resolve_left (by exact_mod_cast hk)
  · intro α x hx
    rw [Submodule.mem_bot] at hx ⊢
    subst hx
    ext i
    simp [act]
  · intro x hx y hy
    rw [Submodule.mem_bot] at hx hy
    subst hx hy
    simp [Hf]
  · intro x hx
    rw [Submodule.mem_bot] at hx
    subst hx
    exact X.eps_iso 0 (Submodule.zero_mem _) (fun α => by simp [Hf])
  · intro x hxL _ hx
    rw [Submodule.mem_bot] at hx
    rw [hIR]
    have hinf : Metric.infDist x ((⊥ : Submodule ℝ (Vsp X.dim)) : Set (Vsp X.dim)) = ‖x‖ := by
      rw [Submodule.bot_coe, Metric.infDist_singleton, dist_zero_right]
    rw [hinf]
    have hle : X.la1 ≤ ‖x‖ := by
      unfold PT.la1
      apply csInf_le
      · exact ⟨0, fun t ⟨y, _, _, ht⟩ => by rw [ht]; exact norm_nonneg y⟩
      · exact ⟨x, hxL, hx, rfl⟩
    exact (not_lt.mp h).trans hle
  · intro x _ u hu hu0
    exfalso
    apply hu0
    unfold IsU at hu
    have hu1 := hu.1
    rw [hIR, Submodule.mem_bot] at hu1
    exact hu1
  · haveI : IsEmpty (Fin (Module.finrank ℝ (IR (⊥ : Submodule ℤ (Vsp X.dim))))) := by
      rw [h0]; infer_instance
    exact ⟨fun _ => 0, fun _ => 0, fun j => isEmptyElim j, linearIndependent_empty_type,
      fun j => isEmptyElim j⟩
  · intro k x u _ _
    rw [hph]
    exact Finset.sum_nonneg fun j _ => by positivity

theorem le_of_forall_pos_div_sq {a c S : ℝ} (ha : 0 < a) (hc : 0 < c) (h : ∀ ε > 0, c / (a + ε) ^ 2 ≤ S) :
    c / a ^ 2 ≤ S := by
  have hcont : ContinuousAt (fun ε : ℝ => c / (a + ε) ^ 2) 0 := by
    apply ContinuousAt.div continuousAt_const
    · exact ((continuous_const.add continuous_id).pow 2).continuousAt
    · simpa using ha.ne'
  have ht : Filter.Tendsto (fun ε : ℝ => c / (a + ε) ^ 2) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (c / a ^ 2)) := by
    have := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    simpa using this
  apply le_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with ε hε using h ε hε

theorem sq_le_pow_four_div_sq {d N la u : ℝ} (hd : 2 ≤ d) (hN : N ≤ d) (hla : 0 < la) (hu0 : 0 ≤ u)
    (hu : u ≤ N / la + 1 / la) : u ^ 2 ≤ d ^ 4 / la ^ 2 := by
  have key : u * la ≤ N + 1 := by
    have e : N / la + 1 / la = (N + 1) / la := by ring
    rw [e] at hu
    have e2 : (N + 1) / la * la = N + 1 := by field_simp
    calc u * la ≤ (N + 1) / la * la := mul_le_mul_of_nonneg_right hu hla.le
      _ = N + 1 := e2
  have hla2 : 0 < la ^ 2 := by positivity
  rw [le_div_iff₀ hla2]
  have h2 : u * la ≤ d ^ 2 := by nlinarith
  have h3 : 0 ≤ u * la := mul_nonneg hu0 hla.le
  nlinarith [mul_le_mul h2 h2 h3 (by positivity : (0:ℝ) ≤ d ^ 2)]

theorem split_pos (X : PT E) {DF : ℕ} (P : Par X DF) (h : X.la1 < P.th) : ∃ I, IsSplit P I := by
  obtain ⟨n, ω, hω, hsp⟩ := omega_exists' (E := E)
  have hf1n : 1 ≤ PT.f E := le_trans (Nat.one_le_pow _ _ P.hm1) P.hmf
  have hf1 : (1 : ℝ) ≤ PT.f E := by exact_mod_cast hf1n
  have hrd := P.hrd
  have hRR : (0 : ℝ) < RR (E := E) := by rw [RR]; positivity
  have hq : (0 : ℝ) < P.q := by exact_mod_cast P.hq
  have hR0 : (0 : ℝ) < P.R0 ^ 2 := by linarith [P.hR0.1]
  set Ω := omStar (E := E) with hΩdef
  have hΩ : 0 < Ω := by rw [hΩdef, omStar]; positivity
  have hΩ2 : Ω ^ 2 = 4 * (PT.f E : ℝ) ^ 3 * PT.rd E ^ 2 := by
    rw [hΩdef, omStar, mul_pow, mul_pow, ← Real.rpow_natCast ((PT.f E : ℝ) ^ ((3 : ℝ) / 2)),
      ← Real.rpow_mul (by positivity)]
    norm_num
  have hth2 : P.th ^ 2 = PT.f E * P.R0 ^ 2 * RR (E := E) ^ 3 / P.q := by
    rw [Par.th, th, Real.sq_sqrt]; positivity
  have hth : 0 < P.th := by
    rw [Par.th, th]; apply Real.sqrt_pos.2; positivity
  have hd2n : 2 ≤ dstar (E := E) P.m := by
    rw [dstar]; have := P.hm1; nlinarith
  have hd2 : (2 : ℝ) ≤ dstar (E := E) P.m := by exact_mod_cast hd2n
  have hC1 : (dstar (E := E) P.m : ℝ) ^ 2 * Ω * P.th ^ 2 < 1 := P.C1
  have hΩth : Ω * P.th ^ 2 ≤ 1 := by nlinarith [sq_nonneg P.th, hΩ]
  obtain ⟨I, hI, hmax⟩ := exists_maximal X ω hΩ hth hΩth hω hsp
  obtain ⟨τ, hτ⟩ := P.hm
  have hr : 1 ≤ X.r := by
    have := P.hfr
    rcases Nat.eq_zero_or_pos X.r with h0 | h0
    · rw [h0] at this; simp at this
    · exact h0
  have hne := L_ne_zero X hr τ
  have hla := first_minimum_pos X hne
  have h' : X.la1 < th (E := E) P.q P.R0 := h
  have hph : P.ph = 2 * PT.f E / (PT.rd E ^ 2 * X.la1 ^ 2) := by rw [Par.ph, PT.ph, if_pos h']
  obtain ⟨ρ, hρ, hfr⟩ := rank_iso X I hI.le hI.stable hI.iso
  have hin : ∀ x ∈ X.L, ‖x‖ < P.th → x ∈ I := by
    intro x hx hxs
    by_contra hxI
    have h1 := hmax x hx hxI
    have h2 : Metric.infDist x (IR I) ≤ ‖x‖ := by
      rw [← dist_zero_right]; exact Metric.infDist_le_dist_of_mem (IR I).zero_mem
    linarith
  refine ⟨I, hI.le, sat_of_IR hI.sat, hI.stable, hI.iso, ?_, ⟨ρ, le_trans (hρ τ) hτ, hfr⟩, ?_,
    ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact X.eps_iso x (hI.le hx) (fun α => hI.iso _ (hI.stable α x hx) x hx)
  · refine ⟨fun _ => h, fun _ hbot => ?_⟩
    obtain ⟨x, hx, hx0, hxs⟩ := exists_short X hne h
    have := hin x hx hxs
    rw [hbot, Submodule.mem_bot] at this
    exact hx0 this
  · intro x hx _ hxI
    exact hmax x hx hxI
  · intro x hx u hu hne
    have h1 := hI.sep x hx u hu hne
    have key : b0 (E := E) P.q P.R0 * (Ω ^ 2 * P.th ^ 2) = 4 * (PT.f E : ℝ) ^ 4 * PT.rd E ^ 2 / RR (E := E) := by
      have hR0ne : P.R0 ≠ 0 := fun h0 => by rw [h0] at hR0; simp at hR0
      rw [hΩ2, hth2, b0]; field_simp
    have hf4 : (PT.f E : ℝ) ^ 4 ≤ PT.rd E ^ 2 := by
      have := P.hf2
      calc (PT.f E : ℝ) ^ 4 = ((PT.f E : ℝ) ^ 2) ^ 2 := by ring
        _ ≤ PT.rd E ^ 2 := pow_le_pow_left₀ (by positivity) this 2
    have hb : b0 (E := E) P.q P.R0 * (Ω ^ 2 * P.th ^ 2) ≤ 1 := by
      rw [key, div_le_one hRR, RR]
      have : 4 * PT.rd E ^ 4 ≤ PT.rd E ^ 7 := by
        have h3 : (4 : ℝ) ≤ PT.rd E ^ 3 := by nlinarith
        calc 4 * PT.rd E ^ 4 ≤ PT.rd E ^ 3 * PT.rd E ^ 4 :=
              mul_le_mul_of_nonneg_right h3 (by positivity)
          _ = PT.rd E ^ 7 := by ring
      nlinarith [pow_pos (show (0:ℝ) < PT.rd E by linarith) 2]
    have hb' : b0 (E := E) P.q P.R0 ≤ (1 / (Ω * P.th)) ^ 2 := by
      rw [div_pow, one_pow, mul_pow, le_div_iff₀ (by positivity)]
      exact hb
    exact hb'.trans (pow_le_pow_left₀ (by positivity) h1.le 2)
  · obtain ⟨x, u, hxu, hli, hb⟩ := exists_short_vectors_realSpan X I hI.le hI.sat hla (ε := 1 / X.la1) (by positivity)
    refine ⟨x, u, hxu, hli, fun j => ?_⟩
    have hN : (Module.finrank ℝ (IR I) : ℝ) ≤ dstar (E := E) P.m := by
      have : Module.finrank ℝ (IR I) ≤ dstar (E := E) P.m := by
        rw [hfr, dstar]; exact Nat.mul_le_mul_left _ (le_trans (hρ τ) hτ)
      exact_mod_cast this
    set d : ℝ := (dstar (E := E) P.m : ℝ)
    have hR : PT.rd E ^ 2 * d ^ 4 * P.ph / (2 * PT.f E) = d ^ 4 / X.la1 ^ 2 := by
      rw [hph]; field_simp
    rw [hR]
    exact sq_le_pow_four_div_sq hd2 hN hla (norm_nonneg _) (hb j)
  · intro k x u hxu hspan
    rw [hph]
    set S := ∑ j, ‖u j‖ ^ 2 / 2
    set c : ℝ := 2 * PT.f E / PT.rd E ^ 2 with hc
    have hcpos : 0 < c := by rw [hc]; positivity
    have hbound : ∀ ε > 0, c / (X.la1 + ε) ^ 2 ≤ S := by
      intro ε hε
      obtain ⟨ξ, hξ, hξ0, hξs⟩ := exists_short X hne (lt_min h (by linarith : X.la1 < X.la1 + ε))
      have hξI := hin ξ hξ (lt_of_lt_of_le hξs (min_le_left _ _))
      have h1 := sum_sq_norm_ge_of_span X I hI.le hI.stable hξI hξ0 k x u hxu hspan
      have h2 : c / (X.la1 + ε) ^ 2 ≤ c / ‖ξ‖ ^ 2 := by
        apply div_le_div_of_nonneg_left hcpos.le (by positivity)
        exact pow_le_pow_left₀ (norm_nonneg _) (le_of_lt (lt_of_lt_of_le hξs (min_le_right _ _))) 2
      refine h2.trans (le_of_eq_of_le ?_ h1)
      rw [hc]; field_simp
    have hl := le_of_forall_pos_div_sq hla hcpos hbound
    calc 2 * PT.f E / (PT.rd E ^ 2 * X.la1 ^ 2) = c / X.la1 ^ 2 := by rw [hc]; field_simp
      _ ≤ S := hl

end

end ReciprocityTheory.ChartRestriction.G.I2
end

namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex

theorem split (hx : Ext.All) : SplitStatement := by
  intro E _ _ _ X DF P
  by_cases h : X.la1 < P.th
  · exact split_pos X P h
  · exact ⟨⊥, split_bot X P h⟩

end ReciprocityTheory.ChartRestriction.G.I2
end

namespace ReciprocityTheory.ChartRestriction.G.I2

theorem gSup_holds : GSupStatement := gSup Ext.all.1

theorem propA_holds : PropAStatement := propA Ext.all.1 Ext.all.2.1

theorem dim_holds : DimStatement := dim

theorem split_holds : SplitStatement := split Ext.all

theorem char_holds : CharStatement := char Ext.all

theorem J_holds : JStatement :=
  jOf Ext.all split_holds char_holds (colTorus Ext.all propA_holds gSup_holds)
    (colAbel Ext.all propA_holds gSup_holds) (colEmpty Ext.all propA_holds gSup_holds)

theorem N_holds : NStatement := lemmaN dim_holds

theorem I_holds : IStatement := iOf J_holds N_holds

theorem T_holds : TStatement := tOf Ext.all split_holds gSup_holds dim_holds

end ReciprocityTheory.ChartRestriction.G.I2

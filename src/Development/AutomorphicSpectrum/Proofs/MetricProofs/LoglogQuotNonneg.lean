module

public import ReciprocityTheory.AnalyticForms.LeviForms.PullDominateStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeSpanProjectionBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsHorizontalTwist
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LoglogQuotNonneg
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem log_inv_bounds {t : ℝ} (ht : 0 < t) (hte : t ≤ Real.exp (-Real.exp 1)) :
    Real.exp 1 ≤ Real.log (1 / t) ∧ 1 ≤ Real.log (Real.log (1 / t)) := by
  have h1 : Real.exp 1 ≤ Real.log (1 / t) := by
    rw [one_div, Real.log_inv]
    have := Real.log_le_log ht hte
    rw [Real.log_exp] at this
    linarith
  refine ⟨h1, ?_⟩
  have := Real.log_le_log (Real.exp_pos 1) h1
  rwa [Real.log_exp] at this

theorem loglog_quot_nonneg {t : ℝ} (ht : 0 < t) (hte : t ≤ Real.exp (-Real.exp 1)) :
    0 ≤ Real.log (Real.log (1 / t)) / Real.log (1 / t) := by
  obtain ⟨h1, h2⟩ := log_inv_bounds ht hte
  exact div_nonneg (by linarith) (by linarith [Real.exp_pos 1])

theorem epsT_eq_mul (C t : ℝ) :
    epsT C t = C * (Real.log (Real.log (1 / t)) / Real.log (1 / t)) := by
  rw [epsT, mul_div_assoc]

theorem epsT_le_epsT {C C' t : ℝ} (hC : C ≤ C') (ht : 0 < t)
    (hte : t ≤ Real.exp (-Real.exp 1)) : epsT C t ≤ epsT C' t := by
  rw [epsT_eq_mul, epsT_eq_mul]
  exact mul_le_mul_of_nonneg_right hC (loglog_quot_nonneg ht hte)

theorem mul_epsT_le {C C' t : ℝ} (hC : |C| ≤ C') (ht : 0 < t)
    (hte : t ≤ Real.exp (-Real.exp 1)) : C * epsT C t ≤ C' * epsT C' t := by
  have hx := loglog_quot_nonneg ht hte
  rw [epsT_eq_mul, epsT_eq_mul, ← mul_assoc, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ hx
  have h2 : C ^ 2 ≤ C' ^ 2 := by
    rw [← sq_abs C]
    exact pow_le_pow_left₀ (abs_nonneg C) hC 2
  nlinarith

theorem isPsh_rsmul_mono {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Θ th : LocPot X) (u : X → ℝ) {ε ε' : ℝ} (hΘ : IsPotential A Θ) (hΘp : IsPsh A Θ)
    (hth : IsPotential A th) (hu : A.Smooth u) (hε : ε ≤ ε')
    (h : IsPsh A (th + LocPot.ofFun u + Θ.rsmul ε)) :
    IsPsh A (th + LocPot.ofFun u + Θ.rsmul ε') := by
  intro x j y hy w
  obtain ⟨hyt, hyU⟩ := hy
  have hU : (A.chart j).symm y ∈ (th.U x ∩ Set.univ) ∩ Θ.U x := hyU
  have hO1 : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' th.U x) :=
    (A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target (th.isOpen_U x)
  have hO2 : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Θ.U x) :=
    (A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target (Θ.isOpen_U x)
  have hO3 : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (Set.univ : Set X)) :=
    (A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target isOpen_univ
  have hth2 : ContDiffAt ℝ 2 (th.φ x ∘ (A.chart j).symm) y :=
    ((hth.1 x j).contDiffAt (hO1.mem_nhds ⟨hyt, hU.1.1⟩)).of_le (by norm_cast)
  have hΘ2 : ContDiffAt ℝ 2 (Θ.φ x ∘ (A.chart j).symm) y :=
    ((hΘ.1 x j).contDiffAt (hO2.mem_nhds ⟨hyt, hU.2⟩)).of_le (by norm_cast)
  have hu2 : ContDiffAt ℝ 2 (u ∘ (A.chart j).symm) y :=
    ((hu j).contDiffAt (hO3.mem_nhds ⟨hyt, Set.mem_univ _⟩)).of_le (by norm_cast)
  have hP2 : ContDiffAt ℝ 2
      ((th + LocPot.ofFun u + Θ.rsmul ε).φ x ∘ (A.chart j).symm) y :=
    (hth2.add hu2).add (contDiffAt_const.mul hΘ2)
  have hfun : (th + LocPot.ofFun u + Θ.rsmul ε').φ x ∘ (A.chart j).symm =
      fun z => ((th + LocPot.ofFun u + Θ.rsmul ε).φ x ∘ (A.chart j).symm) z +
        (ε' - ε) * (Θ.φ x ∘ (A.chart j).symm) z := by
    funext z
    show th.φ x _ + u _ + ε' * Θ.φ x _ = th.φ x _ + u _ + ε * Θ.φ x _ + (ε' - ε) * Θ.φ x _
    ring
  rw [hfun, levi_add_smul (ε' - ε) hP2 hΘ2 w]
  exact add_nonneg (h x j y ⟨hyt, hyU⟩ w)
    (mul_nonneg (sub_nonneg.2 hε) (hΘp x j y ⟨hyt, hU.2⟩ w))

theorem isRegFamily_mono {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Θ L : LocPot X) (s : X → X → ℂ) (th : LocPot X) (ph : X → ℝ) (phT : ℝ → X → ℝ)
    (C t₀ C' t₁ : ℝ) (hΘ : IsPotential A Θ) (hΘp : IsPsh A Θ) (hth : IsPotential A th)
    (hs : ∀ y, logNormSec L s y ≤ 0) (hF : IsRegFamily A Θ L s th ph phT C t₀)
    (hC : |C| ≤ C') (ht₁ : 0 < t₁) (ht₁₀ : t₁ ≤ t₀) (hte : t₁ ≤ Real.exp (-Real.exp 1)) :
    IsRegFamily A Θ L s th ph phT C' t₁ := by
  obtain ⟨-, ht₀1, hF⟩ := hF
  have hCC : C ≤ C' := (le_abs_self C).trans hC
  have hr : ∀ y, 0 ≤ rW L s y := fun y => by
    have := hs y
    have := Real.exp_pos 1
    unfold rW
    linarith
  refine ⟨ht₁, ht₁₀.trans_lt ht₀1, fun t ht htt => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hF t ht (htt.trans ht₁₀)
  have hte' : t ≤ Real.exp (-Real.exp 1) := htt.trans hte
  have hε := epsT_le_epsT hCC ht hte'
  have hll := (log_inv_bounds ht hte').2
  refine ⟨h1, fun y => (h2 y).trans hCC, h3, fun y => ?_,
    isPsh_rsmul_mono A Θ th (phT t) hΘ hΘp hth h1 hε h5, fun y hy hyr => ?_, fun y hy => ?_,
    fun t' htt' ht' y => ?_⟩
  · have := h4 y
    nlinarith
  · have := h6 y hy hyr
    linarith
  · have := h7 y hy
    have := mul_le_mul_of_nonneg_right hε (hr y)
    linarith
  · have := h8 t' htt' (ht'.trans ht₁₀) y
    have := mul_epsT_le hC (ht.trans_le htt') (ht'.trans hte)
    linarith

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.GenUIsGenFam
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

open GlobalTheory.CompanionTheory.Ar.FlagBun

def IsGenFam (Ω G : Type) [Field Ω] [Field G] [Algebra Ω G] {S : Type} {r : S → ℕ}
    (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) G) : Prop :=
  (∀ s a, u s a a = 1) ∧ (∀ s a b, a < b → u s a b = 0) ∧
    AlgebraicIndependent Ω (fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} => u q.1 q.2.1.1 q.2.1.2) ∧
    IntermediateField.adjoin Ω (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => u q.1 q.2.1 q.2.2) = ⊤

def revInv {G : Type} [Field G] {r : ℕ} (u : Matrix (Fin r) (Fin r) G) : Matrix (Fin r) (Fin r) G :=
  (u.transpose⁻¹).submatrix Fin.rev Fin.rev

theorem genU_isGenFam (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) : IsGenFam Ω (GenField Ω r) (genU Ω r) := by
  have hdiag : ∀ s (a : Fin (r s)), genU Ω r s a a = 1 := fun s a => by
    simp [genU]
  have habove : ∀ s (a b : Fin (r s)), a < b → genU Ω r s a b = 0 := fun s a b h => by
    simp [genU, not_lt.2 h.le, h.ne]
  have hbelow : ∀ q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1},
      genU Ω r q.1 q.2.1.1 q.2.1.2 =
        algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X (R := Ω) (σ := GenIx r) q) :=
    fun q => by
      simp only [genU]
      exact dif_pos q.2.2
  refine ⟨hdiag, habove, ?_, ?_⟩
  · have hinj : Function.Injective
        (IsScalarTower.toAlgHom Ω (MvPolynomial (GenIx r) Ω) (GenField Ω r)) := by
      rw [IsScalarTower.coe_toAlgHom']
      exact IsFractionRing.injective _ _
    have hX := (MvPolynomial.algebraicIndependent_X (GenIx r) Ω).map' hinj
    have hfun : (fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} =>
        genU Ω r q.1 q.2.1.1 q.2.1.2) =
        (IsScalarTower.toAlgHom Ω (MvPolynomial (GenIx r) Ω) (GenField Ω r)) ∘ MvPolynomial.X := by
      funext q
      exact hbelow q
    rw [hfun]
    exact hX
  · rw [eq_top_iff]
    intro x _
    have hXmem : ∀ q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1},
        algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X (R := Ω) (σ := GenIx r) q) ∈
          IntermediateField.adjoin Ω
            (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => genU Ω r q.1 q.2.1 q.2.2) := by
      intro q
      rw [← hbelow q]
      exact IntermediateField.subset_adjoin _ _ ⟨⟨q.1, q.2.1⟩, rfl⟩
    have hA : ∀ a : MvPolynomial (GenIx r) Ω,
        algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) a ∈
          IntermediateField.adjoin Ω
            (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => genU Ω r q.1 q.2.1 q.2.2) := by
      intro a
      induction a using MvPolynomial.induction_on
      · rename_i c
        rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
        exact IntermediateField.algebraMap_mem _ c
      · rename_i p q hp hq
        rw [map_add (f := _)]
        exact add_mem hp hq
      · rename_i p i hp
        rw [map_mul]
        exact mul_mem hp (hXmem i)
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (GenIx r) Ω) x
    exact div_mem (hA a) (hA b)

end GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.CompChartEventuallyEq
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

section PullPsh

variable {e e' : ℕ} {X X' : Type} [TopologicalSpace X] [TopologicalSpace X']

theorem comp_chart_eventuallyEq {A : FinHolAtlas e X} {A' : FinHolAtlas e' X'} {h : X' → X}
    (hh : HoloMap A' A h) (g : X → ℝ) (j : Fin A'.n) (k : Fin A.n) {t : Fin e' → ℂ}
    (ht : t ∈ (A'.chart j).target) (hk : h ((A'.chart j).symm t) ∈ (A.chart k).source) :
    (g ∘ h ∘ (A'.chart j).symm) =ᶠ[𝓝 t]
      (g ∘ (A.chart k).symm) ∘ (A.chart k ∘ h ∘ (A'.chart j).symm) := by
  have hc : ContinuousAt (h ∘ (A'.chart j).symm) t :=
    hh.1.continuousAt.comp ((A'.chart j).continuousAt_symm ht)
  have hmem : ∀ᶠ s in 𝓝 t, h ((A'.chart j).symm s) ∈ (A.chart k).source :=
    hc.preimage_mem_nhds ((A.chart k).open_source.mem_nhds hk)
  filter_upwards [hmem] with s hs
  simp only [Function.comp_apply, (A.chart k).left_inv hs]

theorem levi_pull_nonneg {A : FinHolAtlas e X} {A' : FinHolAtlas e' X'} {h : X' → X}
    (hh : HoloMap A' A h) (g : X → ℝ) (j : Fin A'.n) (k : Fin A.n) {t : Fin e' → ℂ}
    (ht : t ∈ (A'.chart j).target) (hk : h ((A'.chart j).symm t) ∈ (A.chart k).source)
    (hg : ContDiffAt ℝ 2 (g ∘ (A.chart k).symm) ((A.chart k ∘ h ∘ (A'.chart j).symm) t))
    (hn : ∀ v, 0 ≤ levi (g ∘ (A.chart k).symm) ((A.chart k ∘ h ∘ (A'.chart j).symm) t) v)
    (w : Fin e' → ℂ) : 0 ≤ levi (g ∘ h ∘ (A'.chart j).symm) t w := by
  rw [ReciprocityTheory.AnForm.levi_congr (comp_chart_eventuallyEq hh g j k ht hk) w,
    ReciprocityTheory.AnForm.levi_comp w (hh.2 j k t ⟨ht, hk⟩) hg]
  exact hn _

theorem chart_image_mem {A : FinHolAtlas e X} {A' : FinHolAtlas e' X'} {h : X' → X}
    (j : Fin A'.n) (k : Fin A.n) {t : Fin e' → ℂ}
    (hk : h ((A'.chart j).symm t) ∈ (A.chart k).source) :
    (A.chart k ∘ h ∘ (A'.chart j).symm) t ∈ (A.chart k).target ∧
      (A.chart k).symm ((A.chart k ∘ h ∘ (A'.chart j).symm) t) = h ((A'.chart j).symm t) := by
  exact ⟨(A.chart k).map_source hk, (A.chart k).left_inv hk⟩

theorem contDiffAt_of_smoothOn {A : FinHolAtlas e X} {U : Set X} (hU : IsOpen U) {f : X → ℝ}
    (hf : A.SmoothOn U f) (k : Fin A.n) {z : Fin e → ℂ} (hz : z ∈ (A.chart k).target)
    (hzU : (A.chart k).symm z ∈ U) : ContDiffAt ℝ ∞ (f ∘ (A.chart k).symm) z := by
  have ho : IsOpen ((A.chart k).target ∩ (A.chart k).symm ⁻¹' U) :=
    (A.chart k).continuousOn_symm.isOpen_inter_preimage (A.chart k).open_target hU
  exact (hf k).contDiffAt (ho.mem_nhds ⟨hz, hzU⟩)

theorem smoothOn_pull {A : FinHolAtlas e X} {A' : FinHolAtlas e' X'} {h : X' → X}
    (hh : HoloMap A' A h) {U : Set X} (hU : IsOpen U) {f : X → ℝ} (hf : A.SmoothOn U f) :
    A'.SmoothOn (h ⁻¹' U) (f ∘ h) := by
  intro j
  have key : ∀ t ∈ (A'.chart j).target ∩ (A'.chart j).symm ⁻¹' (h ⁻¹' U),
      ContDiffAt ℝ ∞ ((f ∘ h) ∘ (A'.chart j).symm) t := by
    rintro t ⟨ht, htU⟩
    obtain ⟨k, hk⟩ := A.cover (h ((A'.chart j).symm t))
    have hF : AnalyticAt ℂ (A.chart k ∘ h ∘ (A'.chart j).symm) t := hh.2 j k t ⟨ht, hk⟩
    have hF' : ContDiffAt ℂ ∞ (A.chart k ∘ h ∘ (A'.chart j).symm) t := hF.contDiffAt
    have hci := chart_image_mem (A := A) (A' := A') (h := h) j k hk
    have hzU : (A.chart k).symm ((A.chart k ∘ h ∘ (A'.chart j).symm) t) ∈ U := by
      rw [hci.2]; exact htU
    have hfk : ContDiffAt ℝ ∞ (f ∘ (A.chart k).symm) ((A.chart k ∘ h ∘ (A'.chart j).symm) t) :=
      contDiffAt_of_smoothOn hU hf k hci.1 hzU
    have hcomp : ContDiffAt ℝ ∞ ((f ∘ (A.chart k).symm) ∘ (A.chart k ∘ h ∘ (A'.chart j).symm)) t :=
      hfk.comp t (hF'.restrict_scalars ℝ)
    exact hcomp.congr_of_eventuallyEq (comp_chart_eventuallyEq hh f j k ht hk)
  intro t ht
  exact (key t ht).contDiffWithinAt

theorem isPsh_pull {A : FinHolAtlas e X} {A' : FinHolAtlas e' X'} {h : X' → X}
    (hh : HoloMap A' A h) {P : LocPot X} (hP : IsPotential A P) (hpsh : IsPsh A P) :
    IsPsh A' (P.pullback h hh.1) := by
  intro x j y hy w
  obtain ⟨k, hk⟩ := A.cover (h ((A'.chart j).symm y))
  have hci := chart_image_mem (A := A) (A' := A') (h := h) j k hk
  have hyP : h ((A'.chart j).symm y) ∈ P.U (h x) := hy.2
  have hzU : (A.chart k).symm ((A.chart k ∘ h ∘ (A'.chart j).symm) y) ∈ P.U (h x) := by
    rw [hci.2]; exact hyP
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have hg : ContDiffAt ℝ 2 (P.φ (h x) ∘ (A.chart k).symm)
      ((A.chart k ∘ h ∘ (A'.chart j).symm) y) :=
    (contDiffAt_of_smoothOn (P.isOpen_U (h x)) (hP.1 (h x)) k hci.1 hzU).of_le h2
  exact levi_pull_nonneg hh (P.φ (h x)) j k hy.1 hk hg (fun v => hpsh (h x) k _ ⟨hci.1, hzU⟩ v) w

theorem isPshOn_pull {A : FinHolAtlas e X} {A' : FinHolAtlas e' X'} {h : X' → X}
    (hh : HoloMap A' A h) {P : LocPot X} {U : Set X} {f : X → ℝ} (hU : IsOpen U)
    (hP : IsPotential A P) (hf : A.SmoothOn U f) (hpsh : IsPshOn A U (P + LocPot.ofFun f)) :
    IsPshOn A' (h ⁻¹' U) (P.pullback h hh.1 + LocPot.ofFun (f ∘ h)) := by
  intro x j y hy w
  obtain ⟨k, hk⟩ := A.cover (h ((A'.chart j).symm y))
  have hci := chart_image_mem (A := A) (A' := A') (h := h) j k hk
  have hyP : h ((A'.chart j).symm y) ∈ P.U (h x) := hy.2.1.1
  have hyU : h ((A'.chart j).symm y) ∈ U := hy.2.2
  have hzP : (A.chart k).symm ((A.chart k ∘ h ∘ (A'.chart j).symm) y) ∈ P.U (h x) := by
    rw [hci.2]; exact hyP
  have hzU : (A.chart k).symm ((A.chart k ∘ h ∘ (A'.chart j).symm) y) ∈ U := by
    rw [hci.2]; exact hyU
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have hg : ContDiffAt ℝ 2 ((fun z => P.φ (h x) z + f z) ∘ (A.chart k).symm)
      ((A.chart k ∘ h ∘ (A'.chart j).symm) y) :=
    ((contDiffAt_of_smoothOn (P.isOpen_U (h x)) (hP.1 (h x)) k hci.1 hzP).add
      (contDiffAt_of_smoothOn hU hf k hci.1 hzU)).of_le h2
  have hmem : (A.chart k ∘ h ∘ (A'.chart j).symm) y ∈
      (A.chart k).target ∩ (A.chart k).symm ⁻¹' ((P + LocPot.ofFun f).U (h x) ∩ U) :=
    ⟨hci.1, ⟨hzP, Set.mem_univ _⟩, hzU⟩
  exact levi_pull_nonneg hh (fun z => P.φ (h x) z + f z) j k hy.1 hk hg
    (fun v => hpsh (h x) k _ hmem v) w

theorem pullPsh : PullPshStatement := by
  intro e e' X X' _ _ A A' h hh P U f hU hP
  exact ⟨fun hf => smoothOn_pull hh hU hf, fun hpsh => isPsh_pull hh hP hpsh,
    fun hf hpsh => isPshOn_pull hh hU hP hf hpsh⟩

end PullPsh

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionExistsOfArithSystem
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionExistsOfArithSystem
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem exists_family_of_system :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → ReciprocityTheory.ChartRestriction.G.AI.I2.ExistsStatement := by
  rintro ⟨II, hII, -⟩
  exact ⟨II, hII⟩

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionExistsOfArithSystemStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_exists_of_arith_system : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → ReciprocityTheory.ChartRestriction.G.AI.I2.ExistsStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.exists_family_of_system | exact GlobalTheory.CompanionTheory.Ar.Giv.exists_family_of_system | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.exists_family_of_system <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FinitePrimesSumSquaresZero
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FinitePrimesSumSquaresZero
namespace GlobalTheory.CompanionTheory.QuadFin

theorem exists_eq_add_mul_of_mem_adjoin {E : Type*} [Field E] [Algebra ℚ E] (x : E) (c : ℚ)
    (hx : x ^ 2 = algebraMap ℚ E c) {y : E} (hy : y ∈ IntermediateField.adjoin ℚ {x}) :
    ∃ a b : ℚ, y = algebraMap ℚ E a + algebraMap ℚ E b * x := by
  have hint : IsIntegral ℚ x :=
    ⟨Polynomial.X ^ 2 - Polynomial.C c, Polynomial.monic_X_pow_sub_C c two_ne_zero, by simp [hx]⟩
  have hy' : y ∈ Algebra.adjoin ℚ {x} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
    exact hy
  refine Algebra.adjoin_induction (fun z hz => ?_) (fun r => ?_) (fun u v _ _ hu hv => ?_)
    (fun u v _ _ hu hv => ?_) hy'
  · exact ⟨0, 1, by rw [Set.mem_singleton_iff.mp hz]; simp⟩
  · exact ⟨r, 0, by simp⟩
  · obtain ⟨a, b, rfl⟩ := hu
    obtain ⟨a', b', rfl⟩ := hv
    exact ⟨a + a', b + b', by simp only [map_add (f := _)]; ring⟩
  · obtain ⟨a, b, rfl⟩ := hu
    obtain ⟨a', b', rfl⟩ := hv
    refine ⟨a * a' + b * b' * c, a * b' + a' * b, ?_⟩
    simp only [map_add (f := _), map_mul]
    linear_combination (algebraMap ℚ E b * algebraMap ℚ E b') * hx

theorem not_sq_eq_of_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (b : ℚ)
    (h : (p : ℚ) = q * b ^ 2) : False := by
  haveI := Fact.mk hq
  have hb : b ≠ 0 := by
    rintro rfl
    have h0 : (p : ℚ) = 0 := by rw [h]; ring
    exact hp.ne_zero (by exact_mod_cast h0)
  have h1 := congrArg (padicValRat q) h
  rw [padicValRat.mul (by exact_mod_cast hq.ne_zero) (pow_ne_zero 2 hb), padicValRat.pow b,
    padicValRat.self hq.one_lt, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd] at h1
  · push_cast at h1
    omega
  · intro hd
    exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp hd).symm

theorem false_of_sq_eq {E : Type*} [Field E] [CharZero E] [Algebra ℚ E] {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (x : E) (hx : x ^ 2 = -(q : E)) (a b : ℚ)
    (h : (algebraMap ℚ E a + algebraMap ℚ E b * x) ^ 2 = -(p : E)) : False := by
  have hφ : Function.Injective (algebraMap ℚ E) := (algebraMap ℚ E).injective
  have key : algebraMap ℚ E (a ^ 2 - q * b ^ 2 + p) + algebraMap ℚ E (2 * a * b) * x = 0 := by
    simp only [map_add (f := _), map_sub, map_mul, map_pow, map_natCast, map_ofNat]
    linear_combination h - algebraMap ℚ E b ^ 2 * hx
  have hq0 : (0 : ℚ) < q := by exact_mod_cast hq.pos
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.pos
  by_cases hab : 2 * a * b = 0
  · rw [hab, map_zero, zero_mul, add_zero, map_eq_zero_iff _ hφ] at key
    rcases mul_eq_zero.mp hab with h2a | hb
    · have ha : a = 0 := by linarith
      subst ha
      exact not_sq_eq_of_prime hp hq hpq b (by linear_combination key)
    · subst hb
      nlinarith [sq_nonneg a]
  · have hne : algebraMap ℚ E (2 * a * b) ≠ 0 := (map_ne_zero _).mpr hab
    have hx' : x = -algebraMap ℚ E (a ^ 2 - q * b ^ 2 + p) / algebraMap ℚ E (2 * a * b) :=
      eq_div_of_mul_eq hne (by linear_combination key)
    rw [← map_neg, ← map_div₀] at hx'
    rw [hx', ← map_pow, show -(q : E) = algebraMap ℚ E (-(q : ℚ)) by rw [map_neg, map_natCast]] at hx
    have h2 := hφ hx
    nlinarith [sq_nonneg (-(a ^ 2 - q * b ^ 2 + p) / (2 * a * b))]

theorem finite_primes_of_finiteDimensional (E : Type*) [Field E] [CharZero E] [Algebra ℚ E]
    [FiniteDimensional ℚ E] : {p : ℕ | p.Prime ∧ ∃ x : E, x ^ 2 = -(p : E)}.Finite := by
  classical
  haveI : Finite (IntermediateField ℚ E) :=
    (Field.exists_primitive_element_iff_finite_intermediateField ℚ E).mp
      ⟨inferInstance, Field.exists_primitive_element ℚ E⟩
  have key : ∀ p q : ℕ, p.Prime → q.Prime → ∀ x y : E, x ^ 2 = -(p : E) → y ^ 2 = -(q : E) →
      IntermediateField.adjoin ℚ {x} = IntermediateField.adjoin ℚ {y} → p = q := by
    intro p q hp hq x y hx hy he
    by_contra hpq
    have hmem : x ∈ IntermediateField.adjoin ℚ {y} := by
      rw [← he]
      exact IntermediateField.mem_adjoin_simple_self ℚ x
    obtain ⟨a, b, hab⟩ :=
      exists_eq_add_mul_of_mem_adjoin y (-(q : ℚ)) (by rw [hy, map_neg, map_natCast]) hmem
    exact false_of_sq_eq hp hq hpq y hy a b (by rw [← hab]; exact hx)
  have hinj : Function.Injective (fun p : {p : ℕ | p.Prime ∧ ∃ x : E, x ^ 2 = -(p : E)} =>
      IntermediateField.adjoin ℚ {Classical.choose p.2.2}) := by
    rintro ⟨p, hp⟩ ⟨q, hq⟩ he
    exact Subtype.ext (key p q hp.1 hq.1 _ _ (Classical.choose_spec hp.2) (Classical.choose_spec hq.2) he)
  exact Set.finite_coe_iff.mp (Finite.of_injective _ hinj)

theorem finite_primes_field (F : Type*) [Field F] [CharZero F] [Algebra ℚ F]
    [Algebra.EssFiniteType ℚ F] : {p : ℕ | p.Prime ∧ ∃ x : F, x ^ 2 = -(p : F)}.Finite := by
  have hfd := GlobalTheory.finiteDimensional_algebraicClosure_of_essFiniteType ℚ F
  refine (@finite_primes_of_finiteDimensional (algebraicClosure ℚ F) _ _ (algebraicClosure ℚ F).algebra' hfd).subset ?_
  rintro p ⟨hp, x, hx⟩
  have hint : IsIntegral ℚ x :=
    ⟨Polynomial.X ^ 2 - Polynomial.C (-(p : ℚ)), Polynomial.monic_X_pow_sub_C _ two_ne_zero, by simp [hx]⟩
  have hmem : x ∈ algebraicClosure ℚ F := mem_algebraicClosure_iff'.mpr hint
  exact ⟨hp, ⟨x, hmem⟩, Subtype.ext (by simp [hx])⟩

theorem finite_primes_of_isFractionRing (A F : Type*) [CommRing A] [IsDomain A] [CharZero A]
    [Algebra.FiniteType ℤ A] [Field F] [Algebra A F] [IsFractionRing A F] :
    {p : ℕ | p.Prime ∧ ∃ a b : A, b ≠ 0 ∧ a ^ 2 + (p : A) * b ^ 2 = 0}.Finite := by
  haveI : CharZero F := charZero_of_injective_algebraMap (IsFractionRing.injective A F)
  haveI : Algebra.EssFiniteType A F := Algebra.EssFiniteType.of_isLocalization F (nonZeroDivisors A)
  haveI : Algebra.EssFiniteType ℤ F := Algebra.EssFiniteType.comp ℤ A F
  haveI : Algebra.EssFiniteType ℚ F := Algebra.EssFiniteType.of_comp ℤ ℚ F
  refine (finite_primes_field F).subset ?_
  rintro p ⟨hp, a, b, hb, hab⟩
  have hb' : algebraMap A F b ≠ 0 := fun h0 =>
    hb (IsFractionRing.injective A F (by rw [h0, map_zero]))
  refine ⟨hp, algebraMap A F a / algebraMap A F b, ?_⟩
  have e := congrArg (algebraMap A F) hab
  simp only [map_add (f := _), map_mul, map_pow, map_natCast, map_zero] at e
  rw [div_pow, div_eq_iff (pow_ne_zero 2 hb')]
  linear_combination e

theorem finite_primes_neg_sq : ∀ (σ : Type) [Finite σ] (A : Type) [CommRing A] [IsDomain A] [CharZero A] (f : MvPolynomial σ ℤ →+* A), Function.Surjective f → {p : ℕ | p.Prime ∧ ∃ a b : A, b ≠ 0 ∧ a ^ 2 + (p : A) * b ^ 2 = 0}.Finite := by
  intro σ _ A _ _ _ f hf
  haveI : Algebra.FiniteType ℤ A := by
    obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
    refine Algebra.FiniteType.iff_quotient_mvPolynomial''.mpr
      ⟨n, MvPolynomial.aeval (R := ℤ) (fun i : Fin n => f (MvPolynomial.X (e.symm i))), ?_⟩
    have hcomp : ((MvPolynomial.aeval (R := ℤ) (fun i : Fin n => f (MvPolynomial.X (e.symm i)))).toRingHom).comp
        (MvPolynomial.rename (R := ℤ) e).toRingHom = f := by
      apply MvPolynomial.ringHom_ext'
      · exact RingHom.ext_int _ _
      · intro s
        simp
    intro a
    obtain ⟨p, rfl⟩ := hf a
    exact ⟨MvPolynomial.rename (R := ℤ) e p, RingHom.congr_fun hcomp p⟩
  exact finite_primes_of_isFractionRing A (FractionRing A)

end GlobalTheory.CompanionTheory.QuadFin
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FinitePrimesSumSquaresZeroStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_primes_sum_squares_zero : ∀ (σ : Type) [Finite σ] (A : Type) [CommRing A] [IsDomain A] [CharZero A] (f : MvPolynomial σ ℤ →+* A), Function.Surjective f → {p : ℕ | p.Prime ∧ ∃ a b : A, b ≠ 0 ∧ a ^ 2 + (p : A) * b ^ 2 = 0}.Finite := by
  first | exact @GlobalTheory.CompanionTheory.QuadFin.finite_primes_neg_sq | exact GlobalTheory.CompanionTheory.QuadFin.finite_primes_neg_sq | (intros; apply GlobalTheory.CompanionTheory.QuadFin.finite_primes_neg_sq <;> assumption)
end
end

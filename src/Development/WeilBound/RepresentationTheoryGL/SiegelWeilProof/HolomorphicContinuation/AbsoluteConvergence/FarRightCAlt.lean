module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ContinuousSecondCayleyBlockMap

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SplitMulAlt
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.HzBound
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.RpowLeAdd
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.FarK

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.AbsSt.Far

variable {m n : ℕ} {ε : Fin m → Bool} {c t : ℝ} {p q : ℕ} {e : ℤ} {sL : PX m n →ₗ[ℂ] (GR n → ℂ)}
  {ρ : GR n → PX m n →ₗ[ℂ] PX m n}

theorem sL_bound (hI : Iwa) (hM : Mult) (hD : CayleyBlocksInvertible) (hL : LocData ε c t p q e sL ρ) (Q : PX m n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : GR n, ‖sL Q y‖ ≤ C * ‖F0 p q e y‖ := by
  have hK := isCompact_KR (n := n)
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (hL.cont Q).continuousOn
  have hne : ((KR n : Subgroup (GR n)) : Set (GR n)).Nonempty := ⟨1, (KR n).one_mem⟩
  obtain ⟨k0, -, hmin⟩ := hK.exists_isMinOn hne (continuous_weight_factor (n := n) hD p q e).norm.continuousOn
  have hδ : 0 < ‖F0 p q e k0‖ := norm_pos_iff.mpr (weight_factor_ne_zero hD p q e k0)
  refine ⟨max B 0 / ‖F0 p q e k0‖, div_nonneg (le_max_right _ _) hδ.le, fun y => ?_⟩
  obtain ⟨u, k, hu, hk, rfl⟩ := hI n y
  have hmk : ‖F0 p q e k0‖ ≤ ‖F0 p q e k‖ := hmin hk
  rw [hL.law Q u k hu, ((hM n p q e).1 u k hk).1, norm_mul, norm_mul]
  have h1 : ‖sL Q k‖ ≤ max B 0 := (hB k hk).trans (le_max_left _ _)
  have h2 : max B 0 ≤ max B 0 / ‖F0 p q e k0‖ * ‖F0 p q e k‖ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
    exact mul_le_mul_of_nonneg_left hmk (le_max_right _ _)
  calc ‖F0 p q e u‖ * ‖sL Q k‖ ≤ ‖F0 p q e u‖ * (max B 0 / ‖F0 p q e k0‖ * ‖F0 p q e k‖) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (norm_nonneg _)
    _ = max B 0 / ‖F0 p q e k0‖ * (‖F0 p q e u‖ * ‖F0 p q e k‖) := by ring

theorem rpow_le_add {a x₁ x₂ s : ℝ} (ha : 0 < a) (h₁ : x₁ ≤ s) (h₂ : s ≤ x₂) : a ^ s ≤ a ^ x₁ + a ^ x₂ := by
  rcases le_total 1 a with h | h
  · have := Real.rpow_le_rpow_of_exponent_le h h₂
    have := Real.rpow_nonneg ha.le x₁
    linarith
  · have := Real.rpow_le_rpow_of_exponent_ge ha h h₁
    have := Real.rpow_nonneg ha.le x₂
    linarith

section Glob

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0}
  {sec I : PX m n →ₗ[ℂ] (G → ℂ)}

theorem Ht_pos (hD : CayleyBlocksInvertible) (hG : GlobCore ε c sL ρ G Pp Γ ι s₀ Ht sec I) (x : G) : 0 < (Ht x : ℝ) := by
  obtain ⟨x₀, y, S, r, hr, rfl, h⟩ := hG.split x
  rw [(h y).1]
  exact mul_pos hr (hLoc_pos hD y)

theorem sec_bound (hI : Iwa) (hM : Mult) (hD : CayleyBlocksInvertible) (hL : LocData ε c t p q e sL ρ)
    (hG : GlobCore ε c sL ρ G Pp Γ ι s₀ Ht sec I) (Q : PX m n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : G, ‖sec Q x‖ ≤ C * ‖sec 1 x‖ := by
  obtain ⟨C, hC0, hC⟩ := PositivityTheory.Rg.Sw.AbsSt.FarK.sL_bound hI hM hD hL Q
  refine ⟨C, hC0, fun x => ?_⟩
  obtain ⟨x0, y, S, r, -, hx, hy⟩ := hG.split x
  subst hx
  rw [(hy y).2 Q, (hy y).2 1, hL.vac y, norm_mul, norm_mul, mul_left_comm]
  exact mul_le_mul_of_nonneg_left (hC y) (norm_nonneg S)

theorem norm_hz (hD : CayleyBlocksInvertible) (hG : GlobCore ε c sL ρ G Pp Γ ι s₀ Ht sec I) (z : ℂ) (Q : PX m n) (x : G) :
    ‖hz Ht sec s₀ z Q x‖ = (Ht x : ℝ) ^ (z.re - s₀.re) * ‖sec Q x‖ := by
  have hpos := PositivityTheory.Rg.Sw.AbsSt.FarK.Ht_pos hD hG x
  simp only [hz, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos, Complex.sub_re]

end Glob

end PositivityTheory.Rg.Sw.AbsSt.FarK
end
end

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.FarK

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.AbsSt.Far

variable {m n : ℕ} {ε : Fin m → Bool} {c t : ℝ} {p q : ℕ} {e : ℤ} {sL : PX m n →ₗ[ℂ] (GR n → ℂ)}
  {ρ : GR n → PX m n →ₗ[ℂ] PX m n}
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0}
  {sec I : PX m n →ₗ[ℂ] (G → ℂ)}

theorem hz_bound (hD : CayleyBlocksInvertible) (hG : GlobCore ε c sL ρ G Pp Γ ι s₀ Ht sec I) {Q : PX m n} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, ‖sec Q x‖ ≤ C * ‖sec 1 x‖) {σ₁ σ₂ : ℝ} {z : ℂ} (h₁ : σ₁ ≤ z.re) (h₂ : z.re ≤ σ₂) (x : G) :
    ‖hz Ht sec s₀ z Q x‖ ≤ C * (‖hz Ht sec s₀ (σ₁ : ℂ) 1 x‖ + ‖hz Ht sec s₀ (σ₂ : ℂ) 1 x‖) := by
  rw [norm_hz hD hG, norm_hz hD hG, norm_hz hD hG, Complex.ofReal_re, Complex.ofReal_re]
  have hx := Ht_pos hD hG x
  have hr := rpow_le_add hx (show σ₁ - s₀.re ≤ z.re - s₀.re by linarith) (show z.re - s₀.re ≤ σ₂ - s₀.re by linarith)
  calc (Ht x : ℝ) ^ (z.re - s₀.re) * ‖sec Q x‖
      ≤ ((Ht x : ℝ) ^ (σ₁ - s₀.re) + (Ht x : ℝ) ^ (σ₂ - s₀.re)) * (C * ‖sec 1 x‖) :=
        mul_le_mul hr (hC x) (norm_nonneg _) (by positivity)
    _ = C * ((Ht x : ℝ) ^ (σ₁ - s₀.re) * ‖sec 1 x‖ + (Ht x : ℝ) ^ (σ₂ - s₀.re) * ‖sec 1 x‖) := by ring

theorem hz_bound0 (hD : CayleyBlocksInvertible) (hG : GlobCore ε c sL ρ G Pp Γ ι s₀ Ht sec I) {Q : PX m n} {C : ℝ}
    (hC : ∀ x, ‖sec Q x‖ ≤ C * ‖sec 1 x‖) (z : ℂ) (x : G) :
    ‖hz Ht sec s₀ z Q x‖ ≤ C * ‖hz Ht sec s₀ z 1 x‖ := by
  rw [norm_hz hD hG, norm_hz hD hG]
  calc (Ht x : ℝ) ^ (z.re - s₀.re) * ‖sec Q x‖ ≤ (Ht x : ℝ) ^ (z.re - s₀.re) * (C * ‖sec 1 x‖) :=
        mul_le_mul_of_nonneg_left (hC x) (Real.rpow_nonneg (Ht_pos hD hG x).le _)
    _ = C * ((Ht x : ℝ) ^ (z.re - s₀.re) * ‖sec 1 x‖) := by ring

theorem farHol (hI : Iwa) (hM : Mult) (hD : CayleyBlocksInvertible) (hL : LocData ε c t p q e sL ρ)
    (hG : GlobCore ε c sL ρ G Pp Γ ι s₀ Ht sec I) : ∃ σ : ℝ,
    (∀ Q g, DifferentiableOn ℂ (fun z => GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z Q) g) (GlobalTheory.Cont.rightOf σ)) ∧
    (∀ Q g (z : ℂ), σ < z.re → Summable fun q => GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z Q) g q) ∧
    (∀ z : ℂ, σ < z.re → ∀ C : Set G, IsCompact C → ∃ u : GlobalTheory.Eis.Cosets Pp Γ → ℝ, Summable u ∧
      ∀ g ∈ C, ∀ q', ‖GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z 1) g q'‖ ≤ u q') := by
  obtain ⟨U, d, E, σ, -, -, -, -, -, -, -, hconv⟩ := hG.eis
  have hmaj : ∀ z : ℂ, σ < z.re → ∀ C : Set G, IsCompact C → ∃ u : GlobalTheory.Eis.Cosets Pp Γ → ℝ, Summable u ∧
      ∀ g ∈ C, ∀ q', ‖GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z 1) g q'‖ ≤ u q' :=
    fun z hzr C hC => (hconv z hzr).1 C hC
  refine ⟨σ, ?_, ?_, hmaj⟩
  · intro Q g z₀ hz₀
    have hz₀' : σ < z₀.re := hz₀
    obtain ⟨C, hC0, hC⟩ := sec_bound hI hM hD hL hG Q
    set σ₁ : ℝ := (σ + z₀.re) / 2
    set σ₂ : ℝ := z₀.re + 1
    have hσ₁ : σ < ((σ₁ : ℂ)).re := by simp only [Complex.ofReal_re, σ₁]; linarith
    have hσ₂ : σ < ((σ₂ : ℂ)).re := by simp only [Complex.ofReal_re, σ₂]; linarith
    obtain ⟨u₁, hu₁, hb₁⟩ := hmaj _ hσ₁ {g} isCompact_singleton
    obtain ⟨u₂, hu₂, hb₂⟩ := hmaj _ hσ₂ {g} isCompact_singleton
    set V : Set ℂ := {z | σ₁ < z.re ∧ z.re < σ₂}
    have hV : IsOpen V := (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
    have hz₀V : z₀ ∈ V := ⟨by simp only [σ₁]; linarith, by simp only [σ₂]; linarith⟩
    have hdiff : DifferentiableOn ℂ (fun w => ∑' q', GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ w Q) g q') V := by
      refine Complex.differentiableOn_tsum_of_summable_norm ((hu₁.add hu₂).mul_left C) (fun q' => ?_) hV
        (fun q' w hw => ?_)
      · have hne : (((Ht (((q'.out : Γ) : G) * g) : ℝ) : ℂ)) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (Ht_pos hD hG _).ne'
        exact (((differentiable_id.sub_const s₀).const_cpow (Or.inl hne)).mul_const _).differentiableOn
      · have h := hz_bound hD hG hC0 hC (σ₁ := σ₁) (σ₂ := σ₂) (z := w) hw.1.le hw.2.le (((q'.out : Γ) : G) * g)
        calc ‖GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ w Q) g q'‖ ≤ C * (‖GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ (σ₁ : ℂ) 1) g q'‖ +
              ‖GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ (σ₂ : ℂ) 1) g q'‖) := h
          _ ≤ C * (u₁ q' + u₂ q') := mul_le_mul_of_nonneg_left
              (add_le_add (hb₁ g (mem_singleton g) q') (hb₂ g (mem_singleton g) q')) hC0
          _ = (fun q' => C * (u₁ q' + u₂ q')) q' := rfl
    exact (hdiff.differentiableAt (hV.mem_nhds hz₀V)).differentiableWithinAt
  · intro Q g z hzr
    obtain ⟨C, hC0, hC⟩ := sec_bound hI hM hD hL hG Q
    obtain ⟨u, hu, hb⟩ := hmaj z hzr {g} isCompact_singleton
    refine Summable.of_norm_bounded (hu.mul_left C) fun q' => ?_
    calc ‖GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z Q) g q'‖ ≤ C * ‖GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z 1) g q'‖ :=
          hz_bound0 hD hG hC z _
      _ ≤ C * u q' := mul_le_mul_of_nonneg_left (hb g (mem_singleton g) q') hC0

end PositivityTheory.Rg.Sw.AbsSt.FarK
end
end

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.FarK

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.AbsSt.Far

variable {m n : ℕ} {ε : Fin m → Bool} {c t : ℝ} {p q : ℕ} {e : ℤ} {sL : PX m n →ₗ[ℂ] (GR n → ℂ)}
  {ρ : GR n → PX m n →ₗ[ℂ] PX m n}
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0}
  {sec I : PX m n →ₗ[ℂ] (G → ℂ)}

theorem split_mul (x₀ : G) (y k : GR n) : x₀ * ι y * ι k = x₀ * ι (y * k) := by
  rw [mul_assoc, ← map_mul]

theorem cont_hz (hD : CayleyBlocksInvertible) (hL : LocData ε c t p q e sL ρ) (hG : GlobCore ε c sL ρ G Pp Γ ι s₀ Ht sec I)
    (z : ℂ) (b : GR n) (x : G) : Continuous fun k : KR n => hz Ht sec s₀ z 1 (x * ι ((k : GR n) * b)) := by
  obtain ⟨x₀, y, S, r, hr, rfl, h⟩ := hG.split x
  have hfun : (fun k : KR n => hz Ht sec s₀ z 1 (x₀ * ι y * ι ((k : GR n) * b))) =
      fun k : KR n => ((r * hLoc (y * (k : GR n) * b) : ℝ) : ℂ) ^ (z - s₀) * (S * F0 p q e (y * (k : GR n) * b)) := by
    funext k
    unfold hz
    rw [split_mul, ← mul_assoc y (k : GR n) b, (h _).1, (h _).2 1, hL.vac]
  rw [hfun]
  have hc : Continuous fun k : KR n => y * (k : GR n) * b :=
    (continuous_const.mul continuous_subtype_val).mul continuous_const
  refine Continuous.mul ?_ (continuous_const.mul ((continuous_weight_factor hD p q e).comp hc))
  refine Continuous.cpow ?_ continuous_const (fun k => ?_)
  · exact Complex.continuous_ofReal.comp (continuous_const.mul ((continuous_hLoc hD).comp hc))
  · exact Complex.ofReal_mem_slitPlane.mpr (mul_pos hr (hLoc_pos hD _))

theorem pointId [MeasurableSpace (KR n)] (hD : CayleyBlocksInvertible) (hL : LocData ε c t p q e sL ρ)
    (hG : GlobCore ε c sL ρ G Pp Γ ι s₀ Ht sec I) {ν : Measure (KR n)} {κ : KR n → ℂ} {N : ℕ}
    {yy : Fin N → GR n} {QQ : Fin N → PX m n} {M : ℂ → Matrix (Fin N) (Fin N) ℂ}
    (hMid : ∀ (w : ℂ) (i : Fin N) (y' : GR n), ∫ k, κ k * ((hLoc (y' * (k : GR n) * yy i) : ℂ) ^ w *
        F0 p q e (y' * (k : GR n) * yy i)) ∂ν = (hLoc y' : ℂ) ^ w * ∑ j, M w i j * sL (QQ j) y')
    (z : ℂ) (i : Fin N) (x : G) :
    ∫ k, κ k * hz Ht sec s₀ z 1 (x * ι ((k : GR n) * yy i)) ∂ν = ∑ j, M (z - s₀) i j * hz Ht sec s₀ z (QQ j) x := by
  obtain ⟨x₀, y, S, r, hr, rfl, h⟩ := hG.split x
  have hfun : (fun k : KR n => κ k * hz Ht sec s₀ z 1 (x₀ * ι y * ι ((k : GR n) * yy i))) =
      fun k : KR n => ((r : ℂ) ^ (z - s₀) * S) *
        (κ k * ((hLoc (y * (k : GR n) * yy i) : ℂ) ^ (z - s₀) * F0 p q e (y * (k : GR n) * yy i))) := by
    funext k
    unfold hz
    rw [split_mul, ← mul_assoc y (k : GR n) (yy i), (h _).1, (h _).2 1, hL.vac, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg hr.le (hLoc_pos hD _).le]
    ring
  rw [hfun, integral_const_mul, hMid (z - s₀) i y, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold hz
  rw [(h y).1, (h y).2 (QQ j), Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hr.le (hLoc_pos hD _).le]
  ring

end PositivityTheory.Rg.Sw.AbsSt.FarK
end
end

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.FarK

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.AbsSt.Far

variable {m n : ℕ} {ε : Fin m → Bool} {c t : ℝ} {p q : ℕ} {e : ℤ} {sL : PX m n →ₗ[ℂ] (GR n → ℂ)}
  {ρ : GR n → PX m n →ₗ[ℂ] PX m n}
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0}
  {sec I : PX m n →ₗ[ℂ] (G → ℂ)}

theorem farId [MeasurableSpace (KR n)] [BorelSpace (KR n)] (hD : CayleyBlocksInvertible) (hL : LocData ε c t p q e sL ρ)
    (hG : GlobCore ε c sL ρ G Pp Γ ι s₀ Ht sec I) {ν : Measure (KR n)} {κ : KR n → ℂ} {N : ℕ}
    {yy : Fin N → GR n} {QQ : Fin N → PX m n} {M : ℂ → Matrix (Fin N) (Fin N) ℂ}
    (hν : IsFiniteMeasure ν) (hκ : Continuous κ)
    (hMid : ∀ (w : ℂ) (i : Fin N) (y' : GR n), ∫ k, κ k * ((hLoc (y' * (k : GR n) * yy i) : ℂ) ^ w *
        F0 p q e (y' * (k : GR n) * yy i)) ∂ν = (hLoc y' : ℂ) ^ w * ∑ j, M w i j * sL (QQ j) y')
    {z : ℂ} (hmaj : ∀ C : Set G, IsCompact C → ∃ u : GlobalTheory.Eis.Cosets Pp Γ → ℝ, Summable u ∧
      ∀ g ∈ C, ∀ q', ‖GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z 1) g q'‖ ≤ u q')
    (g : G) (hsum : ∀ j, Summable fun q' => GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z (QQ j)) g q') (i : Fin N) :
    ∫ k, κ k * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z 1) (g * ι ((k : GR n) * yy i)) ∂ν =
      ∑ j, M (z - s₀) i j * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z (QQ j)) g := by
  classical
  have hCc : IsCompact (range fun k : KR n => g * ι ((k : GR n) * yy i)) :=
    isCompact_range (continuous_const.mul (hG.ιcont.comp (continuous_subtype_val.mul continuous_const)))
  obtain ⟨u, hu, hbu⟩ := hmaj _ hCc
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hκ.continuousOn
  set B' := max B 0 with hB'
  set F : GlobalTheory.Eis.Cosets Pp Γ → KR n → ℂ :=
    fun q' k => κ k * hz Ht sec s₀ z 1 (((q'.out : Γ) : G) * (g * ι ((k : GR n) * yy i))) with hFdef
  have hFb : ∀ q' k, ‖F q' k‖ ≤ B' * u q' := by
    intro q' k
    simp only [hFdef, norm_mul]
    exact mul_le_mul ((hB k (mem_univ _)).trans (le_max_left _ _)) (hbu _ ⟨k, rfl⟩ q') (norm_nonneg _)
      (le_max_right _ _)
  have hFc : ∀ q', Continuous (F q') := by
    intro q'
    have := cont_hz hD hL hG z (yy i) (((q'.out : Γ) : G) * g)
    simp only [hFdef]
    refine hκ.mul ?_
    simpa only [mul_assoc] using this
  have hFi : ∀ q', Integrable (F q') ν := fun q' =>
    Integrable.mono' (integrable_const (B' * u q')) (hFc q').aestronglyMeasurable (ae_of_all _ (hFb q'))
  have hFn : ∀ q', ∫ k, ‖F q' k‖ ∂ν ≤ B' * u q' * ν.real univ := by
    intro q'
    calc ∫ k, ‖F q' k‖ ∂ν ≤ ∫ _k, B' * u q' ∂ν := integral_mono (hFi q').norm (integrable_const _) (hFb q')
      _ = B' * u q' * ν.real univ := by rw [integral_const, smul_eq_mul, mul_comm]
  have hF0 : ∀ q', q' ∉ Function.support u → ∀ k, F q' k = 0 := by
    intro q' hq k
    have h0 : u q' = 0 := Function.notMem_support.mp hq
    have := hFb q' k
    rw [h0, mul_zero] at this
    exact norm_le_zero_iff.mp this
  have : Countable (Function.support u) := hu.countable_support.to_subtype
  have hL1 : ∀ k, κ k * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z 1) (g * ι ((k : GR n) * yy i)) =
      ∑' s : Function.support u, F s k := by
    intro k
    rw [tsum_subtype_eq_of_support_subset (f := fun q' => F q' k) ?_]
    · simp only [hFdef, GlobalTheory.Eis.cosetSum, GlobalTheory.Eis.term]
      rw [tsum_mul_left]
    · intro q' hq
      by_contra h
      exact hq (hF0 q' h k)
  have hsumn : Summable fun s : Function.support u => ∫ k, ‖F s k‖ ∂ν :=
    Summable.of_nonneg_of_le (fun s => integral_nonneg fun _ => norm_nonneg _) (fun s => hFn s)
      (((hu.subtype _).mul_left B').mul_right (ν.real univ))
  have hint : ∫ k, κ k * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z 1) (g * ι ((k : GR n) * yy i)) ∂ν =
      ∑' s : Function.support u, ∫ k, F s k ∂ν := by
    simp_rw [hL1]
    exact (integral_tsum_of_summable_integral_norm (F := fun (s : Function.support u) k => F s k)
      (fun s => hFi s) hsumn).symm
  have hint2 : ∑' s : Function.support u, ∫ k, F s k ∂ν = ∑' q', ∫ k, F q' k ∂ν := by
    refine tsum_subtype_eq_of_support_subset (f := fun q' => ∫ k, F q' k ∂ν) ?_
    intro q' hq
    by_contra h
    exact hq (by simp only [hF0 q' h, integral_zero])
  have hpt : ∀ q', ∫ k, F q' k ∂ν = ∑ j, M (z - s₀) i j * hz Ht sec s₀ z (QQ j) (((q'.out : Γ) : G) * g) := by
    intro q'
    have := pointId hD hL hG hMid z i (((q'.out : Γ) : G) * g)
    simpa only [hFdef, mul_assoc] using this
  rw [hint, hint2, tsum_congr hpt]
  have hS : HasSum (fun b => ∑ j, M (z - s₀) i j * GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z (QQ j)) g b)
      (∑ j, M (z - s₀) i j * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z (QQ j)) g) :=
    hasSum_sum fun j _ => ((hsum j).hasSum).mul_left (M (z - s₀) i j)
  exact hS.tsum_eq

end PositivityTheory.Rg.Sw.AbsSt.FarK

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

theorem farRightC : Iwa → CayleyBlocksInvertible → Mult → HolParam → FarRightC := by
  intro hI hD hM _hH m n ε c t p q e sL ρ hL G _ _ _ _ _ _ Pp Γ ι s₀ Ht sec I hG
  obtain ⟨σ, h1, h2, hmaj⟩ := FarK.farHol hI hM hD hL hG
  refine ⟨σ, h1, h2, ?_⟩
  intro _ _ ν κ N yy QQ M hν hκ hMid z hzr g i
  exact FarK.farId hD hL hG hν hκ hMid (hmaj z hzr) g (fun j => h2 (QQ j) g z hzr) i

end PositivityTheory.Rg.Sw.AbsSt

module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsFurther
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistGenerated
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGraphChangeOfModel
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlock
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PZCombLimit
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreChartZeroSet
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionsDimZero
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNmSectionsFinite
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AnResBridgeSheet
public import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEmbeddingWeight
public import GroundTheory.GlobalFields.ComplexMultiplication.EllipticFunctions
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChangeOfLattice

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionPointValue
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry SectionBounded

noncomputable section

set_option linter.unusedSectionVars false

namespace SectionPointValue

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def IsRep (y : (Σ k, ι k) → Ω) (a : K → ℤ) (n : ℕ) (s : Ω) (g h : MRing ι) : Prop :=
  ∃ dg dh : K → ℕ, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g dg ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog h dh ∧ (∀ k, (dg k : ℤ) = dh k + n * a k) ∧
    aeval y g = s * aeval y h

theorem y_ne_zero {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y))
    {p : Σ k, ι k} (hp : z p ≠ 0) : y p ≠ 0 := by
  intro h0
  apply hp
  have hX : (X p : MRing ι) ∈ mCoordIdeal y := by
    show X p ∈ RingHom.ker (mConeMap y)
    rw [RingHom.mem_ker]
    simp [mConeMap, h0]
  simpa using hz.2 _ hX

theorem cross {y : (Σ k, ι k) → Ω} {a : K → ℤ} {n : ℕ} {s : Ω} {g h g' h' : MRing ι}
    (hr : IsRep y a n s g h) (hr' : IsRep y a n s g' h') {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y)) :
    eval z (map (Int.castRingHom ℂ) g) * eval z (map (Int.castRingHom ℂ) h') =
      eval z (map (Int.castRingHom ℂ) g') * eval z (map (Int.castRingHom ℂ) h) := by
  obtain ⟨dg, dh, hg, hh, hd, hy⟩ := hr
  obtain ⟨dg', dh', hg', hh', hd', hy'⟩ := hr'
  have hF : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (g * h' - g' * h) (dg + dh') :=
    homog_sub (homog_mul hg hh') (homog_congr (homog_mul hg' hh) fun k => by
      simp only [Pi.add_apply]
      zify
      linear_combination hd' k - hd k)
  have hFy : aeval y (g * h' - g' * h) = 0 := by
    rw [map_sub, map_mul, map_mul, hy, hy']
    ring
  have := vanish hz hF hFy
  simp only [map_sub, map_mul, sub_eq_zero] at this
  exact this

theorem exists_rep_at {y : (Σ k, ι k) → Ω} {a : K → ℤ} {n : ℕ} {s : Ω} (hs : s ∈ chartLat y a n)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) :
    ∃ gh : MRing ι × MRing ι, IsRep y a n s gh.1 gh.2 ∧ eval z (map (Int.castRingHom ℂ) gh.2) ≠ 0 := by
  choose c hc using hz.1
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => y_ne_zero hz (hc k)
  obtain ⟨N, δ, G, hG, hdeg, hGv⟩ := exists_chartForm y c hyc (fun k => (n : ℤ) * a k) (hs c hyc)
  refine ⟨(G, chartMon c N), ⟨δ, N, hG, homog_chartMon c N, fun k => ?_, ?_⟩, ?_⟩
  · linear_combination hdeg k
  · rw [aeval_chartMon]
    exact hGv
  · rw [eval_chartMon]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)

theorem metric_ne {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {P : Ideal (MRing ι)} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) (n : ℕ) :
    (A.h z : ℂ) ^ n ≠ 0 :=
  pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (A.pos z hz.1).ne')

def val (y : (Σ k, ι k) → Ω) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (n : ℕ) (s : Ω) (z : (Σ k, ι k) → ℂ) : ℂ := by
  classical
  exact if hsz : s ∈ chartLat y A.a n ∧ z ∈ mcPts (mCoordIdeal y) then
    eval z (map (Int.castRingHom ℂ) (exists_rep_at hsz.1 hsz.2).choose.1) /
      (eval z (map (Int.castRingHom ℂ) (exists_rep_at hsz.1 hsz.2).choose.2) * (A.h z : ℂ) ^ n)
  else 0

theorem val_spec {y : (Σ k, ι k) → Ω} {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {n : ℕ} {s : Ω} (hs : s ∈ chartLat y A.a n)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) {g h : MRing ι} (hr : IsRep y A.a n s g h) :
    eval z (map (Int.castRingHom ℂ) g) =
      val y A n s z * eval z (map (Int.castRingHom ℂ) h) * (A.h z : ℂ) ^ n := by
  have H := (exists_rep_at hs hz).choose_spec
  rw [val, dite_eq_left ⟨hs, hz⟩]
  have hc := cross hr H.1 hz
  have h1 := H.2
  have h2 := metric_ne (A := A) hz n
  rw [eq_comm, div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff (mul_ne_zero h1 h2)]
  linear_combination (-(A.h z : ℂ) ^ n) * hc

theorem val_eq {y : (Σ k, ι k) → Ω} {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {n : ℕ} {s : Ω} (hs : s ∈ chartLat y A.a n)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) {g h : MRing ι} (hr : IsRep y A.a n s g h)
    (hh : eval z (map (Int.castRingHom ℂ) h) ≠ 0) :
    val y A n s z = eval z (map (Int.castRingHom ℂ) g) /
      (eval z (map (Int.castRingHom ℂ) h) * (A.h z : ℂ) ^ n) := by
  rw [eq_div_iff (mul_ne_zero hh (metric_ne hz n)), val_spec hs hz hr]
  ring

theorem rep_add {y : (Σ k, ι k) → Ω} {a : K → ℤ} {n : ℕ} {s t : Ω} {g₁ h₁ g₂ h₂ : MRing ι}
    (r₁ : IsRep y a n s g₁ h₁) (r₂ : IsRep y a n t g₂ h₂) :
    IsRep y a n (s + t) (g₁ * h₂ + g₂ * h₁) (h₁ * h₂) := by
  obtain ⟨dg₁, dh₁, hg₁, hh₁, hd₁, hy₁⟩ := r₁
  obtain ⟨dg₂, dh₂, hg₂, hh₂, hd₂, hy₂⟩ := r₂
  refine ⟨dg₁ + dh₂, dh₁ + dh₂, homog_add (homog_mul hg₁ hh₂) (homog_congr (homog_mul hg₂ hh₁) fun k => ?_),
    homog_mul hh₁ hh₂, fun k => ?_, ?_⟩
  · simp only [Pi.add_apply]
    zify
    linear_combination hd₂ k - hd₁ k
  · simp only [Pi.add_apply]
    push_cast
    linear_combination hd₁ k
  · rw [map_add (f := _), map_mul, map_mul, map_mul, hy₁, hy₂]
    ring

theorem rep_mul {y : (Σ k, ι k) → Ω} {a : K → ℤ} {n m : ℕ} {s t : Ω} {g₁ h₁ g₂ h₂ : MRing ι}
    (r₁ : IsRep y a n s g₁ h₁) (r₂ : IsRep y a m t g₂ h₂) :
    IsRep y a (n + m) (s * t) (g₁ * g₂) (h₁ * h₂) := by
  obtain ⟨dg₁, dh₁, hg₁, hh₁, hd₁, hy₁⟩ := r₁
  obtain ⟨dg₂, dh₂, hg₂, hh₂, hd₂, hy₂⟩ := r₂
  refine ⟨dg₁ + dg₂, dh₁ + dh₂, homog_mul hg₁ hg₂, homog_mul hh₁ hh₂, fun k => ?_, ?_⟩
  · simp only [Pi.add_apply]
    push_cast
    linear_combination hd₁ k + hd₂ k
  · rw [map_mul, map_mul, hy₁, hy₂]
    ring

def w (y : (Σ k, ι k) → Ω) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (n : ℕ) : chartLat y A.a n →+ (((Σ k, ι k) → ℂ) → ℂ) :=
  AddMonoidHom.mk' (fun s => val y A n s) fun s t => by
    funext z
    show val y A n ((s + t : chartLat y A.a n) : Ω) z = val y A n s z + val y A n t z
    by_cases hz : z ∈ mcPts (mCoordIdeal y)
    · obtain ⟨⟨g₁, h₁⟩, r₁, n₁⟩ := exists_rep_at s.2 hz
      obtain ⟨⟨g₂, h₂⟩, r₂, n₂⟩ := exists_rep_at t.2 hz
      have hT := metric_ne (A := A) hz n
      rw [AddSubgroup.coe_add, val_eq (add_mem s.2 t.2) hz (rep_add r₁ r₂) (by simpa using mul_ne_zero n₁ n₂),
        val_eq s.2 hz r₁ n₁, val_eq t.2 hz r₂ n₂]
      simp only [map_add (f := _), map_mul]
      field_simp
    · simp [val, hz]

theorem val_continuousOn {y : (Σ k, ι k) → Ω} {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    (hA : ContinuousOn A.h {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}) {n : ℕ} {s : Ω} (hs : s ∈ chartLat y A.a n) :
    ContinuousOn (val y A n s) (mcPts (mCoordIdeal y)) := by
  intro z₀ hz₀
  obtain ⟨⟨g, h⟩, r, hne⟩ := exists_rep_at hs hz₀
  have hcont : ∀ f : MRing ι, Continuous fun z : (Σ k, ι k) → ℂ => eval z (map (Int.castRingHom ℂ) f) :=
    fun f => MvPolynomial.continuous_eval _
  have hAc : ContinuousWithinAt (fun z => (A.h z : ℂ) ^ n) (mcPts (mCoordIdeal y)) z₀ :=
    (Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt
      ((hA z₀ hz₀.1).mono fun z (hz : z ∈ mcPts (mCoordIdeal y)) => hz.1)).pow n
  have hF : ContinuousWithinAt (fun z => eval z (map (Int.castRingHom ℂ) g) /
      (eval z (map (Int.castRingHom ℂ) h) * (A.h z : ℂ) ^ n)) (mcPts (mCoordIdeal y)) z₀ :=
    (hcont g).continuousWithinAt.div ((hcont h).continuousWithinAt.mul hAc)
      (mul_ne_zero hne (metric_ne hz₀ n))
  refine hF.congr_of_eventuallyEq ?_ (val_eq hs hz₀ r hne)
  have hopen : {z | eval z (map (Int.castRingHom ℂ) h) ≠ 0} ∈ nhds z₀ :=
    (isOpen_ne_fun (hcont h) continuous_const).mem_nhds hne
  filter_upwards [nhdsWithin_le_nhds hopen, self_mem_nhdsWithin] with z hz hz'
  exact val_eq hs hz' r hz

theorem secNormAt_eq {y : (Σ k, ι k) → Ω} {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {n : ℕ} {s : Ω} (hs : s ∈ chartLat y A.a n)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) : secNormAt y A n s z = ‖val y A n s z‖ := by
  have hT : 0 < A.h z := A.pos z hz.1
  have hnT : ‖(A.h z : ℂ) ^ n‖ = A.h z ^ n := by
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hT.le]
  have hb : IsBoundedAt y A n ‖val y A n s z‖ s z := by
    intro dg dh g h hg hh hd hy
    rw [val_spec hs hz ⟨dg, dh, hg, hh, hd, hy⟩, norm_mul, norm_mul, hnT]
  refine le_antisymm (secNormAt_le (norm_nonneg _) hb) ?_
  rw [secNormAt]
  refine le_csInf ⟨_, norm_nonneg _, hb⟩ ?_
  rintro c ⟨-, hc⟩
  obtain ⟨⟨g, h⟩, ⟨dg, dh, hg, hh, hd, hy⟩, hne⟩ := exists_rep_at hs hz
  have := hc dg dh g h hg hh hd hy
  rw [val_spec hs hz ⟨dg, dh, hg, hh, hd, hy⟩, norm_mul, norm_mul, hnT, mul_assoc, mul_assoc] at this
  exact le_of_mul_le_mul_right this (mul_pos (norm_pos_iff.mpr hne) (pow_pos hT n))

theorem val_mul {y : (Σ k, ι k) → Ω} {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {n m : ℕ} {s t st : Ω} (hs : s ∈ chartLat y A.a n)
    (ht : t ∈ chartLat y A.a m) (hst : st ∈ chartLat y A.a (n + m)) (he : st = s * t)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) :
    val y A (n + m) st z = val y A n s z * val y A m t z := by
  obtain ⟨⟨g₁, h₁⟩, r₁, n₁⟩ := exists_rep_at hs hz
  obtain ⟨⟨g₂, h₂⟩, r₂, n₂⟩ := exists_rep_at ht hz
  have r := rep_mul r₁ r₂
  rw [← he] at r
  rw [val_eq hst hz r (by simpa using mul_ne_zero n₁ n₂), val_eq hs hz r₁ n₁, val_eq ht hz r₂ n₂]
  simp only [map_mul]
  rw [pow_add]
  ring

theorem exists_chart {y : (Σ k, ι k) → Ω} (hrel : ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant (mCoordIdeal y)) :
    ∃ c : ∀ k, ι k, ∀ k, y ⟨k, c k⟩ ≠ 0 := by
  refine ⟨fun k => (hrel k).choose, fun k h0 => (hrel k).choose_spec ?_⟩
  show X _ ∈ RingHom.ker (mConeMap y)
  rw [RingHom.mem_ker]
  simp [mConeMap, h0]

theorem common_denom {y : (Σ k, ι k) → Ω} {a : K → ℤ} {n r : ℕ} (hrel : ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant (mCoordIdeal y))
    (s : Fin r → Ω) (hs : ∀ i, s i ∈ chartLat y a n) :
    ∃ (e e' : K → ℕ) (h : MRing ι) (g : Fin r → MRing ι),
      ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog h e' ∧ (∀ i, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (g i) e) ∧ (∀ k, (e k : ℤ) = e' k + n * a k) ∧
      aeval y h ≠ 0 ∧ ∀ i, aeval y (g i) = s i * aeval y h := by
  obtain ⟨c, hc⟩ := exists_chart hrel
  choose N δ G hG hdeg hGv using fun i => exists_chartForm y c hc (fun k => (n : ℤ) * a k) (hs i c hc)
  have hN : ∀ i k, N i k ≤ ∑ j, N j k := fun i k =>
    Finset.single_le_sum (f := fun j => N j k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  set L : K → ℕ := fun k => ∑ j, N j k + ((n : ℤ) * a k).natAbs with hL
  refine ⟨fun k => ((L k : ℤ) + n * a k).toNat, L, chartMon c L, fun i => G i * chartMon c (L - N i),
    homog_chartMon c L, fun i => homog_congr (homog_mul (hG i) (homog_chartMon c _)) fun k => ?_,
    fun k => ?_, ?_, fun i => ?_⟩
  · have h1 := hdeg i k
    have h2 := hN i k
    simp only [Pi.add_apply, Pi.sub_apply, hL]
    generalize (n : ℤ) * a k = q at *
    generalize ∑ j, N j k = S at *
    omega
  · simp only [hL]
    generalize (n : ℤ) * a k = q
    generalize ∑ j, N j k = S
    omega
  · rw [aeval_chartMon]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  · rw [map_mul, hGv i, aeval_chartMon, aeval_chartMon, mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← pow_add, Pi.sub_apply]
    congr 1
    have h2 := hN i k
    simp only [hL]
    omega

end SectionPointValue


open SectionPointValue in
theorem SectionPointValue.proof : SectionPointValue.Statement := by
  intro K _ ι _ Ω _ y A hrel hA
  refine ⟨fun n => w y A n, fun n s => val_continuousOn hA s.2, ?_, ?_, ?_, ?_⟩
  · intro n s dg dh g h z hg hh hd hy hz
    exact val_spec s.2 hz ⟨dg, dh, hg, hh, hd, hy⟩
  · intro n s z hz
    exact secNormAt_eq s.2 hz
  · intro n k s t st he z hz
    exact val_mul s.2 t.2 st.2 he hz
  · intro n r s
    exact common_denom hrel (fun i => s i) fun i => (s i).2

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGeneratedPow
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

theorem GeneratedPow.proof : GeneratedPow.Statement := by
  intro S _ K _ _ ι _ _ V n t hn
  induction t with
  | zero =>
    have h0 := GenTwistGenerated.generated_diag (S := S) (ι := ι) (V := V) 0
    have e : (fun _ : K => ((0 : ℕ) : ℤ)) = (0 • n : K → ℤ) := by
      funext k
      simp
    rw [← e]
    exact h0
  | succ t ih =>
    rw [succ_nsmul']
    exact GenTwistGenerated.generated_add hn ih

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockCycleExpand
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def TwoBlockCycleExpand.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω)
    (B : Matrix (Ix κ) (Ix κ) ℚ) (c : κ) (l : Ix κ → ℤ),
    IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → LinearIndependent ℤ x → IsInvMat B →
    Submodule.span ℤ (Set.range x) ≤ Submodule.span ℤ (Set.range (matAct B x)) →
    x ⟨(), c⟩ = ∑ j, (l j : Ω) * matAct B x j →
    ∀ a b : ℕ, twoBlockVert x (matAct B x) c l (fun _ : Fin D => ![(a : ℤ), (b : ℤ)]) =
      ∑ i ∈ Finset.range (D + 1), (D.choose i : ℝ) * (a : ℝ) ^ i * (b : ℝ) ^ (D - i) *
        twoBlockVert x (matAct B x) c l (twoBlockDegList D i)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlockMetric
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def PowerBlockMetric.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (P0 : Ideal (MRing ι)) (m N : ℕ) (v : Fin N → Ω),
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) A → IsConjInvariantH A →
    (∀ j, v j ∈ chartLat y A.a m) → KH.GeneratesOn y (fun k => (m : ℤ) * A.a k) v →
    ∃ (B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (addIdx ι N)) (P0' : Ideal (MRing (addIdx ι N))),
      B.a = unitDeg (none : Option K) ∧ IsConjInvariantH B ∧ P0' ≤ mCoordIdeal (addBlock y v) ∧
      IsSemipositiveRel P0' (mCoordIdeal (addBlock y v)) B ∧
      ∀ z ∈ mcPts (mCoordIdeal (addBlock y v)), ∀ j : Fin N,
        secNormAt y A m (v j) (basePart₂ z) * B.h z = ‖z ⟨none, j⟩‖

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRelSectionsLarge
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def RelSectionsLarge.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (R : Subalgebra ℤ Ω), IsNoetherianRing R → ∀ y : (Σ k, ι k) → Ω, (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) →
      ∃ n₁ : ℕ, ∀ b : K → ℕ, (∀ k, n₁ ≤ b k) → relChartLat R y (fun k => (b k : ℤ)) 1 ≤ relSecM R y b

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGraphIsometricForms
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def GraphIsometricForms.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)]
    (P : Ideal (MRing ι)) (d : ℕ) (g : (Σ k, ι₂ k) → MRing ι) (δ : K₂ → K → ℕ)
    (B₁ : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι₂) (B₁' B' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (Sum.elim ι ι₂)),
    IsArithVar P d → (∀ q, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (g q) (δ q.1)) → IsBasePtFree P g →
    (∀ k, B₁.a k = ∑ k₂, B.a k₂ * (δ k₂ k : ℤ)) →
    (∀ z ∈ mcPts P, B₁.h z = B.h (formApply g z)) →
    IsPullHerm Sum.inl inlV B₁ B₁' → IsPullHerm Sum.inr inrV B B' →
    IsIsometricOn (graphIdeal P g) B₁' B'

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRelOneStep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def RelOneStep.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (R : Subalgebra ℤ Ω), IsNoetherianRing R → ∀ (y : (Σ k, ι k) → Ω) (c0 : ∀ k, ι k),
    (∀ k, y ⟨k, c0 k⟩ ≠ 0) → ∃ n₁ : ℕ, ∀ b : K → ℕ, (∀ k, n₁ ≤ b k) → ∀ k0 : K,
      ∀ t ∈ relChartLat R y (fun k => (b k : ℤ)) 1, y ⟨k0, c0 k0⟩ * t ∈ relSecM R y (b + Pi.single k0 1) →
        t ∈ relSecM R y b

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFSGeomDegPos
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

theorem FSGeomDegPos.proof (hDeg : DegreeStatement) (hPos : MultiDegreePositive.Statement) :
    FSGeomDegPos.Statement := by
  intro K _ ι _ P e hP
  classical
  have hS : ∀ j : Fin e, IsSmoothHerm ((fun _ : Fin e => fsH ι) j) := fun _ =>
    GroundTheory.Heights₂.Heights.Inter.isSmoothHerm_ofMetrics_fs 1
  have ha : (fun j : Fin e => ((fun _ : Fin e => fsH ι) j).a) = fun _ : Fin e => fun _ : K => (1 : ℤ) := by
    funext j k
    simp [fsH, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofMetrics]
  obtain ⟨hq, hd⟩ := ZCombLimit.genericFibre hP
  have hpos := hPos ℚ K ι _ e hq hd
  rw [GroundTheory.Heights₂.Heights.Targets.FibreDegreeSum.proof K ι P e _ 2 hP Nat.prime_two,
    finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P _)] at hpos
  rw [hDeg K ι P e (fun _ => fsH ι) 2 hP hS Nat.prime_two, ha,
    finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P _)]
  exact_mod_cast hpos

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRelTorsionBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def RelTorsionBound.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (R : Subalgebra ℤ Ω), IsNoetherianRing R → ∀ (y : (Σ k, ι k) → Ω) (c0 : ∀ k, ι k),
    (∀ k, y ⟨k, c0 k⟩ ≠ 0) → ∀ k0 : K, ∃ n₁ : ℕ, ∀ b : K → ℕ, (∀ k, n₁ ≤ b k) →
      ∀ f ∈ relSecM R y (b + Pi.single k0 1),
        (∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∃ D : ℕ, ∃ g ∈ relSecM R y (b + fun _ => D),
          (∏ k, y ⟨k, c k⟩) ^ D * f = y ⟨k0, c0 k0⟩ * g) →
        ∃ g ∈ relSecM R y b, f = y ⟨k0, c0 k0⟩ * g

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsCurveSmallCountLower
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def CurveSmallCountLower.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (II : IntersectionSystem),
    IsIntersectionSystem II → IsArithVar (mCoordIdeal y) 1 → Birational y →
    IsSmoothHerm A → IsConjInvariantH A →
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      (n : ℝ) * II K ι (mCoordIdeal y) 1 (fun _ => A) - C ≤
        smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) n

namespace CurveSmallCountLower

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet

end CurveSmallCountLower

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResolutionMixedIntegral
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

namespace ResolutionMixedIntegral

theorem proof (hB : ResolutionMixedBridge.Statement) (hI : ResolutionInterpIntegral.Statement) :
    ResolutionMixedIntegral.Statement := by
  intro D Ω _ _ κ _ d m₁ hm₁
  rw [hI D Ω κ d m₁ hm₁]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hM : ∀ j : Fin D, IsSmoothMetric (if j.val < i then m₁ else d.m) := fun j => by
    split_ifs
    · exact hm₁
    · exact d.smooth
  have hpot : mixPot d.m m₁ D i = fun j z => Real.log ((if j.val < i then m₁ else d.m).ρ z) := by
    funext j z
    unfold mixPot
    split_ifs <;> rfl
  have hres : (fun j : Fin D => resPot d (if j.val < i then m₁ else d.m)) =
      fun j : Fin D => if j.val < i then resPot d m₁ else resPot d d.m := by
    funext j
    split_ifs <;> rfl
  rw [hpot, hB D Ω κ d (fun j => if j.val < i then m₁ else d.m) m₁ hM hm₁, hres]

end ResolutionMixedIntegral

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PCovolumeLeGram
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Module

theorem CovolumeLeGram.proof : CovolumeLeGram.Statement := by
  intro n L _ _ ι _ _ x hxL hx hcard
  have hcard' : Fintype.card ι = finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
    rw [hcard, finrank_euclideanSpace_fin]
  let B : Basis ι ℝ (EuclideanSpace ℝ (Fin n)) := basisOfLinearIndependentOfCardEqFinrank' x hx hcard'
  have hB : ⇑B = x := coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _
  have hML : Submodule.span ℤ (Set.range B) ≤ L :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; rw [hB]; exact hxL i)
  have hcovM : ZLattice.covolume (Submodule.span ℤ (Set.range B)) = Real.sqrt (Matrix.gram ℝ x).det := by
    rw [GroundTheory.Heights₂.Heights.covolume_eq_sqrt_det_gram _ (B.restrictScalars ℤ)]
    congr 3
    funext i
    simp [Basis.restrictScalars_apply, hB]
  have hdiv := ZLattice.covolume_div_covolume_eq_relIndex' _ L hML
  have hposM := ZLattice.covolume_pos (Submodule.span ℤ (Set.range B))
  have hposL := ZLattice.covolume_pos L
  have hne : (Submodule.span ℤ (Set.range B)).toAddSubgroup.relIndex L.toAddSubgroup ≠ 0 := by
    intro h
    rw [h, Nat.cast_zero] at hdiv
    exact (div_pos hposM hposL).ne' hdiv
  have h1 : (1 : ℝ) ≤ ZLattice.covolume (Submodule.span ℤ (Set.range B)) / ZLattice.covolume L := by
    rw [hdiv]
    exact_mod_cast Nat.one_le_iff_ne_zero.2 hne
  rw [← hcovM]
  rwa [le_div_iff₀ hposL, one_mul] at h1

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBigIffGenDeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

namespace BigIffGenDeg

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem charZero_of_isArithVar {y : (Σ k, ι k) → Ω} {d : ℕ} (h : IsArithVar (mCoordIdeal y) d) : CharZero Ω := by
  refine charZero_of_inj_zero fun n hn => ?_
  have hmem : ((n : ℤ)) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
    show mConeMap y (C (n : ℤ)) = 0
    rw [map_natCast C n, map_natCast, ← map_natCast (MvPolynomial.C : Ω →+* MvPolynomial K Ω), hn, map_zero]
  rw [h.2.2.1] at hmem
  exact_mod_cast (Ideal.mem_bot.mp hmem)

theorem coord_ne_zero_of_isArithVar {y : (Σ k, ι k) → Ω} {d : ℕ} (h : IsArithVar (mCoordIdeal y) d) :
    ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
  intro k
  obtain ⟨i, hi⟩ := h.2.1.2.2 k
  refine ⟨i, fun h0 => hi ?_⟩
  show mConeMap y (X ⟨k, i⟩) = 0
  simp [mConeMap, h0]

end BigIffGenDeg

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PComponentResFibreSum
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

namespace ComponentResBridge

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (Res logH)

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {W : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ}
  (R : Res ι W e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))

set_option linter.unusedSectionVars false

theorem isMultiHomogIdeal_of_mem_minimalPrimes {P : Ideal (MRing ι)} (hP : IsArithVar P (e + 1))
    (hW : W ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes) :
    IsMultiHomogIdeal W := by
  have hPCh : IsMultiHomogIdeal (P.map (MvPolynomial.map (Int.castRingHom ℂ))) := by
    obtain ⟨T, hT, hPT⟩ := hP.2.1.2.1
    refine ⟨MvPolynomial.map (Int.castRingHom ℂ) '' T, ?_, by rw [hPT, Ideal.map_span]⟩
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨a, ha⟩ := hT f hf
    exact ⟨a, fun d hd k => ha d (MvPolynomial.support_map_subset _ _ hd) k⟩
  exact (GroundTheory.Heights₂.Heights.NumbersDVR.Objects.isMultiHomogIdeal_iff W).mp
    (GroundTheory.Heights₂.Heights.NumbersDVR.MinimalPrimeMultiHomog.proof ℂ K ι _ W
      ((GroundTheory.Heights₂.Heights.NumbersDVR.Objects.isMultiHomogIdeal_iff _).mpr hPCh) hW)

end ComponentResBridge

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M ComponentResBridge

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPieceDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

noncomputable section

namespace PieceDegreeAlt

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {F : Type} [Field F] [Algebra F Ω]




theorem exists_ringEquiv_comp [NumberField F] (sg sg' : F →+* ℂ) :
    ∃ τ : ℂ ≃+* ℂ, (τ : ℂ →+* ℂ).comp sg = sg' := by
  have hc : Countable F := Countable.of_equiv _ (Module.finBasis ℚ F).equivFun.toEquiv.symm
  have hΩ : Cardinal.aleph0 < Cardinal.mk ℂ := by
    rw [Cardinal.mk_complex]
    exact Cardinal.aleph0_lt_continuum
  have h1 := @GroundTheory.Global.trdeg_eq_cardinalMk_of_countable ℂ _ _ F _ sg.toAlgebra hc hΩ
  have h2 := @GroundTheory.Global.trdeg_eq_cardinalMk_of_countable ℂ _ _ F _ sg'.toAlgebra hc hΩ
  obtain ⟨τ, hτ⟩ := @GroundTheory.Global.exists_ringEquiv_extend_of_trdeg_eq ℂ _ _ F F _ _ sg.toAlgebra sg'.toAlgebra
    (RingEquiv.refl F) (h1.trans h2.symm)
  exact ⟨τ, RingHom.ext fun a => hτ a⟩

end PieceDegreeAlt

open PieceDegreeAlt

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMetricTransportSmooth
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ChangeOfLattice

noncomputable section

namespace MetricTransportSmooth

theorem matActC_one {J : Type} [Fintype J] [DecidableEq J] (z : J → ℂ) : matActC (1 : Matrix J J ℚ) z = z := by
  have h := matActC_smul_one (J := J) (1 : ℚ) z
  simpa using h

theorem matActC_zero {J : Type} [Fintype J] (A : Matrix J J ℚ) : matActC A 0 = 0 := by
  funext i
  simp [matActC]

theorem proof : MetricTransportSmooth.Statement := by
  intro κ _ B m m' hB hm hm'
  classical
  obtain ⟨B', hBB', hB'B⟩ := isInvMat_mul hB
  have hinv : ∀ w, matActC B (matActC B' w) = w := fun w => by
    rw [matActC_mul, hBB', matActC_one]
  have heq : ∀ w, m'.ρ w = m.ρ (matActC B' w) := fun w => by
    rw [← hm' (matActC B' w), hinv]
  have hmaps : Set.MapsTo (matActC B') {z : Ix κ → ℂ | z ≠ 0} {z | z ≠ 0} := fun w hw h0 => by
    apply hw
    rw [← hinv w, h0, matActC_zero]
  exact (hm.comp (contDiff_matActC B').contDiffOn hmaps).congr fun w _ => heq w

end MetricTransportSmooth

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.FibreNormCharpolyFalse
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

namespace FibreNormCharpoly

theorem aeval_mul_of_isHomogeneous {σ' Ω : Type*} [Field Ω] [CharZero Ω] {p : MvPolynomial σ' ℚ} {d : ℕ}
    (hp : p.IsHomogeneous d) (μ : Ω) (f : σ' → Ω) :
    aeval (fun j => μ * f j) p = μ ^ d * aeval f p := by
  classical
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [aeval_monomial, aeval_monomial]
  have hdeg : ∑ i ∈ m.support, m i = d := by
    have := hp (mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

end FibreNormCharpoly

namespace ProjLine

open ProjLine

end ProjLine

namespace FibreNormCharpoly

open ProjLine

end FibreNormCharpoly

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsAddBlockIsometric
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

section Objects

variable {K : Type} {ι : K → Type}

def oldV (N : ℕ) : (Σ k, ι k) → (Σ k, addIdx ι N k) := fun p => ⟨some p.1, p.2⟩

theorem isBlockMap_oldV (N : ℕ) :
    ReciprocityTheory.ChartRestriction.G.AI.I1.IsBlockMap (ι := ι) (ι' := addIdx ι N) some (oldV N) := by
  refine ⟨Option.some_injective K, ?_, fun _ => rfl, ?_⟩
  · rintro ⟨k, i⟩ ⟨k', i'⟩ h
    have h1 : k = k' := Option.some_injective K (congrArg Sigma.fst h)
    subst h1
    have h2 : i = i' := eq_of_heq (Sigma.mk.inj_iff.mp h).2
    rw [h2]
  · rintro ⟨_ | k, i⟩ ⟨k', hk'⟩
    · exact absurd hk' (Option.some_ne_none k')
    · exact ⟨⟨k, i⟩, rfl⟩

end Objects

def AddBlockIsometric.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (m N : ℕ) (v : Fin N → Ω) (B L : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (addIdx ι N)),
    IsArithVar (mCoordIdeal y) (D + 1) → 1 ≤ m →
    (∀ j, v j ∈ chartLat y A.a m) → KH.GeneratesOn y (fun k => (m : ℤ) * A.a k) v →
    B.a = unitDeg (none : Option K) →
    L.a = ReciprocityTheory.ChartRestriction.G.AI.I1.pullDeg some (fun k => (m : ℤ) * A.a k) →
    (∀ z, L.h z = A.h (basePart₂ z) ^ m) →
    (∀ z ∈ mcPts (mCoordIdeal (addBlock y v)), ∀ j : Fin N,
      secNormAt y A m (v j) (basePart₂ z) * B.h z = ‖z ⟨none, j⟩‖) →
    IsIsometricOn (mCoordIdeal (addBlock y v)) B L

namespace PowerBlockProjectiveLine

open ProjLine

end PowerBlockProjectiveLine

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMixedKleimanTop
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

theorem MixedKleimanTop.proof (hFS : ScaledFSHProps.Statement) (hE : ZCombExpand.Statement)
    (hSec : MixedSectionStep.Statement) (hH : ScaledFSTopPos.Statement) (hA : MixedTopAlgebra.Statement) :
    MixedKleimanTop.Statement := by
  intro d hd hAt hLow K _ ι _ P P0 M II hII h1 hP h0 hsM hnM hcM hhM
  obtain ⟨hsH, hcH, hmH⟩ := hFS K ι P P0
  have haH : (scaledFSH ι).a = fun k => (((fun _ => 1 : K → ℕ) k : ℕ) : ℤ) := by
    rw [scaledFSH_a]; rfl
  have e0 : II K ι P d (fun _ => M) =
      (fun i : ℕ => II K ι P d (fun j : Fin d => if (j : ℕ) < d - i then M else scaledFSH ι)) 0 := by
    simp
  rw [e0]
  refine hA d (fun i : ℕ => II K ι P d (fun j : Fin d => if (j : ℕ) < d - i then M else scaledFSH ι)) hd
    (fun i hi1 hid => hLow K ι P P0 M (scaledFSH ι) (fun _ => 1) II hII h1 hP h0 hsM hnM hcM hhM haH hsH hmH hcH
      (d - i) (by omega)) ?_ ?_
  · simpa using hH K ι P d II hII h1 hP
  · intro q p _ hp hpos
    obtain ⟨e1, e2⟩ := hE K ι (II K ι) (hII K ι) P d M (scaledFSH ι) q p hP hsM.1 hsH.1
    rw [← e2 h1]
    exact hSec K ι P P0 d M (scaledFSH ι) II hII hd hP h0 hsM hnM hcM hhM (scaledFSH_a ι) hsH hmH hcH hAt q p hp
      (by rw [e1]; exact hpos)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

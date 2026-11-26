module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformNormDegreeBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformNormAllTowerBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LowHeightOfGiven

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ShiftHEqTensorConstLine
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Small

theorem shiftH_eq_tensor_constLine {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (A : HermLine ι) (t : ℝ) :
    shiftH A t = A.tensor (ReciprocityTheory.ChartRestriction.G.AI.I2.constLine (-t)) := by
  unfold shiftH ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor ReciprocityTheory.ChartRestriction.G.AI.I2.constLine
    ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofWeight
  congr 1
  · exact (add_zero _).symm
  · funext z
    show Real.exp t * A.h z = A.h z * Real.exp (-(-t))
    rw [neg_neg, mul_comm]

theorem selfInt_shiftH : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (D : ℕ)
    (A : HermLine ι) (t : ℝ) (II : IntersectionSystem), IsIntersectionSystem II → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (D + 1) →
    IsSmoothHerm A →
    II K ι P (D + 1) (fun _ => shiftH A t) =
      II K ι P (D + 1) (fun _ => A) + ((D : ℝ) + 1) * t * geomDeg P A D := by
  intro K _ ι _ P D A t II hII hP hA
  have h := GroundTheory.Heights₂.Heights.HilbertSamuel.TopConstantTwist.proof K ι P D A (-t) II hII hP hA
  rw [shiftH_eq_tensor_constLine, h]
  push_cast
  ring

end GlobalTheory.CompanionTheory.Ar.Small
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HermitianLineShiftProperties
section -- merged from Development.WeilBound.CoreStatements.RationalSupMetrics.HermitianLineShiftProperties
section -- merged from Development.WeilBound.CoreStatements.RationalSupMetrics.AevalEqZeroOfMem
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology

namespace MultiProjectiveCoordinates

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isOpen_blocks : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  simp only [Set.setOf_forall, Set.setOf_exists]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

end MultiProjectiveCoordinates
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology

theorem MultiProjectiveCoordinates.levi_shift {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (A : HermLine ι) (t : ℝ)
    {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (w : (Σ k, ι k) → ℂ) :
    leviForm (fun z => Real.log ((shiftH A t).h z)) z w = leviForm (fun z => Real.log (A.h z)) z w := by
  have h1 : (fun z => Real.log ((shiftH A t).h z)) =ᶠ[𝓝 z] fun z => t + Real.log (A.h z) := by
    filter_upwards [MultiProjectiveCoordinates.isOpen_blocks.mem_nhds hz] with z' hz'
    show Real.log (Real.exp t * A.h z') = _
    rw [Real.log_mul (Real.exp_pos t).ne' (A.pos z' hz').ne', Real.log_exp]
  have h2 : fderiv ℝ (fun z => t + Real.log (A.h z)) = fderiv ℝ (fun z => Real.log (A.h z)) :=
    funext fun z => fderiv_const_add t
  unfold leviForm
  rw [h1.fderiv.fderiv_eq, h2]

theorem MultiProjectiveCoordinates.shiftH_smooth_nef_gen : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (A : HermLine ι) (t Λ : ℝ), (IsSmoothHerm A → IsSmoothHerm (shiftH A t)) ∧ (IsNefH P A → IsNefH P (shiftH A t)) ∧ (IsGenH P A Λ → IsGenH P (shiftH A t) (Λ * Real.exp (-t))) := by
  intro K _ ι _ P A t Λ
  have hs : IsSmoothHerm A → IsSmoothHerm (shiftH A t) := fun h => contDiffOn_const.mul h
  have hp : (∃ P0, P0 ≤ P ∧ IsSemipositiveRel P0 P A) →
      ∃ P0, P0 ≤ P ∧ IsSemipositiveRel P0 P (shiftH A t) := by
    rintro ⟨P0, h0, h1, h2⟩
    refine ⟨P0, h0, hs h1, fun z hz w hw => ?_⟩
    rw [MultiProjectiveCoordinates.levi_shift A t hz.1]
    exact h2 z hz w hw
  have hc : IsConjInvariantH A → IsConjInvariantH (shiftH A t) := fun h z => by
    show Real.exp t * _ = Real.exp t * _
    rw [h z]
  refine ⟨hs, fun h => ⟨hp h.semipos, hc h.conj, h.nef⟩, fun h =>
    ⟨mul_pos h.pos (Real.exp_pos _), hp h.semipos, hc h.conj, ?_⟩⟩
  obtain ⟨a, ha, hm⟩ := h.mono
  refine ⟨a, ha, fun z hz μ hμ => (hm z hz μ hμ).trans_eq ?_⟩
  show Λ * A.h z = Λ * Real.exp (-t) * (Real.exp t * A.h z)
  rw [mul_assoc, ← mul_assoc (Real.exp (-t)), ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HermitianLineShiftProperties
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Small

theorem shiftH_props : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (A : HermLine ι) (t Λ : ℝ), (IsSmoothHerm A → IsSmoothHerm (shiftH A t)) ∧ (IsNefH P A → IsNefH P (shiftH A t)) ∧ (IsGenH P A Λ → IsGenH P (shiftH A t) (Λ * Real.exp (-t))) :=
  @MultiProjectiveCoordinates.shiftH_smooth_nef_gen

end GlobalTheory.CompanionTheory.Ar.Small
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HermitianLineShiftPropertiesStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_line_shift_properties : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (A : HermLine ι) (t Λ : ℝ), (IsSmoothHerm A → IsSmoothHerm (shiftH A t)) ∧ (IsNefH P A → IsNefH P (shiftH A t)) ∧ (IsGenH P A Λ → IsGenH P (shiftH A t) (Λ * Real.exp (-t))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.shiftH_props | exact GlobalTheory.CompanionTheory.Ar.Small.shiftH_props | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.shiftH_props <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullIntersectionWeightBound
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullIntersectionWeightBound
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Plug

theorem ofReal_limsup_div_le (x : ℕ → ℝ) (hx : ∀ τ, 0 ≤ x τ) (c : ℝ) (hc : 0 < c) :
    ENNReal.ofReal (limsup x atTop / c) ≤ limsup (fun τ => ENNReal.ofReal (x τ / c)) atTop := by
  by_cases hb : IsBoundedUnder (· ≤ ·) atTop x
  · have hmono : Monotone (fun v : ℝ => ENNReal.ofReal (v / c)) := fun a b h =>
      ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right h hc.le)
    have hcont : Continuous (fun v : ℝ => ENNReal.ofReal (v / c)) :=
      ENNReal.continuous_ofReal.comp (continuous_id.div_const c)
    have hco : IsCoboundedUnder (· ≤ ·) atTop x :=
      isCoboundedUnder_le_of_le atTop hx
    exact (hmono.map_limsup_of_continuousAt x hcont.continuousAt hb hco).le
  · have hset : {a : ℝ | ∀ᶠ n in atTop, x n ≤ a} = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.2 fun a ha => hb ⟨a, ?_⟩
      simpa [eventually_map] using ha
    have h0 : limsup x atTop = 0 := by
      rw [limsup_eq, hset, Real.sInf_empty]
    simp [h0]

theorem arithmeticVolume_div_le_countingVolume {Ω : Type} [Field Ω] (Pr : ℕ → Ω → Prop) (La : ℕ → AddSubgroup Ω) (D d r : ℕ)
    (m : ℕ → ℕ∞) (hd : 0 < d) (hr : 0 < r)
    (hcount : ∀ τ, ((Nat.card {s : La τ // Pr τ (s : Ω)} : ℕ) : ℕ∞) ≤ m (8 * (r * τ))) :
    ENNReal.ofReal (arVolP Pr La 1 D / (((D : ℝ) + 1) * d * ((8 * r : ℕ) : ℝ) ^ (D + 1))) ≤
      GlobalTheory.CompHt.countVol D d 8 m := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = ((D : ℝ) + 1) * d * ((8 * r : ℕ) : ℝ) ^ (D + 1) := ⟨_, rfl⟩
  have hc : 0 < c := by rw [hcdef]; push_cast; positivity
  rw [← hcdef]
  obtain ⟨x, hxdef⟩ : ∃ x : ℕ → ℝ, x = fun k : ℕ => smallSectionCount Pr La (1 * k) /
      (((1 * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := ⟨_, rfl⟩
  have hx : ∀ τ, 0 ≤ x τ := fun τ => by
    rw [hxdef]
    exact div_nonneg (Real.log_natCast_nonneg _) (by positivity)
  have h1 := ofReal_limsup_div_le x hx c hc
  have hav : arVolP Pr La 1 D = limsup x atTop := by rw [hxdef]; rfl
  rw [hav]
  refine h1.trans ?_
  obtain ⟨f, hfdef⟩ : ∃ f : ℕ → ENNReal, f = fun k : ℕ => (D.factorial : ENNReal) * GlobalTheory.CompHt.logCard (m (8 * k)) /
      ((d : ENNReal) * ((8 * k : ℕ) : ENNReal) ^ (D + 1)) := ⟨_, rfl⟩
  have hcv : GlobalTheory.CompHt.countVol D d 8 m = limsup f atTop := by rw [hfdef]; rfl
  rw [hcv]
  have h2 : ∀ τ, ENNReal.ofReal (x τ / c) ≤ f (r * τ) := by
    intro τ
    rcases Nat.eq_zero_or_pos τ with rfl | hτ
    · have : x 0 = 0 := by rw [hxdef]; simp
      simp [this]
    · have hτR : (0 : ℝ) < τ := by exact_mod_cast hτ
      obtain ⟨W, hW⟩ : ∃ W : ℕ, W = d * (8 * (r * τ)) ^ (D + 1) := ⟨_, rfl⟩
      have hWpos : 0 < W := by rw [hW]; positivity
      have hWR : (0 : ℝ) < W := by exact_mod_cast hWpos
      have hle : ENNReal.ofReal (Real.log (Nat.card {s : La τ // Pr τ (s : Ω)})) ≤
          GlobalTheory.CompHt.logCard (m (8 * (r * τ))) := by
        rw [← GlobalTheory.CompHt.logCard_coe]
        exact EReal.toENNReal_le_toENNReal (ENNReal.log_monotone (ENat.toENNReal_le.2 (hcount τ)))
      have hlog : smallSectionCount Pr La (1 * τ) = Real.log (Nat.card {s : La τ // Pr τ (s : Ω)}) := by
        rw [one_mul]; rfl
      have hxe : x τ / c = Real.log (Nat.card {s : La τ // Pr τ (s : Ω)}) * ((D.factorial : ℝ) / W) := by
        rw [hxdef, hcdef, hW]
        simp only [hlog]
        generalize Real.log (Nat.card {s : La τ // Pr τ (s : Ω)}) = large₂
        simp only [one_mul, Nat.factorial_succ]
        push_cast
        field_simp
        ring
      have hfe : f (r * τ) = GlobalTheory.CompHt.logCard (m (8 * (r * τ))) * ((D.factorial : ENNReal) / W) := by
        have : (d : ENNReal) * ((8 * (r * τ) : ℕ) : ENNReal) ^ (D + 1) = W := by
          rw [hW]; push_cast; rfl
        rw [hfdef]
        simp only [this]
        rw [mul_comm, mul_div_assoc]
      rw [hxe, hfe, ENNReal.ofReal_mul (Real.log_natCast_nonneg _),
        ENNReal.ofReal_div_of_pos hWR, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
      gcongr
  have hm : Tendsto (fun τ : ℕ => r * τ) atTop atTop := tendsto_id.const_mul_atTop' hr
  calc limsup (fun τ => ENNReal.ofReal (x τ / c)) atTop
      ≤ limsup (fun τ => f (r * τ)) atTop := limsup_le_limsup (Eventually.of_forall h2)
    _ = limsup f (map (fun τ : ℕ => r * τ) atTop) := by
        rw [limsup, limsup, map_map]; rfl
    _ ≤ limsup f atTop := limsup_le_limsup_of_le hm

theorem card_le_encard_of_mul {Ω : Type} [Field Ω] (L : AddSubgroup Ω) (Pr : Ω → Prop) (S : Set Ω) (θ : Ω)
    (hθ : θ ≠ 0) (h : ∀ σ ∈ L, Pr σ → σ * θ ∈ S) :
    ((Nat.card {s : L // Pr (s : Ω)} : ℕ) : ℕ∞) ≤ S.encard := by
  by_cases hS : S.Finite
  · haveI : Finite S := hS
    let f : {s : L // Pr (s : Ω)} → S := fun s => ⟨(s.1 : Ω) * θ, h _ s.1.2 s.2⟩
    have hf : Function.Injective f := fun a b hab => by
      have h1 : (a.1 : Ω) * θ = (b.1 : Ω) * θ := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext (mul_right_cancel₀ hθ h1))
    rw [← hS.cast_ncard_eq, ← Nat.card_coe_set_eq]
    exact_mod_cast Nat.card_le_card_of_injective f hf
  · rw [Set.Infinite.encard_eq hS]
    exact le_top

theorem le_countVol_of_nef {Ψ : Type} [Fintype Ψ] {N : ℕ} (h6 : BirationalPullbackPushforwardFormula) (RM : Top.RootModel Ψ N)
    (hD : 1 ≤ Top.dimFl Ψ N) (II : IntersectionSystem) (hII : IsIntersectionSystem II) (A : HermLine RM.ι)
    (hA : Small.IsNefH (mCoordIdeal RM.y) A) (κ : ℝ) (r : ℕ) (hr : 0 < r) (m : ℕ → ℕ∞)
    (hcount : ∀ τ, ((Nat.card {s : chartLatNm RM.y A.a τ //
      IsSmallH (mCoordIdeal RM.y) RM.y (Small.shiftH A κ) τ (s : RM.Ω)} : ℕ) : ℕ∞) ≤ m (8 * (r * τ))) :
    ENNReal.ofReal ((II RM.K RM.ι (mCoordIdeal RM.y) (Top.dimFl Ψ N + 1) (fun _ => A) +
        ((Top.dimFl Ψ N : ℝ) + 1) * κ * geomDeg (mCoordIdeal RM.y) A (Top.dimFl Ψ N)) /
        (((Top.dimFl Ψ N : ℝ) + 1) * RM.δ * ((8 * r : ℕ) : ℝ) ^ (Top.dimFl Ψ N + 1))) ≤
      GlobalTheory.CompHt.countVol (Top.dimFl Ψ N) RM.δ 8 m := by
  have hNs := (GlobalTheory.T.hermitian_line_shift_properties RM.K RM.ι (mCoordIdeal RM.y) A κ 1).2.1 hA
  obtain ⟨P1, hP1, hsp⟩ := hNs.semipos
  have h := h6 RM.K RM.ι RM.Ω RM.y (Top.dimFl Ψ N) (Small.shiftH A κ) P1 II hD hII RM.arith RM.birational hP1 hsp
    hNs.nef hNs.conj
  have hsm : IsSmoothHerm A := by
    obtain ⟨_, _, h'⟩ := hA.semipos
    exact h'.1
  rw [GlobalTheory.CompanionTheory.Ar.Small.selfInt_shiftH RM.K RM.ι (mCoordIdeal RM.y) (Top.dimFl Ψ N) A κ II hII RM.arith hsm] at h
  have hδ : (0 : ℝ) < RM.δ := by exact_mod_cast RM.δ_pos
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hden : (0 : ℝ) ≤ ((Top.dimFl Ψ N : ℝ) + 1) * RM.δ * ((8 * r : ℕ) : ℝ) ^ (Top.dimFl Ψ N + 1) := by
    push_cast; positivity
  refine (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right h hden)).trans ?_
  exact arithmeticVolume_div_le_countingVolume _ _ (Top.dimFl Ψ N) RM.δ r m RM.δ_pos hr hcount

theorem slope_alg (I G q δ D t' : ℝ) (hG : G ≠ 0) (hq : q ≠ 0) (hδ : δ ≠ 0) (hD : D + 1 ≠ 0) (e : ℕ) :
    (I / ((D + 1) * G) / q * (G / q ^ e) + t' * (G / q ^ e)) / δ =
      (I + (D + 1) * (q * t') * G) / ((D + 1) * δ * q ^ (e + 1)) := by
  field_simp
  ring

end GlobalTheory.CompanionTheory.Ar.Plug

namespace GlobalTheory.CompanionTheory.Ar.Plug

theorem volume_ge_slope : Top.Given → BirationalPullbackPushforwardFormula → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (B : ℕ) (b : T.Comp) (II : IntersectionSystem) (u : GlobalTheory.AllWt.Weight Dw) (g : ℝ), IsFullIntersectionSystem II → T.T1 II → Top.WeightHyp T.j (reW u) g → Top.bigB0 (reW u) g < B + 1 → ∀ t : ℝ, ENNReal.ofReal (T.vol b * Top.flagDeg (reW u) * (T.slope II B b (reW u) + t)) ≤ GlobalTheory.CompHt.countVol (Top.dimFl (CMType H) (Dw.p + Dw.q)) (T.M B b).δ 8 fun τ => (modelSmall (o.toTowerOrigin.Or B b) (τ • u) (Real.exp (τ * t))).encard := by
  intro hG h6 E _ _ _ H Dw l Xo c Y _ T o B b II u g hII hT1 hW hBig t
  have hanti : ∀ τ, StrictAnti (u τ) := fun τ a b' h => by
    have := hW.2.1 τ a b' h
    simpa [reW] using this
  obtain ⟨C, s, q, m, θ, hC, hs, hs0, hq, hm, hsm⟩ := GlobalTheory.T.strict_weight_growth_bound hG E H Dw l Xo c Y T o B b u hanti
  obtain ⟨hnef, hdeg, hsl, hV⟩ := GlobalTheory.T.weight_threshold_limit_coefficients (CMType H) (Dw.p + Dw.q) T II B (reW u) g b s q m hII hT1 hW hBig
    hs hs0 (fun n => (hq n).1) hm
  have hD : 1 ≤ Top.dimFl (CMType H) (Dw.p + Dw.q) := by
    obtain ⟨τ, hτ⟩ := GlobalTheory.HostModel.exists_embedding_rt_eq H
    haveI : Nonempty (CMType H) := ⟨⟨τ, hτ⟩⟩
    have h1 := T.j_pos
    have h2 := T.j_lt
    have h3 : 2 ≤ Dw.p + Dw.q := by omega
    refine Nat.mul_pos Fintype.card_pos (Nat.div_pos ?_ (by norm_num))
    calc 2 ≤ (Dw.p + Dw.q) * 1 := by omega
      _ ≤ (Dw.p + Dw.q) * (Dw.p + Dw.q - 1) := Nat.mul_le_mul_left _ (by omega)
  choose r hr using fun n => (hq n).2.1
  have hrpos : ∀ n, 0 < r n := fun n => by
    have := (hq n).1
    rw [hr n] at this
    omega
  have hδ : (0 : ℝ) < (T.M B b).δ := by exact_mod_cast (T.M B b).δ_pos
  have hapos := hdeg.eventually_const_lt (mul_pos hδ hV)
  have hst : Tendsto (fun n => t - C * s n) atTop (𝓝 t) := by
    simpa using tendsto_const_nhds.sub (hs0.const_mul C)
  have hlim := ((hsl.mul hdeg).add (hst.mul hdeg)).div_const ((T.M B b).δ : ℝ)
  have hval : (T.slope II B b (reW u) * ((T.M B b).δ * (T.vol b * Top.flagDeg (reW u))) +
      t * ((T.M B b).δ * (T.vol b * Top.flagDeg (reW u)))) / ((T.M B b).δ : ℝ) =
      T.vol b * Top.flagDeg (reW u) * (T.slope II B b (reW u) + t) := by
    field_simp
  rw [hval] at hlim
  refine le_of_tendsto (ENNReal.tendsto_ofReal hlim) ?_
  filter_upwards [hnef, hapos] with n hn ha
  have hqn : (0 : ℝ) < q n := by exact_mod_cast (hq n).1
  have hG0 : geomDeg (T.M B b).P (Top.combLine ((T.M B b).line (Top.scale (s n))) (m n))
      (Top.dimFl (CMType H) (Dw.p + Dw.q)) ≠ 0 := by
    intro h0
    rw [h0] at ha
    simp at ha
  have hkey := le_countVol_of_nef h6 (T.M B b) hD II hII.1 _ hn (q n * (t - C * s n)) (r n) (hrpos n)
    (fun τ => (modelSmall (o.toTowerOrigin.Or B b) (τ • u) (Real.exp (τ * t))).encard) (fun τ => by
      have he : 8 * (r n * τ) = τ * q n := by rw [hr n]; ring
      simp only [he]
      refine card_le_encard_of_mul _ _ _ (θ n ^ τ) (pow_ne_zero _ (hq n).2.2) fun σ h1 h2 => ?_
      have := hsm n τ (t - C * s n) σ h1 h2
      rwa [sub_add_cancel] at this)
  rw [← hr n] at hkey
  have halg := slope_alg (II (T.M B b).K (T.M B b).ι (T.M B b).P (Top.dimFl (CMType H) (Dw.p + Dw.q) + 1)
      (fun _ => Top.combLine ((T.M B b).line (Top.scale (s n))) (m n)))
    (geomDeg (T.M B b).P (Top.combLine ((T.M B b).line (Top.scale (s n))) (m n))
      (Top.dimFl (CMType H) (Dw.p + Dw.q))) (q n) ((T.M B b).δ : ℝ) (Top.dimFl (CMType H) (Dw.p + Dw.q) : ℝ)
    (t - C * s n) hG0 hqn.ne' hδ.ne' (by positivity) (Top.dimFl (CMType H) (Dw.p + Dw.q))
  simp only [Small.normHt]
  rw [halg]
  exact hkey

end GlobalTheory.CompanionTheory.Ar.Plug
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullIntersectionWeightBoundStatement
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.full_intersection_weight_bound : GlobalTheory.CompanionTheory.Ar.Top.Given → BirationalPullbackPushforwardFormula → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (B : ℕ) (b : T.Comp) (II : IntersectionSystem) (u : GlobalTheory.AllWt.Weight Dw) (g : ℝ), IsFullIntersectionSystem II → T.T1 II → Top.WeightHyp T.j (reW u) g → Top.bigB0 (reW u) g < B + 1 → ∀ t : ℝ, ENNReal.ofReal (T.vol b * Top.flagDeg (reW u) * (T.slope II B b (reW u) + t)) ≤ GlobalTheory.CompHt.countVol (Top.dimFl (CMType H) (Dw.p + Dw.q)) (T.M B b).δ 8 fun τ => (modelSmall (o.toTowerOrigin.Or B b) (τ • u) (Real.exp (τ * t))).encard := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Plug.volume_ge_slope | exact GlobalTheory.CompanionTheory.Ar.Plug.volume_ge_slope | (intros; apply GlobalTheory.CompanionTheory.Ar.Plug.volume_ge_slope <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CountVolumePowerComparison
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CountVolumePowerComparison
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Plug

theorem logCard_pow_le (x : ℕ∞) {d : ℕ} (hd : 0 < d) :
    GlobalTheory.CompHt.logCard (x ^ d) ≤ (d : ℝ≥0∞) * GlobalTheory.CompHt.logCard x := by
  induction x using ENat.recTopCoe with
  | top =>
    rw [GlobalTheory.CompHt.logCard_top, ENNReal.mul_top (Nat.cast_ne_zero.2 hd.ne')]
    exact le_top
  | coe a =>
    have h : ((a : ℕ∞) ^ d) = ((a ^ d : ℕ) : ℕ∞) := by push_cast; rfl
    rw [h, GlobalTheory.CompHt.logCard_coe, GlobalTheory.CompHt.logCard_coe, Nat.cast_pow, Real.log_pow,
      ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

theorem logCard_mono {x y : ℕ∞} (h : x ≤ y) : GlobalTheory.CompHt.logCard x ≤ GlobalTheory.CompHt.logCard y :=
  EReal.toENNReal_le_toENNReal (ENNReal.log_monotone (ENat.toENNReal_le.2 h))

theorem natCast_shift_pow (D j k : ℕ) (hk : 0 < k) :
    ((8 * (k + j) : ℕ) : ℝ≥0∞) ^ (D + 1) =
      ENNReal.ofReal ((1 + (j : ℝ) / k) ^ (D + 1)) * ((8 * k : ℕ) : ℝ≥0∞) ^ (D + 1) := by
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hj : (0 : ℝ) ≤ 1 + (j : ℝ) / k := by positivity
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (Nat.cast_nonneg _),
    ← ENNReal.ofReal_pow (Nat.cast_nonneg _), ← ENNReal.ofReal_mul (by positivity), ← mul_pow]
  congr 2
  push_cast
  field_simp

theorem tendsto_shift_ratio (D j : ℕ) :
    Tendsto (fun k : ℕ => ENNReal.ofReal ((1 + (j : ℝ) / k) ^ (D + 1))) atTop (𝓝 1) := by
  have h : Tendsto (fun k : ℕ => (j : ℝ) / k) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat _
  have h2 : Tendsto (fun k : ℕ => (1 + (j : ℝ) / k) ^ (D + 1)) atTop (𝓝 ((1 + 0) ^ (D + 1))) :=
    (tendsto_const_nhds.add h).pow _
  have h3 := ENNReal.tendsto_ofReal h2
  simpa using h3

theorem term_le_shift (D n d j k : ℕ) (hn : 0 < n) (hd : 0 < d) (hk : 0 < k) {x y : ℕ∞} (h : x ≤ y ^ d) :
    (D.factorial : ℝ≥0∞) * GlobalTheory.CompHt.logCard x / (((n * d : ℕ) : ℝ≥0∞) * ((8 * k : ℕ) : ℝ≥0∞) ^ (D + 1)) ≤
      (D.factorial : ℝ≥0∞) * GlobalTheory.CompHt.logCard y / ((n : ℝ≥0∞) * ((8 * (k + j) : ℕ) : ℝ≥0∞) ^ (D + 1)) *
        ENNReal.ofReal ((1 + (j : ℝ) / k) ^ (D + 1)) := by
  set A : ℝ≥0∞ := ((8 * k : ℕ) : ℝ≥0∞) ^ (D + 1) with hA
  set A' : ℝ≥0∞ := ((8 * (k + j) : ℕ) : ℝ≥0∞) ^ (D + 1) with hA'
  set c : ℝ≥0∞ := ENNReal.ofReal ((1 + (j : ℝ) / k) ^ (D + 1)) with hc
  have hcA : A' = c * A := natCast_shift_pow D j k hk
  have hA0 : A ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (by omega))
  have hAt : A ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
  have hA'0 : A' ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (by omega))
  have hA't : A' ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
  have hn0 : (n : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hnt : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hd0 : (d : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  have hdt : (d : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hL : GlobalTheory.CompHt.logCard x ≤ (d : ℝ≥0∞) * GlobalTheory.CompHt.logCard y :=
    (logCard_mono h).trans (logCard_pow_le y hd)
  refine ENNReal.div_le_of_le_mul ?_
  have key : (D.factorial : ℝ≥0∞) * GlobalTheory.CompHt.logCard y / ((n : ℝ≥0∞) * A') * c * (((n * d : ℕ) : ℝ≥0∞) * A) =
      (D.factorial : ℝ≥0∞) * ((d : ℝ≥0∞) * GlobalTheory.CompHt.logCard y) := by
    rw [div_eq_mul_inv, ENNReal.mul_inv (Or.inl hn0) (Or.inl hnt), Nat.cast_mul]
    calc _ = (D.factorial : ℝ≥0∞) * ((d : ℝ≥0∞) * GlobalTheory.CompHt.logCard y) * ((n : ℝ≥0∞)⁻¹ * n) * ((A')⁻¹ * (c * A)) := by
          ring
      _ = _ := by
          rw [← hcA, ENNReal.inv_mul_cancel hn0 hnt, ENNReal.inv_mul_cancel hA'0 hA't, mul_one, mul_one]
  rw [key]
  gcongr

theorem countVol_le_of_le_shift_pow : ∀ (D n d k₀ : ℕ) (m m' : ℕ → ℕ∞), 0 < n → 0 < d → 8 ∣ k₀ →
    (∀ᶠ τ : ℕ in atTop, m τ ≤ m' (τ + k₀) ^ d) →
    GlobalTheory.CompHt.countVol D (n * d) 8 m ≤ GlobalTheory.CompHt.countVol D n 8 m' := by
  rintro D n d _ m m' hn hd ⟨j, rfl⟩ h
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  set b : ℕ → ℝ≥0∞ := fun k => (D.factorial : ℝ≥0∞) * GlobalTheory.CompHt.logCard (m' (8 * k)) /
    ((n : ℝ≥0∞) * ((8 * k : ℕ) : ℝ≥0∞) ^ (D + 1)) with hb
  set c : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal ((1 + (j : ℝ) / k) ^ (D + 1)) with hc
  have hlim : limsup c atTop = 1 := (tendsto_shift_ratio D j).limsup_eq
  have hle : GlobalTheory.CompHt.countVol D (n * d) 8 m ≤ limsup ((fun k => b (k + j)) * c) atTop := by
    refine limsup_le_limsup ?_
    filter_upwards [eventually_ge_atTop (N + 1)] with k hk
    have hx : m (8 * k) ≤ m' (8 * (k + j)) ^ d := by
      have := hN (8 * k) (by omega)
      rwa [show 8 * k + 8 * j = 8 * (k + j) by ring] at this
    exact term_le_shift D n d j k hn hd (by omega) hx
  refine hle.trans ((ENNReal.limsup_mul_le' (Or.inr (by simp [hlim])) (Or.inr (by simp [hlim]))).trans ?_)
  rw [hlim, mul_one, Filter.limsup_nat_add b j]
  rfl

end GlobalTheory.CompanionTheory.Ar.Plug
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CountVolumePowerComparisonStatement
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.count_volume_power_comparison : ∀ (D n d k₀ : ℕ) (m m' : ℕ → ℕ∞), 0 < n → 0 < d → 8 ∣ k₀ → (∀ᶠ τ : ℕ in atTop, m τ ≤ m' (τ + k₀) ^ d) → GlobalTheory.CompHt.countVol D (n * d) 8 m ≤ GlobalTheory.CompHt.countVol D n 8 m' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Plug.countVol_le_of_le_shift_pow | exact GlobalTheory.CompanionTheory.Ar.Plug.countVol_le_of_le_shift_pow | (intros; apply GlobalTheory.CompanionTheory.Ar.Plug.countVol_le_of_le_shift_pow <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformAllNormHeightBound
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Plug.SlopeVol

open scoped ENNReal

theorem encard_le_pow_of_rel {α β : Type*} {A : Set α} {B : Set β} {d : ℕ} (hd : 0 < d)
    (P : α → Fin d → β → Prop) (hex : ∀ a ∈ A, ∀ i, ∃ b ∈ B, P a i b)
    (hinj : ∀ a ∈ A, ∀ a' ∈ A, (∀ i, ∃ b, P a i b ∧ P a' i b) → a = a') :
    A.encard ≤ B.encard ^ d := by
  classical
  rcases B.finite_or_infinite with hB | hB
  · choose F hF hP using hex
    haveI : Fintype B := hB.fintype
    let G : A → (Fin d → B) := fun a i => ⟨F a.1 a.2 i, hF a.1 a.2 i⟩
    have hG : Function.Injective G := fun a a' e => Subtype.ext (hinj a.1 a.2 a'.1 a'.2 fun i =>
      ⟨F a.1 a.2 i, hP a.1 a.2 i, by
        have : F a.1 a.2 i = F a'.1 a'.2 i := congrArg Subtype.val (congrFun e i)
        rw [this]; exact hP a'.1 a'.2 i⟩)
    have h1 : ENat.card A ≤ ENat.card (Fin d → B) := ENat.card_le_card_of_injective hG
    have h2 : ENat.card (Fin d → B) = ENat.card B ^ d := by
      simp [ENat.card_eq_coe_fintype_card, Fintype.card_fun]
    rw [h2] at h1
    exact h1
  · rw [hB.encard_eq, ENat.top_pow hd.ne']
    exact le_top

theorem ofReal_mul_le_of_forall_pos {A y : ℝ} {V : ℝ≥0∞} (H : ∀ ε : ℝ, 0 < ε → ENNReal.ofReal (A * (y - ε)) ≤ V) :
    ENNReal.ofReal (A * y) ≤ V := by
  have h1 : Tendsto (fun ε : ℝ => ENNReal.ofReal (A * (y - ε))) (𝓝[>] 0) (𝓝 (ENNReal.ofReal (A * y))) := by
    have h2 : Continuous fun ε : ℝ => ENNReal.ofReal (A * (y - ε)) :=
      ENNReal.continuous_ofReal.comp (continuous_const.mul (continuous_const.sub continuous_id))
    have h3 := (h2.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using h3
  exact le_of_tendsto h1 (eventually_mem_nhdsWithin.mono fun ε hε => H ε hε)

section Val

variable {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))

theorem vLa_mul {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : vLa la (a * b) = vLa la a + vLa la b := by
  simp only [vLa, map_mul]
  rw [WithZero.log_mul ((Valuation.ne_zero_iff _).2 ha) ((Valuation.ne_zero_iff _).2 hb)]
  ring

theorem vLa_one : vLa la (1 : K) = 0 := by simp [vLa]

theorem vLa_pow {a : K} (ha : a ≠ 0) (n : ℕ) : vLa la (a ^ n) = n * vLa la a := by
  induction n with
  | zero => simp [vLa_one]
  | succ n ih => rw [pow_succ, vLa_mul la (pow_ne_zero _ ha) ha, ih]; push_cast; ring

theorem vLa_natCast_nonneg {n : ℕ} (hn : n ≠ 0) : 0 ≤ vLa la (n : K) := by
  have e : (n : K) = algebraMap (𝓞 K) K (n : 𝓞 K) := (map_natCast _ n).symm
  have h0 : (n : K) ≠ 0 := Nat.cast_ne_zero.2 hn
  have h1 : la.valuation K (n : K) ≤ 1 := by rw [e]; exact la.valuation_le_one _
  have h2 : la.valuation K (n : K) ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  have h3 := (WithZero.log_le_log h2 one_ne_zero).2 h1
  rw [WithZero.log_one] at h3
  simp only [vLa]
  omega

theorem exists_prime_mem : ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ la.asIdeal := by
  haveI := la.isMaximal
  haveI : Finite (𝓞 K ⧸ la.asIdeal) := la.asIdeal.finiteQuotientOfFreeOfNeBot la.ne_bot
  letI := Ideal.Quotient.field la.asIdeal
  obtain ⟨p, hp⟩ := CharP.exists (𝓞 K ⧸ la.asIdeal)
  refine ⟨p, CharP.char_is_prime (𝓞 K ⧸ la.asIdeal) p, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact CharP.cast_eq_zero _ p

theorem vLa_prod_ge {S : Finset ℕ} (hS : ∀ p ∈ S, p ≠ 0) (e : ℕ → ℕ) {q : ℕ} (hq : q ∈ S) :
    (e q : ℤ) * vLa la (q : K) ≤ vLa la (((∏ p ∈ S, p ^ e p : ℕ)) : K) := by
  have hM : (∏ p ∈ S.erase q, p ^ e p) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun p hp => pow_ne_zero _ (hS p (Finset.mem_of_mem_erase hp))
  have hq0 : (q : K) ≠ 0 := Nat.cast_ne_zero.2 (hS q hq)
  rw [← Finset.mul_prod_erase S _ hq, Nat.cast_mul, Nat.cast_pow,
    vLa_mul la (pow_ne_zero _ hq0) (Nat.cast_ne_zero.2 hM), vLa_pow la hq0]
  have := vLa_natCast_nonneg (K := K) la hM
  omega

end Val

section Num

variable (E : Type) [Field E] [NumberField E]

theorem exTwo_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ exTwo E p := by
  have h1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have h2 : 0 ≤ GlobalTheory.CovHt.htEx E p := by
    unfold GlobalTheory.CovHt.htEx
    have : 0 ≤ (p : ℝ) - 1 := by linarith
    positivity
  unfold exTwo
  split_ifs <;> linarith

end Num

end GlobalTheory.CompanionTheory.Ar.Plug.SlopeVol

namespace GlobalTheory.CompanionTheory.Ar.Plug.SlopeVol

open scoped ENNReal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}


variable (E) in
def clearN (S : Finset ℕ) (u : GlobalTheory.AllWt.Weight Dw) : ℕ := ∏ p ∈ S, p ^ ⌈2 * exTwo E p * GlobalTheory.CovHt.l1 u⌉₊

theorem clearN_ne_zero {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (u : GlobalTheory.AllWt.Weight Dw) : clearN E S u ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun p hp => pow_ne_zero _ (hS p hp).ne_zero

theorem weightAbsEntrySum_nonneg (u : GlobalTheory.AllWt.Weight Dw) : 0 ≤ GlobalTheory.CovHt.l1 u :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem weightAbsEntrySum_nsmul (n : ℕ) (u : GlobalTheory.AllWt.Weight Dw) : GlobalTheory.CovHt.l1 (n • u) = n * GlobalTheory.CovHt.l1 u := by
  unfold GlobalTheory.CovHt.l1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [abs_mul]

theorem clearN_le {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (u : GlobalTheory.AllWt.Weight Dw) :
    (clearN E S u : ℝ) ≤
      Real.exp (2 * GlobalTheory.CovHt.l1 u * (∑ p ∈ S, exTwo E p * Real.log p) + ∑ p ∈ S, Real.log p) := by
  have e : 2 * GlobalTheory.CovHt.l1 u * (∑ p ∈ S, exTwo E p * Real.log p) + ∑ p ∈ S, Real.log p =
      ∑ p ∈ S, (2 * exTwo E p * GlobalTheory.CovHt.l1 u + 1) * Real.log (p : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [e, Real.exp_sum, clearN, Nat.cast_prod]
  refine Finset.prod_le_prod₀ (fun p _ => by positivity) fun p hp => ?_
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (hS p hp).pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hS p hp).one_le
  have ha : 0 ≤ 2 * exTwo E p * GlobalTheory.CovHt.l1 u :=
    mul_nonneg (mul_nonneg zero_le_two (exTwo_nonneg E (hS p hp))) (weightAbsEntrySum_nonneg u)
  rw [Nat.cast_pow, ← Real.rpow_natCast, Real.rpow_def_of_pos hp0, Real.exp_le_exp, mul_comm]
  exact mul_le_mul_of_nonneg_right (Nat.ceil_lt_add_one ha).le (Real.log_nonneg hp1)

theorem strictAnti_nsmul {u : GlobalTheory.AllWt.Weight Dw} (h : ∀ τ, StrictAnti (u τ)) {n : ℕ} (hn : 0 < n) (τ) :
    StrictAnti ((n • u) τ) := fun a b hab => by
  have h1 := h τ hab
  have h2 : (0 : ℤ) < n := by exact_mod_cast hn
  simpa using mul_lt_mul_of_pos_left h1 h2

theorem clear_integral {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (hHT : HTLow Xo c) {Bd : ℝ} {S : Finset ℕ}
    (hS : GlobalTheory.CompHt.htPrimes l Bd = ↑S) (Z : Comp Xo c) (u : GlobalTheory.AllWt.Weight Dw) (f : Rul Xo c)
    (hf : f ∈ GlobalTheory.AllWt.cuspOn U Z (GlobalTheory.AllWt.wtOf Dw u 0))
    (hv : ∀ (p : ℕ) (la : HeightOneSpectrum (𝓞 c.F)), p.Prime → ((p : ℕ) : 𝓞 c.F) ∈ la.asIdeal →
      ∀ v ∈ (GlobalTheory.CompHt.recVals Xo c).1 la,
        ((-((vLa la (p : c.F) : ℝ) * (if p ∈ S then exTwo E p else 0) * GlobalTheory.CovHt.l1 u) : ℝ) : EReal) ≤ v f) :
    ∀ la, ∀ w ∈ (GlobalTheory.CompHt.mixVals Xo c Bd).1 la, 0 ≤ w (((clearN E S u : ℕ) : c.F) • f) := by
  intro la w hw
  have hSp : ∀ p ∈ S, p.Prime := fun p hp => by
    have : p ∈ GlobalTheory.CompHt.htPrimes l Bd := by rw [hS]; exact hp
    exact this.1
  obtain ⟨p, hp, hpl⟩ := exists_prime_mem la
  have hval := (GlobalTheory.CompHt.mixVals Xo c Bd).2 la w hw
  have hN0 := clearN_ne_zero (E := E) hSp u
  have hN : ((clearN E S u : ℕ) : c.F) ≠ 0 := Nat.cast_ne_zero.2 hN0
  rw [hval.smul _ _ hN]
  have hvN : 0 ≤ vLa la ((clearN E S u : ℕ) : c.F) := vLa_natCast_nonneg la hN0
  have hbot := hval.ne_bot f
  by_cases hpS : p ∈ S
  · have hpm : p ∈ GlobalTheory.CompHt.htPrimes l Bd := by rw [hS]; exact hpS
    rw [GlobalTheory.CompHt.mixVals_of_mem hpm hpl] at hw
    obtain ⟨v, hv', hle⟩ := hHT p la hp hpl w hw
    have h1 := hle u f ((GlobalTheory.AllWt.cuspOn_le U Z _).trans (GlobalTheory.AllWt.cuspW_le_secZ _) hf)
    have h2 := hv p la hp hpl v hv'
    rw [if_pos hpS] at h2
    have h3 := h2.trans h1
    have hvp : 0 ≤ vLa la (p : c.F) := vLa_natCast_nonneg la hp.ne_zero
    have h4 : (2 * ((vLa la (p : c.F) : ℝ) * exTwo E p * GlobalTheory.CovHt.l1 u)) ≤ (vLa la ((clearN E S u : ℕ) : c.F) : ℝ) := by
      have h5 := vLa_prod_ge (K := c.F) la (fun q hq => (hSp q hq).ne_zero)
        (fun q => ⌈2 * exTwo E q * GlobalTheory.CovHt.l1 u⌉₊) hpS
      have h6 : ((⌈2 * exTwo E p * GlobalTheory.CovHt.l1 u⌉₊ : ℕ) : ℝ) * (vLa la (p : c.F) : ℝ) ≤
          (vLa la ((clearN E S u : ℕ) : c.F) : ℝ) := by exact_mod_cast h5
      have h7 := Nat.le_ceil (2 * exTwo E p * GlobalTheory.CovHt.l1 u)
      have h8 : (0 : ℝ) ≤ (vLa la (p : c.F) : ℝ) := by exact_mod_cast hvp
      nlinarith [mul_le_mul_of_nonneg_right h7 h8]
    generalize w f = W at *
    induction W with
    | bot => exact absurd rfl hbot
    | top => rw [EReal.coe_add_top]; exact le_top
    | coe W =>
      rw [← EReal.coe_add, EReal.coe_le_coe_iff] at h3
      rw [← EReal.coe_add]
      have : (0 : ℝ) ≤ (vLa la ((clearN E S u : ℕ) : c.F) : ℝ) + W := by linarith
      exact_mod_cast this
  · have hpm : p ∉ GlobalTheory.CompHt.htPrimes l Bd := by rw [hS]; exact hpS
    rw [GlobalTheory.CompHt.mixVals_of_not_mem hp hpm hpl] at hw
    have h2 := hv p la hp hpl w hw
    rw [if_neg hpS] at h2
    have h3 : (0 : EReal) ≤ w f := by simpa using h2
    refine add_nonneg ?_ h3
    exact_mod_cast hvN

end GlobalTheory.CompanionTheory.Ar.Plug.SlopeVol

namespace GlobalTheory.CompanionTheory.Ar.Plug.SlopeVol

open scoped ENNReal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

section Tr

variable {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {RM : Top.RootModel (CMType H) (Dw.p + Dw.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))} {Fx : FixedData Y Sys}
  {Or : RootOrigin Y S RM Fx} {Fr : Small.GenFrame Or} {h : GenFrEx Xo c} {Z : Comp Xo c}

theorem trOf_sub (Rd : Reading Fr h Z) (u : GlobalTheory.AllWt.Weight Dw) (a b : RM.Ω) :
    trOf Rd u (a - b) = trOf Rd u a - trOf Rd u b := by
  letI := Rd.φ.toAlgebra
  simp only [trOf, sub_div, map_sub]

end Tr


set_option synthInstance.maxHeartbeats 400000 in
theorem modelSmall_encard_le [IsGalois ℚ E] (hGv : Top.Given) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
    (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c) (hL : CompLaws U h e) (hUn : Ref.UnifAll Xo c) {x : ℝ}
    (hx : ∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x)
    (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q))
    (o : Top.GoodOrigin Y T) (Bn : ℕ) (b : T.Comp) (Fr : Small.GenFrame (o.toTowerOrigin.Or Bn b)) (Z : Comp Xo c)
    (Rd : Reading Fr h Z) (hGeo : GeoRead Rd) (u : GlobalTheory.AllWt.Weight Dw) (hanti : ∀ τ, StrictAnti (u τ)) (hHT : HTLow Xo c) {Bd : ℝ}
    (hS : GlobalTheory.CompHt.htPrimes l Bd = ↑(o.toTowerOrigin.S Bn)) (hd : 0 < (o.toTowerOrigin.Or Bn b).Fl.deg)
    (k₀ : ℕ) (R₀ : ℝ) (hR₀ : 0 ≤ R₀) (f : Fin (o.toTowerOrigin.Or Bn b).Fl.deg → (T.M Bn b).Ω)
    (hfs : ∀ i, f i ∈ modelSmall (o.toTowerOrigin.Or Bn b) (k₀ • u) R₀)
    (hinj : ∀ (v : GlobalTheory.AllWt.Weight Dw) (s : (T.M Bn b).Ω), (∀ i, trOf Rd v (s * f i) = 0) → s = 0)
    (τ : ℕ) (hτ : 0 < τ) {R R' : ℝ} (hR : 0 ≤ R)
    (hnum : (clearN E (o.toTowerOrigin.S Bn) ((τ + k₀) • u) : ℝ) *
      (((o.toTowerOrigin.Or Bn b).Fl.deg : ℝ) * (R * R₀)) ≤ R') :
    (modelSmall (o.toTowerOrigin.Or Bn b) (τ • u) R).encard ≤
      (GlobalTheory.CompHt.smallOn U x (GlobalTheory.CompHt.mixVals Xo c Bd) Z ((τ + k₀) • GlobalTheory.AllWt.wtOf Dw u 0) R').encard ^
        (o.toTowerOrigin.Or Bn b).Fl.deg := by
  have hG : (τ + k₀) • GlobalTheory.AllWt.wtOf Dw u 0 = GlobalTheory.AllWt.wtOf Dw ((τ + k₀) • u) 0 := by
    rw [GlobalTheory.CompHt.nsmul_wtOf]; simp
  rw [hG]
  have hSp : ∀ p ∈ o.toTowerOrigin.S Bn, p.Prime := fun p hp => by
    have : p ∈ GlobalTheory.CompHt.htPrimes l Bd := by rw [hS]; exact hp
    exact this.1
  have hN0 := clearN_ne_zero (E := E) hSp ((τ + k₀) • u)
  have hN : ((clearN E (o.toTowerOrigin.S Bn) ((τ + k₀) • u) : ℕ) : c.F) ≠ 0 := Nat.cast_ne_zero.2 hN0
  refine encard_le_pow_of_rel hd (fun s i (b' : GlobalTheory.AllWt.cuspOn U Z (GlobalTheory.AllWt.wtOf Dw ((τ + k₀) • u) 0)) =>
    ∃ g : Rul Xo c, (b' : Rul Xo c) = ((clearN E (o.toTowerOrigin.S Bn) ((τ + k₀) • u) : ℕ) : c.F) • g ∧
      evC h Z g = trOf Rd ((τ + k₀) • u) (s * f i)) ?_ ?_
  · intro s hs i
    have hprod := GlobalTheory.T.model_small_sections_mul E H Dw l Xo c Y T o Bn b (τ • u) (k₀ • u) R R₀ hR hR₀ s hs (f i) (hfs i)
    rw [← add_nsmul] at hprod
    obtain ⟨g, hg, hev, hnorm, hval⟩ := GlobalTheory.T.uniform_norm_all_tower_bound hGv E H Dw l Xo c r U h e hL hUn x hx Y T o Bn b Fr Z Rd hGeo
      ((τ + k₀) • u) (R * R₀) (strictAnti_nsmul hanti (by omega)) (mul_nonneg hR hR₀) (s * f i) hprod
    refine ⟨⟨((clearN E (o.toTowerOrigin.S Bn) ((τ + k₀) • u) : ℕ) : c.F) • g, Submodule.smul_mem _ _ hg⟩,
      ⟨clear_integral U hHT hS Z _ g hg hval, fun σ hσ z hz => ?_⟩, g, rfl, hev⟩
    show GlobalTheory.AllWt.homN (U σ) x _ (((clearN E (o.toTowerOrigin.S Bn) ((τ + k₀) • u) : ℕ) : c.F) • g) z ≤ R'
    rw [GlobalTheory.FlatLine.homN_smul, map_natCast, Complex.norm_natCast]
    exact (mul_le_mul_of_nonneg_left (hnorm σ hσ z hz) (Nat.cast_nonneg _)).trans hnum
  · intro s _ s' _ Hs
    have h0 : s - s' = 0 := hinj ((τ + k₀) • u) (s - s') fun i => by
      obtain ⟨b', ⟨g, hb, he⟩, ⟨g', hb', he'⟩⟩ := Hs i
      have hgg : g = g' := by
        have h1 := congrArg (fun y => (((clearN E (o.toTowerOrigin.S Bn) ((τ + k₀) • u) : ℕ) : c.F))⁻¹ • y) (hb.symm.trans hb')
        simpa only [inv_smul_smul₀ hN] using h1
      rw [sub_mul, trOf_sub, ← he, ← he', hgg, sub_self]
    exact sub_eq_zero.1 h0

end GlobalTheory.CompanionTheory.Ar.Plug.SlopeVol

namespace GlobalTheory.CompanionTheory.Ar.Plug.SlopeVolM

open GlobalTheory.CompanionTheory.Ar.Plug.SlopeVol

theorem slope_sub_cost_le_compVolSlope : GlobalTheory.CompanionTheory.Ar.Pub.NefRR → Top.Given → BirationalPullbackPushforwardFormula → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → Ref.UnifAll Xo c → ∀ x : ℝ, (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (κ : Comp Xo c ≃ T.Comp) (II : IntersectionSystem), CompOf o.toTowerOrigin κ → IsFullIntersectionSystem II → T.Proportional → T.T1 II → ∀ (Z : Comp Xo c) (u : GlobalTheory.AllWt.Weight Dw) (g B : ℝ), (∀ τ, StrictAnti (u τ)) → Top.WeightHyp T.j (reW u) g → Top.bigB0 (reW u) g ≤ B → ((T.slope II ⌊B⌋₊ (κ Z) (reW u) - 2 * costTwo l B * GlobalTheory.CovHt.l1 u : ℝ) : EReal) ≤ GlobalTheory.CompHt.compVolSlope U x 8 (GlobalTheory.CompHt.mixVals Xo c B) Z u := by
  intro hNef hGv h6 E _ _ _ _ H Dw l Xo c r U h e hL hUn x hx Y _ T o κ II hCO hII hProp hT1 Z u g B hanti hW hB
  obtain ⟨-, hdeg, hpos⟩ := (GlobalTheory.T.uniform_norm_degree_bound hNef hGv E H Dw l Xo c r U h e hL x hx Y T o κ II hCO hII hProp hT1).1 Z u hanti
  have hBn : Top.bigB0 (reW u) g < (⌊B⌋₊ : ℝ) + 1 := lt_of_le_of_lt hB (Nat.lt_floor_add_one B)
  obtain ⟨Fr, Rd, hGeo⟩ := GlobalTheory.T.tower_origin_component_bound E H Dw l Xo c r U h e hL Y T o.toTowerOrigin κ hCO ⌊B⌋₊ Z
  obtain ⟨k₀, R₀, f, h8, hR₀, hfs, -, hinj⟩ := GlobalTheory.T.generic_frame_component_bound hGv E H Dw l Xo c h Y T o ⌊B⌋₊ (κ Z) Fr Z Rd II u g hII hT1 hW hBn
  have hHT : HTLow Xo c := GlobalTheory.T.low_height_of_given hGv E H Dw l Xo c
  have hdim : GlobalTheory.CompHt.dimFlag Dw = Top.dimFl (CMType H) (Dw.p + Dw.q) :=
    (GlobalTheory.T.tower_weight_of_zero E H Dw l Xo c (T.M ⌊B⌋₊ (κ Z)) u).2.2.2.2.2.1
  have hS : GlobalTheory.CompHt.htPrimes l B = ↑(o.toTowerOrigin.S ⌊B⌋₊) := by
    ext p
    simp only [GlobalTheory.CompHt.htPrimes, Set.mem_setOf_eq, Finset.mem_coe, o.toTowerOrigin.S_iff, Top.RootTower.InS,
      o.toTowerOrigin.bad_iff]
    refine and_congr_right fun hp => or_congr (Nat.le_floor_iff' hp.ne_zero).symm ?_
    have key : ((p : ℤ) ∣ 2 * NumberField.discr E * (l.M' : ℤ)) ↔ p ∣ 2 * (NumberField.discr E).natAbs * l.M' := by
      rw [Int.natCast_dvd]; simp [Int.natAbs_mul]
    exact ⟨fun hd => ⟨hp, key.2 hd⟩, fun hd => key.1 hd.2⟩
  have hδ := (o.toTowerOrigin.Or ⌊B⌋₊ (κ Z)).δ_eq
  have hδpos := (T.M ⌊B⌋₊ (κ Z)).δ_pos
  have hn : 0 < Module.finrank ℚ c.F := Module.finrank_pos
  have hd : 0 < (o.toTowerOrigin.Or ⌊B⌋₊ (κ Z)).Fl.deg := by
    rw [hδ] at hδpos; exact Nat.pos_of_mul_pos_left hδpos
  have hSp : ∀ p ∈ o.toTowerOrigin.S ⌊B⌋₊, p.Prime := fun p hp => by
    have : p ∈ GlobalTheory.CompHt.htPrimes l B := by rw [hS]; exact hp
    exact this.1
  have hcost : costTwo (E := E) l B = ∑ p ∈ o.toTowerOrigin.S ⌊B⌋₊, exTwo E p * Real.log p := by
    rw [costTwo, hS, finsum_mem_coe_finset]
  rw [GlobalTheory.CompHt.le_compVolSlope_iff U x 8 _ hpos]
  intro t
  have e0 : (T.slope II ⌊B⌋₊ (κ Z) (reW u) - 2 * costTwo (E := E) l B * GlobalTheory.CovHt.l1 u) + t =
      (T.slope II ⌊B⌋₊ (κ Z) (reW u) - 2 * costTwo (E := E) l B * GlobalTheory.CovHt.l1 u + t) := rfl
  refine ofReal_mul_le_of_forall_pos fun ε hε => ?_
  set t' : ℝ := t - 2 * costTwo (E := E) l B * GlobalTheory.CovHt.l1 u - ε with ht'
  have hcount := GlobalTheory.T.full_intersection_weight_bound hGv h6 E H Dw l Xo c Y T o ⌊B⌋₊ (κ Z) II u g hII hT1 hW hBn t'
  have hev : ∀ᶠ τ : ℕ in atTop, (modelSmall (o.toTowerOrigin.Or ⌊B⌋₊ (κ Z)) (τ • u) (Real.exp (τ * t'))).encard ≤
      (GlobalTheory.CompHt.smallOn U x (GlobalTheory.CompHt.mixVals Xo c B) Z ((τ + k₀) • GlobalTheory.AllWt.wtOf Dw u 0)
        (Real.exp (((τ + k₀ : ℕ) : ℝ) * t))).encard ^ (o.toTowerOrigin.Or ⌊B⌋₊ (κ Z)).Fl.deg := by
    set cc : ℝ := costTwo (E := E) l B with hcc
    set L : ℝ := GlobalTheory.CovHt.l1 u with hLdef
    set d : ℝ := ((o.toTowerOrigin.Or ⌊B⌋₊ (κ Z)).Fl.deg : ℝ) with hdd
    set C : ℝ := ∑ p ∈ o.toTowerOrigin.S ⌊B⌋₊, Real.log p with hC
    have hd0 : 0 < d := by rw [hdd]; exact_mod_cast hd
    have hlim : ∀ᶠ τ : ℕ in atTop,
        (2 * (k₀ : ℝ) * L * cc + C + Real.log (d * R₀) - k₀ * t) ≤ (τ : ℝ) * ε := by
      have := tendsto_natCast_atTop_atTop (R := ℝ)
      exact (this.atTop_mul_const hε).eventually_ge_atTop _
    filter_upwards [hlim, eventually_gt_atTop 0] with τ hτ1 hτ0
    refine modelSmall_encard_le hGv U h e hL hUn hx Y T o ⌊B⌋₊ (κ Z) Fr Z Rd hGeo u hanti hHT hS hd k₀ R₀ hR₀.le f hfs hinj τ hτ0
      (Real.exp_pos _).le ?_
    have h1 := clearN_le (E := E) hSp ((τ + k₀) • u)
    rw [weightAbsEntrySum_nsmul, ← hcost, ← hLdef, ← hC] at h1
    have hdR : 0 < d * R₀ := mul_pos hd0 hR₀
    have h2 : d * (Real.exp (τ * t') * R₀) = Real.exp (τ * t' + Real.log (d * R₀)) := by
      rw [Real.exp_add, Real.exp_log hdR]; ring
    rw [h2]
    refine (mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le).trans ?_
    rw [← Real.exp_add, Real.exp_le_exp, ht']
    push_cast
    nlinarith [hτ1]
  have hshift := GlobalTheory.T.count_volume_power_comparison (GlobalTheory.CompHt.dimFlag Dw) (Module.finrank ℚ c.F) (o.toTowerOrigin.Or ⌊B⌋₊ (κ Z)).Fl.deg k₀
    (fun τ => (modelSmall (o.toTowerOrigin.Or ⌊B⌋₊ (κ Z)) (τ • u) (Real.exp (τ * t'))).encard)
    (fun τ => (GlobalTheory.CompHt.smallOn U x (GlobalTheory.CompHt.mixVals Xo c B) Z (τ • GlobalTheory.AllWt.wtOf Dw u 0) (Real.exp (τ * t))).encard)
    hn hd h8 hev
  have hc2 : GlobalTheory.CompHt.countVol (Top.dimFl (CMType H) (Dw.p + Dw.q)) (T.M ⌊B⌋₊ (κ Z)).δ 8
      (fun τ => (modelSmall (o.toTowerOrigin.Or ⌊B⌋₊ (κ Z)) (τ • u) (Real.exp (τ * t'))).encard) =
      GlobalTheory.CompHt.countVol (GlobalTheory.CompHt.dimFlag Dw) (Module.finrank ℚ c.F * (o.toTowerOrigin.Or ⌊B⌋₊ (κ Z)).Fl.deg) 8
      (fun τ => (modelSmall (o.toTowerOrigin.Or ⌊B⌋₊ (κ Z)) (τ • u) (Real.exp (τ * t'))).encard) := by
    rw [hdim, hδ]
  have e1 : GlobalTheory.CompHt.topDeg U Z u * (T.slope II ⌊B⌋₊ (κ Z) (reW u) - 2 * costTwo (E := E) l B * GlobalTheory.CovHt.l1 u + t - ε) =
      T.vol (κ Z) * Top.flagDeg (reW u) * (T.slope II ⌊B⌋₊ (κ Z) (reW u) + t') := by
    rw [hdeg, ht']; ring
  rw [e1]
  exact hcount.trans (hc2.le.trans hshift)

end GlobalTheory.CompanionTheory.Ar.Plug.SlopeVolM

theorem _root_.GlobalTheory.CompanionTheory.Relay.uniform_all_norm_height_bound : GlobalTheory.CompanionTheory.Ar.Pub.NefRR → Top.Given → BirationalPullbackPushforwardFormula → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → Ref.UnifAll Xo c → ∀ x : ℝ, (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (κ : Comp Xo c ≃ T.Comp) (II : IntersectionSystem), CompOf o.toTowerOrigin κ → IsFullIntersectionSystem II → T.Proportional → T.T1 II → ∀ (Z : Comp Xo c) (u : GlobalTheory.AllWt.Weight Dw) (g B : ℝ), (∀ τ, StrictAnti (u τ)) → Top.WeightHyp T.j (reW u) g → Top.bigB0 (reW u) g ≤ B → ((T.slope II ⌊B⌋₊ (κ Z) (reW u) - 2 * costTwo l B * GlobalTheory.CovHt.l1 u : ℝ) : EReal) ≤ GlobalTheory.CompHt.compVolSlope U x 8 (GlobalTheory.CompHt.mixVals Xo c B) Z u :=
  GlobalTheory.CompanionTheory.Ar.Plug.SlopeVolM.slope_sub_cost_le_compVolSlope
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformAllNormHeightBoundStatement
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_all_norm_height_bound : GlobalTheory.CompanionTheory.Ar.Pub.NefRR → Top.Given → BirationalPullbackPushforwardFormula → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → Ref.UnifAll Xo c → ∀ x : ℝ, (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (κ : Comp Xo c ≃ T.Comp) (II : IntersectionSystem), CompOf o.toTowerOrigin κ → IsFullIntersectionSystem II → T.Proportional → T.T1 II → ∀ (Z : Comp Xo c) (u : GlobalTheory.AllWt.Weight Dw) (g B : ℝ), (∀ τ, StrictAnti (u τ)) → Top.WeightHyp T.j (reW u) g → Top.bigB0 (reW u) g ≤ B → ((T.slope II ⌊B⌋₊ (κ Z) (reW u) - 2 * costTwo l B * GlobalTheory.CovHt.l1 u : ℝ) : EReal) ≤ GlobalTheory.CompHt.compVolSlope U x 8 (GlobalTheory.CompHt.mixVals Xo c B) Z u := by
  first | exact @GlobalTheory.CompanionTheory.Relay.uniform_all_norm_height_bound | exact GlobalTheory.CompanionTheory.Relay.uniform_all_norm_height_bound | (intros; apply GlobalTheory.CompanionTheory.Relay.uniform_all_norm_height_bound <;> assumption)
end

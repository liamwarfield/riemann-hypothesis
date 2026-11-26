module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.ProjLineRankTwoPushforwardHypotheses
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.MemConePtsIffChartIdeal

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.ArithVarZero
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


open Classical in
def killBlocks (S : Set K) : MRing ι →ₐ[ℤ] MRing ι :=
  aeval fun p => if p.1 ∈ S then 0 else X p


open Classical in
theorem killBlocks_X (S : Set K) (p : Σ k, ι k) :
    killBlocks S (X p : MRing ι) = if p.1 ∈ S then 0 else X p := by
  rw [killBlocks, aeval_X]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem killBlocks_monomial_of_forall (S : Set K) (m : (Σ k, ι k) →₀ ℕ) (c : ℤ)
    (h : ∀ p ∈ m.support, p.1 ∉ S) : killBlocks S (monomial m c : MRing ι) = monomial m c := by
  rw [killBlocks, aeval_monomial, monomial_eq, algebraMap_eq]
  congr 1
  refine Finsupp.prod_congr fun p hp => ?_
  rw [if_neg (h p hp)]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem killBlocks_monomial_of_mem (S : Set K) (m : (Σ k, ι k) →₀ ℕ) (c : ℤ) (p : Σ k, ι k)
    (hp : p ∈ m.support) (hS : p.1 ∈ S) : killBlocks S (monomial m c : MRing ι) = 0 := by
  rw [killBlocks, aeval_monomial, Finsupp.prod]
  refine mul_eq_zero_of_right _ (Finset.prod_eq_zero hp ?_)
  rw [if_pos hS, zero_pow (Finsupp.mem_support_iff.mp hp)]

theorem killBlocks_of_isMultiHomog (S : Set K) {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) :
    killBlocks S f = f ∨ killBlocks S f = 0 := by
  by_cases ha : ∀ k ∈ S, a k = 0
  · left
    set_option synthInstance.maxHeartbeats 100000 in
      rw [f.as_sum, map_sum]
    refine Finset.sum_congr rfl fun m hm => killBlocks_monomial_of_forall S m _ ?_
    rintro ⟨k, i⟩ hp hkS
    have h1 := hf m hm k
    rw [ha k hkS] at h1
    have h2 : m ⟨k, i⟩ ≤ ∑ j, m ⟨k, j⟩ :=
      Finset.single_le_sum (f := fun j => m ⟨k, j⟩) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    exact Finsupp.mem_support_iff.mp hp (by omega)
  · right
    push Not at ha
    obtain ⟨k, hkS, hak⟩ := ha
    set_option synthInstance.maxHeartbeats 100000 in
      rw [f.as_sum, map_sum]
    refine Finset.sum_eq_zero fun m hm => ?_
    have h1 := hf m hm k
    obtain ⟨i, hi⟩ : ∃ i, m ⟨k, i⟩ ≠ 0 := by
      by_contra h0
      push Not at h0
      have : ∑ j, m ⟨k, j⟩ = 0 := Finset.sum_eq_zero fun j _ => h0 j
      omega
    exact killBlocks_monomial_of_mem S m _ ⟨k, i⟩ (Finsupp.mem_support_iff.mpr hi) hkS

theorem le_comap_killBlocks {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) (S : Set K) :
    P ≤ P.comap (killBlocks S) := by
  obtain ⟨T, hT, rfl⟩ := hP
  refine Ideal.span_le.mpr fun f hf => ?_
  obtain ⟨a, ha⟩ := hT f hf
  rw [SetLike.mem_coe, Ideal.mem_comap]
  rcases killBlocks_of_isMultiHomog S ha with h | h <;> rw [h]
  · exact Ideal.subset_span hf
  · exact Ideal.zero_mem _


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem killBlocks_comp {S S' : Set K} (h : S ⊆ S') :
    (killBlocks S').comp (killBlocks S) = (killBlocks S' : MRing ι →ₐ[ℤ] MRing ι) := by
  refine MvPolynomial.algHom_ext fun p => ?_
  simp only [AlgHom.comp_apply, killBlocks, aeval_X]
  by_cases hp : p.1 ∈ S
  · simp [hp, h hp]
  · simp [hp, killBlocks, aeval_X]

theorem comap_killBlocks_mono {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) {S S' : Set K}
    (h : S ⊆ S') : P.comap (killBlocks S) ≤ P.comap (killBlocks S') := by
  intro f hf
  rw [Ideal.mem_comap] at hf ⊢
  have e : killBlocks S' f = killBlocks S' (killBlocks S f) := by
    rw [← AlgHom.comp_apply, killBlocks_comp h]
  rw [e]
  exact le_comap_killBlocks hP S' hf

theorem arithVarZero : ReciprocityTheory.ChartRestriction.G.AI.I2.ArithVarZeroStatement := by
  intro K _ ι _ P hP
  obtain ⟨_, ⟨hPp, hPh, hPr⟩, hhor, hdim⟩ := hP
  have := hPp
  set m := Fintype.card K with hm
  let e : K ≃ Fin m := Fintype.equivFin K
  let S : ℕ → Set K := fun n => {k | (e k : ℕ) < n}
  let Q : ℕ → Ideal (MRing ι) := fun n => P.comap (killBlocks (S n))
  let Q2 : Ideal (MRing ι) :=
    RingHom.ker ((Int.castRingHom (ZMod 2)).comp (constantCoeff : MRing ι →+* ℤ))
  have hQp : ∀ n, (Q n).IsPrime := fun n => Ideal.IsPrime.comap _
  have hQ2p : Q2.IsPrime := RingHom.ker_isPrime _
  have hstep : ∀ n, n < m → Q n < Q (n + 1) := by
    intro n hn
    obtain ⟨i, hi⟩ := hPr (e.symm ⟨n, hn⟩)
    refine SetLike.lt_iff_le_and_exists.mpr
      ⟨comap_killBlocks_mono hPh fun k hk => Nat.lt_succ_of_lt hk, X ⟨e.symm ⟨n, hn⟩, i⟩, ?_, ?_⟩
    · show killBlocks _ _ ∈ P
      rw [killBlocks_X, if_pos (by simp [S])]
      exact P.zero_mem
    · intro h2
      change killBlocks _ _ ∈ P at h2
      rw [killBlocks_X, if_neg (by simp [S])] at h2
      exact hi h2
  have hall : ∀ f : MRing ι, killBlocks (S m) f = C (constantCoeff f) := by
    intro f
    have : killBlocks (S m) = aeval (0 : (Σ k, ι k) → MRing ι) := by
      refine MvPolynomial.algHom_ext fun p => ?_
      rw [killBlocks_X, if_pos (by simp [S]), aeval_X]
      rfl
    rw [this, aeval_zero, algebraMap_eq]
  have hQm : ∀ f, f ∈ Q m ↔ constantCoeff f = 0 := by
    intro f
    change killBlocks (S m) f ∈ P ↔ _
    rw [hall]
    change constantCoeff f ∈ P.comap (C : ℤ →+* MRing ι) ↔ _
    rw [hhor, Ideal.mem_bot]
  have hstep2 : Q m < Q2 := by
    refine SetLike.lt_iff_le_and_exists.mpr ⟨fun f hf => ?_, C 2, ?_, fun h2 => ?_⟩
    · rw [RingHom.mem_ker, RingHom.comp_apply, (hQm f).mp hf, map_zero]
    · rw [RingHom.mem_ker, RingHom.comp_apply, constantCoeff_C]
      rfl
    · have := (hQm _).mp h2
      rw [constantCoeff_C] at this
      norm_num at this
  let T : ℕ → Ideal (MRing ι) := fun n => if n ≤ m then Q n else Q2
  have hTp : ∀ n, (T n).IsPrime := by
    intro n
    dsimp only [T]
    split_ifs
    exacts [hQp n, hQ2p]
  have hPT : ∀ n, P ≤ T n := by
    intro n
    dsimp only [T]
    split_ifs
    · exact le_comap_killBlocks hPh _
    · exact (le_comap_killBlocks hPh _).trans hstep2.le
  have hTlt : ∀ n, n ≤ m → T n < T (n + 1) := by
    intro n hn
    dsimp only [T]
    rw [if_pos hn]
    rcases hn.lt_or_eq with h | h
    · rw [if_pos (Nat.succ_le_of_lt h)]
      exact hstep n h
    · rw [if_neg (by omega), h]
      exact hstep2
  let g : Fin (m + 2) → PrimeSpectrum.zeroLocus (R := MRing ι) (P : Set (MRing ι)) :=
    fun j => ⟨⟨T j, hTp j⟩, hPT j⟩
  have hg : StrictMono g := by
    refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
    exact hTlt i (Nat.lt_succ_iff.mp i.isLt)
  have hlen := Order.LTSeries.length_le_krullDim (LTSeries.mk (m + 1) g hg)
  rw [← ringKrullDim_quotient, hdim] at hlen
  have h3 : ((m + 1 : ℕ) : WithBot ℕ∞) ≤ ((0 + m : ℕ) : WithBot ℕ∞) := hlen
  have h4 : m + 1 ≤ 0 + m := by exact_mod_cast h3
  omega

end GroundTheory.Heights₂.Heights.Inter

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.AnalyticResolutionHypothesesProjectiveLine
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial MeasureTheory Topology
open scoped ContDiff
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiHomog IsMultiHomogIdeal IsRelevant IsMultiProjPrime
  divCycle intNum)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection IsSNC HoloMap mInt MIntegrable
  logNormSec)

abbrev HLine {K : Type} [Fintype K] (ι : K → Type) := ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι

section Objects

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

abbrev MCone (ι : K → Type) := (Σ k, ι k) → ℂ

def logH (L : HLine ι) : MCone ι → ℝ := fun z => Real.log (L.h z)


variable (ι) in
structure Res (P : Ideal (MRing ι ℂ)) (e : ℕ) where

  D : Ideal (MRing ι ℂ)
  homog : IsMultiHomogIdeal D
  not_le : ¬ D ≤ P

  R : ReciprocityTheory.AnForm.R.AlgRes ι P D e

namespace Res

variable {P : Ideal (MRing ι ℂ)} {e : ℕ} (R : Res ι P e)

end Res


def IsProjVarQ (P0 : Ideal (MRing ι ℚ)) (e : ℕ) : Prop :=
  IsMultiProjPrime P0 ∧ ringKrullDim (MRing ι ℚ ⧸ P0) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞)

end Objects

section Ring

variable {K : Type} {ι : K → Type}

end Ring

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFStep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def PFAt (I : AllFam) (r : ℕ) : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (d : ℕ)
    (G : GenFibre v P') (J : IFamily G.Φ (fibreIdx ι' κ))
    (L : Fin d → HermLine ι) (L' : Fin d → HermLine ι') (N : Fin r → HermLine ι'),
    IsBlockMap κ v → IsArithVar P' (d + r) → IsArithVar (imageZ v P') d → IsFieldIntersection J →
    (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) → (∀ j, IsSmoothHerm (N j)) →
    I K' ι' P' (d + r) (Fin.append L' N) =
      (J (fibreIdeal κ G) r (fun j => fibreDeg κ (N j).a) : ℝ) * I K ι (imageZ v P') d L

def PFStep.Statement : Prop :=
  ∀ (I : AllFam), I.IsFamily → ∀ r : ℕ, PFAt I r → PFAt I (r + 1)

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTerFurther
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityFunctionFieldNumber.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)),
    IsArithVar P 1 → ∃ hF : IsField (funField P), @NumberField (funField P) hF.toField

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StLocRingFrac
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def LocRingFrac.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι)),
    P.IsPrime → W.IsPrime → P ≤ W →
    ∀ y ∈ locRing P W, ∃ (u v : MRing ι) (a : K → ℕ),
      IsMultiHomog u a ∧ IsMultiHomog v a ∧ v ∉ W ∧ y * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P v) = algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u)

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.EqZeroOfEventuallyEval
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial Filter Topology ReciprocityTheory.ChartRestriction.G.Geo

theorem pointFormRank_holds.exists_surj_coords {σ : Type*} {n : ℕ} (ℓ : σ → (Fin n → ℂ) →ₗ[ℂ] ℂ)
    (hℓ : ∀ x, (∀ s, ℓ s x = 0) → x = 0) :
    ∀ m, m ≤ n → ∃ q : Fin m → σ, Function.Surjective (fun x : Fin n → ℂ => fun j => ℓ (q j) x) := by
  intro m
  induction m with
  | zero => intro _; exact ⟨Fin.elim0, fun t => ⟨0, funext fun j => j.elim0⟩⟩
  | succ m ih =>
    intro hm
    obtain ⟨q, hq⟩ := ih (by omega)
    let Φ : (Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ) := LinearMap.pi fun j => ℓ (q j)
    have hrank := LinearMap.finrank_range_add_finrank_ker Φ
    have hle : Module.finrank ℂ (LinearMap.range Φ) ≤ m := by
      simpa using Submodule.finrank_le (LinearMap.range Φ)
    have hpos : 0 < Module.finrank ℂ (LinearMap.ker Φ) := by
      rw [Module.finrank_fin_fun] at hrank; omega
    obtain ⟨⟨x, hxk⟩, hx0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
    have hx : x ≠ 0 := fun h => hx0 (Subtype.ext h)
    have hΦx : ∀ j, ℓ (q j) x = 0 := fun j => congr_fun (LinearMap.mem_ker.mp hxk) j
    obtain ⟨s, hs⟩ : ∃ s, ℓ s x ≠ 0 := by
      by_contra h
      push Not at h
      exact hx (hℓ x h)
    refine ⟨Fin.snoc q s, fun t => ?_⟩
    obtain ⟨x0, hx0'⟩ := hq (Fin.init t)
    refine ⟨x0 + ((t (Fin.last m) - ℓ s x0) / ℓ s x) • x, funext fun j => ?_⟩
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [Fin.snoc_last, map_add (f := _), map_smul, smul_eq_mul]
      rw [div_mul_cancel₀ _ hs]
      ring
    · simp only [Fin.snoc_castSucc, map_add (f := _), map_smul, hΦx, smul_eq_mul, mul_zero, add_zero]
      exact congr_fun hx0' j

theorem pointFormRank_holds.eq_zero_of_eventually_eval {d : ℕ} (f : MvPolynomial (Fin d) ℂ) (a : Fin d → ℂ)
    (h : ∀ᶠ z in 𝓝 a, eval z f = 0) : f = 0 := by
  have han : AnalyticOnNhd ℂ (fun z => eval z f) Set.univ := AnalyticOnNhd.eval_mvPolynomial f
  have h0 := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ a) h
  exact MvPolynomial.funext fun z => by simpa using h0 (Set.mem_univ z)

theorem pointFormRank_holds.proof (hA : RatioAlgDep.Statement) : pointFormRank_holds.Statement := by
  intro K _ ι _ Q d n F y hQ hdn hF hev
  classical
  have hy : F y ∈ mcPts Q := hev.self_of_nhds
  choose c hc using hy.1
  have hcomp : ∀ p, AnalyticAt ℂ (fun y' => F y' p) y := analyticAt_pi_iff.mp hF
  have hDy : ∀ p : Σ k, ι k, F y ⟨p.1, c p.1⟩ ≠ 0 := fun p => hc p.1
  set r : (Σ k, ι k) → (Fin n → ℂ) → ℂ := fun p y' => F y' p / F y' ⟨p.1, c p.1⟩ with hr_def
  have hr : ∀ p, AnalyticAt ℂ (r p) y := fun p => (hcomp p).div (hcomp _) (hDy p)
  have hnear : ∀ᶠ y' in 𝓝 y, ∀ k, F y' ⟨k, c k⟩ ≠ 0 :=
    Filter.eventually_all.mpr fun k => (hcomp ⟨k, c k⟩).continuousAt.eventually_ne (hc k)
  set F' := fderiv ℂ F y with hF'_def
  have hF' : HasFDerivAt F F' y := hF.differentiableAt.hasFDerivAt
  set ℓ : (Σ k, ι k) → (Fin n → ℂ) →L[ℂ] ℂ := fun p => fderiv ℂ (r p) y with hℓ_def
  have hℓ : ∀ p, HasFDerivAt (r p) (ℓ p) y := fun p => (hr p).differentiableAt.hasFDerivAt
  have hprod : ∀ p, HasFDerivAt (fun y' => r p y' * F y' ⟨p.1, c p.1⟩)
      (r p y • (ContinuousLinearMap.proj ⟨p.1, c p.1⟩).comp F' + F y ⟨p.1, c p.1⟩ • ℓ p) y :=
    fun p => (hℓ p).mul (hasFDerivAt_pi'.mp hF' _)
  have heq : ∀ p, (fun y' => F y' p) =ᶠ[𝓝 y] fun y' => r p y' * F y' ⟨p.1, c p.1⟩ :=
    fun p => hnear.mono fun y' hy' => (div_mul_cancel₀ _ (hy' p.1)).symm
  have hderiv : ∀ p, (ContinuousLinearMap.proj p).comp F' =
      r p y • (ContinuousLinearMap.proj ⟨p.1, c p.1⟩).comp F' + F y ⟨p.1, c p.1⟩ • ℓ p :=
    fun p => (hasFDerivAt_pi'.mp hF' p).unique ((hprod p).congr_of_eventuallyEq (heq p))
  by_contra hno
  push Not at hno
  have hinj : ∀ x, (∀ p, ℓ p x = 0) → x = 0 := by
    intro x hx
    by_contra hx0
    refine hno x hx0 (fun k => F' x ⟨k, c k⟩ / F y ⟨k, c k⟩) ?_
    funext p
    have h1 := congrArg (fun L => L x) (hderiv p)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, FunLike.coe_add, Pi.add_apply,
      FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, hx p, mul_zero, add_zero] at h1
    rw [h1, bsmul, hr_def]
    ring
  obtain ⟨q, hq⟩ := pointFormRank_holds.exists_surj_coords (fun p => (ℓ p).toLinearMap)
    (fun x hx => hinj x (by simpa using hx)) d hdn
  have hg : HasStrictFDerivAt (fun y' j => r (q j) y') (ContinuousLinearMap.pi fun j => ℓ (q j)) y :=
    hasStrictFDerivAt_pi.mpr fun j => (hr (q j)).hasStrictFDerivAt
  have hrange : (ContinuousLinearMap.pi fun j => ℓ (q j) : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ)).range = ⊤ := by
    refine LinearMap.range_eq_top.mpr fun t => ?_
    obtain ⟨x, hx⟩ := hq t
    exact ⟨x, hx⟩
  have hmap := hg.map_nhds_eq_of_surj hrange
  obtain ⟨f, hf0, hfz⟩ := hA K ι Q d c q hQ
  have hev' : ∀ᶠ y' in 𝓝 y, eval (fun j => r (q j) y') (map (Int.castRingHom ℂ) f) = 0 := by
    filter_upwards [hev, hnear] with y' hy' hy'c
    exact hfz (F y') hy'.2 hy'c
  have hz : ∀ᶠ z in 𝓝 ((fun y' j => r (q j) y') y), eval z (map (Int.castRingHom ℂ) f) = 0 := by
    rw [← hmap]
    exact Filter.eventually_map.mpr hev'
  have h0 := pointFormRank_holds.eq_zero_of_eventually_eval _ _ hz
  exact hf0 (MvPolynomial.map_injective _ (Int.castRingHom ℂ).injective_int (h0.trans (map_zero _).symm))

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PPtsAddFirst
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo

theorem PtsAddFirst.cxHessian_add {D : ℕ} {a b ψ : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ}
    (ha : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 a y') (hb : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 b y')
    (hψ : ψ =ᶠ[𝓝 y] fun y' => a y' + b y') :
    cxHessian ψ y = cxHessian a y + cxHessian b y := by
  have h1 : fderiv ℝ ψ =ᶠ[𝓝 y] fun y' => fderiv ℝ a y' + fderiv ℝ b y' := by
    filter_upwards [hψ.fderiv (𝕜 := ℝ), ha, hb] with y' h1 h2 h3
    rw [h1]
    exact ((h2.differentiableAt (by norm_num)).hasFDerivAt.add
      (h3.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  have da2 : DifferentiableAt ℝ (fderiv ℝ a) y :=
    (ha.self_of_nhds.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have db2 : DifferentiableAt ℝ (fderiv ℝ b) y :=
    (hb.self_of_nhds.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hH : fderiv ℝ (fderiv ℝ ψ) y = fderiv ℝ (fderiv ℝ a) y + fderiv ℝ (fderiv ℝ b) y := by
    rw [h1.fderiv_eq]
    exact (da2.hasFDerivAt.add db2.hasFDerivAt).fderiv
  ext i j
  simp only [cxHessian, hH, Matrix.add_apply, add_apply]
  push_cast
  ring

theorem PtsAddFirst.mixedDisc_cons_add {D : ℕ} (A B : Matrix (Fin (D + 1)) (Fin (D + 1)) ℂ)
    (C : Fin D → Matrix (Fin (D + 1)) (Fin (D + 1)) ℂ) :
    mixedDisc (Fin.cons (A + B) C : Fin (D + 1) → _) =
      mixedDisc (Fin.cons A C : Fin (D + 1) → _) + mixedDisc (Fin.cons B C : Fin (D + 1) → _) := by
  have h := ReciprocityTheory.AnForm.A.mdisc_update_add (Fin.cons A C : Fin (D + 1) → _) 0 A B
  simp only [Fin.update_cons_zero] at h
  exact h

theorem PtsAddFirst.maDensity_cons_add {D : ℕ} (f g h : (Fin (D + 1) → ℂ) → ℝ)
    (ψ : Fin D → (Fin (D + 1) → ℂ) → ℝ) (y : Fin (D + 1) → ℂ)
    (hH : cxHessian h y = cxHessian f y + cxHessian g y) :
    maDensity (Fin.cons h ψ) y = maDensity (Fin.cons f ψ) y + maDensity (Fin.cons g ψ) y := by
  have hc : ∀ u : (Fin (D + 1) → ℂ) → ℝ, (fun k => cxHessian ((Fin.cons u ψ : Fin (D + 1) → _) k) y) =
      Fin.cons (cxHessian u y) (fun k => cxHessian (ψ k) y) := by
    intro u
    funext k
    refine Fin.cases ?_ (fun i => ?_) k <;> simp
  simp only [maDensity, hc, hH, PtsAddFirst.mixedDisc_cons_add, Complex.add_re]
  ring

theorem PtsAddFirst.pot_cons {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}
    (M : HermLine ι) (L : Fin e → HermLine ι) :
    pot (Fin.cons M L : Fin (e + 1) → HermLine ι) = Fin.cons (fun z => Real.log (M.h z)) (pot L) := by
  funext j z
  refine Fin.cases ?_ (fun i => ?_) j <;> simp [pot]

theorem PtsAddFirst.sheetDensity_add {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {e : ℕ} (Q : Ideal (MRing ι)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1 + 1) → ℂ))
    (L : Fin e → HermLine ι) (M N : HermLine ι) (hM : IsSmoothHerm M) (hN : IsSmoothHerm N)
    (g : ((Σ k, ι k) → ℂ) → ℝ) (y : Fin (e + 1) → ℂ) (w : ((k : K) → ι k) → ℂ) :
    sheetDensity Q Ψ (Fin.cons (fun z => Real.log ((M.tensor N).h z)) (pot L)) g y w =
      sheetDensity Q Ψ (Fin.cons (fun z => Real.log (M.h z)) (pot L)) g y w +
        sheetDensity Q Ψ (Fin.cons (fun z => Real.log (N.h z)) (pot L)) g y w := by
  by_cases hγ : ∃ γ, IsSheet Q Ψ y w γ
  · simp only [sheetDensity, dif_pos hγ]
    set γ := hγ.choose
    have hs : IsSheet Q Ψ y w γ := hγ.choose_spec
    have han : ∀ᶠ y' in 𝓝 y, AnalyticAt ℂ γ y' := (sheet_analyticAt osgood hs).eventually_analyticAt
    have hmc : ∀ᶠ y' in 𝓝 y, γ y' ∈ mcPts Q := hs.2.mono fun _ h => h.2.1
    have hcd : ∀ {A : HermLine ι}, IsSmoothHerm A →
        ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 (fun y'' => Real.log (A.h (γ y''))) y' := fun hA =>
      (han.and hmc).mono fun y' h => pot_contDiffAt hA h.1 h.2.1
    have hsum : (fun y' => Real.log ((M.tensor N).h (γ y'))) =ᶠ[𝓝 y]
        fun y' => Real.log (M.h (γ y')) + Real.log (N.h (γ y')) := hmc.mono fun y' h =>
      Real.log_mul (M.pos _ h.1).ne' (N.pos _ h.1).ne'
    have hcons : ∀ u : ((Σ k, ι k) → ℂ) → ℝ,
        (fun j y' => (Fin.cons u (pot L) : Fin (e + 1) → _) j (γ y')) =
          Fin.cons (fun y' => u (γ y')) (fun j y' => pot L j (γ y')) := by
      intro u
      funext j y'
      refine Fin.cases ?_ (fun i => ?_) j <;> simp
    rw [hcons, hcons, hcons, PtsAddFirst.maDensity_cons_add _ _ _ _ _
      (PtsAddFirst.cxHessian_add (hcd hM) (hcd hN) hsum), mul_add]
  · simp only [sheetDensity, dif_neg hγ, add_zero]

theorem PtsAddFirst.proof (hInt : PtsIntegrableStatement) : PtsAddFirst.Statement := by
  intro K _ ι _ Q e L M N E t hQ hL hM hN hE ht
  have hL' : ∀ A : HermLine ι, IsSmoothHerm A → ∀ j, IsSmoothHerm ((Fin.cons A L : Fin (e + 1) → _) j) :=
    fun A hA j => Fin.cases hA (fun i => hL i) j
  have hMN : IsSmoothHerm (M.tensor N) := hM.mul hN
  by_cases hΨ : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1 + 1) → ℂ), IsGoodProj Q Ψ
  · simp only [ptsIntegral, dif_pos hΨ, ptsIntegralAt]
    have hI : ∀ A : HermLine ι, IsSmoothHerm A → Integrable (fun y => ∑ᶠ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre Q hΨ.choose y,
        sheetDensity Q hΨ.choose (Fin.cons (fun z => Real.log (A.h z)) (pot L)) (logNorm E t) y w) := by
      intro A hA
      have h := hInt K ι Q (e + 1) hΨ.choose (Fin.cons A L) E t hQ hΨ.choose_spec (hL' A hA) hE ht
      rwa [PtsAddFirst.pot_cons] at h
    rw [← integral_add (hI M hM) (hI N hN)]
    congr 1
    funext y
    rw [← finsum_mem_add_distrib (fibreFinite K ι Q (e + 1) hΨ.choose hQ hΨ.choose_spec y)]
    exact finsum_mem_congr rfl fun w _ => PtsAddFirst.sheetDensity_add Q _ L M N hM hN _ y w
  · simp only [ptsIntegral, dif_neg hΨ, add_zero]

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.LeviOfRealSmulRight
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open Matrix Filter Topology ReciprocityTheory.ChartRestriction.G.Geo

namespace pointFormEuler_holds

section Levi

variable {n : ℕ}

def leviOf (H : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ) (u v : Fin n → ℂ) : ℂ :=
  ((H u v + H (Complex.I • u) (Complex.I • v) : ℝ) +
    Complex.I * ((H u (Complex.I • v) - H (Complex.I • u) v : ℝ))) / 4

theorem leviOf_add_right (H : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ) (u v w : Fin n → ℂ) :
    leviOf H u (v + w) = leviOf H u v + leviOf H u w := by
  simp only [leviOf, smul_add, map_add (f := _)]
  push_cast
  ring

theorem leviOf_real_smul_right (H : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ) (u v : Fin n → ℂ) (r : ℝ) :
    leviOf H u (r • v) = r * leviOf H u v := by
  simp only [leviOf, smul_comm Complex.I r v, map_smul, smul_eq_mul]
  push_cast
  ring

theorem leviOf_I_smul_right (H : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ) (u v : Fin n → ℂ) :
    leviOf H u (Complex.I • v) = -Complex.I * leviOf H u v := by
  have h : Complex.I • Complex.I • v = -v := by rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  simp only [leviOf, h, map_neg]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem leviOf_sum_right (H : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ) (u : Fin n → ℂ) (v : Fin n → Fin n → ℂ) :
    leviOf H u (∑ j, v j) = ∑ j, leviOf H u (v j) := by
  classical
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty =>
    have h0 : leviOf H u 0 = 0 := by simp [leviOf]
    simpa using h0
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, leviOf_add_right, ih]

theorem cxHessian_mulVec_star (f : (Fin n → ℂ) → ℝ) (y x : Fin n → ℂ) (i : Fin n) :
    (cxHessian f y *ᵥ star x) i = leviOf (fderiv ℝ (fderiv ℝ f) y) (Pi.single i 1) x := by
  set H := fderiv ℝ (fderiv ℝ f) y
  have hx : x = ∑ j, ((x j).re • (Pi.single j 1 : Fin n → ℂ) +
      (x j).im • (Complex.I • (Pi.single j 1 : Fin n → ℂ))) := by
    funext p
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Pi.single_apply, Complex.real_smul, smul_eq_mul,
      mul_ite, mul_one, mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    conv_lhs => rw [← Complex.re_add_im (x p)]
  have hent : ∀ j, cxHessian f y i j = leviOf H (Pi.single i 1) (Pi.single j 1) := fun j => rfl
  conv_rhs => rw [hx]
  rw [leviOf_sum_right]
  simp only [mulVec, dotProduct, hent]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [leviOf_add_right, leviOf_real_smul_right, leviOf_real_smul_right, leviOf_I_smul_right]
  have hs : star (x j) = ((x j).re : ℂ) - (x j).im * Complex.I := by
    apply Complex.ext <;> simp
  simp only [Pi.star_apply, hs]
  ring

end Levi

section Ambient

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem logh_contDiffAt {A : HermLine ι} (hA : IsSmoothHerm A) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : ContDiffAt ℝ 2 (fun z' => Real.log (A.h z')) z :=
  ((hA.contDiffAt (isOpen_blockNonzero.mem_nhds hz)).of_le (WithTop.coe_le_coe.mpr le_top)).log
    (A.pos z hz).ne'

def bsmulCLM (d : K → ℂ) : ((Σ k, ι k) → ℂ) →L[ℂ] ((Σ k, ι k) → ℂ) :=
  ContinuousLinearMap.pi fun p => d p.1 • ContinuousLinearMap.proj p

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem bsmulCLM_apply (d : K → ℂ) (z : (Σ k, ι k) → ℂ) : bsmulCLM d z = bsmul d z := by
  funext p
  simp [bsmulCLM, bsmul]

theorem fderiv_logh_bsmul (A : HermLine ι) (hA : IsSmoothHerm A) (d : K → ℂ) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    fderiv ℝ (fun z' => Real.log (A.h z')) z (bsmul d z) =
      deriv (fun s : ℝ => Real.log (∏ k, ‖1 + (s : ℂ) * d k‖ ^ A.a k)) 0 := by
  set φ : ((Σ k, ι k) → ℂ) → ℝ := fun z' => Real.log (A.h z')
  have hφ : HasFDerivAt φ (fderiv ℝ φ z) z :=
    ((logh_contDiffAt hA hz).differentiableAt (by norm_num)).hasFDerivAt
  have hpath : HasDerivAt (fun s : ℝ => z + s • bsmul d z) (bsmul d z) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (bsmul d z)).const_add z
  have h1 : HasDerivAt (fun s : ℝ => φ (z + s • bsmul d z)) (fderiv ℝ φ z (bsmul d z)) 0 := by
    exact hφ.comp_hasDerivAt_of_eq (0 : ℝ) hpath (by simp)
  have hne : ∀ᶠ s : ℝ in 𝓝 0, ∀ k, 1 + (s : ℂ) * d k ≠ 0 :=
    eventually_all.mpr fun k => ContinuousAt.eventually_ne (by fun_prop) (by simp)
  have heq : (fun s : ℝ => φ (z + s • bsmul d z)) =ᶠ[𝓝 0]
      fun s : ℝ => Real.log (∏ k, ‖1 + (s : ℂ) * d k‖ ^ A.a k) + φ z := by
    filter_upwards [hne] with s hs
    have hp : z + s • bsmul d z = fun p => (1 + (s : ℂ) * d p.1) * z p := by
      funext p
      simp only [Pi.add_apply, Pi.smul_apply, bsmul, Complex.real_smul]
      ring
    have hpos : 0 < ∏ k, ‖1 + (s : ℂ) * d k‖ ^ A.a k :=
      Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.mpr (hs k)) _
    simp only [φ]
    rw [hp, A.smul (fun k => 1 + (s : ℂ) * d k) z hs, Real.log_mul hpos.ne' (A.pos z hz).ne']
  rw [(h1.congr_of_eventuallyEq heq.symm).deriv.symm, deriv_add_const]

theorem hess_logh_bsmul (A : HermLine ι) (hA : IsSmoothHerm A) (d : K → ℂ) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (w : (Σ k, ι k) → ℂ) :
    fderiv ℝ (fderiv ℝ (fun z' => Real.log (A.h z'))) z w (bsmul d z) =
      -fderiv ℝ (fun z' => Real.log (A.h z')) z (bsmul d w) := by
  set φ : ((Σ k, ι k) → ℂ) → ℝ := fun z' => Real.log (A.h z')
  set L : ((Σ k, ι k) → ℂ) →L[ℝ] ((Σ k, ι k) → ℂ) := (bsmulCLM d).restrictScalars ℝ
  have hL : ∀ v, L v = bsmul d v := fun v => bsmulCLM_apply d v
  have hconst : (fun z' => fderiv ℝ φ z' (L z')) =ᶠ[𝓝 z]
      fun _ => deriv (fun s : ℝ => Real.log (∏ k, ‖1 + (s : ℂ) * d k‖ ^ A.a k)) 0 := by
    filter_upwards [isOpen_blockNonzero.mem_nhds hz] with z' hz'
    rw [hL]
    exact fderiv_logh_bsmul A hA d hz'
  have hd1 : DifferentiableAt ℝ (fderiv ℝ φ) z :=
    ((logh_contDiffAt hA hz).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h0 : fderiv ℝ (fun z' => fderiv ℝ φ z' (L z')) z w = 0 := by
    rw [hconst.fderiv_eq]
    simp
  rw [fderiv_clm_apply hd1 L.differentiableAt, L.fderiv] at h0
  simp only [_root_.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, hL] at h0
  linarith

end Ambient

section Chain

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {n : ℕ}

theorem hess_comp_holo {φ : ((Σ k, ι k) → ℂ) → ℝ} {F : (Fin n → ℂ) → (Σ k, ι k) → ℂ} {y : Fin n → ℂ}
    (hφ : ContDiffAt ℝ 2 φ (F y)) (hF : AnalyticAt ℂ F y) (u v : Fin n → ℂ) :
    fderiv ℝ (fderiv ℝ (fun y' => φ (F y'))) y u v =
      fderiv ℝ (fderiv ℝ φ) (F y) (fderiv ℂ F y u) (fderiv ℂ F y v) +
        fderiv ℝ φ (F y) (fderiv ℂ (fun y' => fderiv ℂ F y' v) y u) := by
  have hψ : ContDiffAt ℝ 2 (fun y' => φ (F y')) y := hφ.comp y (hF.contDiffAt.restrict_scalars ℝ)
  have hψ1 : DifferentiableAt ℝ (fderiv ℝ (fun y' => φ (F y'))) y :=
    (hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hφev : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 φ (F y') :=
    hF.continuousAt.tendsto.eventually (hφ.eventually (by simp))
  have hFev := hF.eventually_analyticAt
  have hcw : fderiv ℝ (fderiv ℝ (fun y' => φ (F y'))) y u v =
      fderiv ℝ (fun y' => fderiv ℝ (fun y'' => φ (F y'')) y' v) y u := by
    rw [fderiv_clm_apply hψ1 (differentiableAt_const v)]
    simp
  have hev : (fun y' => fderiv ℝ (fun y'' => φ (F y'')) y' v) =ᶠ[𝓝 y]
      fun y' => fderiv ℝ φ (F y') (fderiv ℂ F y' v) := by
    filter_upwards [hφev, hFev] with y' h1 h2
    rw [fderiv_fun_comp y' (h1.differentiableAt (by norm_num)) (h2.differentiableAt.restrictScalars ℝ),
      h2.differentiableAt.fderiv_restrictScalars ℝ]
    rfl
  have hd1 : DifferentiableAt ℝ (fderiv ℝ φ) (F y) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hc : DifferentiableAt ℝ (fun y' => fderiv ℝ φ (F y')) y :=
    hd1.comp y (hF.differentiableAt.restrictScalars ℝ)
  have hG : DifferentiableAt ℂ (fun y' => fderiv ℂ F y' v) y :=
    hF.fderiv.differentiableAt.clm_apply (differentiableAt_const v)
  rw [hcw, hev.fderiv_eq, fderiv_clm_apply hc (hG.restrictScalars ℝ),
    fderiv_fun_comp y hd1 (hF.differentiableAt.restrictScalars ℝ),
    hG.fderiv_restrictScalars ℝ, hF.differentiableAt.fderiv_restrictScalars ℝ]
  simp only [_root_.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.coe_restrictScalars']
  ring

end Chain

theorem proof : pointFormEuler_holds.Statement := by
  intro K _ ι _ A n F y x c hA hF hblk hx
  have hφ : ContDiffAt ℝ 2 (fun z' => Real.log (A.h z')) (F y) := logh_contDiffAt hA hblk
  have hchain : ∀ u v, fderiv ℝ (fderiv ℝ (fun y' => Real.log (A.h (F y')))) y u v =
      fderiv ℝ (fderiv ℝ (fun z' => Real.log (A.h z'))) (F y) (fderiv ℂ F y u) (fderiv ℂ F y v) +
        fderiv ℝ (fun z' => Real.log (A.h z')) (F y) (fderiv ℂ (fun y' => fderiv ℂ F y' v) y u) :=
    fun u v => hess_comp_holo (φ := fun z' => Real.log (A.h z')) hφ hF u v
  have hG : DifferentiableAt ℂ (fun y' => fderiv ℂ F y' x) y :=
    hF.fderiv.differentiableAt.clm_apply (differentiableAt_const x)
  have hGI : fderiv ℂ (fun y' => fderiv ℂ F y' (Complex.I • x)) y =
      Complex.I • fderiv ℂ (fun y' => fderiv ℂ F y' x) y := by
    have : (fun y' => fderiv ℂ F y' (Complex.I • x)) = fun y' => Complex.I • fderiv ℂ F y' x := by
      funext y'
      exact map_smul _ _ _
    rw [this, fderiv_fun_const_smul hG]
  have hJIx : fderiv ℂ F y (Complex.I • x) = bsmul (fun k => Complex.I * c k) (F y) := by
    rw [map_smul, hx]
    funext p
    simp only [Pi.smul_apply, bsmul, smul_eq_mul]
    ring
  have hbI : ∀ (d : K → ℂ) (w : (Σ k, ι k) → ℂ),
      bsmul d (Complex.I • w) = bsmul (fun k => Complex.I * d k) w := by
    intro d w
    funext p
    simp only [Pi.smul_apply, bsmul, smul_eq_mul]
    ring
  have hbII : ∀ (d : K → ℂ) (w : (Σ k, ι k) → ℂ),
      bsmul (fun k => Complex.I * d k) (Complex.I • w) = -bsmul d w := by
    intro d w
    funext p
    simp only [Pi.smul_apply, Pi.neg_apply, bsmul, smul_eq_mul]
    linear_combination (d p.1 * w p) * Complex.I_sq
  have hII : ∀ w : (Σ k, ι k) → ℂ, Complex.I • Complex.I • w = -w := fun w => by
    rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  have heul := fun d w => hess_logh_bsmul A hA d hblk w
  funext i
  rw [cxHessian_mulVec_star, Pi.zero_apply]
  unfold leviOf
  rw [hchain, hchain, hchain, hchain, hJIx, hx, hGI]
  simp only [map_smul, _root_.smul_apply]
  rw [heul, heul, heul, heul, hbII, hbI, hII]
  simp only [map_neg]
  push_cast
  ring

end pointFormEuler_holds

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StLocRingNoeth
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def LocRingNoeth.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι)),
    P.IsPrime → W.IsPrime → P ≤ W → IsRelevant W → IsNoetherianRing (locRing P W)

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StLocRingPow
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def LocRingPow.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (s t : MRing ι) (a : K → ℕ) (W : Ideal (MRing ι)) (x : FractionRing (MRing ι ⧸ P))
    (u v : MRing ι) (b : K → ℕ) (y : FractionRing (MRing ι ⧸ P)),
    P.IsPrime → IsMultiHomogIdeal P → IsMultiHomog s a → s ∉ P → W ∈ divSupp P s →
    IsMultiHomog t a → t ∉ W → x * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P t) = algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P s) →
    IsMultiHomog u b → IsMultiHomog v b → u ∈ W → v ∉ W → y * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P v) = algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u) →
    ∃ n : ℕ, ∃ z ∈ locRing P W, y ^ n = x * z

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTerBis
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def regularityDehomogenization_holds.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (s t : MRing ι) (a : K → ℕ) (W : Ideal (MRing ι)) (y : FractionRing (MRing ι ⧸ P)),
    IsMultiProjPrime P → IsMultiHomog s a → s ∉ P → W ∈ divSupp P s → IsMultiHomog t a → t ∉ W →
    y * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P t) =
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P s) →
    y ∈ locRing P W ∧
      multAt (P ⊔ Ideal.span {s}) W = (Module.length (locRing P W) (locRing P W ⧸ locIdeal P W y)).toNat

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTerMore
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityDivisorSupportClosed.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (s : MRing ι) (a : K → ℕ)
    (W : Ideal (MRing ι)),
    IsArithVar P 1 → IsMultiHomog s a → s ∉ P → (W ∈ divSupp P s ↔ IsClosedPt W ∧ P ≤ W ∧ s ∈ W)

end

end GroundTheory.Heights₂.Heights.Inter
end

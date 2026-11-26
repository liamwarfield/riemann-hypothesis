module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PQuotPartGraded
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenSESStep
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AssemblyBase
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionPointValue
public import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiProjPrimeImageZ
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRealFormsOnPoints

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenNear
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def IsClosedMultiPt {S : Type*} [CommRing S] {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (P : Ideal (MRingOver S ι)) : Prop :=
  IsMultiProjPrime P ∧ ∀ Q : Ideal (MRingOver S ι), IsMultiProjPrime Q → P ≤ Q → Q = P

def GenNear (S : Type*) [CommRing S] {K : Type*} [Fintype K] [LinearOrder K] (ι : K → Type*)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] {M : Type*} [AddCommGroup M] [Module (MRingOver S ι) M]
    [Module S M] [IsScalarTower S (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M) (d : K → ℤ)
    (f : MRingOver S ι) (δ : K → ℕ) : Prop :=
  ∀ I : KH.Cell K ι 0, ∀ x ∈ KH.locPart ι 𝓜 (KH.cellMon S I.1) d,
    ∃ (n : ℕ) (t : MRingOver S ι) (a : K → ℕ) (r : ℕ) (p : Fin r → MRingOver S ι) (z : Fin r → KH.CechC S ι M 0),
      t ∈ KH.cellMon S I.1 ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog t a ∧ (∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (p j) (a + n • δ)) ∧
      (∀ j, z j ∈ KH.cechZc ι 𝓜 d 0) ∧ (f ^ n * t) • x = ∑ j, p j • z j I

def locIdealPart {S : Type*} [CommRing S] {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    {M : Type*} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
    (𝓜 : (K → ℤ) → Submodule S M) (T : Submonoid (MRingOver S ι)) (P : Ideal (MRingOver S ι)) (d : K → ℤ) :
    Submodule S (LocalizedModule T M) :=
  Submodule.span S {w | ∃ (p : MRingOver S ι) (a : K → ℕ) (y : LocalizedModule T M), p ∈ P ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog p a ∧
    y ∈ KH.locPart ι 𝓜 T (d - fun k => (a k : ℤ)) ∧ w = p • y}

section Point

end Point

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftBirationalAmple
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace LiftBirationalAmple

set_option linter.unusedSectionVars false

section Sections

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  (y : (Σ k, ι k) → Ω)

theorem mem_chartLat_one {a : K → ℤ} {s : Ω} :
    s ∈ chartLat y a 1 ↔
      ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → s * ∏ k, y ⟨k, c k⟩ ^ (-a k) ∈ chartRingZ y c := by
  show (∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
      s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k)) ∈ chartRingZ y c) ↔ _
  simp only [Nat.cast_one, one_mul]

variable {y}

theorem chartLat_mul {a b : K → ℤ} {s u : Ω} (hs : s ∈ chartLat y a 1) (hu : u ∈ chartLat y b 1) :
    s * u ∈ chartLat y (a + b) 1 := by
  rw [mem_chartLat_one] at hs hu ⊢
  intro c hc
  have e : s * u * ∏ k, y ⟨k, c k⟩ ^ (-(a + b) k) =
      (s * ∏ k, y ⟨k, c k⟩ ^ (-a k)) * (u * ∏ k, y ⟨k, c k⟩ ^ (-b k)) := by
    rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_add₀ (hc k)]
    congr 1
    simp only [Pi.add_apply]
    ring
  rw [e]
  exact mul_mem (hs c hc) (hu c hc)

theorem chartLat_one_mem : (1 : Ω) ∈ chartLat y 0 1 := by
  rw [mem_chartLat_one]
  intro c _
  simp

theorem chartLat_pow {a : K → ℤ} {s : Ω} (hs : s ∈ chartLat y a 1) (n : ℕ) : s ^ n ∈ chartLat y (n • a) 1 := by
  induction n with
  | zero => simpa using (chartLat_one_mem (y := y))
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact chartLat_mul ih hs

theorem chartLat_prod {β : Type} (t : Finset β) (f : β → Ω) (a : β → K → ℤ)
    (h : ∀ b ∈ t, f b ∈ chartLat y (a b) 1) : ∏ b ∈ t, f b ∈ chartLat y (∑ b ∈ t, a b) 1 := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using (chartLat_one_mem (y := y))
  | insert b t hb ih =>
    rw [Finset.prod_insert hb, Finset.sum_insert hb]
    exact chartLat_mul (h b (Finset.mem_insert_self b t)) (ih fun b' hb' => h b' (Finset.mem_insert_of_mem hb'))

theorem chartLat_var [DecidableEq K] (p : Σ k, ι k) : y p ∈ chartLat y (Pi.single p.1 1) 1 := by
  rw [mem_chartLat_one]
  intro c hc
  have e : ∏ k, y ⟨k, c k⟩ ^ (-(Pi.single p.1 (1 : ℤ) : K → ℤ) k) = (y ⟨p.1, c p.1⟩)⁻¹ := by
    rw [Finset.prod_eq_single p.1 (fun k _ hk => by simp [hk]) (by simp)]
    simp
  rw [e, ← div_eq_mul_inv]
  exact Algebra.subset_adjoin ⟨p, rfl⟩


open Classical in
theorem chartLat_form {g : MRing ι} {d : K → ℕ} (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g d) :
    aeval y g ∈ chartLat y (fun k => (d k : ℤ)) 1 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [g.as_sum, map_sum]
  refine AddSubgroup.sum_mem _ fun m hm => ?_
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), algebraMap_int_eq, eq_intCast,
    ← zsmul_eq_mul]
  refine AddSubgroup.zsmul_mem _ ?_ _
  have hdeg : (fun k => (d k : ℤ)) = ∑ p : Σ k, ι k, (m p) • (Pi.single p.1 1 : K → ℤ) := by
    funext k
    rw [Finset.sum_apply, Fintype.sum_sigma, Finset.sum_eq_single k]
    · simp only [Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul, mul_one]
      rw [← hg m hm k]
      push_cast
      rfl
    · intro k' _ hk'
      refine Finset.sum_eq_zero fun i _ => ?_
      simp [Ne.symm hk']
    · simp
  rw [hdeg]
  exact chartLat_prod _ _ _ fun p _ => chartLat_pow (chartLat_var p) _

end Sections

section Ratios

variable {Ω : Type} [Field Ω] {J : Type} [Fintype J] (z : (Σ _ : Unit, J) → Ω)

def IsRatio (w : Ω) : Prop :=
  ∃ (d : Unit → ℕ) (g h : MRing (fun _ : Unit => J)), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g d ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog h d ∧
    aeval z h ≠ 0 ∧ aeval z g = w * aeval z h

theorem homog_X_unit (j : J) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (X ⟨(), j⟩ : MRing (fun _ : Unit => J)) (fun _ => 1) := by
  have h := GenOnFibres.homog_X (R := ℤ) (ι := fun _ : Unit => J) () j
  intro m hm k
  rw [h m hm k]
  cases k
  simp

variable {z}

theorem IsRatio.intCast (r : ℤ) : IsRatio z (r : Ω) :=
  ⟨0, C r, 1, GenOnFibres.homog_C r, GenOnFibres.homog_one, by simp, by simp⟩

theorem IsRatio.add {w w' : Ω} (hw : IsRatio z w) (hw' : IsRatio z w') : IsRatio z (w + w') := by
  obtain ⟨d, g, h, hg, hh, h0, e⟩ := hw
  obtain ⟨d', g', h', hg', hh', h0', e'⟩ := hw'
  refine ⟨d + d', g * h' + h * g', h * h', GenOnFibres.homog_add (GenOnFibres.homog_mul hg hh')
    (GenOnFibres.homog_mul hh hg'), GenOnFibres.homog_mul hh hh', by simp [h0, h0'], ?_⟩
  simp only [map_add (f := _), map_mul, e, e']
  ring

theorem IsRatio.mul {w w' : Ω} (hw : IsRatio z w) (hw' : IsRatio z w') : IsRatio z (w * w') := by
  obtain ⟨d, g, h, hg, hh, h0, e⟩ := hw
  obtain ⟨d', g', h', hg', hh', h0', e'⟩ := hw'
  refine ⟨d + d', g * g', h * h', GenOnFibres.homog_mul hg hg', GenOnFibres.homog_mul hh hh',
    by simp [h0, h0'], ?_⟩
  simp only [map_mul, e, e']
  ring

theorem IsRatio.inv {w : Ω} (hw : IsRatio z w) : IsRatio z w⁻¹ := by
  by_cases hw0 : w = 0
  · rw [hw0, inv_zero]
    simpa using IsRatio.intCast (z := z) 0
  obtain ⟨d, g, h, hg, hh, h0, e⟩ := hw
  refine ⟨d, h, g, hh, hg, by rw [e]; exact mul_ne_zero hw0 h0, ?_⟩
  rw [e, ← mul_assoc, inv_mul_cancel₀ hw0, one_mul]

end Ratios

end LiftBirationalAmple


open LiftBirationalAmple in
theorem LiftBirationalAmple.proof (h : GeneratedNonzeroSection.Statement) : LiftBirationalAmple.Statement := by
  classical
  intro K _ _ ι _ _ Ω _ _ y D N c hvar hbir hc hample
  obtain ⟨q', hq', hgen, -⟩ := hample
  obtain ⟨s, hs, hs0⟩ := h K ι Ω y _ hgen

  have hrel : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hvar.2.1.2.2 k
    refine ⟨i, fun hy => hi ?_⟩
    rw [mCoordIdeal, RingHom.mem_ker]
    simp [mConeMap, aeval_X, hy]
  choose c0 hc0 using hrel
  refine ⟨q' * c, 1, Nat.mul_le_mul hq' hc, fun t ht => ?_⟩
  have hm : 1 ≤ t * q' := Nat.mul_le_mul ht hq'

  let E : (Σ k, ι k) → K → ℕ := fun p k => if k = p.1 then t * q' - 1 else t * q'
  let xx : (Σ k, ι k) → Ω := fun p => s ^ t * (y p * ∏ k, y ⟨k, c0 k⟩ ^ E p k)
  have hxx : ∀ p, xx p ∈ chartLat y ((t * (q' * c)) • N) 1 := by
    intro p
    have hy1 : ∀ k, y ⟨k, c0 k⟩ ^ E p k ∈ chartLat y (E p k • (Pi.single k (1 : ℤ) : K → ℤ)) 1 :=
      fun k => chartLat_pow (chartLat_var (y := y) ⟨k, c0 k⟩) _
    have hyp : y p ∈ chartLat y (Pi.single p.1 (1 : ℤ) : K → ℤ) 1 := chartLat_var (y := y) p
    have hpr := chartLat_prod Finset.univ (fun k => y ⟨k, c0 k⟩ ^ E p k)
      (fun k => E p k • (Pi.single k (1 : ℤ) : K → ℤ)) fun k _ => hy1 k
    have h1 := chartLat_mul (chartLat_pow hs t) (chartLat_mul hyp hpr)
    have hdeg : (t * (q' * c)) • N = t • (q' • (c • N - fun _ => (1 : ℤ))) +
        ((Pi.single p.1 (1 : ℤ) : K → ℤ) + ∑ k, E p k • (Pi.single k (1 : ℤ) : K → ℤ)) := by
      funext k
      have hs1 : (∑ b, E p b • (Pi.single b (1 : ℤ) : K → ℤ)) k = (E p k : ℤ) := by
        rw [Finset.sum_apply, Finset.sum_eq_single k (fun b _ hb => by simp [Ne.symm hb])
          (by simp)]
        simp
      by_cases hk : k = p.1
      · rw [hk] at hs1 ⊢
        rw [Pi.add_apply, Pi.add_apply, hs1]
        simp only [Pi.smul_apply, Pi.sub_apply, Pi.single_eq_same, E, if_true]
        simp only [nsmul_eq_mul]
        push_cast [Nat.cast_sub hm]
        ring
      · rw [Pi.add_apply, Pi.add_apply, hs1]
        simp only [Pi.smul_apply, Pi.sub_apply, Pi.single_eq_of_ne hk, E, if_neg hk]
        simp only [nsmul_eq_mul]
        push_cast
        ring
    rw [hdeg]
    exact h1
  have hxx0 : ∀ k, xx ⟨k, c0 k⟩ ≠ 0 := by
    intro k
    refine mul_ne_zero (pow_ne_zero _ hs0) (mul_ne_zero (hc0 k) ?_)
    exact Finset.prod_ne_zero_iff.mpr fun k' _ => pow_ne_zero _ (hc0 k')
  have hratio : ∀ p : Σ k, ι k, xx p = y p / y ⟨p.1, c0 p.1⟩ * xx ⟨p.1, c0 p.1⟩ := by
    intro p
    show s ^ t * (y p * ∏ k, y ⟨k, c0 k⟩ ^ E p k) =
      y p / y ⟨p.1, c0 p.1⟩ * (s ^ t * (y ⟨p.1, c0 p.1⟩ * ∏ k, y ⟨k, c0 k⟩ ^ E p k))
    rw [div_mul_eq_mul_div, eq_div_iff (hc0 p.1)]
    ring

  let e := Fintype.equivFin (Σ k, ι k)
  refine ⟨Fintype.card (Σ k, ι k), fun j => xx (e.symm j), fun j => hxx _, ?_⟩
  set z : (Σ _ : Unit, Fin (Fintype.card (Σ k, ι k))) → Ω := fun p => xx (e.symm p.2) with hz
  have hzX : ∀ p : Σ k, ι k, aeval z (X ⟨(), e p⟩ : MRing (fun _ : Unit => Fin (Fintype.card (Σ k, ι k)))) = xx p := by
    intro p
    simp [hz]

  have hgen' : ∀ p : Σ k, ι k, IsRatio z (y p / y ⟨p.1, c0 p.1⟩) := by
    intro p
    refine ⟨fun _ => 1, X ⟨(), e p⟩, X ⟨(), e ⟨p.1, c0 p.1⟩⟩, homog_X_unit _, homog_X_unit _, ?_, ?_⟩
    · rw [hzX]; exact hxx0 p.1
    · rw [hzX, hzX]; exact hratio p
  have hring : ∀ w ∈ chartRingZ y c0, IsRatio z w := by
    intro w hw
    induction hw using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨p, rfl⟩ := hx
      exact hgen' p
    | algebraMap r => simpa using IsRatio.intCast (z := z) r
    | add x x' _ _ hx hx' => exact hx.add hx'
    | mul x x' _ _ hx hx' => exact hx.mul hx'

  intro w
  obtain ⟨d, g, hh, hg, hhh, hh0, hgh⟩ := hbir w
  have hA := (mem_chartLat_one y).mp (chartLat_form (y := y) hg) c0 hc0
  have hB := (mem_chartLat_one y).mp (chartLat_form (y := y) hhh) c0 hc0
  have hP : ∏ k, y ⟨k, c0 k⟩ ^ (-(d k : ℤ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc0 k)
  have hw : w = (aeval y g * ∏ k, y ⟨k, c0 k⟩ ^ (-(d k : ℤ))) *
      (aeval y hh * ∏ k, y ⟨k, c0 k⟩ ^ (-(d k : ℤ)))⁻¹ := by
    rw [hgh, mul_assoc w, mul_inv_cancel_right₀ (mul_ne_zero hh0 hP)]
  rw [hw]
  exact (hring _ hA).mul (hring _ hB).inv

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefAmpleGeneric
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

namespace NefAmpleGeneric

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem isArithVar_comap_of_isProjVarF {K : Type} [Fintype K] [Nonempty K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {W : Ideal (MRingOver ℚ ι)} {d : ℕ} (hW : IsProjVarF W d) :
    IsArithVar (W.comap (MvPolynomial.map (Int.castRingHom ℚ))) (d + 1) ∧
      (W.comap (MvPolynomial.map (Int.castRingHom ℚ))).map (MvPolynomial.map (Int.castRingHom ℚ)) = W := by
  classical
  obtain ⟨⟨hprime, hhom, hrel⟩, hdim⟩ := hW
  set φ : MRing ι →+* MRingOver ℚ ι := MvPolynomial.map (Int.castRingHom ℚ) with hφdef
  set P := W.comap φ with hPdef
  have := hprime
  have hPp : P.IsPrime := Ideal.comap_isPrime φ W
  let S : Submonoid (MRing ι) := (nonZeroDivisors ℤ).map (C (σ := Σ k, ι k))
  have : IsLocalization S (MRingOver ℚ ι) := MvPolynomial.isLocalization (nonZeroDivisors ℤ) ℚ
  have hφ : algebraMap (MRing ι) (MRingOver ℚ ι) = φ := by
    show MvPolynomial.map (algebraMap ℤ ℚ) = _
    rw [RingHom.ext_int (algebraMap ℤ ℚ) (Int.castRingHom ℚ)]
  have hmap : P.map φ = W := by
    have h := IsLocalization.map_under S (MRingOver ℚ ι) W
    rwa [hφ] at h
  have hch : ∀ m : ℤ, (C m : MRing ι) ∈ P → m = 0 := by
    intro m hm
    by_contra h0
    have hu : IsUnit (φ (C m)) := by
      rw [hφdef, map_C]
      exact (isUnit_iff_ne_zero.mpr (by simpa using h0 : ((Int.castRingHom ℚ) m) ≠ 0)).map C
    exact hprime.ne_top (Ideal.eq_top_of_isUnit_mem _ hm hu)
  have hWN : NumbersDVR.IsMultiProjPrime (K := K) W :=
    (GroundTheory.Heights₂.Heights.Bridge.isMultiProjPrime_iff W).mpr ⟨hprime, hhom, hrel⟩
  have hPN : NumbersDVR.IsMultiProjPrime (K := K) P := by
    refine ⟨hPp, fun f hf b => ?_, fun k => ?_⟩
    · show φ _ ∈ W
      rw [hφdef, ← NumbersDVR.weightedHomogeneousComponent_map]
      exact hWN.multiHomog _ hf b
    · obtain ⟨i, hi⟩ := hrel k
      exact ⟨i, fun h => hi (by simpa [hPdef, hφdef] using h)⟩
  obtain ⟨-, hhomP, hrelP⟩ := (GroundTheory.Heights₂.Heights.Bridge.isMultiProjPrime_iff P).mp hPN
  obtain ⟨-, -, hd⟩ := ReciprocityTheory.AnForm.R.extQ_spec P hch
  refine ⟨⟨‹Nonempty K›, ⟨hPp, hhomP, hrelP⟩, ?_, ?_⟩, hmap⟩
  · ext m
    simp only [Ideal.mem_comap, Ideal.mem_bot]
    exact ⟨hch m, fun h => by rw [h, map_zero]; exact P.zero_mem⟩
  · have hext : ReciprocityTheory.AnForm.R.extQ P = W := hmap
    rw [← hd, hext, hdim, show d + 1 + Fintype.card K = (d + Fintype.card K) + 1 by omega, Nat.cast_succ]

end NefAmpleGeneric

theorem NefAmpleGeneric.proof (hKA : KH.KAmpStatement)
    (hDG : GroundTheory.Heights₂.Heights.Inter.DegreeGeneric.Statement) : NefAmpleGeneric.Statement := by
  intro K _ _ ι _ _ Ω _ _ y D M P0 b a hV hP0 hs hb ha
  classical
  have : Nonempty K := hV.1
  let I : IFamily ℚ ι := fun V _ L => NumbersDVR.intNum ℚ V L
  have hI : IsFieldIntersection I := NumbersDVR.IntNumIsFieldIntersection.full ℚ K ι
  have hnef : KH.NefOnF I (KH.genIdeal y) M.a := by
    intro W hW hle
    obtain ⟨hWar, hWmap⟩ := NefAmpleGeneric.isArithVar_comap_of_isProjVarF hW
    have hPW : mCoordIdeal y ≤ W.comap (MvPolynomial.map (Int.castRingHom ℚ)) :=
      Ideal.map_le_iff_le_comap.mp hle
    have h0 : 0 ≤ geomDeg (W.comap (MvPolynomial.map (Int.castRingHom ℚ))) M 1 :=
      NefOnGenericOfSemipos.proof K ι _ P0 M hP0 hs _ hWar hPW
    have hdeg := hDG K ι (W.comap (MvPolynomial.map (Int.castRingHom ℚ))) 1 ![M] hWar (fun j => by fin_cases j; exact hs.1)
    rw [hWmap] at hdeg
    have hpot : pot ![M] = fun (_ : Fin 1) z => Real.log (M.h z) := by
      funext j z
      fin_cases j
      rfl
    have hL : (fun j => (![M] j).a) = ![M.a] := by
      funext j
      fin_cases j
      rfl
    rw [hpot, hL] at hdeg
    have h1 : (0 : ℝ) ≤ (NumbersDVR.intNum ℚ W ![M.a] : ℝ) := by
      rw [← hdeg]
      exact h0
    show 0 ≤ NumbersDVR.intNum ℚ W ![M.a]
    exact_mod_cast h1
  have h := hKA ℚ K ι I (KH.genIdeal y) D M.a b a hI (isProjVarF_map_of_isArithVar hV) hnef hb ha
  rwa [← natCast_zsmul] at h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSecEq
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

namespace SecEqProof

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]


variable (ι) in
abbrev Mono (a : K → ℕ) : Type := {μ : (Σ k, ι k) → ℕ // ∀ k, ∑ i, μ ⟨k, i⟩ = a k}

theorem Mono.le {a : K → ℕ} (μ : Mono ι a) (p : Σ k, ι k) : μ.1 p ≤ a p.1 := by
  obtain ⟨k, i⟩ := p
  rw [← μ.2 k]
  exact Finset.single_le_sum (f := fun i => μ.1 ⟨k, i⟩) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

instance (a : K → ℕ) : Finite (Mono ι a) :=
  Finite.of_injective
    (fun μ : Mono ι a => fun p => (⟨μ.1 p, Nat.lt_succ_of_le (μ.le p)⟩ : Fin (a p.1 + 1)))
    fun _ _ h => Subtype.ext (funext fun p => congrArg Fin.val (congrFun h p))

def monVal (y : (Σ k, ι k) → Ω) (μ : (Σ k, ι k) → ℕ) : Ω := ∏ p, y p ^ μ p

def monPoly (μ : (Σ k, ι k) → ℕ) : MRing ι := monomial (Finsupp.equivFunOnFinite.symm μ) 1

theorem aeval_monPoly (y : (Σ k, ι k) → Ω) (μ : (Σ k, ι k) → ℕ) : aeval y (monPoly μ) = monVal y μ := by
  rw [monPoly, aeval_monomial, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rfl

theorem homog_monPoly {a : K → ℕ} (μ : Mono ι a) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (monPoly μ.1) a := by
  intro m hm k
  have := support_monomial_subset hm
  rw [Finset.mem_singleton] at this
  subst this
  simpa using μ.2 k

theorem homog_prod {J : Type} (s : Finset J) (f : J → MRing ι) (d : J → K → ℕ)
    (h : ∀ j ∈ s, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (f j) (d j)) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (∏ j ∈ s, f j) (∑ j ∈ s, d j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using SectionBounded.homog_one (ι := ι)
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    exact SectionBounded.homog_mul (h j (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem homog_bind₁ {a : K → ℕ} {N : ℕ} (φ : Fin (N + 1) → MRing ι) (hφ : ∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (φ j) a)
    {f : MvPolynomial (Fin (N + 1)) ℤ} {n : ℕ} (hf : f.IsHomogeneous n) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (bind₁ φ f) (fun k => n * a k) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [f.as_sum, map_sum]
  refine SectionBounded.homog_sum _ fun m hm => ?_
  rw [bind₁_monomial]
  refine SectionBounded.homog_congr (SectionBounded.homog_mul (SectionBounded.homog_C _)
    (homog_prod _ _ _ fun j _ => SectionBounded.homog_pow (hφ j) (m j))) fun k => ?_
  have hdeg : ∑ j ∈ m.support, m j = n := by
    have := hf (mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  rw [← hdeg, Finset.sum_mul]
  simp [Finset.sum_apply]

variable [DecidableEq K] [∀ k, DecidableEq (ι k)]

def swap (μ : (Σ k, ι k) → ℕ) (q p : Σ k, ι k) : (Σ k, ι k) → ℕ :=
  fun r => μ r + (if p = r then 1 else 0) - (if q = r then 1 else 0)

theorem sum_boole_block (k : K) (i₀ : ι k) (k' : K) :
    ∑ i : ι k', (if (⟨k, i₀⟩ : Σ k, ι k) = ⟨k', i⟩ then 1 else 0) = if k = k' then 1 else 0 := by
  by_cases h : k = k'
  · subst h; simp
  · simp [h]

theorem swap_mem {a : K → ℕ} (μ : Mono ι a) (k : K) (i₀ i : ι k) (h : μ.1 ⟨k, i₀⟩ ≠ 0) (k' : K) :
    ∑ i', swap μ.1 ⟨k, i₀⟩ ⟨k, i⟩ ⟨k', i'⟩ = a k' := by
  unfold swap
  rw [Finset.sum_tsub_distrib, Finset.sum_add_distrib, μ.2 k', sum_boole_block, sum_boole_block,
    Nat.add_sub_cancel]
  intro i' _
  by_cases hq : (⟨k, i₀⟩ : Σ k, ι k) = ⟨k', i'⟩
  · cases hq
    rw [if_pos rfl]
    omega
  · rw [if_neg hq]
    exact Nat.zero_le _

theorem monVal_swap (y : (Σ k, ι k) → Ω) (μ : (Σ k, ι k) → ℕ) (q p : Σ k, ι k) (h : μ q ≠ 0) :
    monVal y (swap μ q p) * y q = monVal y μ * y p := by
  have hq : ∏ r, y r ^ (if q = r then 1 else 0) = y q := by simp
  have hp : ∏ r, y r ^ (if p = r then 1 else 0) = y p := by simp
  rw [← hq, ← hp, monVal, monVal, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun r _ => ?_
  rw [← pow_add, ← pow_add, swap, Nat.sub_add_cancel]
  by_cases h1 : q = r
  · subst h1
    rw [if_pos rfl]
    omega
  · rw [if_neg h1]
    exact Nat.zero_le _

def pure (c : ∀ k, ι k) (a : K → ℕ) : Mono ι a :=
  ⟨fun r => if c r.1 = r.2 then a r.1 else 0, fun k => by simp⟩

theorem monVal_pure (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (a : K → ℕ) :
    monVal y (pure c a).1 = ∏ k, y ⟨k, c k⟩ ^ a k := by
  rw [monVal, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp [pure, pow_ite]

def svPt (y : (Σ k, ι k) → Ω) {a : K → ℕ} {N : ℕ} (e : Mono ι a ≃ Fin (N + 1)) : Fin (N + 1) → Ω :=
  fun j => monVal y (e.symm j).1

theorem chartLat_le_secs (y : (Σ k, ι k) → Ω) {a : K → ℕ} (ha : ∀ k, 1 ≤ a k) {N : ℕ}
    (e : Mono ι a ≃ Fin (N + 1)) (τ : ℕ) {s : Ω} (hs : s ∈ chartLat y (fun k => (a k : ℤ)) τ) :
    s ∈ (Kleiman.twistSys ℤ (svPt y e) (τ : ℤ)).secs := by
  rw [Kleiman.SubSystem.secs, Submodule.mem_iInf]
  intro I
  obtain ⟨j, hj⟩ := I.2.1
  have hzj : monVal y (e.symm j).1 ≠ 0 := (Kleiman.mem_support (svPt y e)).mp (I.2.2 hj)
  have hex : ∀ k, ∃ i, (e.symm j).1 ⟨k, i⟩ ≠ 0 := fun k => by
    have h0 : ∑ i, (e.symm j).1 ⟨k, i⟩ ≠ 0 := by rw [(e.symm j).2 k]; exact Nat.one_le_iff_ne_zero.mp (ha k)
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h0
    exact ⟨i, hi⟩
  choose c hc using hex
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h0 =>
    hzj (Finset.prod_eq_zero (Finset.mem_univ ⟨k, c k⟩) (by rw [h0, zero_pow (hc k)]))
  have hle : chartRingZ y c ≤ Kleiman.chartRing ℤ (svPt y e) I := by
    rw [chartRingZ, Algebra.adjoin_le_iff]
    rintro _ ⟨⟨k, i⟩, rfl⟩
    refine ⟨X (e ⟨swap (e.symm j).1 ⟨k, c k⟩ ⟨k, i⟩, swap_mem (e.symm j) k (c k) i (hc k)⟩), X j, 1,
      Kleiman.X_mem_monos hj, isHomogeneous_X _ _, isHomogeneous_X _ _, ?_⟩
    simp only [aeval_X, svPt, Equiv.symm_apply_apply]
    rw [div_eq_div_iff (hyc k) hzj, monVal_swap y _ _ _ (hc k), mul_comm]
  have hj0 : svPt y e (e (pure c a)) ^ τ ∈ Kleiman.twistMod ℤ (svPt y e) (τ : ℤ) I :=
    Submodule.subset_span ⟨X (e (pure c a)) ^ τ, 1, 0, τ, one_mem _, isHomogeneous_X_pow _ _,
      isHomogeneous_one _ _, by simp, by simp⟩
  have hmem := Submodule.smul_mem _ (⟨_, hle (hs c hyc)⟩ : Kleiman.chartRing ℤ (svPt y e) I) hj0
  rw [Submodule.restrictScalars_mem]
  change s ∈ Kleiman.twistMod ℤ (svPt y e) (τ : ℤ) I
  convert hmem using 1
  change s = (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * (a k : ℤ)))) * _
  rw [svPt, Equiv.symm_apply_apply, monVal_pure, ← Finset.prod_pow, mul_assoc, ← Finset.prod_mul_distrib,
    Finset.prod_eq_one, mul_one]
  intro k _
  rw [← pow_mul, zpow_neg, show (τ : ℤ) * (a k : ℤ) = ((a k * τ : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
    inv_mul_cancel₀ (pow_ne_zero _ (hyc k))]

theorem piece_le_secM (y : (Σ k, ι k) → Ω) {a : K → ℕ} {N : ℕ} (e : Mono ι a ≃ Fin (N + 1)) (τ : ℕ) {s : Ω}
    (hs : s ∈ (Kleiman.coordGraded ℤ (svPt y e)).piece (τ : ℤ)) : s ∈ secM y (fun k => τ * a k) := by
  have hle : (Kleiman.coordGraded ℤ (svPt y e)).piece (τ : ℤ) ≤
      Submodule.span ℤ {s | ∃ g : MRing ι, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g (fun k => τ * a k) ∧ aeval y g = s} := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, n, hf, hn, rfl⟩
    obtain rfl : n = τ := by exact_mod_cast hn
    refine Submodule.subset_span ⟨bind₁ (fun j => monPoly (e.symm j).1) f,
      homog_bind₁ _ (fun j => homog_monPoly (e.symm j)) hf, ?_⟩
    rw [aeval_bind₁]
    simp only [aeval_monPoly]
    rfl
  exact hle hs

end SecEqProof


open SecEqProof in
theorem SecEq.proof : SecEq.Statement := by
  intro K _ ι _ Ω _ y a ha hy
  classical
  choose c hc using hy
  obtain ⟨N, ⟨e⟩⟩ : ∃ N, Nonempty (Mono ι a ≃ Fin (N + 1)) := by
    have : Nonempty (Mono ι a) := ⟨pure c a⟩
    exact ⟨Nat.card (Mono ι a) - 1,
      ⟨(Finite.equivFin _).trans (finCongr (Nat.sub_add_cancel Nat.card_pos).symm)⟩⟩
  have hz : svPt y e ≠ 0 := fun h => by
    have h1 := congrFun h (e (pure c a))
    simp only [svPt, Equiv.symm_apply_apply, monVal_pure, Pi.zero_apply] at h1
    exact Finset.prod_ne_zero_iff.mpr (fun k _ => pow_ne_zero _ (hc k)) h1
  obtain ⟨τ₀, hτ₀⟩ := Filter.eventually_atTop.mp (Kleiman.TwistSections.full ℤ Ω N (svPt y e) hz)
  refine ⟨τ₀, fun τ hτ => le_antisymm (fun s hs => ?_)
    (UpperNormalisation.secM_le_chartLat y _ τ fun k => by push_cast; ring)⟩
  exact piece_le_secM y e τ ((hτ₀ τ hτ) ▸ chartLat_le_secs y ha e τ hs)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullFormsGeneric
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def PullFormsGeneric.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    (∀ k, 1 ≤ e k) → (∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (L j) e) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) →
    ∀ (d : ℕ) (F : MvPolynomial (Fin (D + 1)) ℚ), F.IsHomogeneous d →
      aeval (fun j => aeval y (L j)) F = 0 → F = 0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsDehomCharpolyForms
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

noncomputable section

def DehomCharpolyForms.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (D : ℕ) (l : Fin (D + 1) → Ω) (P : IntermediateField ℚ Ω)
    [FiniteDimensional P Ω],
    P = IntermediateField.adjoin ℚ {x | ∃ i k, l k ≠ 0 ∧ x = l i / l k} →
    (∀ (d : ℕ) (F : MvPolynomial (Fin (D + 1)) ℚ), F.IsHomogeneous d → aeval l F = 0 → F = 0) →
    ∀ (j : Fin (D + 1)) (m : ℕ) (u : Ω),
      (∀ k, u * (l j / l k) ^ m ∈ integralClosure (Algebra.adjoin ℚ (Set.range fun i => l i / l k)) Ω) →
      ∃ c : ℕ → MvPolynomial (Fin (D + 1)) ℚ, c 0 = 1 ∧
        (∀ i ≤ Module.finrank P Ω, (c i).IsHomogeneous (i * m)) ∧
        (LinearMap.charpoly (Algebra.lmul P Ω u)).map (algebraMap P Ω) =
          ∑ i ∈ Finset.range (Module.finrank P Ω + 1),
            Polynomial.C (aeval (fun i' => l i' / l j) (c i)) * Polynomial.X ^ (Module.finrank P Ω - i) ∧
        (u ≠ 0 → c (Module.finrank P Ω) ≠ 0)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ProjFrameGraphChart
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace ProjFrameGraph

variable {κ : Type} {D : ℕ}

theorem linForm_projMat [Fintype κ] (e : Fin (D + 1) → Ix κ) (k : Fin (D + 1)) :
    ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e) ⟨(), k⟩ = X (e k) := by
  classical
  simp only [ReciprocityTheory.ChartRestriction.G.AI.I4.linForm, projMat]
  rw [Finset.sum_eq_single (e k).2]
  · simp
  · intro i _ hi
    simp [Ne.symm hi]
  · simp

theorem graphIdeal_isPrime {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]
    (P : Ideal (MRing ι)) [P.IsPrime] (g : (Σ k, ι₂ k) → MRing ι) : (graphIdeal P g).IsPrime :=
  RingHom.ker_isPrime _

variable {Ω : Type} [Field Ω]

theorem frame_ne_zero {x : Ix κ → Ω} {e : Fin (D + 1) → Ix κ} (hF : IsProjFrame x e) (k : Fin (D + 1)) :
    x (e k) ≠ 0 := by
  intro h
  have hX : (X k : MvPolynomial (Fin (D + 1)) ℤ) ∈ coordIdeal ℤ (x ∘ e) := by
    rw [coordIdeal, RingHom.mem_ker]
    simp [coneMap, h]
  rw [hF.free, Ideal.mem_bot] at hX
  exact X_ne_zero k hX

theorem genFibre_x'_ne_zero {x : Ix κ → Ω} {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]
    [Fintype κ] {g : (Σ k, ι₂ k) → MRing (GlobalTheory κ)}
    (G : GenFibre (inrV (ι := GlobalTheory κ) (ι₂ := ι₂)) (graphIdeal (coordIdeal ℤ x) g)) (j : κ) (hj : x ⟨(), j⟩ ≠ 0) :
    G.x' ⟨Sum.inl (), j⟩ ≠ 0 := by
  intro h
  have h1 : (X ⟨Sum.inl (), j⟩ : MRing (Sum.elim (GlobalTheory κ) ι₂)) ∈ graphIdeal (coordIdeal ℤ x) g := by
    rw [← G.genericFibre_ker_target, RingHom.mem_ker]
    simpa using h
  rw [graphIdeal, RingHom.mem_ker, graphMap, eval₂Hom_X'] at h1
  have h2 : (X ⟨(), j⟩ : MvPolynomial (Ix κ) ℤ) ∈ coordIdeal ℤ x := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact MvPolynomial.C_eq_zero.1 h1
  rw [coordIdeal, RingHom.mem_ker] at h2
  simp [coneMap] at h2
  exact hj h2

def fibreChart {K₂ : Type} {ι₂ : K₂ → Type} (j : κ) :
    (k : FibreBlock (Sum.inr : K₂ → Unit ⊕ K₂)) → fibreIdx (Sum.elim (GlobalTheory κ) ι₂) Sum.inr k
  | ⟨Sum.inl _, _⟩ => j
  | ⟨Sum.inr k, h⟩ => absurd ⟨k, rfl⟩ h

theorem isChart_fibreChart {x : Ix κ → Ω} {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]
    [Fintype κ] {g : (Σ k, ι₂ k) → MRing (GlobalTheory κ)}
    (G : GenFibre (inrV (ι := GlobalTheory κ) (ι₂ := ι₂)) (graphIdeal (coordIdeal ℤ x) g)) (j : κ) (hj : x ⟨(), j⟩ ≠ 0) :
    IsChart (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) (fibreChart (ι₂ := ι₂) j) := by
  rintro ⟨(u | k), h⟩
  · cases u
    rw [ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, RingHom.mem_ker, aeval_X]
    exact genFibre_x'_ne_zero G j hj
  · exact absurd ⟨k, rfl⟩ h

end ProjFrameGraph

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreNormDehomIntegral
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def FibreNormDehomIntegral.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι) (q : ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    (∀ k, 1 ≤ e k) → (∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (L j) e) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) →
    ∃ M₀ : ℕ, 1 ≤ M₀ ∧
      ∀ τ : ℕ, ∀ s ∈ chartLatNm y (fun k => ((q * e k : ℕ) : ℤ)) τ, ∀ (j : Fin (D + 1))
        (c : ℕ → MvPolynomial (Fin (D + 1)) ℚ), IsDehomNormForms y L j (q * τ) s c →
          ∃ F : MvPolynomial (Fin (D + 1)) ℤ,
            map (Int.castRingHom ℚ) F = ((M₀ : ℚ) ^ τ) • c (Module.finrank (pullField y L) Ω)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGeneratedProductNonneg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace GeneratedProductNonneg

variable {F : Type} [Field F] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem le_of_mem_support_ratDiv {V : Ideal (MRingOver F ι)} {f g : MRingOver F ι} {W : Ideal (MRingOver F ι)}
    (hW : W ∈ (ratDiv V f g).support) : V ≤ W := by
  have key : ∀ s : MRingOver F ι, ReciprocityTheory.ChartRestriction.G.Geo.divCycle V s W ≠ 0 → V ≤ W := by
    intro s hs
    unfold ReciprocityTheory.ChartRestriction.G.Geo.divCycle at hs
    rw [Finsupp.ofSupportFinite_coe] at hs
    split_ifs at hs with h
    · exact le_sup_left.trans h.1.1.2
    · exact absurd rfl hs
  rw [Finsupp.mem_support_iff, ratDiv, Finsupp.sub_apply, Finsupp.mapRange_apply,
    Finsupp.mapRange_apply] at hW
  by_cases hf : ReciprocityTheory.ChartRestriction.G.Geo.divCycle V f W = 0
  · refine key g fun h => hW ?_
    rw [hf, h]
    simp
  · exact key f hf

end GeneratedProductNonneg

theorem GeneratedProductNonneg.proof (hR : GeneratedRestrict.Statement)
    (hE : GeneratedEffectiveSection.Statement) : GeneratedProductNonneg.Statement := by
  classical
  intro F _ K _ _ ι _ _ I V m β hI hV hgen
  induction m generalizing V with
  | zero =>
    choose i hi using hV.1.2.2
    rw [hI.1 V β i hV hi]
    exact Int.natCast_nonneg _
  | succ m ih =>
    obtain ⟨f, g, hs, heff⟩ := hE F K ι V (β (Fin.last m)) hV.1 (hgen (Fin.last m))
    have e := hI.2 V m (Fin.init β) (β (Fin.last m)) f g hV hs
    rw [Fin.snoc_init_self] at e
    rw [e, cycEval]
    refine Finsupp.sum_nonneg fun W hW => mul_nonneg (heff W) ?_
    obtain ⟨α, γ, hf, hg, hfV, hgV, -⟩ := hs
    have hWm : IsProjVarF W m := KleimanNefF.isProjVarF_of_mem_support hV
      ((NumbersDVR.VocabMultiHomog.proof F K ι f α).1 hf) ((NumbersDVR.VocabMultiHomog.proof F K ι g γ).1 hg)
      hfV hgV hW
    have hle : V ≤ W := GeneratedProductNonneg.le_of_mem_support_ratDiv hW
    exact ih W (Fin.init β) hWm fun j => hR F K ι V W _ hle (hgen _)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullSectionIntegral
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def PullSectionIntegral.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι) (q : ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    (∀ k, 1 ≤ e k) → (∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (L j) e) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) →
      ∀ τ : ℕ, ∀ s ∈ chartLatNm y (fun k => ((q * e k : ℕ) : ℤ)) τ, ∀ j : Fin (D + 1), aeval y (L j) ≠ 0 →
        s / aeval y (L j) ^ (q * τ) ∈
          integralClosure (Algebra.adjoin ℚ (Set.range fun i => aeval y (L i) / aeval y (L j))) Ω

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullConeNull
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def coneNullIdeal {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    (y : (Σ k, ι k) → Ω) {D : ℕ} (L : Fin (D + 1) → MRing ι) : Ideal (MvPolynomial (Σ k, ι k) ℚ) :=
  Ideal.span (map (Int.castRingHom ℚ) '' (mCoordIdeal y : Set (MRing ι)) ∪
    Set.range fun j => map (Int.castRingHom ℚ) (L j))

def PullConeNull.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (L : Fin (D + 1) → MRing ι),
    (∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) →
    ∃ N : ℕ, ∀ c : ∀ k, ι k, (∏ k, (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℚ)) ^ N ∈ coneNullIdeal y L

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

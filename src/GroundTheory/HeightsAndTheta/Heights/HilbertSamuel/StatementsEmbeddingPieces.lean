module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKodairaGeneric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsMultiHomogX
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRatNoetherFrame
public import GroundTheory.HeightsAndTheta.Heights.Intersections.ProjLineRankTwoPushforwardHypotheses
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResVolume

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEmbeddingPieces
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology

noncomputable section

def EmbeddingPieces.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (F : Type) [Field F] [NumberField F] [Algebra F Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (L : Fin D → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : (F →+* ℂ) → ℝ)
    (w : ((Σ k, ι k) → ℂ) → ℝ),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y → (∀ j, IsSmoothHerm (L j)) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃! sg : F →+* ℂ, LiesOver y sg z) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∀ sg : F →+* ℂ, LiesOver y sg z → w =ᶠ[𝓝 z] fun _ => c sg) →
    ptsIntegral (mCoordIdeal y) (pot L) w =
      (∑ sg, c sg) / Fintype.card (F →+* ℂ) * ptsIntegral (mCoordIdeal y) (pot L) (fun _ => 1)

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsAmpleOfGenTwist
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def GenTwistGenerated.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (V : Ideal (MRingOver S ι)) (α : K → ℤ) (m n : ℕ),
    KH.GeneratedV S V α → KH.GeneratedV S V ((m : ℤ) • α + fun _ => (n : ℤ))

def GenTwistVanish.Statement : Prop :=
  ∀ (S : Type) [Field S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (V : Ideal (MRingOver S ι)) (α : K → ℤ),
    IsMultiHomogIdeal V → KH.GeneratedV S V α →
    ∀ e : K → ℤ, ∃ c₀ : ℕ, ∀ m n : ℕ, c₀ ≤ n →
      Subsingleton (KH.cechHc ι (KH.quotPart S V) (e + (m : ℤ) • α + fun _ => (n : ℤ)) 1)

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBirationalModelExists
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

namespace BirationalModelExists

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isMultiHomog_zero' (a : K → ℕ) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (0 : MRing ι) a := by
  intro m hm
  simp at hm

theorem isMultiHomog_add' {f g : MRing ι} {a : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g a) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (f + g) a := by
  classical
  intro m hm
  rcases Finset.mem_union.1 (support_add hm) with h | h
  exacts [hf m h, hg m h]

theorem isMultiHomog_neg' {f : MRing ι} {a : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (-f) a := by
  intro m hm
  rw [support_neg] at hm
  exact hf m hm

theorem aeval_scale {S : Type*} [CommRing S] [Algebra ℤ S] {g : MRing ι} {a : K → ℕ} (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g a)
    (z : (Σ k, ι k) → S) (u : K → S) :
    aeval (fun p => z p * u p.1) g = aeval z g * ∏ k, u k ^ a k := by
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hprod : ∏ p, (z p * u p.1) ^ m p = (∏ p, z p ^ m p) * ∏ k, u k ^ a k := by
    simp_rw [mul_pow, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, u k ^ m ⟨k, i⟩ = u k ^ a k
    rw [Finset.prod_pow_eq_pow_sum, hg m hm k]
  rw [hprod]
  ring

theorem hom_aeval {S T : Type*} [CommRing S] [CommRing T] [Algebra ℤ S] [Algebra ℤ T] (φ : S →+* T) (z : (Σ k, ι k) → S) (g : MRing ι) :
    φ (aeval z g) = aeval (fun p => φ (z p)) g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp => simp [hp]

variable (P : Ideal (MRing ι)) [P.IsPrime]

def coordClass (p : Σ k, ι k) : FractionRing (MRing ι ⧸ P) :=
  algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (X p))

theorem aeval_coordClass (g : MRing ι) :
    aeval (coordClass P) g = algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P g) := by
  set_option synthInstance.maxHeartbeats 200000 in
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    rw [map_add (aeval (coordClass P)), map_add (Ideal.Quotient.mk P),
      map_add (algebraMap _ _), hp, hq]
  | mul_X p n hp => simp only [map_mul, hp, aeval_X, coordClass]

theorem aeval_coordClass_eq_zero (g : MRing ι) : aeval (coordClass P) g = 0 ↔ g ∈ P := by
  rw [aeval_coordClass, map_eq_zero_iff _ (IsFractionRing.injective (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P))),
    Ideal.Quotient.eq_zero_iff_mem]

def fnField : Subfield (FractionRing (MRing ι ⧸ P)) where
  carrier := {s | ∃ (d : K → ℕ) (g h : MRing ι), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g d ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog h d ∧
    aeval (coordClass P) h ≠ 0 ∧ aeval (coordClass P) g = s * aeval (coordClass P) h}
  zero_mem' := ⟨0, 0, 1, isMultiHomog_zero' 0, ReciprocityTheory.ChartRestriction.G.Geo.isMultiHomog_one, by simp, by simp⟩
  one_mem' := ⟨0, 1, 1, ReciprocityTheory.ChartRestriction.G.Geo.isMultiHomog_one, ReciprocityTheory.ChartRestriction.G.Geo.isMultiHomog_one, by simp, by simp⟩
  add_mem' := by
    rintro s t ⟨d, g, h, hg, hh, h0, hs⟩ ⟨d', g', h', hg', hh', h0', ht⟩
    refine ⟨d + d', g * h' + h * g', h * h',
      isMultiHomog_add' (isMultiHomog_mul hg hh') (isMultiHomog_mul hh hg'), isMultiHomog_mul hh hh',
      by simp [h0, h0'], ?_⟩
    simp only [map_add (f := _), map_mul, hs, ht]
    ring
  mul_mem' := by
    rintro s t ⟨d, g, h, hg, hh, h0, hs⟩ ⟨d', g', h', hg', hh', h0', ht⟩
    refine ⟨d + d', g * g', h * h', isMultiHomog_mul hg hg', isMultiHomog_mul hh hh', by simp [h0, h0'], ?_⟩
    simp only [map_mul, hs, ht]
    ring
  neg_mem' := by
    rintro s ⟨d, g, h, hg, hh, h0, hs⟩
    exact ⟨d, -g, h, isMultiHomog_neg' hg, hh, h0, by simp [hs]⟩
  inv_mem' := by
    rintro s ⟨d, g, h, hg, hh, h0, hs⟩
    by_cases s0 : s = 0
    · subst s0
      exact ⟨0, 0, 1, isMultiHomog_zero' 0, ReciprocityTheory.ChartRestriction.G.Geo.isMultiHomog_one, by simp, by simp⟩
    · refine ⟨d, h, g, hh, hg, ?_, ?_⟩
      · rw [hs]
        exact mul_ne_zero s0 h0
      · rw [hs, ← mul_assoc, inv_mul_cancel₀ s0, one_mul]

variable {P}

theorem coordClass_ne_zero {p : Σ k, ι k} (hp : (X p : MRing ι) ∉ P) : coordClass P p ≠ 0 := by
  have h := (aeval_coordClass_eq_zero P (X p)).not.2 hp
  rwa [aeval_X] at h


open Classical in
def birPoint (c : ∀ k, ι k) (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ P) (p : Σ k, ι k) : fnField P :=
  ⟨coordClass P p / coordClass P ⟨p.1, c p.1⟩,
    ⟨Pi.single p.1 1, X p, X ⟨p.1, c p.1⟩, isMultiHomog_X' p.1 p.2, isMultiHomog_X' p.1 (c p.1),
      by rw [aeval_X]; exact coordClass_ne_zero (hc p.1),
      by rw [aeval_X, aeval_X, div_mul_cancel₀ _ (coordClass_ne_zero (hc p.1))]⟩⟩

theorem coe_aeval_birPoint (c : ∀ k, ι k) (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ P) {g : MRing ι} {a : K → ℕ}
    (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g a) :
    ((aeval (birPoint c hc) g : fnField P) : FractionRing (MRing ι ⧸ P)) =
      aeval (coordClass P) g * ∏ k, (coordClass P ⟨k, c k⟩)⁻¹ ^ a k := by
  have h := hom_aeval (fnField P).subtype (birPoint c hc) g
  have hf : (fun p => (fnField P).subtype (birPoint c hc p)) =
      fun p => coordClass P p * (fun k => (coordClass P ⟨k, c k⟩)⁻¹) p.1 := by
    funext p
    exact div_eq_mul_inv _ _
  rw [hf] at h
  exact h.trans (aeval_scale hg (coordClass P) fun k => (coordClass P ⟨k, c k⟩)⁻¹)

theorem prod_inv_ne_zero (c : ∀ k, ι k) (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ P) (a : K → ℕ) :
    ∏ k, (coordClass P ⟨k, c k⟩)⁻¹ ^ a k ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (inv_ne_zero (coordClass_ne_zero (hc k)))

theorem eval_mConeMap_birPoint (c : ∀ k, ι k) (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ P) (f : MRing ι) :
    eval₂ (fnField P).subtype (fun k => coordClass P ⟨k, c k⟩) (mConeMap (birPoint c hc) f) =
      aeval (coordClass P) f := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    have e1 := map_intCast (eval₂Hom (fnField P).subtype (fun k => coordClass P ⟨k, c k⟩)) a
    simp only [coe_eval₂Hom] at e1
    simpa [mConeMap] using e1
  | add p q hp hq => simp only [map_add (f := _), eval₂_add, hp, hq]
  | mul_X p n hp =>
    have hX : mConeMap (birPoint c hc) (X n) = C (birPoint c hc n) * X n.1 := by simp [mConeMap]
    have e : (fnField P).subtype (birPoint c hc n) * coordClass P ⟨n.1, c n.1⟩ = coordClass P n :=
      div_mul_cancel₀ _ (coordClass_ne_zero (hc n.1))
    rw [map_mul, eval₂_mul, hp, hX, eval₂_mul, eval₂_C, eval₂_X, map_mul, aeval_X, e]

theorem mCoordIdeal_birPoint (hP : IsMultiHomogIdeal P) (c : ∀ k, ι k)
    (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ P) : mCoordIdeal (birPoint c hc) = P := by
  apply le_antisymm
  · intro f hf
    rw [mCoordIdeal, RingHom.mem_ker] at hf
    have h := eval_mConeMap_birPoint c hc f
    rw [hf, eval₂_zero] at h
    exact (aeval_coordClass_eq_zero P f).1 h.symm
  · obtain ⟨S, hS, rfl⟩ := hP
    rw [Ideal.span_le]
    intro g hgS
    obtain ⟨a, ha⟩ := hS g hgS
    have hgP : aeval (coordClass (Ideal.span S)) g = 0 :=
      (aeval_coordClass_eq_zero _ g).2 (Ideal.subset_span hgS)
    have hy : aeval (birPoint c hc) g = 0 := by
      apply Subtype.ext
      rw [coe_aeval_birPoint c hc ha, hgP, zero_mul]
      rfl
    show g ∈ RingHom.ker (mConeMap (birPoint c hc))
    rw [RingHom.mem_ker]
    show aeval (fun p => C (birPoint c hc p) * X p.1) g = 0
    refine (aeval_scale ha (fun p => C (birPoint c hc p)) X).trans ?_
    rw [← hom_aeval C, hy, map_zero, zero_mul]

theorem birational_birPoint (c : ∀ k, ι k) (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ P) :
    Birational (birPoint c hc) := by
  rintro ⟨s, d, g, h, hg, hh, h0, hs⟩
  refine ⟨d, g, h, hg, hh, ?_, ?_⟩
  · intro h'
    have := congrArg (fun t : fnField P => (t : FractionRing (MRing ι ⧸ P))) h'
    simp only [coe_aeval_birPoint c hc hh, ZeroMemClass.coe_zero] at this
    exact mul_ne_zero h0 (prod_inv_ne_zero c hc d) this
  · apply Subtype.ext
    rw [Subfield.coe_mul, coe_aeval_birPoint c hc hg, coe_aeval_birPoint c hc hh]
    show _ = s * _
    rw [hs, mul_assoc]

end BirationalModelExists

theorem BirationalModelExists.proof : BirationalModelExists.Statement := by
  intro K _ ι _ P d hP
  obtain ⟨_, ⟨hprime, hhom, hrel⟩, _, _⟩ := hP
  choose c hc using hrel
  have := hprime
  exact ⟨BirationalModelExists.fnField P, inferInstance, BirationalModelExists.birPoint c hc,
    BirationalModelExists.mCoordIdeal_birPoint hhom c hc, BirationalModelExists.birational_birPoint c hc⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ResolutionMetricObjects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory
open scoped ComplexConjugate

noncomputable section

set_option linter.unusedSectionVars false

variable {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

def resCGram (d : HSMDatum D Ω κ) (n : ℕ) {r : ℕ} (b : Fin r → MvPolynomial (Ix κ) ℚ) :
    Matrix (Fin r) (Fin r) ℂ :=
  fun k l => ∫ y, pairVal d.m n (b k) (b l) (resPt d y) ∂d.dV


open Classical in
def resCChi (d : HSMDatum D Ω κ) (n : ℕ) : ℝ :=
  if h : ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis d.x n p.2 then
    -(1 / 2) * Real.log (resCGram d n h.choose.2).det.re
  else 0

def resPot (d : HSMDatum D Ω κ) (m : ConeMetric ℂ (Ix κ)) : LocPot d.R.X where
  U := d.R.U
  isOpen_U := d.R.isOpen_U
  mem_U := d.R.mem_U
  φ x y := Real.log (m.ρ (d.R.lift x y))

def resMetricInt (d : HSMDatum D Ω κ) (m₁ : ConeMetric ℂ (Ix κ)) : ℝ :=
  ∫ t in (0 : ℝ)..1, mInt d.R.A (fun _ => resPot d (interp d.m m₁ t)) fun y => logRatio d.m m₁ (resPt d y)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsShiftSectionBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

def ShiftSectionBound.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (a : K → ℤ) (m : ℕ),
    1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a) 1) : ℝ) ≤
          (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a + fun _ => (m : ℤ)) 1) : ℝ) ∧
        (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a + fun _ => (m : ℤ)) 1) : ℝ) ≤
          (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a) 1) : ℝ) + C * (n : ℝ) ^ (D - 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.TwoBlockModel
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

section TwoBlock

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

def twoBlockIdeal (x x' : Ix κ → Ω) : Ideal (MRing (FinTwoTypeFamily κ)) :=
  mCoordIdeal (ι := FinTwoTypeFamily κ) (pair x x')

def blockLine (m : ConeMetric (C := ℂ) (ι := Ix κ)) (k₀ : Fin 2) :
    ReciprocityTheory.ChartRestriction.G.Geo.HermLine (ι := FinTwoTypeFamily κ) where
  a := Pi.single k₀ 1
  h z := m.ρ fun p : Ix κ => z ⟨k₀, p.2⟩
  pos z hz := m.pos _ fun h0 => by
    obtain ⟨i, hi⟩ := hz k₀
    exact hi (congrFun h0 ⟨(), i⟩)
  smul c z _ := by
    have e : (fun p : Ix κ => c k₀ * z ⟨k₀, p.2⟩) = c k₀ • fun p : Ix κ => z ⟨k₀, p.2⟩ := rfl
    show m.ρ (fun p : Ix κ => c k₀ * z ⟨k₀, p.2⟩) = _
    rw [e, m.smul, Finset.prod_eq_single k₀ (fun k _ hk => by simp [hk]) (by simp)]
    simp

def twoBlockList (m m' : ConeMetric (C := ℂ) (ι := Ix κ)) (D i : ℕ) :
    Fin (D + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine (ι := FinTwoTypeFamily κ) :=
  fun j => if (j : ℕ) < i then blockLine m 0 else blockLine m' 1

def twoBlockCoeff (I : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.AllFam)
    (x x' : Ix κ → Ω) (m m' : ConeMetric (C := ℂ) (ι := Ix κ)) (D i : ℕ) : ℝ :=
  I (Fin 2) (FinTwoTypeFamily κ) (twoBlockIdeal x x') (D + 1) (twoBlockList m m' D i) -
    I (Fin 2) (FinTwoTypeFamily κ) (twoBlockIdeal x x') (D + 1) (twoBlockList m m' D (i + 1))

def twoBlockStep (x x' : Ix κ → Ω) (a b : ℕ) : ℝ :=
  Real.log ((sec ℤ x (a + 1) * sec ℤ x' b).toAddSubgroup.relIndex (sec ℤ x a * sec ℤ x' (b + 1)).toAddSubgroup)

theorem twoBlockList_zero (m m' : ConeMetric (C := ℂ) (ι := Ix κ)) (D : ℕ) :
    twoBlockList m m' D 0 = fun _ => blockLine m' 1 := by
  funext j
  simp [twoBlockList]

theorem twoBlockList_last (m m' : ConeMetric (C := ℂ) (ι := Ix κ)) (D : ℕ) :
    twoBlockList m m' D (D + 1) = fun _ => blockLine m 0 := by
  funext j
  simp [twoBlockList, j.2]

theorem sum_twoBlockCoeff (I : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.AllFam)
    (x x' : Ix κ → Ω) (m m' : ConeMetric (C := ℂ) (ι := Ix κ)) (D : ℕ) :
    ∑ i ∈ Finset.range (D + 1), twoBlockCoeff I x x' m m' D i =
      I (Fin 2) (FinTwoTypeFamily κ) (twoBlockIdeal x x') (D + 1) (fun _ => blockLine m' 1) -
        I (Fin 2) (FinTwoTypeFamily κ) (twoBlockIdeal x x') (D + 1) (fun _ => blockLine m 0) := by
  unfold twoBlockCoeff
  rw [Finset.sum_range_sub', twoBlockList_zero, twoBlockList_last]

end TwoBlock

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionLatticeFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SectionLatticeFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (n : ℕ),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (chartLat y a n).FG

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BirationalYPt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def ArithmeticVolumeDimensionOne.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (M : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (P0 : Ideal (MRing ι)) (II : IntersectionSystem),
    IsIntersectionSystem II → IsArithVar (mCoordIdeal y) 1 → Birational y →
    IsNefBigDatum P0 y 0 M → 0 < II K ι (mCoordIdeal y) 1 (fun _ => M) →
    ∃ (n : ℕ) (s : Ω), 1 ≤ n ∧ s ∈ chartLat y M.a n ∧ s ≠ 0 ∧
      ∃ c : ℝ, c < 1 ∧ IsBoundedH (mCoordIdeal y) y M n c s

namespace ArithmeticVolumeDimensionOne

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet

end ArithmeticVolumeDimensionOne

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChangeOfModel
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

section Objects

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def IsIsometricOn (P : Ideal (MRing ι)) (A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) : Prop :=
  ∃ (f g : MRing ι) (α β : K → ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f α ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g β ∧ f ∉ P ∧ g ∉ P ∧
    (∀ k, (α k : ℤ) - β k = A.a k - B.a k) ∧ divCycle P f = divCycle P g ∧
    ∀ z ∈ mcPts P, ‖eval z (map (Int.castRingHom ℂ) f)‖ * B.h z = ‖eval z (map (Int.castRingHom ℂ) g)‖ * A.h z

end Objects

def IsomInvariance.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ), IsIntersectionFamily I →
    ∀ (P : Ideal (MRing ι)) (n : ℕ) (L L' : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι),
      IsArithVar P n → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsSmoothHerm (L' j)) →
      (∀ j, IsIsometricOn P (L j) (L' j)) → I P n L = I P n L'

def GraphIsometric.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι ι₂ : K → Type) [∀ k, Fintype (ι k)] [∀ k, Fintype (ι₂ k)]
    (P : Ideal (MRing ι)) (d : ℕ) (A : ∀ k, ι₂ k → ι k → ℤ) (B₁ : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι₂)
    (B₁' B' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (Sum.elim ι ι₂)),
    IsArithVar P d → IsBasePtFree P (linForm A) → B₁.a = B.a →
    (∀ z ∈ mcPts P, B₁.h z = B.h (linApply A z)) →
    IsPullHerm Sum.inl inlV B₁ B₁' → IsPullHerm Sum.inr inrV B B' →
    IsIsometricOn (graphIdeal P (linForm A)) B₁' B'

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLocalRep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace LocalRep

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]


omit [Fintype K] in
theorem isMultiHomog_mul {f g : MRing ι} {a b : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a)
    (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g b) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]


omit [Fintype K] in
theorem isMultiHomog_add {f g : MRing ι} {a : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a)
    (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g a) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k


omit [Fintype K] in
theorem isMultiHomog_C (r : ℤ) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (C r : MRing ι) 0 := by
  classical
  intro m hm k
  have : m = 0 := by
    by_contra h
    exact (mem_support_iff.mp hm) (by rw [coeff_C, if_neg (Ne.symm h)])
  subst this
  simp


omit [Fintype K] in
theorem isMultiHomog_X [DecidableEq K] (k : K) (i : ι k) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (X ⟨k, i⟩ : MRing ι) (Pi.single k 1) := by
  classical
  intro m hm k'
  rw [MvPolynomial.support_X, Finset.mem_singleton] at hm
  subst hm
  by_cases h : k' = k
  · subst h
    simp [Finsupp.single_apply]
  · have : ∀ j : ι k', (⟨k, i⟩ : Σ k, ι k) ≠ ⟨k', j⟩ := fun j e => h (congrArg Sigma.fst e).symm
    simp [h]

theorem isMultiHomog_chartMono (c : ∀ k, ι k) (e : K → ℕ) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ e k) e := by
  classical
  have key : ∀ s : Finset K, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (∏ k ∈ s, (X ⟨k, c k⟩ : MRing ι) ^ e k)
      (∑ k ∈ s, e k • Pi.single k 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using isMultiHomog_C (ι := ι) 1
    | insert k s hk ih =>
      rw [Finset.prod_insert hk, Finset.sum_insert hk]
      refine isMultiHomog_mul ?_ ih
      induction e k with
      | zero => simpa using isMultiHomog_C (ι := ι) 1
      | succ m ihm =>
        rw [pow_succ, succ_nsmul]
        exact isMultiHomog_mul ihm (isMultiHomog_X k (c k))
  have h : (∑ k, e k • (Pi.single k 1 : K → ℕ)) = e := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  have := key Finset.univ
  rwa [h] at this

theorem exists_form_of_mem_chartRingZ (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    {x : Ω} (hx : x ∈ chartRingZ y c) :
    ∃ (N : K → ℕ) (H : MRing ι), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog H N ∧ aeval y H = x * ∏ k, y ⟨k, c k⟩ ^ N k := by
  classical
  induction hx using Algebra.adjoin_induction with
  | mem u hu =>
    obtain ⟨⟨k, i⟩, rfl⟩ := hu
    refine ⟨Pi.single k 1, X ⟨k, i⟩, isMultiHomog_X k i, ?_⟩
    rw [aeval_X, Finset.prod_eq_single k (fun b _ hb => by simp [hb]) (by simp)]
    simp only [Pi.single_eq_same, pow_one]
    exact (div_mul_cancel₀ _ (hc k)).symm
  | algebraMap r =>
    exact ⟨0, C r, isMultiHomog_C r, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨N₁, H₁, h₁, e₁⟩ := hu
    obtain ⟨N₂, H₂, h₂, e₂⟩ := hv
    refine ⟨N₁ + N₂, H₁ * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ N₂ k + H₂ * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ N₁ k,
      isMultiHomog_add (isMultiHomog_mul h₁ (isMultiHomog_chartMono c N₂))
        (add_comm N₂ N₁ ▸ isMultiHomog_mul h₂ (isMultiHomog_chartMono c N₁)), ?_⟩
    simp only [map_add (f := _), map_mul, map_prod, map_pow, aeval_X, e₁, e₂, Pi.add_apply, pow_add,
      Finset.prod_mul_distrib]
    ring
  | mul u v _ _ hu hv =>
    obtain ⟨N₁, H₁, h₁, e₁⟩ := hu
    obtain ⟨N₂, H₂, h₂, e₂⟩ := hv
    refine ⟨N₁ + N₂, H₁ * H₂, isMultiHomog_mul h₁ h₂, ?_⟩
    simp only [map_mul, e₁, e₂, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    ring

theorem proof : LocalRep.Statement := by
  intro K _ ι _ Ω _ y a n s z hs hz
  classical
  choose c hzc using hz.1
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := by
    intro k h0
    apply hzc k
    have hmem : (X ⟨k, c k⟩ : MRing ι) ∈ mCoordIdeal y := by
      show mConeMap y (X ⟨k, c k⟩) = 0
      simp [mConeMap, h0]
    simpa using hz.2 _ hmem
  obtain ⟨N, H, hH, he⟩ := exists_form_of_mem_chartRingZ y c hyc (hs c hyc)
  refine ⟨N + fun k => ((n : ℤ) * a k).toNat, N + fun k => (-((n : ℤ) * a k)).toNat,
    H * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ ((n : ℤ) * a k).toNat,
    ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ (N + fun k => (-((n : ℤ) * a k)).toNat) k,
    isMultiHomog_mul hH (isMultiHomog_chartMono c _), isMultiHomog_chartMono c _, fun k => ?_, ?_, ?_⟩
  · simp only [Pi.add_apply]
    push_cast
    omega
  · simp only [map_mul, map_prod, map_pow, aeval_X]
    rw [he, mul_assoc, mul_assoc, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hyc k), ← zpow_add₀ (hyc k)]
    congr 1
    simp only [Pi.add_apply]
    push_cast
    omega
  · simp only [map_prod, map_pow, map_X, eval_X]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hzc k)

end LocalRep

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IsBoundedAtOfIsBoundedH
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory

noncomputable section

section Objects

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def IsBoundedAt (y : (Σ k, ι k) → Ω) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (τ : ℕ) (c : ℝ) (s : Ω) (z : (Σ k, ι k) → ℂ) : Prop :=
  ∀ (dg dh : K → ℕ) (g h : MRing ι),
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g dg → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog h dh → (∀ k, (dg k : ℤ) = dh k + τ * A.a k) →
    aeval y g = s * aeval y h →
    ‖eval z (map (Int.castRingHom ℂ) g)‖ ≤ c * ‖eval z (map (Int.castRingHom ℂ) h)‖ * A.h z ^ τ

def secNormAt (y : (Σ k, ι k) → Ω) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (τ : ℕ) (s : Ω) (z : (Σ k, ι k) → ℂ) : ℝ :=
  sInf {c : ℝ | 0 ≤ c ∧ IsBoundedAt y A τ c s z}

def sectionL2Norm (μ : Measure ((Σ k, ι k) → ℂ)) (y : (Σ k, ι k) → Ω) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (τ : ℕ) (s : Ω) : ℝ :=
  Real.sqrt (∫ z, secNormAt y A τ s z ^ 2 ∂μ)

def IsZariskiDenseMeasure (P : Ideal (MRing ι)) (μ : Measure ((Σ k, ι k) → ℂ)) : Prop :=
  ∀ (d : K → ℕ) (f : MRingOver ℂ ι), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f d → (∀ᵐ z ∂μ, eval z f = 0) →
    ∀ z ∈ mcPts P, eval z f = 0

theorem isBoundedAt_of_isBoundedH {P : Ideal (MRing ι)} {y : (Σ k, ι k) → Ω} {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {τ : ℕ} {c : ℝ}
    {s : Ω} (hs : IsBoundedH P y A τ c s) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) : IsBoundedAt y A τ c s z :=
  fun dg dh g h hg hh hd he => hs dg dh g h z hg hh hd he hz

theorem secNormAt_le {y : (Σ k, ι k) → Ω} {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {τ : ℕ} {c : ℝ} {s : Ω} {z : (Σ k, ι k) → ℂ}
    (hc : 0 ≤ c) (hs : IsBoundedAt y A τ c s z) : secNormAt y A τ s z ≤ c :=
  csInf_le ⟨0, fun _ hx => hx.1⟩ ⟨hc, hs⟩

theorem secNormAt_nonneg (y : (Σ k, ι k) → Ω) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (τ : ℕ) (s : Ω) (z : (Σ k, ι k) → ℂ) :
    0 ≤ secNormAt y A τ s z := by
  rcases Set.eq_empty_or_nonempty {c : ℝ | 0 ≤ c ∧ IsBoundedAt y A τ c s z} with h | h
  · simp [secNormAt, h]
  · exact le_csInf h fun _ hx => hx.1

end Objects

def SectionL2Lattice.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y → ContinuousOn A.h {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} →
    ∀ μ : Measure ((Σ k, ι k) → ℂ), IsProbabilityMeasure μ → μ (mcPts (mCoordIdeal y))ᶜ = 0 →
      IsZariskiDenseMeasure (mCoordIdeal y) μ →
    ∃ (r : ℕ → ℕ) (φ : ∀ n : ℕ, chartLat y A.a n →+ EuclideanSpace ℝ (Fin (r n))),
      (∀ n, Function.Injective (φ n)) ∧
      (∀ n, DiscreteTopology (imageLattice (φ n))) ∧
      (∀ n [DiscreteTopology (imageLattice (φ n))], IsZLattice ℝ (imageLattice (φ n))) ∧
      (∀ (n : ℕ) (c : ℝ) (s : chartLat y A.a n), 0 ≤ c →
        IsBoundedH (mCoordIdeal y) y A n c (s : Ω) → ‖φ n s‖ ≤ c) ∧
      (∀ (n k : ℕ) (s : chartLat y A.a n) (t : chartLat y A.a k) (st : chartLat y A.a (n + k)),
        IsSmallH (mCoordIdeal y) y A k (t : Ω) → (st : Ω) = s * t → ‖φ (n + k) st‖ ≤ ‖φ n s‖) ∧
      (∃ C : ℝ, ∀ n : ℕ, (r n : ℝ) ≤ C * ((n : ℝ) + 1) ^ D) ∧
      ∀ (n : ℕ) (s : chartLat y A.a n), ‖φ n s‖ = sectionL2Norm μ y A n (s : Ω)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMetricMaxComparison
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem MetricMaxComparison.proof : MetricMaxComparison.Statement := by
  intro K _ ι _ A hA

  let blk : (k : K) → ((Σ k, ι k) → ℂ) → (ι k → ℂ) := fun k z i => z ⟨k, i⟩
  have hblkc : ∀ k, Continuous (blk k) := fun k => continuous_pi fun i => continuous_apply _
  let S : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, ‖blk k z‖ = 1}
  have hSc : IsCompact S := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · have hS : S = ⋂ k, (fun z => ‖blk k z‖) ⁻¹' {1} := by ext z; simp [S]
      rw [hS]
      exact isClosed_iInter fun k => isClosed_singleton.preimage (hblkc k).norm
    · refine (Metric.isBounded_closedBall (x := (0 : (Σ k, ι k) → ℂ)) (r := 1)).subset fun z hz => ?_
      rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
      intro p
      calc ‖z p‖ = ‖blk p.1 z p.2‖ := rfl
        _ ≤ ‖blk p.1 z‖ := norm_le_pi_norm _ _
        _ = 1 := hz p.1
  have hSU : S ⊆ {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    intro z hz k
    by_contra h
    simp only [not_exists, not_not] at h
    have h0 : blk k z = 0 := funext h
    have h1 : ‖blk k z‖ = 1 := hz k
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  obtain ⟨C0, hC0⟩ := hSc.exists_bound_of_continuousOn (hA.continuousOn.mono hSU)
  refine ⟨max C0 1, le_max_right _ _, fun z hz => ?_⟩
  have hn : ∀ k, 0 < ‖blk k z‖ := fun k => by
    obtain ⟨i, hi⟩ := hz k
    exact norm_pos_iff.mpr fun h0 => hi (congrFun h0 i)
  let c : K → ℂ := fun k => ((‖blk k z‖⁻¹ : ℝ) : ℂ)
  have hc0 : ∀ k, c k ≠ 0 := fun k => by
    simp only [c, ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]
    exact (hn k).ne'
  have hcn : ∀ k, ‖c k‖ = ‖blk k z‖⁻¹ := fun k => by
    simp only [c, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_pos (inv_pos.mpr (hn k))
  have hwS : (fun p : Σ k, ι k => c p.1 * z p) ∈ S := fun k => by
    have h1 : blk k (fun p : Σ k, ι k => c p.1 * z p) = c k • blk k z := rfl
    rw [h1, norm_smul, hcn, inv_mul_cancel₀ (hn k).ne']
  have hmax : (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofMetrics (fun k => maxMetric (C := ℂ) (ι := ι k)) A.a).h z = ∏ k, ‖blk k z‖ ^ A.a k := rfl
  have hprod : (∏ k, ‖blk k z‖ ^ A.a k) * (∏ k, ‖c k‖ ^ A.a k) = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun k _ => ?_
    rw [hcn, ← mul_zpow, mul_inv_cancel₀ (hn k).ne', one_zpow]
  have hz' : A.h z = (∏ k, ‖blk k z‖ ^ A.a k) * A.h (fun p : Σ k, ι k => c p.1 * z p) := by
    rw [A.smul c z hc0, ← mul_assoc, hprod, one_mul]
  have hpos : 0 ≤ ∏ k, ‖blk k z‖ ^ A.a k :=
    Finset.prod_nonneg fun k _ => zpow_nonneg (norm_nonneg _) _
  have hbw : A.h (fun p : Σ k, ι k => c p.1 * z p) ≤ max C0 1 := by
    have h1 := hC0 _ hwS
    rw [Real.norm_eq_abs] at h1
    exact (le_abs_self _).trans (h1.trans (le_max_left _ _))
  rw [hmax, hz', mul_comm (max C0 1)]
  exact mul_le_mul_of_nonneg_left hbw hpos

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenDegGeomDeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

theorem GenDegGeomDeg.proof (hDG : GroundTheory.Heights₂.Heights.Inter.DegreeGeneric.Statement) :
    GenDegGeomDeg.Statement := by
  intro K _ ι _ Ω _ y D A hV hA
  classical
  have h := hDG K ι (mCoordIdeal y) D (fun _ => A) hV (fun _ => hA)
  have hpot : pot (fun _ : Fin D => A) = fun (_ : Fin D) z => Real.log (A.h z) := rfl
  rw [hpot] at h
  unfold geomDeg genDeg
  rw [h]

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHyperplaneQuotientBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

def chartDivSec {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (b : K → ℤ) : Submodule ℚ (chartLatQ y b 1) :=
  (Submodule.map (LinearMap.mulLeft ℚ (∏ k, y ⟨k, c k⟩)) (chartLatQ y (b - 1) 1)).comap
    (chartLatQ y b 1).subtype

def HyperplaneQuotientBound.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (a : K → ℤ) (c : ∀ k, ι k),
    1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) → Birational y → (∀ k, y ⟨k, c k⟩ ≠ 0) →
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a) 1 ⧸ chartDivSec y c ((n : ℤ) • a)) : ℝ) ≤
        C * (n : ℝ) ^ (D - 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFrameGraph
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section


open Classical in
def projMat {κ : Type} {D : ℕ} (e : Fin (D + 1) → Ix κ) : ∀ _ : Unit, Fin (D + 1) → κ → ℤ :=
  fun _ k i => if (e k).2 = i then 1 else 0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

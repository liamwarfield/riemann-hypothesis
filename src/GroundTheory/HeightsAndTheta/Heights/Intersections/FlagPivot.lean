module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.ProjLineRankTwoPushforwardHypotheses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KappaB
public import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Assembly
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.SwapLoc

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.FlagPivot
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial

def pivotCols {n : ℕ} (a : Fin (n - 1)) (b : Fin n) : Fin (a + 1) → Fin n :=
  fun c => if h : (c : ℕ) < a then ⟨c, by have := a.2; omega⟩ else b

def pivotMinor {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (a : Fin (n - 1)) (b : Fin n) : R :=
  (M.submatrix (Fin.castLE (by have := a.2; omega)) (pivotCols a b)).det

def leadMinor {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (a : Fin (n - 1)) : R :=
  pivotMinor M a (Fin.castLE (Nat.sub_le n 1) a)

def pivotMatrix {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun r b => if h : (r : ℕ) < n - 1 then pivotMinor M ⟨r, h⟩ b else 0

theorem pivotCols_strictMono {n : ℕ} (a : Fin (n - 1)) (b : Fin n) (hab : (a : ℕ) ≤ b) :
    StrictMono (pivotCols a b) := by
  intro c d hcd
  have hcd' : (c : ℕ) < d := hcd
  simp only [pivotCols]
  split_ifs with h1 h2 h2
  · exact Fin.mk_lt_mk.mpr hcd'
  · exact Fin.mk_lt_mk.mpr (by omega)
  · omega
  · omega

theorem card_image_pivotCols {n : ℕ} (a : Fin (n - 1)) (b : Fin n) (hab : (a : ℕ) ≤ b) :
    (Finset.univ.image (pivotCols a b)).card = a + 1 := by
  rw [Finset.card_image_of_injective _ (pivotCols_strictMono a b hab).injective, Finset.card_univ, Fintype.card_fin]

theorem pivotMinor_eq_flagMinor {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (a : Fin (n - 1))
    (b : Fin n) (hab : (a : ℕ) ≤ b) :
    pivotMinor M a b = flagMinor M a ⟨Finset.univ.image (pivotCols a b), card_image_pivotCols a b hab⟩ := by
  unfold pivotMinor flagMinor
  congr 2
  exact (Finset.orderEmbOfFin_unique (card_image_pivotCols a b hab) (fun c => Finset.mem_image_of_mem _ (Finset.mem_univ c))
    (pivotCols_strictMono a b hab))

theorem pivotMinor_eq_zero {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (a : Fin (n - 1))
    (b : Fin n) (hba : (b : ℕ) < a) : pivotMinor M a b = 0 := by
  unfold pivotMinor
  refine Matrix.det_zero_of_column_eq (i := ⟨b, by omega⟩) (j := Fin.last a) (fun h => by
    have := congrArg Fin.val h; simp at this; omega) fun k => ?_
  simp [pivotCols, hba]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.IsFieldIntersectionNoBlockFam
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

def GenDegAt (I : AllFam) (d : ℕ) : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι'))
    (G : GenFibre v P') (J : IFamily G.Φ (fibreIdx ι' κ))
    (L : Fin d → HermLine ι) (L' : Fin d → HermLine ι'),
    IsBlockMap κ v → IsArithVar P' d → IsArithVar (imageZ v P') d → IsFieldIntersection J →
    (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) →
    I K' ι' P' d L' = (J (fibreIdeal κ G) 0 Fin.elim0 : ℝ) * I K ι (imageZ v P') d L

def ArithmeticIntersectionCycle.Statement : Prop :=
  ∀ (I : AllFam), I.IsFamily → ∀ n : ℕ, GenDegAt I n →
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
      (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι'))
      (G : GenFibre v P') (J : IFamily G.Φ (fibreIdx ι' κ))
      (L : Fin n → HermLine ι) (L' : Fin n → HermLine ι') (s : MRing ι) (α : K → ℕ),
      IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) → IsFieldIntersection J →
      (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) →
      IsMultiHomog s α → s ∉ imageZ v P' →
      cycR (I K' ι') P' L' (rename v s) =
        (J (fibreIdeal κ G) 0 Fin.elim0 : ℝ) * cycR (I K ι) (imageZ v P') L s

def ArithmeticIntersectionIntegral.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ)
    (G : GenFibre v P') (J : IFamily G.Φ (fibreIdx ι' κ))
    (L : Fin n → HermLine ι) (L' : Fin n → HermLine ι') (A : HermLine ι) (A' : HermLine ι') (f g : MRing ι),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) → IsFieldIntersection J →
    (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) → IsSmoothHerm A → IsPullHerm κ v A A' →
    IsRatSectionOn (imageZ v P') A f g →
    ptsIntegral P' (pot L') (logNormRat A' (rename v f) (rename v g)) =
      (J (fibreIdeal κ G) 0 Fin.elim0 : ℝ) * ptsIntegral (imageZ v P') (pot L) (logNormRat A f g)

section Inhabitants

open IndefiniteRowSideFullHecke.Inter

variable {F : Type} [Field F] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PHorizNotMem
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

theorem HorizNotMem.ringKrullDim_quotient_add_one_le {R : Type*} [CommRing R] {W₀ W : Ideal R}
    [hW₀ : W₀.IsPrime] [hW : W.IsPrime] (hlt : W₀ < W) :
    ringKrullDim (R ⧸ W) + 1 ≤ ringKrullDim (R ⧸ W₀) := by
  rw [ringKrullDim_quotient, ringKrullDim_quotient]
  have : Nonempty (PrimeSpectrum.zeroLocus (R := R) W) :=
    ⟨⟨⟨W, hW⟩, fun _ h => h⟩⟩
  rw [← Order.krullDim_withBot]
  let f : WithBot (PrimeSpectrum.zeroLocus (R := R) W) → PrimeSpectrum.zeroLocus (R := R) W₀ :=
    fun x => WithBot.recBotCoe ⟨⟨W₀, hW₀⟩, fun _ h => h⟩ (fun q => ⟨q.1, fun _ h => q.2 (hlt.le h)⟩) x
  refine Order.krullDim_le_of_strictMono f ?_
  intro a b hab
  induction a using WithBot.recBotCoe with
  | bot =>
    induction b using WithBot.recBotCoe with
    | bot => exact absurd hab (lt_irrefl _)
    | coe q =>
      change (⟨⟨W₀, hW₀⟩, _⟩ : PrimeSpectrum.zeroLocus (R := R) W₀) < ⟨q.1, _⟩
      exact Subtype.mk_lt_mk.mpr ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).mp
        (hlt.trans_le (fun _ h => q.2 h)))
  | coe p =>
    induction b using WithBot.recBotCoe with
    | bot => exact absurd hab (WithBot.not_lt_bot _)
    | coe q =>
      change (⟨p.1, _⟩ : PrimeSpectrum.zeroLocus (R := R) W₀) < ⟨q.1, _⟩
      exact Subtype.mk_lt_mk.mpr (Subtype.mk_lt_mk.mp (WithBot.coe_lt_coe.mp hab))

theorem HorizNotMem.proof : HorizNotMem.Statement := by
  intro K _ ι _ P d s s' W hP hsP hs'P hnc hW hWh hs'W
  have : P.IsPrime := hP.2.1.1
  have hWp : W.IsPrime := hW.1.1.1
  have hle : P ⊔ Ideal.span {s'} ≤ W :=
    sup_le (le_sup_left.trans hW.1.1.2) ((Ideal.span_singleton_le_iff_mem _).mpr hs'W)
  obtain ⟨W₀, hW₀, hW₀W⟩ := Ideal.exists_minimalPrimes_le hle
  have : W₀.IsPrime := hW₀.1.1
  have h1 := dim_quot_minimal_add_one P W s hsP hW.1
  have h2 := dim_quot_minimal_add_one P W₀ s' hs'P hW₀
  have heq : W₀ = W := by
    by_contra hne
    have hstep := HorizNotMem.ringKrullDim_quotient_add_one_le (lt_of_le_of_ne hW₀W hne)
    have h3 := add_le_add hstep (le_refl (1 : WithBot ℕ∞))
    rw [h1, h2, hP.2.2.2] at h3
    have h4 : ((d + Fintype.card K + 1 : ℕ) : WithBot ℕ∞) ≤ ((d + Fintype.card K : ℕ) : WithBot ℕ∞) := by
      exact_mod_cast h3
    have h5 := WithBot.coe_le_coe.mp h4
    have h6 : d + Fintype.card K + 1 ≤ d + Fintype.card K := by exact_mod_cast h5
    omega
  exact hnc W hW ⟨heq ▸ hW₀, hW.2⟩ hWh

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTerTer
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityDenominator.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (x : funField P),
    IsArithVar P 1 → ∃ c : funField P, c ≠ 0 ∧ ∀ W, IsClosedPt W → P ≤ W →
      (c : FractionRing (MRing ι ⧸ P)) ∈ locRing P W ∧ ((x * c : funField P) : FractionRing (MRing ι ⧸ P)) ∈ locRing P W

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.TwoMemFunFieldSpecZ
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityFormula.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (b : funField P),
    IsArithVar P 1 → b ≠ 0 → (∀ W, IsClosedPt W → P ≤ W → (b : FractionRing (MRing ι ⧸ P)) ∈ locRing P W) →
    {W | IsClosedPt W ∧ P ≤ W ∧ Nat.card (locRing P W ⧸ locIdeal P W b) ≠ 1}.Finite ∧
      ∑ᶠ W ∈ {W : Ideal (MRing ι) | IsClosedPt W ∧ P ≤ W},
          Real.log (Nat.card (locRing P W ⧸ locIdeal P W b)) =
        ∑ᶠ σ : funField P →+* ℂ, Real.log ‖σ b‖

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StLocRingLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def LocRingLocal.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι)),
    P.IsPrime → W.IsPrime → P ≤ W →
    IsLocalRing (locRing P W) ∧
      ∀ (y : locRing P W) (u v : MRing ι) (a : K → ℕ), IsMultiHomog u a → IsMultiHomog v a → v ∉ W →
        (y : FractionRing (MRing ι ⧸ P)) * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P v) = algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u) →
        (IsUnit y ↔ u ∉ W)

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTerSide
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def regularityLocalCardinality_holds.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (s : MRing ι) (a : K → ℕ) (W : Ideal (MRing ι)) (b : Fin 0 → K → ℤ) (y : FractionRing (MRing ι ⧸ P)),
    IsArithVar P 1 → IsMultiHomog s a → s ∉ P → W ∈ divSupp P s → y ∈ locRing P W → y ≠ 0 →
    ((Module.length (locRing P W) (locRing P W ⧸ locIdeal P W y)).toNat : ℝ) *
        ((geoNum 0 W b : ℝ) * Real.log (charOf W)) =
      Real.log (Nat.card (locRing P W ⧸ locIdeal P W y))

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.FlagBundleSt
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

section Gen

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem aeval_comp_X {σ A B : Type} [CommRing A] [CommRing B] {_ : Algebra ℤ B}
    (φ : MvPolynomial σ ℤ →+* A) (e : A →+* B) (f : MvPolynomial σ ℤ) :
    aeval (fun q => e (φ (X q))) f = e (φ f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [aeval_C]
    exact (eq_intCast (algebraMap ℤ B) a).trans (eq_intCast ((e.comp φ).comp C) a).symm
  | add p q hp hq => rw [map_add (f := _), hp, hq, map_add (f := _), map_add (f := _)]
  | mul_X p q hp => rw [map_mul, hp, aeval_X, map_mul, map_mul]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem aeval_genPt (P : Ideal (MRing ι)) {_ : Algebra ℤ (FnField P)} (f : MRing ι) :
    aeval (genPt P) f = algebraMap (MRing ι ⧸ P) (FnField P) (Ideal.Quotient.mk P f) :=
  aeval_comp_X (Ideal.Quotient.mk P) (algebraMap (MRing ι ⧸ P) (FnField P)) f


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem ker_algebraMap_comp_mk (P : Ideal (MRing ι)) :
    RingHom.ker ((algebraMap (MRing ι ⧸ P) (FnField P)).comp (Ideal.Quotient.mk P)) = P := by
  rw [RingHom.ker_comp_of_injective _ (IsFractionRing.injective (MRing ι ⧸ P) (FnField P)), Ideal.mk_ker]

end Gen

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PFibreLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MeasureTheory MvPolynomial ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

namespace FibreLocal

@[local instance] theorem isProbabilityMeasure_sphere : IsProbabilityMeasure sphereMeasure :=
  sphereInv_thm.1

theorem add_mul_gPoly (k : ℕ) :
    (X 0 + X 1 : MvPolynomial (Fin 2) ℝ) * gPoly k = X 1 * (X 0 ^ (2 * k) - X 1 ^ (2 * k)) := by
  have h := (Commute.all (-(X 1 : MvPolynomial (Fin 2) ℝ)) (X 0)).geom_sum₂_mul (2 * k)
  have hs : ∑ j ∈ Finset.range (2 * k),
      (-1 : ℝ) ^ j • ((X 0 : MvPolynomial (Fin 2) ℝ) ^ (2 * k - 1 - j) * X 1 ^ j) =
      ∑ i ∈ Finset.range (2 * k), (-(X 1 : MvPolynomial (Fin 2) ℝ)) ^ i * X 0 ^ (2 * k - 1 - i) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, map_pow, map_neg, map_one, neg_pow (X 1 : MvPolynomial (Fin 2) ℝ)]
    ring
  rw [gPoly, hs]
  rw [(even_two_mul k).neg_pow] at h
  linear_combination (-(X 1 : MvPolynomial (Fin 2) ℝ)) * h

theorem gPoly_eq (k : ℕ) : gPoly k = FlagBundles.gKernel ℝ k := by
  have hne : (X 0 + X 1 : MvPolynomial (Fin 2) ℝ) ≠ 0 := by
    intro h
    have := congrArg (eval ![1, 0]) h
    simp at this
  exact mul_left_cancel₀ hne (by rw [add_mul_gPoly, (FlagBundles.GKernelIdentity.full ℝ k).1])

theorem dgPoly_eq (k : ℕ) : dgPoly k = FlagBundles.gMixed k := by
  rw [dgPoly, FlagBundles.gMixed, gPoly_eq]

theorem integrable_kernel :
    Integrable (fun p : S2 × S2 => (1 / 2 : ℝ) * Real.log ((1 - inner ℝ (p.1 : E3) (p.2 : E3)) / 2))
      (sphereMeasure.prod sphereMeasure) :=
  FlagBundles.FibreIntegralInvariant.integrable_kernel FlagBundles.FibreConstantClosedForm.full

theorem integrable_mul (f : S2 × S2 → ℝ) (hf : Continuous f) :
    Integrable (fun p : S2 × S2 =>
      (1 / 2 : ℝ) * Real.log ((1 - inner ℝ (p.1 : E3) (p.2 : E3)) / 2) * f p)
      (sphereMeasure.prod sphereMeasure) :=
  FlagBundles.FibreIntegralInvariant.integrable_term integrable_kernel f hf

theorem continuous_evalPair (g : MvPolynomial (Fin 2) ℝ) (u v : S2 × S2 → ℝ) (hu : Continuous u)
    (hv : Continuous v) : Continuous fun p => eval ![u p, v p] g := by
  have h2 : Continuous fun p => (![u p, v p] : Fin 2 → ℝ) := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · simpa using hu
    · simpa using hv
  exact (MvPolynomial.continuous_eval g).comp h2

theorem kappa_eq (k : ℕ) : kappa k = -FlagBundles.fibreConstant k := by
  have hc : Continuous fun p : S2 × S2 => eval ![(p.1 : E3) 2, (p.2 : E3) 2] (dgPoly k) :=
    continuous_evalPair _ _ _ ((EuclideanSpace.proj (2 : Fin 3)).continuous.comp
      (continuous_subtype_val.comp continuous_fst))
      ((EuclideanSpace.proj (2 : Fin 3)).continuous.comp (continuous_subtype_val.comp continuous_snd))
  rw [kappa, FlagBundles.fibreConstant, neg_inj]
  refine (integral_prod _ (integrable_mul _ hc)).symm.trans ?_
  simp_rw [dgPoly_eq]
  rfl

theorem sphere_moment (a : E3) (m : ℕ) :
    ∫ n : S2, inner ℝ a (n : E3) ^ (2 * m) ∂sphereMeasure = inner ℝ a a ^ m / (2 * m + 1) := by
  by_cases ha : a = 0
  · subst ha
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · simp [inner_zero_left, zero_pow (by omega : 2 * m ≠ 0), zero_pow (by omega : m ≠ 0)]
  · set r : ℝ := ‖a‖ with hr
    have hr0 : r ≠ 0 := norm_ne_zero_iff.mpr ha
    set u : E3 := r⁻¹ • a with hu
    have hu1 : ‖u‖ = 1 := by rw [hu, norm_smul, norm_inv, norm_norm, ← hr, inv_mul_cancel₀ hr0]
    have hin : ∀ n : S2, inner ℝ a (n : E3) = r * inner ℝ (n : E3) u := by
      intro n
      rw [hu, inner_smul_right, real_inner_comm, ← mul_assoc, mul_inv_cancel₀ hr0, one_mul]
    have hA := (archimedes_thm u u u (fun t => (r * t) ^ (2 * m)) hu1
      (Continuous.intervalIntegrable (by fun_prop) _ _)).2.1
    simp_rw [hin]
    rw [hA]
    simp_rw [mul_pow]
    rw [intervalIntegral.integral_const_mul, integral_pow, real_inner_self_eq_norm_sq, ← hr]
    have h1 : ((-1 : ℝ)) ^ (2 * m + 1) = -1 := by rw [pow_succ, (even_two_mul m).neg_one_pow]; ring
    rw [h1, ← pow_mul]
    push_cast
    field_simp
    ring

theorem eval_momentPoly {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (w : Ω → ℝ)
    (Q : MvPolynomial (Fin 3) (Ω → ℝ)) (hQ : ∀ m, Integrable (fun p => w p * AddMonoidAlgebra.coeff Q m p) μ)
    (a : Fin 3 → ℝ) :
    eval a (momentPoly μ w Q) = ∫ p, w p * eval₂ (Pi.evalRingHom (fun _ : Ω => ℝ) p) a Q ∂μ := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [momentPoly, map_sum]
  simp only [eval_monomial]
  simp_rw [← integral_mul_const]
  rw [← integral_finsetSum _ (fun m _ => (hQ m).mul_const _)]
  congr 1
  funext p
  rw [eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [Finsupp.prod]
  ring

def coordS (i : Fin 3) : C(S2, ℝ) :=
  ⟨fun n => (n : E3) i, (EuclideanSpace.proj i).continuous.comp continuous_subtype_val⟩

theorem dotPoly_id_pow (N : ℕ) :
    (dotPoly (id : S2 → S2)) ^ N =
      MvPolynomial.map (ContinuousMap.coeFnRingHom : C(S2, ℝ) →+* (S2 → ℝ)) ((∑ i, X i * C (coordS i)) ^ N) := by
  rw [map_pow, dotPoly]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_X, map_C]
  rfl

theorem pushMomentPoly_eq (k : ℕ) (hk : 1 ≤ k) :
    pushMomentPoly k = -(∑ i, X i ^ 2) ^ (k - 1) := by
  apply MvPolynomial.funext
  intro a
  have hQ : ∀ m, Integrable (fun p : S2 => (1 : ℝ) * AddMonoidAlgebra.coeff ((dotPoly (id : S2 → S2)) ^ (2 * k - 2)) m p)
      sphereMeasure := by
    intro m
    rw [dotPoly_id_pow, coeff_map]
    simp only [one_mul]
    exact (ContinuousMap.continuous (AddMonoidAlgebra.coeff ((∑ i, X i * C (coordS i)) ^ (2 * k - 2)) m)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [pushMomentPoly, smul_eval, eval_momentPoly _ _ _ hQ]
  have he : ∀ p : S2, eval₂ (Pi.evalRingHom (fun _ : S2 => ℝ) p) a ((dotPoly id) ^ (2 * k - 2)) =
      inner ℝ (WithLp.toLp 2 a : E3) (p : E3) ^ (2 * k - 2) := by
    intro p
    rw [eval₂_pow, dotPoly]
    simp [eval₂_sum, PiLp.inner_apply, mul_comm]
  simp_rw [he, one_mul]
  have hkk : 2 * k - 2 = 2 * (k - 1) := by omega
  rw [hkk, sphere_moment]
  have haa : inner ℝ (WithLp.toLp 2 a : E3) (WithLp.toLp 2 a) = ∑ i, a i ^ 2 := by
    rw [real_inner_self_eq_norm_sq, EuclideanSpace.norm_sq_eq]
    simp [sq_abs]
  rw [haa]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_neg, map_pow, map_sum, eval_X]
  have hc : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub hk, Nat.cast_one]
  rw [hc]
  have hk' : (2 * ((k : ℝ) - 1) + 1) ≠ 0 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  field_simp
  ring

theorem fibreMomentPoly_eq (k : ℕ) : fibreMomentPoly k = FlagBundles.fibrePoly k := by
  have hQ : aeval ![dotPoly (Prod.fst : S2 × S2 → S2), dotPoly Prod.snd] (dgPoly k) =
      FlagBundles.FibreIntegralInvariant.fibreQ k := by
    rw [FlagBundles.FibreIntegralInvariant.fibreQ, dgPoly_eq]
    refine congrArg (fun x => aeval x (FlagBundles.gMixed k)) ?_
    funext r
    fin_cases r <;> simp [dotPoly]
  rw [FlagBundles.FibreIntegralInvariant.fibrePoly_eq, fibreMomentPoly, momentPoly, hQ]
  rfl

theorem proof : FibreLocal.Statement := by
  refine ⟨fun k a => ?_, fun k B _ _ a => ?_, fun k hk a => ?_, fun k hk B _ _ a => ?_, fun k => ?_⟩
  · have hc : Continuous fun p : S2 × S2 => eval ![inner ℝ a (p.1 : E3), inner ℝ a (p.2 : E3)] (dgPoly k) :=
      continuous_evalPair _ _ _ (continuous_const.inner (continuous_subtype_val.comp continuous_fst))
        (continuous_const.inner (continuous_subtype_val.comp continuous_snd))
    refine (integral_prod _ (integrable_mul _ hc)).symm.trans ?_
    simp_rw [dgPoly_eq]
    rw [kappa_eq, neg_neg]
    exact FlagBundles.FibreIntegralInvariant.full.1 k a
  · rw [fibreMomentPoly_eq, FlagBundles.FibreIntegralInvariant.full.2 k B a, kappa_eq, neg_neg]
  · have hkk : 2 * k - 2 = 2 * (k - 1) := by omega
    rw [hkk, sphere_moment]
    have hc : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub hk, Nat.cast_one]
    rw [hc]
    have hk' : (2 * ((k : ℝ) - 1) + 1) ≠ 0 := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    field_simp
    ring
  · rw [pushMomentPoly_eq k hk]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_neg, map_pow, map_sum, aeval_X]
  · rw [kappa_eq, FlagBundles.fibreConstant_eq]
    ring

end FibreLocal

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StRegCurvBound
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def RegCurvBound.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (E : HermLine ι) (t : MRing ι)
    (ht : ∃ a : K → ℕ, (∀ k, E.a k = a k) ∧ IsMultiHomog t a),
    IsSmoothHerm E → ∃ C : ℕ, ∀ ε : ℝ, 0 < ε →
      IsSemiPosHerm ((E.tensor (regLine E t ht ε)).tensor
        (HermLine.ofMetrics (fun k => fsMetric (ι := ι k)) (fun _ => (C : ℤ))))

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StPtsMonoSemiPos
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def PtsMonoSemiPos.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Q : Ideal (MRing ι)) (e : ℕ)
    (M : Fin e → HermLine ι) (E D : HermLine ι) (t : MRing ι),
    IsArithVar Q (e + 1) → (∀ j, IsSmoothHerm (M j)) → (∀ j, IsSemiPosHerm (M j)) →
    IsSmoothHerm E → IsSectionOn Q E t → IsSmoothHerm D → D.a = 0 →
    (∀ z ∈ mcPts Q, eval z (map (Int.castRingHom ℂ) t) ≠ 0 → logNorm E t z ≤ Real.log (D.h z)) →
    ptsIntegral Q (pot M) (logNorm E t) ≤ ptsIntegral Q (pot M) (fun z => Real.log (D.h z))

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StPtsRegLimit
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def PtsRegLimit.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Q : Ideal (MRing ι)) (e : ℕ)
    (M : Fin e → HermLine ι) (E : HermLine ι) (t : MRing ι)
    (ht : ∃ a : K → ℕ, (∀ k, E.a k = a k) ∧ IsMultiHomog t a),
    IsArithVar Q (e + 1) → (∀ j, IsSmoothHerm (M j)) → IsSmoothHerm E → t ∉ Q →
    Filter.Tendsto (fun ε => ptsIntegral Q (pot M) (fun z => Real.log ((regLine E t ht ε).h z)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (ptsIntegral Q (pot M) (logNorm E t)))

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StPtsAbsMeasurable
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

def PtsAbsMeasurable.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (L : Fin e → HermLine ι) (A : HermLine ι)
    (s : MRing ι),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A →
    IsSectionOn P A s →
    AEStronglyMeasurable (fun y => ∑ᶠ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y, |sheetDensity P Ψ (pot L) (logNorm A s) y w|)

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTerExtra
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def regularityLocalDimension_holds.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (s : MRing ι) (a : K → ℕ) (W : Ideal (MRing ι)),
    IsArithVar P 1 → IsMultiHomog s a → s ∉ P → W ∈ divSupp P s →
    IsLocalRing (locRing P W) ∧ IsNoetherianRing (locRing P W) ∧ ringKrullDim (locRing P W) = 1

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsFurtherTail
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def pointForm_holds.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (d n : ℕ)
    (L : Fin n → HermLine ι) (L' : Fin n → HermLine ι') (g : ((Σ k', ι' k') → ℂ) → ℝ),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') d → d < n + 1 →
    (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) →
    ptsIntegral P' (fun j z => Real.log ((L' j).h z)) g = 0

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiHomogFirstCoordinate
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

def ProjectivePointVertical.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (d n : ℕ)
    (L : Fin n → HermLine ι) (L' : Fin n → HermLine ι') (t : MRing ι) (a : K → ℕ),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') d → d < n + 1 →
    (∀ j, IsPullHerm κ v (L j) (L' j)) → IsMultiHomog t a → t ∉ imageZ v P' →
    vertR P' L' (rename v t) = 0

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTerRest
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def regularityLocalResidue_holds.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (s : MRing ι) (a : K → ℕ) (W : Ideal (MRing ι)) (b : Fin 0 → K → ℤ),
    IsArithVar P 1 → IsMultiHomog s a → s ∉ P → W ∈ divSupp P s → ∀ [IsLocalRing (locRing P W)],
    Finite (IsLocalRing.ResidueField (locRing P W)) ∧
      Nat.card (IsLocalRing.ResidueField (locRing P W)) = charOf W ^ (geoNum 0 W b).toNat

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.XcNotMemOfIsRelevant
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityLocalProduct.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (f g : MRing ι) (a : K → ℕ) (x : funField P) (t : Ideal (MRing ι) → MRing ι)
    (yf yg : Ideal (MRing ι) → FractionRing (MRing ι ⧸ P)),
    IsArithVar P 1 → IsMultiHomog f a → IsMultiHomog g a → f ∉ P → g ∉ P →
    (x : FractionRing (MRing ι ⧸ P)) *
        algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P g) =
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P f) →
    (∀ W ∈ divSupp P f ∪ divSupp P g, IsMultiHomog (t W) a ∧ t W ∉ W ∧
      yf W * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (t W)) =
        algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P f) ∧
      yg W * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (t W)) =
        algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P g)) →
    ∑ᶠ W ∈ divSupp P f, Real.log (Nat.card (locRing P W ⧸ locIdeal P W (yf W))) -
        ∑ᶠ W ∈ divSupp P g, Real.log (Nat.card (locRing P W ⧸ locIdeal P W (yg W))) =
      ∑ᶠ σ : funField P →+* ℂ, Real.log ‖σ x‖

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.MultAtPosOfMemDivSupp
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem multAt_pos_of_mem_divSupp {P : Ideal (MRing ι)} {s : MRing ι} {W : Ideal (MRing ι)}
    (hW : W ∈ divSupp P s) : 0 < multAt (P ⊔ Ideal.span {s}) W := by
  have hmin := hW.1
  have hWp : W.IsPrime := hmin.1.1
  have hm : IsLocalRing.maximalIdeal (Localization.AtPrime W) ∈
      ((P ⊔ Ideal.span {s}).map (algebraMap (MRing ι) (Localization.AtPrime W))).minimalPrimes := by
    rw [IsLocalization.minimalPrimes_map W.primeCompl (Localization.AtPrime W)]
    rw [Set.mem_preimage, Localization.AtPrime.under_maximalIdeal]
    exact hmin
  have hne := ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc.length_quot_ne_top_of_mem_minimalPrimes _ hm
  have : Nontrivial (Localization.AtPrime W ⧸
      (P ⊔ Ideal.span {s}).map (algebraMap (MRing ι) (Localization.AtPrime W))) :=
    Ideal.Quotient.nontrivial_iff.mpr
      (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top hm.1.2)
  have hpos := Module.length_pos (R := Localization.AtPrime W)
    (M := Localization.AtPrime W ⧸
      (P ⊔ Ideal.span {s}).map (algebraMap (MRing ι) (Localization.AtPrime W)))
  rw [multAt, dite_eq_left hWp, ReciprocityTheory.ChartRestriction.G.AI.I1.inh_length_locQuot]
  exact ENat.toNat_pos hpos.ne' hne

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PrimeComplMapLeNonZeroDivisorsQuot
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo IsLocalRing

noncomputable section

section Cone

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem primeCompl_map_le_nonZeroDivisors_quot (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime]
    (hPW : P ≤ W) : W.primeCompl.map (Ideal.Quotient.mk P) ≤ nonZeroDivisors (MRing ι ⧸ P) := by
  rintro _ ⟨g, hg, rfl⟩
  refine mem_nonZeroDivisors_of_ne_zero ?_
  rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
  exact fun h => hg (hPW h)

def coneLocRing (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) :
    Subalgebra (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) :=
  Localization.subalgebra.ofField _ _ (primeCompl_map_le_nonZeroDivisors_quot P W hPW)

instance coneLocRing.isLocalization (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) :
    IsLocalization (W.primeCompl.map (Ideal.Quotient.mk P)) (coneLocRing P W hPW) :=
  Localization.subalgebra.isLocalization_ofField _ _ _

theorem locRing_le_coneLocRing (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) :
    ∀ x ∈ locRing P W, x ∈ coneLocRing P W hPW := by
  intro x hx
  have hle : locRing P W ≤ (coneLocRing P W hPW).toSubring := by
    refine Subring.closure_le.mpr ?_
    rintro _ ⟨u, v, a, hv, hvW, -, -, rfl⟩
    exact ⟨Ideal.Quotient.mk P u, Ideal.Quotient.mk P v, ⟨v, hvW, rfl⟩,
      by rw [IsFractionRing.mk'_eq_div, div_eq_mul_inv]⟩
  exact hle hx

def locRingToCone (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) :
    locRing P W →+* coneLocRing P W hPW :=
  (locRing P W).subtype.codRestrict (coneLocRing P W hPW)
    (fun x => locRing_le_coneLocRing P W hPW x x.2)

instance locRing.algebraCone (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) :
    Algebra (locRing P W) (coneLocRing P W hPW) :=
  (locRingToCone P W hPW).toAlgebra

theorem locRing.algebraMap_cone_coe (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W)
    (x : locRing P W) :
    ((algebraMap (locRing P W) (coneLocRing P W hPW) x : coneLocRing P W hPW) :
      FractionRing (MRing ι ⧸ P)) = x :=
  rfl

end Cone

def regularityLocalFlat_holds.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι))
    (hP : IsMultiProjPrime P) (hW : IsMultiProjPrime W) (hPW : P ≤ W),
    haveI := hP.1
    haveI := hW.1
    ∃ (_ : IsLocalRing (locRing P W)) (_ : IsLocalRing (coneLocRing P W hPW)),
      Module.Flat (locRing P W) (coneLocRing P W hPW) ∧
        (maximalIdeal (locRing P W)).map (algebraMap (locRing P W) (coneLocRing P W hPW)) =
          maximalIdeal (coneLocRing P W hPW)

end

end GroundTheory.Heights₂.Heights.Inter
end

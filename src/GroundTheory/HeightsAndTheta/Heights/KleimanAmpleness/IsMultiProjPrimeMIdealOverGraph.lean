module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsGraphGenTwistBundleZero
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.BaseComap
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleZFamily
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ConstVanishHypSegment

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsMultiProjPrimeMIdealOverGraph
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mConeMapOver mIdealOver)

noncomputable section

section Homog

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω]

theorem sum_block_eq_blockWeight (e : (Σ k, ι k) →₀ ℕ) (k : K) :
    ∑ i, e ⟨k, i⟩ = Finsupp.weight (NumbersDVR.blockWeight ι) e k := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma]
  simp [NumbersDVR.blockWeight, Pi.single_apply]


omit [DecidableEq K] in
theorem mConeMapOver_eq_of_block (y : (Σ k, ι k) → Ω) {f : MvPolynomial (Σ k, ι k) S} {d : K → ℕ}
    (hf : ∀ e ∈ f.support, ∀ k, ∑ i, e ⟨k, i⟩ = d k) :
    mConeMapOver S y f = MvPolynomial.C (aeval y f) * ∏ k, MvPolynomial.X k ^ d k := by
  classical
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun e he => ?_
  have hX : ∏ p : (Σ k, ι k), (MvPolynomial.X p.1 : MvPolynomial K Ω) ^ e p =
      ∏ k, MvPolynomial.X k ^ d k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, (MvPolynomial.X k : MvPolynomial K Ω) ^ e ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hf e he k]
  simp only [mConeMapOver, aeval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun i => by simp), Finsupp.prod_fintype _ _ (fun i => by simp)]
  simp only [mul_pow, Finset.prod_mul_distrib, hX, map_mul, map_prod, map_pow,
    MvPolynomial.algebraMap_apply]
  ring

theorem coeff_mConeMapOver (y : (Σ k, ι k) → Ω) (b : K → ℕ) (f : MvPolynomial (Σ k, ι k) S) :
    AddMonoidAlgebra.coeff (mConeMapOver S y f) (Finsupp.equivFunOnFinite.symm b) =
      aeval y (weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f) := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial e c =>
    have hm := isWeightedHomogeneous_monomial (NumbersDVR.blockWeight ι) e c
      (rfl : Finsupp.weight (NumbersDVR.blockWeight ι) e = _)
    have hb : ∀ e' ∈ (monomial e c : MvPolynomial (Σ k, ι k) S).support, ∀ k,
        ∑ i, e' ⟨k, i⟩ = Finsupp.weight (NumbersDVR.blockWeight ι) e k := by
      intro e' he' k
      rw [sum_block_eq_blockWeight, hm (mem_support_iff.mp he')]
    rw [mConeMapOver_eq_of_block y hb,
      weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hm)]
    have hX : (∏ k, (X k : MvPolynomial K Ω) ^ Finsupp.weight (NumbersDVR.blockWeight ι) e k) =
        monomial (Finsupp.equivFunOnFinite.symm (Finsupp.weight (NumbersDVR.blockWeight ι) e)) 1 := by
      rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp)]
      simp
    rw [hX, coeff_C_mul, coeff_monomial]
    by_cases h : b = Finsupp.weight (NumbersDVR.blockWeight ι) e
    · subst h; simp
    · rw [ite_eq_right h, ite_eq_right (fun h' => h (Finsupp.equivFunOnFinite.symm.injective h').symm)]
      simp
  | add p q hp hq => simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq]

theorem isMultiHomogIdeal_mIdealOver (y : (Σ k, ι k) → Ω) :
    NumbersDVR.IsMultiHomogIdeal (R := S) (mIdealOver S y) := by
  intro f hf b
  have hf' : mConeMapOver S y f = 0 := RingHom.mem_ker.mp hf
  refine RingHom.mem_ker.mpr ?_
  have hb : ∀ e' ∈ (weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f).support, ∀ k,
      ∑ i, e' ⟨k, i⟩ = b k := by
    intro e' he' k
    rw [sum_block_eq_blockWeight,
      weightedHomogeneousComponent_isWeightedHomogeneous b f (mem_support_iff.mp he')]
  rw [mConeMapOver_eq_of_block y hb, ← coeff_mConeMapOver, hf']
  simp

theorem isMultiProjPrime_mIdealOver (y : (Σ k, ι k) → Ω) (hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) :
    NumbersDVR.IsMultiProjPrime (R := S) (mIdealOver S y) := by
  refine ⟨RingHom.ker_isPrime (mConeMapOver S y), isMultiHomogIdeal_mIdealOver y, ?_⟩
  intro k
  obtain ⟨i, hi⟩ := hy k
  refine ⟨i, fun h => ?_⟩
  have h' : mConeMapOver S y (X ⟨k, i⟩) = 0 := RingHom.mem_ker.mp h
  simp only [mConeMapOver, aeval_X] at h'
  exact mul_ne_zero (by rwa [Ne, MvPolynomial.C_eq_zero]) (X_ne_zero _) h'

end Homog

section Graph

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {N m : ℕ}

theorem mConeMapOver_graph_comp_base (x : Fin (N + 1) → Ω) (s : Fin m → Ω) :
    (mConeMapOver S (graphVec x s)).comp
        (rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ b, graphIdx N m b)) =
      ((Polynomial.aeval (X baseBlock : MvPolynomial (Unit ⊕ Unit) Ω)).restrictScalars S).comp
        (Kleiman.cone (S := S) x) := by
  apply MvPolynomial.algHom_ext
  intro a
  simp [mConeMapOver, Kleiman.cone, ReciprocityTheory.ChartRestriction.G.Geo.coneMap]
  rfl

theorem cone_eq_graph_comp (x : Fin (N + 1) → Ω) (s : Fin m → Ω) :
    Kleiman.cone (S := S) x =
      ((aeval fun _ : Unit ⊕ Unit => (Polynomial.X : Polynomial Ω)).restrictScalars S).comp
        ((mConeMapOver S (graphVec x s)).comp
          (rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ b, graphIdx N m b))) := by
  apply MvPolynomial.algHom_ext
  intro a
  simp [mConeMapOver, Kleiman.cone, ReciprocityTheory.ChartRestriction.G.Geo.coneMap]
  rfl

theorem comap_mIdealOver_graph (x : Fin (N + 1) → Ω) (s : Fin m → Ω) :
    (mIdealOver S (graphVec x s)).comap
        (rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ b, graphIdx N m b)) =
      Kleiman.primeOf (S := S) x := by
  ext f
  rw [Ideal.mem_comap, Kleiman.primeOf_eq, RingHom.mem_ker]
  change mConeMapOver S (graphVec x s) (rename _ f) = 0 ↔ _
  constructor
  · intro h
    rw [cone_eq_graph_comp x s, AlgHom.comp_apply, AlgHom.comp_apply, h, map_zero]
  · intro h
    rw [← AlgHom.comp_apply, mConeMapOver_graph_comp_base, AlgHom.comp_apply, h, map_zero]

theorem isMultiProjPrime_mIdealOver_graph (x : Fin (N + 1) → Ω) (s : Fin m → Ω) (hx : ∃ i, x i ≠ 0)
    (hs : ∃ j, s j ≠ 0) : NumbersDVR.IsMultiProjPrime (R := S) (mIdealOver S (graphVec x s)) :=
  isMultiProjPrime_mIdealOver _ (by rintro (⟨⟩ | ⟨⟩); exacts [hx, hs])

end Graph

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SecsTwistSysPtX
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver)

noncomputable section

def BundleRealises {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {K : Type} [Fintype K]
    [DecidableEq K] {ι : K → Type} (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} {x : Fin (N + 1) → Ω}
    (Q : Kleiman.LineBundle S x) (β : K → ℤ) : Prop :=
  ∀ c : ℤ, (Q.toSubSystem.twist (Kleiman.twistSys S x c)).secs =
    secOver S y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)

section Graph

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {N m : ℕ} {x : Fin (N + 1) → Ω}

theorem realises_graph (Q : Kleiman.LineBundle S x) (n : ℤ) (s : Fin m → Ω) (hgen : IsGraphGen Q n s) :
    BundleRealises (graphVec x s) baseBlock Q (graphDeg n) :=
  fun c => twist_secs_eq_secOver Q n s hgen c

end Graph

section Point

variable (k : Type) [Field k]

end Point

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerAlt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver)

def BundleOfDeg.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y k₀ → ∀ β : K → ℤ,
      ∃ Q : Kleiman.LineBundle S (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm), ∀ c : ℤ,
        (Q.twist (Kleiman.twistSys S (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) c)).secs =
          secOver S y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SegreLiftVal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiProjPrime)

noncomputable section

section Objects

variable {K : Type} [Fintype K] (ι : K → Type)

abbrev segreIdx : Unit ⊕ K → Type := Sum.elim (fun _ : Unit => ∀ k, ι k) ι

variable (R : Type*) [CommRing R]

def segreIncl : MRing ι R →ₐ[R] MRing (segreIdx ι) R :=
  rename fun v => (⟨Sum.inr v.1, v.2⟩ : Σ k, segreIdx ι k)

variable {ι R}

def segreY (c : ∀ k, ι k) : MRing (segreIdx ι) R :=
  X (⟨Sum.inl (), c⟩ : Σ k, segreIdx ι k)

def segreMon (c : ∀ k, ι k) : MRing (segreIdx ι) R :=
  ∏ k, X (⟨Sum.inr k, c k⟩ : Σ k, segreIdx ι k)

variable (ι R)

def segreRels : Set (MRing (segreIdx ι) R) :=
  {g | ∃ c d : ∀ k, ι k, g = segreY c * segreMon d - segreY d * segreMon c}

def segreLiftVal (W : Ideal (MRing ι R)) : (Σ k, segreIdx ι k) → Polynomial (MRing ι R ⧸ W)
  | ⟨Sum.inl _, c⟩ => Polynomial.X * Polynomial.C (Ideal.Quotient.mk W (∏ k, X ⟨k, c k⟩))
  | ⟨Sum.inr k, i⟩ => Polynomial.C (Ideal.Quotient.mk W (X ⟨k, i⟩))

def segreLiftMap (W : Ideal (MRing ι R)) :
    MRing (segreIdx ι) R →ₐ[R] Polynomial (MRing ι R ⧸ W) :=
  aeval (segreLiftVal ι R W)

def segreLift (W : Ideal (MRing ι R)) : Ideal (MRing (segreIdx ι) R) :=
  RingHom.ker (segreLiftMap ι R W)

end Objects

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockEqChartRing
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver)

noncomputable section

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω]

section Frac

theorem coe_ne_zero_of_not_mem {A : Subalgebra S Ω} {p : Ideal A} {b : A} (hb : b ∉ p) : (b : Ω) ≠ 0 := by
  intro h
  apply hb
  have : b = 0 := Subtype.ext h
  rw [this]
  exact p.zero_mem

theorem one_not_mem_of_prime {A : Subalgebra S Ω} {p : Ideal A} (hp : p.IsPrime) : (1 : A) ∉ p :=
  fun h => hp.ne_top ((Ideal.eq_top_iff_one _).mpr h)

def fracSub (A : Subalgebra S Ω) (p : Ideal A) [hp : p.IsPrime] : Subalgebra S Ω where
  carrier := {u | ∃ a b : A, b ∉ p ∧ u = (a : Ω) / b}
  mul_mem' := by
    rintro _ _ ⟨a, b, hb, rfl⟩ ⟨a', b', hb', rfl⟩
    refine ⟨a * a', b * b', fun h => (hp.mem_or_mem h).elim hb hb', ?_⟩
    push_cast
    rw [div_mul_div_comm]
  add_mem' := by
    rintro _ _ ⟨a, b, hb, rfl⟩ ⟨a', b', hb', rfl⟩
    refine ⟨a * b' + b * a', b * b', fun h => (hp.mem_or_mem h).elim hb hb', ?_⟩
    push_cast
    rw [div_add_div _ _ (coe_ne_zero_of_not_mem hb) (coe_ne_zero_of_not_mem hb')]
  algebraMap_mem' r := ⟨algebraMap S A r, 1, one_not_mem_of_prime hp, by simp⟩

theorem mem_locIn {A : Subalgebra S Ω} {p : Ideal A} [p.IsPrime] {u : Ω} :
    u ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A p ↔ ∃ a b : A, b ∉ p ∧ u = (a : Ω) / b := by
  constructor
  · intro h
    exact (Subring.closure_le (t := (fracSub A p).toSubring)).mpr (fun v hv => hv) h
  · intro h
    exact Subring.subset_closure h

theorem span_subset_span {A B : Subalgebra S Ω} (hAB : A ≤ B) (s : Set Ω) :
    (Submodule.span A s : Set Ω) ⊆ Submodule.span B s := by
  intro z (hz : z ∈ Submodule.span A s)
  induction hz using Submodule.span_induction with
  | mem z hz => exact Submodule.subset_span hz
  | zero => exact Submodule.zero_mem _
  | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
  | smul a z _ hz =>
    have e : a • z = (⟨a, hAB a.2⟩ : B) • z := by
      rw [Subalgebra.smul_def, Subalgebra.smul_def]
    rw [SetLike.mem_coe, e]
    exact Submodule.smul_mem _ _ hz

theorem exists_sum_eq_one {A : Subalgebra S Ω} {m : ℕ} (g : Fin m → Ω) (Q' : Submodule A Ω)
    (hQQ : Submodule.span A (Set.range g) * Q' = 1) :
    ∃ w : Fin m → Ω, (∀ b, w b ∈ Q') ∧ (∀ a b, g a * w b ∈ A) ∧ ∑ b, g b * w b = 1 := by
  classical
  have hone : (1 : Ω) ∈ Submodule.span A (Set.range g) * Q' := by
    rw [hQQ]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  obtain ⟨w, hwQ, hsum⟩ : ∃ w : Fin m → Ω, (∀ b, w b ∈ Q') ∧ ∑ b, g b * w b = 1 := by
    refine Submodule.mul_induction_on
      (C := fun z => ∃ w : Fin m → Ω, (∀ b, w b ∈ Q') ∧ ∑ b, g b * w b = z) hone ?_ ?_
    · intro q hq q' hq'
      obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp hq
      refine ⟨fun b => (a b : Ω) * q', fun b => Q'.smul_mem (a b) hq', ?_⟩
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Subalgebra.smul_def, smul_eq_mul]
      ring
    · rintro _ _ ⟨w, hw, rfl⟩ ⟨w', hw', rfl⟩
      refine ⟨w + w', fun b => Q'.add_mem (hw b) (hw' b), ?_⟩
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ => by simp [mul_add]
  refine ⟨w, hwQ, fun a b => ?_, hsum⟩
  have h := Submodule.mul_mem_mul (Submodule.subset_span ⟨a, rfl⟩ : g a ∈ Submodule.span A (Set.range g))
    (hwQ b)
  rw [hQQ, Submodule.mem_one] at h
  obtain ⟨y, hy⟩ := h
  rw [← hy]
  exact y.2

theorem chartRingOver_oneBlock_eq_chartRing {N : ℕ} (x : Fin (N + 1) → Ω) (c : Unit → Fin (N + 1)) (h : x (c ()) ≠ 0) :
    chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) c =
      Kleiman.chartRing (S := S) (x := x) (Kleiman.singleChart h) := by
  have hChart : ReciprocityTheory.ChartRestriction.G.Geo.chartRing S x (c ()) =
      Kleiman.chartRing (S := S) (x := x) (Kleiman.singleChart h) := by
    apply le_antisymm
    · rw [ReciprocityTheory.ChartRestriction.G.Geo.chartRing, Algebra.adjoin_le_iff]
      rintro _ ⟨j, rfl⟩
      exact ⟨X j, X (c ()), 1, Kleiman.X_mem_monos (Finset.mem_singleton_self _),
        isHomogeneous_X S j, isHomogeneous_X S (c ()), by simp⟩
    · rintro _ ⟨f, s, e, hs, hf, hse, rfl⟩
      have hs₀ := Kleiman.eval_ne_zero_of_mem_monos (Kleiman.singleChart h) hs
      have hsne : s ≠ 0 := fun he => hs₀ (by rw [he, map_zero])
      obtain ⟨e', hse', hden⟩ := TranslateEq.pow_div_mem_chartRingI S x
        (Kleiman.singleChart h) (c ()) hs
      have he : e = e' := hse.inj_right hse' hsne
      subst e'
      change x (c ()) ^ e / aeval x s ∈
        IndefiniteRowSideFullHecke.Kleiman.chartRingI S x {c ()} at hden
      rw [IndefiniteRowSideFullHecke.Kleiman.chartRingI_singleton] at hden
      have hnum : aeval x f / x (c ()) ^ e ∈
          ReciprocityTheory.ChartRestriction.G.Geo.chartRing S x (c ()) := by
        rw [← Kleiman.aeval_div_of_isHomogeneous hf, ReciprocityTheory.ChartRestriction.G.Geo.chartRing,
          ← MvPolynomial.aeval_range]
        exact ⟨f, rfl⟩
      have hquot : aeval x f / aeval x s = (aeval x f / x (c ()) ^ e) * (x (c ()) ^ e / aeval x s) := by
        field_simp
      rw [hquot]
      exact mul_mem hnum hden
  rw [← hChart]
  unfold chartRingOver ReciprocityTheory.ChartRestriction.G.Geo.chartRing
  congr 1
  ext z
  constructor
  · rintro ⟨⟨⟨⟩, a⟩, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨⟨(), a⟩, rfl⟩

end Frac

section Dom

variable {N N' : ℕ}


end Dom

section Join

variable {N N' m : ℕ}



variable {x' : Fin (N' + 1) → Ω} {x : Fin (N + 1) → Ω}


end Join

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsLastRest
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver)

def VeryAmpleEq.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (N : ℕ) (Ω : Type) [Field Ω] [Algebra S Ω] (x : Fin (N + 1) → Ω)
    (Q : Kleiman.LineBundle S x) (n : ℤ) (m : ℕ) (s : Fin m → Ω),
    IsGraphGen Q n s →
      (Kleiman.IsVeryAmple Q.toSubSystem ↔ IndefiniteRowSideFullHecke.Kleiman2.VeryAmple S (graphVec x s) (graphDeg n))

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.BlockVecSegreJoin
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

instance segreIdx.fintype {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] :
    ∀ k, Fintype (Sum.elim (fun _ : Unit => ∀ k, ι k) ι k) := fun k => by
  cases k <;> infer_instance

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.MemChartSecOverOfMem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open scoped Pointwise
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver)

variable (S : Type) [CommRing S] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {Ω : Type} [Field Ω]
  [Algebra S Ω]

def chartSecOver (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) (δ : K → ℤ)
    (I : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) : Set Ω :=
  {t | ∃ n : ℕ, Kleiman.xProd I ^ n * t ∈
    secOver S y (δ + ((n * I.1.card : ℕ) : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)}

def ChartSecMul.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y k₀ → ∀ (γ β : K → ℤ)
      (I : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)),
      (Submodule.span (Kleiman.chartRing S (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) I)
          (chartSecOver S y k₀ e γ I * chartSecOver S y k₀ e β I) : Set Ω) =
        chartSecOver S y k₀ e (γ + β) I

theorem mem_chartSecOver_of_mem (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) (δ : K → ℤ)
    (I : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) {t : Ω} (ht : t ∈ secOver S y δ) :
    t ∈ chartSecOver S y k₀ e δ I :=
  ⟨0, by simpa using ht⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraTer
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver)

def GraphModel.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (N : ℕ) (Ω : Type) [Field Ω] [Algebra S Ω] (x : Fin (N + 1) → Ω)
    (Q : Kleiman.LineBundle S x) (n : ℤ) (m : ℕ) (s : Fin m → Ω),
    (∃ i, x i ≠ 0) → IsGraphGen Q n s → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S (graphVec x s) baseBlock

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraTail
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver)

def NefEq.Statement : Prop :=
  ∀ (k : Type) [Field k] (N : ℕ) (Ω : Type) [Field Ω] [Algebra k Ω] (x : Fin (N + 1) → Ω)
    (Q : Kleiman.LineBundle k x) (n : ℤ) (m : ℕ) (s : Fin m → Ω),
    IsGraphGen Q n s → (Kleiman.Nef Q.toSubSystem ↔ IndefiniteRowSideFullHecke.Kleiman2.IsNef k (graphVec x s) (graphDeg n))

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.OneBlockPnPt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def ModelCurvesLift.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1))
    (x : Fin (N + 1) → Ω), x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ →
      ∀ P : Ideal (NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) F), NumbersDVR.IsMultiProjPrime P →
        mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) ≤ P →
          ∃ W : Ideal (NumbersDVR.MRing ι F), NumbersDVR.IsMultiProjPrime W ∧ mIdealOver F y ≤ W ∧
            baseComap F k₀ e W = P

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSide
section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PReindexDim
section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisAltTer
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver secOver secMOver)

def ReindexDim.Statement : Prop :=
  ∀ (F : Type) [Field F] (κ : Type) [Fintype κ] (Ω : Type) [Field Ω] [Algebra F Ω] (x' : κ → Ω) (N : ℕ)
    (e : κ ≃ Fin (N + 1)),
    ringKrullDim (NumbersDVR.MRing (fun _ : Unit => κ) F ⧸ mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x')) =
      ringKrullDim (Kleiman.Poly F N ⧸ Kleiman.primeOf (S := F) (x' ∘ e.symm))

section Inhabitants

open IndefiniteRowSideFullHecke.Kleiman2

variable (F : Type) [Field F]

end Inhabitants

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver mConeMapOver)

theorem coneMap_rename {F : Type} [Field F] {κ : Type} {Ω : Type} [Field Ω] [Algebra F Ω] (x' : κ → Ω) {N : ℕ}
    (e : κ ≃ Fin (N + 1)) (p : NumbersDVR.MRing (fun _ : Unit => κ) F) :
    uniqueAlgEquiv Ω Unit (mConeMapOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') p) =
      ReciprocityTheory.ChartRestriction.G.Geo.coneMap F (x' ∘ e.symm) (rename (fun v : Σ _ : Unit, κ => e v.2) p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp [mConeMapOver, ReciprocityTheory.ChartRestriction.G.Geo.coneMap, MvPolynomial.algebraMap_eq, Polynomial.algebraMap_apply]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, rename_X]
    congr 1
    simp [mConeMapOver, ReciprocityTheory.ChartRestriction.G.Geo.coneMap, IndefiniteRowSideFullHecke.Kleiman2.oneBlock]

theorem ReindexDim.proof : ReindexDim.Statement := by
  intro F _ κ _ Ω _ _ x' N e
  let σ : (Σ _ : Unit, κ) ≃ Fin (N + 1) :=
    { toFun := fun v => e v.2, invFun := fun i => ⟨(), e.symm i⟩, left_inv := fun _ => by simp,
      right_inv := fun _ => by simp }
  let f : NumbersDVR.MRing (fun _ : Unit => κ) F ≃+* Kleiman.Poly F N := (renameEquiv F σ).toRingEquiv
  have hc : mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') =
      (Kleiman.primeOf (S := F) (x' ∘ e.symm)).comap f.toRingHom := by
    ext p
    change mConeMapOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') p = 0 ↔
      ReciprocityTheory.ChartRestriction.G.Geo.coneMap F (x' ∘ e.symm) (rename σ p) = 0
    rw [← (uniqueAlgEquiv Ω Unit).injective.eq_iff, map_zero]
    exact Iff.of_eq (congrArg (· = 0) (coneMap_rename x' e p))
  have h : Kleiman.primeOf (S := F) (x' ∘ e.symm) = (mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x')).map f.toRingHom := by
    rw [hc, Ideal.map_comap_of_surjective f.toRingHom f.surjective]
  exact ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ _ f h)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver chartRingOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

theorem ModelDimEq.full : ModelDimEq.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e hmod d
  obtain ⟨hnz, hsame⟩ := hmod
  choose c hc using hnz
  obtain ⟨c', hc', htr⟩ := exists_trdeg_chartRing_eq y _ hsame c hc
  have hy := trdeg_quotient_mIdealOver (F := F) y c hc
  have hx := trdeg_quotient_mIdealOver (F := F) (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) c' hc'
  rw [← htr, Fintype.card_unit] at hx

  have _ : (mIdealOver F y).IsPrime := RingHom.ker_isPrime _
  have _ : (mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀))).IsPrime :=
    RingHom.ker_isPrime _
  have hfin := trdeg_lt_aleph0_of_finiteType (R := F) (S := MvPolynomial (Σ k, ι k) F ⧸ mIdealOver F y)
  rw [hy] at hfin
  obtain ⟨t, ht⟩ := Cardinal.lt_aleph0.1 (lt_of_le_of_lt le_self_add hfin)
  have dimy : ringKrullDim (MvPolynomial (Σ k, ι k) F ⧸ mIdealOver F y) = ((t + Fintype.card K : ℕ) : ℕ∞) := by
    rw [GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F, hy, ht]
    simp
  have dimx : ringKrullDim (Kleiman.Poly F N ⧸ Kleiman.primeOf (S := F) (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) =
      ((t + 1 : ℕ) : WithBot ℕ∞) := by
    rw [← ReindexDim.proof F (ι k₀) Ω (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀) N e,
      GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F, hx, ht]
    simp
  have hrel : relDim (mIdealOver F y) = ((t : ℕ) : WithBot (WithTop ℤ)) := by
    unfold relDim
    rw [dimy]
    have e₁ : WithBot.map (fun d : ℕ∞ => WithTop.map (fun e : ℕ => (e : ℤ) - Fintype.card K) d)
        ((((t + Fintype.card K : ℕ) : ℕ∞)) : WithBot ℕ∞) =
        (((((t + Fintype.card K : ℕ) : ℤ) - Fintype.card K : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) := rfl
    rw [e₁, Nat.cast_add, add_sub_cancel_right]
    rfl
  rw [hrel]
  constructor
  · intro h
    have h' := h.dim
    rw [dimx] at h'
    have htd : t + 1 = d + 1 := by exact_mod_cast h'
    rw [show t = d by omega]
  · intro h
    have htd : t = d := by exact_mod_cast h
    refine ⟨inferInstance, fun p hp n => Kleiman.homogeneousComponent_mem_primeOf _ hp n, le_rfl,
      ⟨e (c k₀), ?_⟩, by rw [dimx, htd]⟩
    rw [Kleiman.mem_primeOf_of_isHomogeneous _ (isHomogeneous_X F _), aeval_X]
    simpa [IndefiniteRowSideFullHecke.Kleiman2.blockVec] using hc k₀

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurtherFurther
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

def ModelCurvesDim.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ →
      ∀ W : Ideal (NumbersDVR.MRing ι F), NumbersDVR.IsMultiProjPrime W → mIdealOver F y ≤ W →
        relDim (baseComap F k₀ e W) = relDim W

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTailRest
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver mIdealOver)

def SegreRealise.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ a, Fintype (ι a)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ a, ι a) → Ω) (d : ℕ)
    (μs : Fin d → K → ℤ),
    (∀ a, ∃ i, y ⟨a, i⟩ ≠ 0) → FieldNumbers.relDim (mIdealOver F y) = ((d : ℕ) : WithBot (WithTop ℤ)) →
    ∃ (N : ℕ) (eqv : (∀ a, ι a) ≃ Fin (N + 1)) (x : Fin (N + 1) → Ω)
      (Ms : Fin d → Kleiman.LineBundle F x),
      (∀ i, x (eqv i) = ∏ a, y ⟨a, i a⟩) ∧
      Kleiman.IsSubvar x (Kleiman.primeOf (S := F) x) d ∧
      (∀ j (c : ℤ), ((Ms j).twist (Kleiman.twistSys F x c)).secs =
        secOver F y (μs j + fun _ => c)) ∧
      (∀ j, Kleiman.Nef (Ms j).toSubSystem ↔ IndefiniteRowSideFullHecke.Kleiman2.IsNef F y (μs j)) ∧
      Kleiman.interNum (Kleiman.primeOf (S := F) x) (fun j => (Ms j).toSubSystem) =
        NumbersDVR.intNum F (mIdealOver F y) μs

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurtherMore
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver secOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

def ModelCurveNum.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω] (N : ℕ)
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (k₀ : K) (e : ι k₀ ≃ Fin (N + 1))
    (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (y' : (Σ k, ι' k) → Ω) (k₀' : K') (e' : ι' k₀' ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y' k₀' →
    IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm = IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀' ∘ e'.symm →
    ∀ (β : K → ℤ) (β' : K' → ℤ),
      (∀ c : ℤ, secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) =
          secOver F y' (β' + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀')) →
      ∀ (W : Ideal (NumbersDVR.MRing ι F)) (W' : Ideal (NumbersDVR.MRing ι' F)),
        NumbersDVR.IsMultiProjPrime W → mIdealOver F y ≤ W → relDim W = ((1 : ℕ) : WithBot (WithTop ℤ)) →
        NumbersDVR.IsMultiProjPrime W' → mIdealOver F y' ≤ W' → relDim W' = ((1 : ℕ) : WithBot (WithTop ℤ)) →
        baseComap F k₀ e W = baseComap F k₀' e' W' →
        NumbersDVR.intNum F W ![β] = NumbersDVR.intNum F W' ![β']

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PZChartSmul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

theorem ZChartSmul.proof : ZChartSmul.Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ G H r h hh J j hj I a ha z hz
  classical
  have hmem : ∀ l, h l ∈ H.sub I := fun l => (Submodule.mem_iInf _).mp (hh l) I
  refine Submodule.span_induction (p := fun z _ => a • z ∈ secsOnZChart G H h I J) ?_ ?_ ?_ ?_ hz
  · rintro e ⟨m, hm⟩
    obtain ⟨n, hn⟩ := Set.mem_iInter.mp ha I
    rw [one_mul] at hn
    set u := ∏ l ∈ J.1.erase j, h l with hu
    have hxu : xProd J = h j * u := (Finset.mul_prod_erase J.1 h hj).symm
    have hk : J.1.card = (J.1.erase j).card + 1 := by
      rw [Finset.card_erase_of_mem hj]
      have := Finset.card_pos.mpr ⟨j, hj⟩
      omega
    have hun : u ^ n ∈ (H.pow ((J.1.erase j).card * n)).sub I :=
      AmpleTwistLocal.pow_mem_pow H I (VeryAmpleZTwist.prod_mem_pow H I hmem _) n
    have hw : a * h j ^ n * u ^ n ∈ (H.pow (n + (J.1.erase j).card * n)).sub I :=
      AmpleTwistLocal.mul_mem_pow H I hn _ hun
    have h1 := VeryAmpleZTwist.smul_mem_twist_pow G H I hw hm
    refine Submodule.subset_span ⟨m + n, ?_⟩
    have e1 : xProd J ^ (m + n) • a • e = (a * h j ^ n * u ^ n) • xProd J ^ m • e := by
      rw [smul_smul, smul_smul, hxu]; ring_nf
    have e2 : J.1.card * (m + n) = J.1.card * m + (n + (J.1.erase j).card * n) := by
      rw [hk]; ring
    rw [e1, e2]
    exact h1
  · rw [smul_zero]; exact Submodule.zero_mem _
  · intro b c _ _ hb hc; rw [smul_add]; exact Submodule.add_mem _ hb hc
  · intro s y _ hy; rw [smul_comm]; exact Submodule.smul_mem _ s hy

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CellResMemLocPart
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (Cell cellMon CechC cellRes faceSign cechD locPart cechCc cechZc cechBc cechHc
  mIdealOver mConeMapOver chartRingOver quotPart)

namespace CechPointVanish

set_option linter.unusedSectionVars false

section Cells

variable {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, LinearOrder (ι k)]

theorem face_subset (I : ∀ k, Finset (ι k)) (k : K) (i : ι k) (l : K) :
    Function.update I k ((I k).erase i) l ⊆ I l := by
  by_cases hl : l = k
  · subst hl
    rw [Function.update_self]
    exact Finset.erase_subset _ _
  · rw [Function.update_of_ne hl]

theorem constD_congr {V : Type} [AddCommGroup V] (G : ∀ k, Finset (ι k)) (n : ℕ)
    {f f' : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → V}
    (h : ∀ J : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n, (∀ k, J.1 k ⊆ G k) → f J = f' J)
    (I : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι (n + 1)) (hI : ∀ k, I.1 k ⊆ G k) :
    constD K ι V n f I = constD K ι V n f' I := by
  unfold constD
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hc
  · exact congrArg _ (h _ fun l => (face_subset I.1 k i l).trans (hI l))
  · rfl

variable {S : Type} [CommRing S]

theorem cellMon_mono {J I : ∀ k, Finset (ι k)} (h : ∀ k, J k ⊆ I k) : cellMon S J ≤ cellMon S I := by
  apply Submonoid.closure_mono
  rintro f ⟨k, i, hi, rfl⟩
  exact ⟨k, i, h k hi, rfl⟩

theorem cellRes_mk {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] {J I : ∀ k, Finset (ι k)}
    (h : cellMon S J ≤ cellMon S I) (m : M) (t : cellMon S J) :
    cellRes S M J I (LocalizedModule.mk m t) = LocalizedModule.mk m ⟨t.1, h t.2⟩ := by
  unfold cellRes
  rw [dif_pos h, IsLocalizedModule.mk_eq_mk', IsLocalizedModule.liftOfLE_mk', ← IsLocalizedModule.mk_eq_mk']


open Classical in
theorem cechD_apply {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] (n : ℕ) (f : CechC S ι M n)
    (I : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι (n + 1)) :
    cechD S ι M n f I = ∑ k, ∑ i ∈ I.1 k,
      if h : (∀ l, (Function.update I.1 k ((I.1 k).erase i) l).Nonempty) ∧
          ∑ l, ((Function.update I.1 k ((I.1 k).erase i) l).card - 1) = n then
        faceSign I.1 k i • cellRes S M _ I.1 (f ⟨Function.update I.1 k ((I.1 k).erase i), h⟩)
      else 0 := by
  simp only [cechD, LinearMap.pi_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> rfl

end Cells

section Point

variable {F : Type} [Field F] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
  [∀ k, LinearOrder (ι k)] {Ω : Type} [Field Ω] [Algebra F Ω] {y : (Σ k, ι k) → Ω}

end Point

end CechPointVanish

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

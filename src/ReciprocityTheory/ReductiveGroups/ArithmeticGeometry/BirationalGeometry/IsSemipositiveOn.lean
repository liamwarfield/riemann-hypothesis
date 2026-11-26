module

public import Mathlib

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

section Coord

variable (o : Type*) {Ω : Type*} [CommRing o] [CommRing Ω] [Algebra o Ω] {ι : Type*}

def coneMap (x : ι → Ω) : MvPolynomial (ι) o →ₐ[o] Polynomial Ω :=
  aeval fun i => Polynomial.C (x i) * Polynomial.X

def coneRing (x : ι → Ω) : Subalgebra o (Polynomial Ω) :=
  (coneMap o x).range

def coordIdeal (x : ι → Ω) : Ideal (MvPolynomial (ι) o) :=
  RingHom.ker (coneMap o x)

def sec (x : ι → Ω) (d : ℕ) : Submodule o Ω :=
  (homogeneousSubmodule (ι) o d).map
    (aeval x : MvPolynomial (ι) o →ₐ[o] Ω).toLinearMap

def gradedPiece (I : Ideal (MvPolynomial (ι) o)) (d : ℕ) :
    Submodule o (MvPolynomial (ι) o ⧸ I) :=
  (homogeneousSubmodule (ι) o d).map (Ideal.Quotient.mkₐ o I).toLinearMap

def IsHomogIdeal (I : Ideal (MvPolynomial (ι) o)) : Prop :=
  ∀ f ∈ I, ∀ d, homogeneousComponent d f ∈ I

end Coord

section Points

variable {o : Type*} [CommRing o] {C : Type*} [NormedField C] {ι : Type*}

def conePts (σ : o →+* C) (I : Ideal (MvPolynomial (ι) o)) : Set (ι → C) :=
  {z | z ≠ 0 ∧ ∀ f ∈ I, eval z (map σ f) = 0}


variable (C ι) in
structure ConeMetric where

  ρ : (ι → C) → ℝ
  pos : ∀ z, z ≠ 0 → 0 < ρ z
  smul : ∀ (c : C) (z : ι → C), ρ (c • z) = ‖c‖ * ρ z


variable (C ι) in
def maxMetric [Fintype ι] : ConeMetric (C := C) (ι := ι) where
  ρ z := ‖z‖
  pos _ hz := norm_pos_iff.mpr hz
  smul c z := norm_smul c z


variable (ι) in
def fsMetric [Fintype ι] : ConeMetric (C := ℂ) (ι := ι) where
  ρ z := ‖WithLp.toLp 2 z‖
  pos _ hz := norm_pos_iff.mpr (by simpa using hz)
  smul c z := by rw [WithLp.toLp_smul, norm_smul]

def ptNorm (m : ConeMetric (C := C) (ι := ι)) (σ : o →+* C) (d : ℕ) (f : MvPolynomial (ι) o)
    (z : ι → C) : ℝ :=
  ‖eval z (map σ f)‖ / m.ρ z ^ d

def IsConjInvariant (m : ConeMetric (C := ℂ) (ι := ι)) : Prop :=
  ∀ z, m.ρ (fun i => (starRingEnd ℂ) (z i)) = m.ρ z

end Points

section Heights

def hgt {K ι : Type*} [Field K] [NumberField K] (y : ι → K) : ℝ :=
  Height.logHeight y / Height.totalWeight K

end Heights

section Curvature

variable {ι : Type*} [Fintype ι]

def IsSmoothMetric (m : ConeMetric (C := ℂ) (ι := ι)) : Prop :=
  ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m.ρ {z | z ≠ 0}

def leviForm (φ : (ι → ℂ) → ℝ) (z w : ι → ℂ) : ℝ :=
  (fderiv ℝ (fderiv ℝ φ) z w w + fderiv ℝ (fderiv ℝ φ) z (Complex.I • w) (Complex.I • w)) / 4

def IsSemipositive (m : ConeMetric (C := ℂ) (ι := ι)) : Prop :=
  IsSmoothMetric m ∧ ∀ z, z ≠ 0 → ∀ w, 0 ≤ leviForm (fun z => Real.log (m.ρ z)) z w

end Curvature

section Chow

open NumberField

variable {e n : ℕ}

def IsMultihomog {K : Type*} [CommSemiring K] (P : MvPolynomial (Fin (e + 1) × Fin n) K) (δ : ℕ) :
    Prop :=
  ∀ m ∈ P.support, ∀ k, ∑ j, m (k, j) = δ

end Chow

section MetrisedHeight

open NumberField

variable {ι : Type*}

end MetrisedHeight

section SphereMeasure

variable {e n : ℕ}

end SphereMeasure

section Joins

variable {Ω : Type*} [CommRing Ω] {ι κ : Type*}

def segreJoin (x : ι → Ω) (y : κ → Ω) : ι × κ → Ω := fun p => x p.1 * y p.2

end Joins

section Multi

variable {r : ℕ} {ι : Fin r → Type*} [∀ k, Fintype (ι k)]

end Multi

section Along

variable {o : Type*} [CommRing o] {ι : Type*} [Fintype ι]

def IsConeTangent (σ : o →+* ℂ) (I : Ideal (MvPolynomial ι o)) (z w : ι → ℂ) : Prop :=
  ∀ f ∈ I, ∑ i, eval z (pderiv i (map σ f)) * w i = 0

def IsSemipositiveOn (m : ConeMetric (C := ℂ) (ι := ι)) (σ : o →+* ℂ) (I : Ideal (MvPolynomial ι o))
    (S : Set (ι → ℂ)) : Prop :=
  IsSmoothMetric m ∧
    ∀ z ∈ S, z ≠ 0 → ∀ w, IsConeTangent σ I z w → 0 ≤ leviForm (fun z => Real.log (m.ρ z)) z w

end Along

section MongeAmpere

variable {D : ℕ}

def cxHessian (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  fun i j =>
    let H := fderiv ℝ (fderiv ℝ φ) z
    let ei : Fin D → ℂ := Pi.single i 1
    let ej : Fin D → ℂ := Pi.single j 1
    ((H ei ej + H (Complex.I • ei) (Complex.I • ej) : ℝ) +
      Complex.I * ((H ei (Complex.I • ej) - H (Complex.I • ei) ej : ℝ))) / 4

def mixedDisc (A : Fin D → Matrix (Fin D) (Fin D) ℂ) : ℂ :=
  (1 / (D.factorial : ℂ)) *
    ∑ S : Finset (Fin D), (-1) ^ (D - S.card) * (∑ k ∈ S, A k).det

def maDensity (φ : Fin D → (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) : ℝ :=
  (D.factorial : ℝ) * (2 / Real.pi) ^ D * (mixedDisc fun k => cxHessian (φ k) z).re

end MongeAmpere

section LatticeDegree

open NumberField ComplexConjugate

variable {ι : Type*} {r : ℕ}

def realGram {K : Type*} [Field K] [NumberField K] (m : InfinitePlace K → ConeMetric (C := ℂ) (ι := ι))
    (μ : InfinitePlace K → MeasureTheory.Measure (ι → ℂ)) (d : ℕ)
    (b : Fin r → MvPolynomial ι K) : Matrix (Fin r) (Fin r) ℝ :=
  fun k l => ∑ w : InfinitePlace K, (w.mult : ℝ) *
    (∫ z, eval z (map w.embedding (b k)) * conj (eval z (map w.embedding (b l))) /
      (((m w).ρ z ^ (2 * d) : ℝ) : ℂ) ∂μ w).re

def l2Degree {K : Type*} [Field K] [NumberField K] (m : InfinitePlace K → ConeMetric (C := ℂ) (ι := ι))
    (μ : InfinitePlace K → MeasureTheory.Measure (ι → ℂ)) (d : ℕ)
    (b : Fin r → MvPolynomial ι K) : ℝ :=
  -(Real.log (realGram m μ d b).det / 2) / Height.totalWeight K

end LatticeDegree

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodA
namespace ReciprocityTheory.ChartRestriction.G.Geo

open Ideal

theorem exists_ltSeries_lift {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] (hinj : Function.Injective (algebraMap R S)) :
    ∀ (n : ℕ) (p : LTSeries (PrimeSpectrum R)), p.length = n →
      ∃ q : LTSeries (PrimeSpectrum S), q.length = n ∧
        q.last.asIdeal.comap (algebraMap R S) = p.last.asIdeal := by
  intro n
  induction n with
  | zero =>
    intro p _
    have hker : RingHom.ker (algebraMap R S) ≤ p.last.asIdeal := by
      rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
      exact bot_le
    obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p.last.asIdeal (⊥ : Ideal S)
      (by rw [Ideal.under_def, ← RingHom.ker_eq_comap_bot]; exact hker)
    exact ⟨RelSeries.singleton _ ⟨Q, hQ⟩, rfl, hQc⟩
  | succ n ih =>
    intro p hp
    obtain ⟨q', hq'len, hq'c⟩ := ih p.eraseLast (by
      simp [hp])
    have hlt : p.eraseLast.last < p.last := p.eraseLast_last_rel_last (by omega)
    obtain ⟨Q, hQle, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime
      p.last.asIdeal q'.last.asIdeal (by
        calc
          under R q'.last.asIdeal = p.eraseLast.last.asIdeal := hq'c
          _ ≤ p.last.asIdeal := hlt.le)
    have hlt' : q'.last.asIdeal < Q := by
      refine lt_of_le_of_ne hQle fun h => hlt.ne ?_
      ext1
      calc
        p.eraseLast.last.asIdeal = under R q'.last.asIdeal := hq'c.symm
        _ = under R Q := congrArg (under R) h
        _ = p.last.asIdeal := hQc
    refine ⟨q'.snoc ⟨Q, hQ⟩ hlt', ?_, ?_⟩
    · show q'.length + 1 = n + 1
      rw [hq'len]
    · rw [RelSeries.last_snoc]
      exact hQc

theorem le_ringKrullDim_of_isIntegral {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : f.IsIntegral) (hinj : Function.Injective f) (n : ℕ)
    (h : (n : WithBot ℕ∞) ≤ ringKrullDim R) : (n : WithBot ℕ∞) ≤ ringKrullDim S := by
  letI := f.toAlgebra
  haveI : Algebra.IsIntegral R S := ⟨hf⟩
  obtain ⟨p, hp⟩ := Order.le_krullDim_iff.mp h
  obtain ⟨q, hq, -⟩ := exists_ltSeries_lift hinj n p hp
  exact Order.le_krullDim_iff.mpr ⟨q, hq⟩

theorem int_isJacobsonRing : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  by_cases hb : P = ⊥
  · subst hb
    refine le_antisymm (fun x hx => ?_) bot_le
    rw [Ideal.mem_jacobson_bot] at hx
    have h1 := Int.isUnit_iff.mp (by simpa using hx 1)
    have h2 := Int.isUnit_iff.mp (hx 2)
    rw [Ideal.mem_bot]
    omega
  · haveI : P.IsMaximal := hP.isMaximal hb
    exact Ideal.jacobson_eq_self_of_isMaximal

theorem exists_gt_of_comap_int_eq_bot {σ A : Type*} [Finite σ] [CommRing A]
    (g : MvPolynomial σ ℤ →+* A) (hg : Function.Surjective g) (p : Ideal A) (hp : p.IsPrime)
    (hb : p.comap (g.comp MvPolynomial.C) = ⊥) : ∃ q : Ideal A, q.IsPrime ∧ p < q := by
  haveI := int_isJacobsonRing
  have hnm : ¬ p.IsMaximal := by
    intro hm
    haveI := hm
    letI : Field (A ⧸ p) := Ideal.Quotient.field p
    let f : MvPolynomial σ ℤ →+* A ⧸ p := (Ideal.Quotient.mk p).comp g
    have hf : Function.Surjective f := Ideal.Quotient.mk_surjective.comp hg
    have hint : (f.comp MvPolynomial.C).IsIntegral := by
      exact MvPolynomial.comp_C_integral_of_surjective_of_isJacobsonRing f hf
    have hinj : Function.Injective (f.comp MvPolynomial.C) := by
      rw [RingHom.injective_iff_ker_eq_bot, eq_bot_iff]
      intro x hx
      rw [RingHom.mem_ker] at hx
      have hx' : x ∈ p.comap (g.comp MvPolynomial.C) := by
        rw [Ideal.mem_comap]
        exact Ideal.Quotient.eq_zero_iff_mem.mp hx
      rw [hb] at hx'
      exact hx'
    letI := (f.comp MvPolynomial.C).toAlgebra
    haveI : Algebra.IsIntegral ℤ (A ⧸ p) := ⟨hint⟩
    have hZ : IsField ℤ := isField_of_isIntegral_of_isField hinj (Field.toIsField (A ⧸ p))
    obtain ⟨y, hy⟩ := hZ.mul_inv_cancel (two_ne_zero : (2 : ℤ) ≠ 0)
    omega
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p hp.ne_top
  refine ⟨m, hm.isPrime, lt_of_le_of_ne hpm ?_⟩
  rintro rfl
  exact hnm hm

theorem succ_le_ringKrullDim_of_isLocalization {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (M : Submonoid A) [IsLocalization M B]
    (hext : ∀ p : Ideal A, p.IsPrime → Disjoint (M : Set A) p → ∃ q : Ideal A, q.IsPrime ∧ p < q)
    (n : ℕ) (h : (n : WithBot ℕ∞) ≤ ringKrullDim B) :
    ((n + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim A := by
  let φ : PrimeSpectrum B → PrimeSpectrum A := fun q => ⟨q.asIdeal.comap (algebraMap A B), inferInstance⟩
  have hsm : StrictMono φ := fun a b hab => by
    refine lt_of_le_of_ne (Ideal.comap_mono hab.le) fun e => hab.ne ?_
    have e' : (φ a).asIdeal = (φ b).asIdeal := congrArg PrimeSpectrum.asIdeal e
    ext1
    rw [← IsLocalization.map_under M B a.asIdeal, ← IsLocalization.map_under M B b.asIdeal]
    exact congrArg (Ideal.map (algebraMap A B)) e'
  obtain ⟨p, hp⟩ := Order.le_krullDim_iff.mp h
  let p' := p.map φ hsm
  have hdisj : Disjoint (M : Set A) (p'.last.asIdeal : Set A) :=
    ((IsLocalization.isPrime_iff_isPrime_disjoint M B p.last.asIdeal).mp inferInstance).2
  obtain ⟨q, hq, hlt⟩ := hext p'.last.asIdeal inferInstance hdisj
  have hlen : (p'.snoc ⟨q, hq⟩ hlt).length = n + 1 := by
    show p.length + 1 = n + 1
    rw [hp]
  exact Order.le_krullDim_iff.mpr ⟨_, hlen⟩

end ReciprocityTheory.ChartRestriction.G.Geo
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeK
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open Set Filter Topology Module

variable {e : ℕ}

theorem eventually_surjective_clm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [FiniteDimensional ℂ F] {Y : Type*} [TopologicalSpace Y] {A : Y → (Fin e → ℂ) →L[ℂ] F}
    {y0 : Y} (hA : ContinuousAt A y0) (h0 : Function.Surjective (A y0)) :
    ∀ᶠ y in 𝓝 y0, Function.Surjective (A y) := by
  obtain ⟨Bl, hBl⟩ := (A y0 : (Fin e → ℂ) →ₗ[ℂ] F).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr h0)
  set B : F →L[ℂ] (Fin e → ℂ) := LinearMap.toContinuousLinearMap Bl
  have hB : (A y0).comp B = 1 := by
    ext1 v
    exact LinearMap.congr_fun hBl v
  have hc : ContinuousAt (fun y => (A y).comp B) y0 := hA.clm_comp continuousAt_const
  have hU : ∀ᶠ y in 𝓝 y0, IsUnit ((A y).comp B) :=
    hc.eventually (Units.isOpen.mem_nhds (by show IsUnit ((A y0).comp B); rw [hB]; exact isUnit_one))
  filter_upwards [hU] with y hy
  obtain ⟨S, hS⟩ := hy.exists_right_inv
  intro v
  refine ⟨B (S v), ?_⟩
  have := congrArg (fun T : F →L[ℂ] F => T v) hS
  simpa using this

theorem exists_infinite_fibre {W : Set (Fin e → ℂ)} (hW : IsOpen W) (hne : W.Nonempty)
    {Q : (Fin e → ℂ) → (Fin e → ℂ)} (hQ : AnalyticOnNhd ℂ Q W)
    (hdet : ∀ u ∈ W, LinearMap.det (fderiv ℂ Q u : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0) :
    ∃ y, (W ∩ Q ⁻¹' {y}).Infinite := by
  classical
  set rk : (Fin e → ℂ) → ℕ := fun u =>
    finrank ℂ (LinearMap.range (fderiv ℂ Q u : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))) with hrk
  have hbdd : BddAbove (rk '' W) := ⟨e, by
    rintro _ ⟨u, -, rfl⟩
    exact (Submodule.finrank_le _).trans (le_of_eq (finrank_fin_fun ℂ))⟩
  have hmax : ∀ u ∈ W, rk u ≤ sSup (rk '' W) := fun u hu => le_csSup hbdd ⟨u, hu, rfl⟩
  obtain ⟨u0, hu0, hru0⟩ := Nat.sSup_mem (hne.image rk) hbdd
  generalize hrdef : sSup (rk '' W) = r at hru0 hmax
  set L0 : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ) := fderiv ℂ Q u0
  set R0 := LinearMap.range (L0 : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))
  have hR0 : finrank ℂ R0 = r := hru0
  have hr_lt : r < e := by
    by_contra hge
    have hre : finrank ℂ R0 = finrank ℂ (Fin e → ℂ) := by
      rw [hR0, finrank_fin_fun]
      exact le_antisymm (hru0 ▸ (Submodule.finrank_le _).trans (le_of_eq (finrank_fin_fun ℂ)))
        (not_lt.mp hge)
    have htop : R0 = ⊤ := Submodule.eq_top_of_finrank_eq hre
    have hsurj : Function.Surjective (L0 : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) :=
      LinearMap.range_eq_top.mp htop
    have hbij : Function.Bijective (L0 : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) :=
      ⟨LinearMap.injective_iff_surjective.mpr hsurj, hsurj⟩
    have hu : IsUnit (L0 : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) := (Module.End.isUnit_iff _).mpr hbij
    exact ((LinearMap.isUnit_iff_isUnit_det _).mp hu).ne_zero (hdet u0 hu0)
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl R0
  set PL : (Fin e → ℂ) →L[ℂ] R0 := LinearMap.toContinuousLinearMap (R0.projectionOnto C hC)
  have hPL : ∀ x : R0, PL x = x := fun x => Submodule.projectionOnto_apply_left hC x
  set Df0 : (Fin e → ℂ) →L[ℂ] R0 := PL.comp L0
  have hDf0 : Function.Surjective Df0 := by
    intro w
    obtain ⟨v, hv⟩ := LinearMap.mem_range.mp w.2
    refine ⟨v, ?_⟩
    show PL (L0 v) = w
    rw [show L0 v = (w : Fin e → ℂ) from hv]
    exact hPL w
  set K0 := LinearMap.ker (Df0 : (Fin e → ℂ) →ₗ[ℂ] R0)
  have hK0 : finrank ℂ K0 = e - r := by
    show finrank ℂ (LinearMap.ker (Df0 : (Fin e → ℂ) →ₗ[ℂ] R0)) = e - r
    have := LinearMap.finrank_range_add_finrank_ker (Df0 : (Fin e → ℂ) →ₗ[ℂ] R0)
    rw [LinearMap.range_eq_top.mpr hDf0, finrank_top, hR0, finrank_fin_fun] at this
    omega
  obtain ⟨C', hC'⟩ := Submodule.exists_isCompl K0
  set gL : (Fin e → ℂ) →L[ℂ] K0 := LinearMap.toContinuousLinearMap (K0.projectionOnto C' hC')
  have hgL : ∀ x : K0, gL x = x := fun x => Submodule.projectionOnto_apply_left hC' x
  set Φl : (Fin e → ℂ) →ₗ[ℂ] R0 × K0 :=
    LinearMap.prod (Df0 : (Fin e → ℂ) →ₗ[ℂ] R0) (gL : (Fin e → ℂ) →ₗ[ℂ] K0)
  have hinj : Function.Injective Φl := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have h1 : Df0 v = 0 := congrArg Prod.fst hv
    have h2 : gL v = 0 := congrArg Prod.snd hv
    have hvK : v ∈ K0 := h1
    have := hgL ⟨v, hvK⟩
    rw [h2] at this
    exact (congrArg Subtype.val this).symm
  have hdim : finrank ℂ (Fin e → ℂ) = finrank ℂ (R0 × K0) := by
    rw [finrank_prod, finrank_fin_fun, hR0, hK0]; omega
  have hbij : Function.Bijective Φl :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩
  set Φ' : (Fin e → ℂ) ≃L[ℂ] R0 × K0 := (LinearEquiv.ofBijective Φl hbij).toContinuousLinearEquiv
  have hΦ'c : (Φ' : (Fin e → ℂ) →L[ℂ] R0 × K0) = Df0.prod gL := by ext1 v; rfl
  set Φ : (Fin e → ℂ) → R0 × K0 := fun u => (PL (Q u), gL u) with hΦdef
  have hQa0 := hQ u0 hu0
  have hΦd : ∀ u ∈ W, HasFDerivAt Φ ((PL.comp (fderiv ℂ Q u)).prod gL) u := fun u hu =>
    (PL.hasFDerivAt.comp u (hQ u hu).differentiableAt.hasFDerivAt).prodMk gL.hasFDerivAt
  have hΦa : ∀ u ∈ W, AnalyticAt ℂ Φ u := fun u hu =>
    ((PL.analyticAt _).comp (hQ u hu)).prod (gL.analyticAt u)
  have hstrict : HasStrictFDerivAt Φ (Φ' : (Fin e → ℂ) →L[ℂ] R0 × K0) u0 := by
    rw [hΦ'c]
    have := (hΦa u0 hu0).hasStrictFDerivAt
    rwa [(hΦd u0 hu0).fderiv] at this
  set H := hstrict.toOpenPartialHomeomorph Φ
  have hHc : (H : (Fin e → ℂ) → R0 × K0) = Φ := hstrict.toOpenPartialHomeomorph_coe
  have hus : u0 ∈ H.source := hstrict.mem_toOpenPartialHomeomorph_source
  have hpt : Φ u0 ∈ H.target := hstrict.image_mem_toOpenPartialHomeomorph_target
  have hsym0 : H.symm (Φ u0) = u0 := by have := H.left_inv hus; rwa [hHc] at this
  have hsa : AnalyticAt ℂ H.symm (Φ u0) := by
    refine H.analyticAt_symm (i := Φ') hpt ?_ ?_
    · rw [hsym0, hHc]; exact hΦa u0 hu0
    · rw [hsym0, hHc, (hΦd u0 hu0).fderiv, hΦ'c]
  have hA : ContinuousAt (fun u => PL.comp (fderiv ℂ Q u)) u0 :=
    continuousAt_const.clm_comp hQa0.fderiv.continuousAt
  have hev_u : ∀ᶠ u in 𝓝 u0, u ∈ W ∧ Function.Surjective (PL.comp (fderiv ℂ Q u)) :=
    (Filter.eventually_of_mem (hW.mem_nhds hu0) fun u hu => hu).and (eventually_surjective_clm hA hDf0)
  have hev : ∀ᶠ p in 𝓝 (Φ u0), p ∈ H.target ∧ AnalyticAt ℂ H.symm p ∧ H.symm p ∈ W ∧
      Function.Surjective (PL.comp (fderiv ℂ Q (H.symm p))) := by
    have h1 : ∀ᶠ p in 𝓝 (Φ u0), H.symm p ∈ W ∧
        Function.Surjective (PL.comp (fderiv ℂ Q (H.symm p))) :=
      (H.continuousAt_symm hpt).eventually (by rw [hsym0]; exact hev_u)
    filter_upwards [H.open_target.mem_nhds hpt, hsa.eventually_analyticAt, h1] with p h2 h3 h4
    exact ⟨h2, h3, h4⟩
  have hkey : ∀ p, p ∈ H.target → AnalyticAt ℂ H.symm p → H.symm p ∈ W →
      Function.Surjective (PL.comp (fderiv ℂ Q (H.symm p))) → ∀ κ : K0,
      fderiv ℂ (Q ∘ H.symm) p (0, κ) = 0 := by
    intro p hp han hW' hs κ
    have hcomp : HasFDerivAt (Φ ∘ H.symm)
        (((PL.comp (fderiv ℂ Q (H.symm p))).prod gL).comp (fderiv ℂ H.symm p)) p :=
      (hΦd _ hW').comp p han.differentiableAt.hasFDerivAt
    have hid : HasFDerivAt (Φ ∘ H.symm) (ContinuousLinearMap.id ℂ (R0 × K0)) p := by
      refine (hasFDerivAt_id p).congr_of_eventuallyEq ?_
      filter_upwards [H.open_target.mem_nhds hp] with p' hp'
      show Φ (H.symm p') = p'
      rw [← hHc]; exact H.right_inv hp'
    have heq := hcomp.unique hid
    have hw := congrArg (fun T => T (0, κ)) heq
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply] at hw
    have hw1 : PL (fderiv ℂ Q (H.symm p) (fderiv ℂ H.symm p (0, κ))) = 0 := congrArg Prod.fst hw
    have hker : LinearMap.ker (fderiv ℂ Q (H.symm p) : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) =
        LinearMap.ker ((PL.comp (fderiv ℂ Q (H.symm p))) : (Fin e → ℂ) →ₗ[ℂ] R0) := by
      apply Submodule.eq_of_le_of_finrank_le
      · intro v hv
        rw [LinearMap.mem_ker] at hv ⊢
        show PL (fderiv ℂ Q (H.symm p) v) = 0
        rw [show (fderiv ℂ Q (H.symm p)) v = 0 from hv, map_zero]
      · have h1 := LinearMap.finrank_range_add_finrank_ker
          ((PL.comp (fderiv ℂ Q (H.symm p))) : (Fin e → ℂ) →ₗ[ℂ] R0)
        have h2 := LinearMap.finrank_range_add_finrank_ker
          (fderiv ℂ Q (H.symm p) : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))
        rw [LinearMap.range_eq_top.mpr hs, finrank_top, hR0] at h1
        have h3 : finrank ℂ (LinearMap.range (fderiv ℂ Q (H.symm p) :
            (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))) ≤ r := hmax _ hW'
        omega
    have hwker : fderiv ℂ H.symm p (0, κ) ∈
        LinearMap.ker (fderiv ℂ Q (H.symm p) : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) := by
      rw [hker]; exact hw1
    rw [fderiv_comp p (hQ _ hW').differentiableAt han.differentiableAt]
    exact hwker
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  set c0 := Φ u0
  set ι : K0 → R0 × K0 := fun k => (c0.1, c0.2 + k) with hιdef
  have hιball : ∀ k ∈ Metric.ball (0 : K0) ε, ι k ∈ Metric.ball c0 ε := by
    intro k hk
    have h0 : ι k - c0 = (0, k) := by
      simp only [hιdef]
      ext <;> simp
    rw [Metric.mem_ball, dist_eq_norm, h0, Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg k)]
    rwa [Metric.mem_ball, dist_zero_right] at hk
  have hιd : ∀ k, HasFDerivAt ι (ContinuousLinearMap.inr ℂ R0 K0) k := fun k =>
    (hasFDerivAt_const c0.1 k).prodMk ((hasFDerivAt_id k).const_add c0.2)
  have hGd : ∀ k ∈ Metric.ball (0 : K0) ε, HasFDerivAt (fun k => Q (H.symm (ι k))) (0 : K0 →L[ℂ] (Fin e → ℂ)) k := by
    intro k hk
    obtain ⟨hp, han, hW', hs⟩ := hball _ (hιball k hk)
    have hG : HasFDerivAt (Q ∘ H.symm) (fderiv ℂ (Q ∘ H.symm) (ι k)) (ι k) :=
      ((hQ _ hW').differentiableAt.comp _ han.differentiableAt).hasFDerivAt
    have := hG.comp k (hιd k)
    have h0 : (fderiv ℂ (Q ∘ H.symm) (ι k)).comp (ContinuousLinearMap.inr ℂ R0 K0) = 0 := by
      ext1 κ
      simp [hkey _ hp han hW' hs κ]
    rw [h0] at this
    exact this
  have hconst : ∀ k ∈ Metric.ball (0 : K0) ε, Q (H.symm (ι k)) = Q (H.symm (ι 0)) := by
    intro k hk
    exact (convex_ball (0 : K0) ε).is_const_of_fderivWithin_eq_zero (𝕜 := ℂ)
      (fun k' hk' => (hGd k' hk').differentiableAt.differentiableWithinAt)
      (fun k' hk' => by
        rw [fderivWithin_of_isOpen Metric.isOpen_ball hk']; exact (hGd k' hk').fderiv)
      hk (Metric.mem_ball_self hε)
  have hι0 : ι 0 = c0 := by simp [hιdef]
  have : Nontrivial K0 := Module.nontrivial_of_finrank_pos (by rw [hK0]; omega)
  have hinf : (Metric.ball (0 : K0) ε).Infinite :=
    infinite_of_mem_nhds (0 : K0) (Metric.ball_mem_nhds 0 hε)
  refine ⟨Q u0, (Set.Infinite.image (f := fun k => H.symm (ι k)) ?_ hinf).mono ?_⟩
  · intro k hk k' hk' hkk
    have h1 := (hball _ (hιball k hk)).1
    have h2 := (hball _ (hιball k' hk')).1
    have : ι k = ι k' := H.symm.injOn h1 h2 hkk
    simpa [hιdef] using this
  · rintro _ ⟨k, hk, rfl⟩
    refine ⟨(hball _ (hιball k hk)).2.2.1, ?_⟩
    show Q (H.symm (ι k)) = Q u0
    rw [hconst k hk, hι0, hsym0]

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeG
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MeasureTheory Set Filter Topology Function

variable {e : ℕ}

def jacN (Q : (Fin e → ℂ) → (Fin e → ℂ)) (u : Fin e → ℂ) : ℝ :=
  ‖LinearMap.det (fderiv ℂ Q u : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ^ 2

def fibSum (D : Set (Fin e → ℂ)) (Q : (Fin e → ℂ) → (Fin e → ℂ)) (h : (Fin e → ℂ) → ℝ)
    (y : Fin e → ℂ) : ℝ :=
  ∑ᶠ u ∈ D ∩ Q ⁻¹' {y}, h u / jacN Q u

theorem abs_det_restrictScalars (f : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) :
    |(f.restrictScalars ℝ).det| = ‖LinearMap.det (f : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ^ 2 := by
  have h : (f.restrictScalars ℝ).det =
      Complex.normSq (LinearMap.det (f : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))) := by
    show LinearMap.det ((f : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)).restrictScalars ℝ) = _
    rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply]
  rw [h, abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]

theorem piece_change {D : Set (Fin e → ℂ)} (hD : MeasurableSet D) {Q : (Fin e → ℂ) → (Fin e → ℂ)}
    (hQd : ∀ u ∈ D, DifferentiableAt ℂ Q u)
    (hdet : ∀ u ∈ D, LinearMap.det (fderiv ℂ Q u : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)
    (hinj : InjOn Q D) {h : (Fin e → ℂ) → ℝ} (hh : IntegrableOn h D) :
    Integrable (fibSum D Q h) ∧ ∫ y, fibSum D Q h y = ∫ u in D, h u ∧
      ∫ y, ‖fibSum D Q h y‖ = ∫ u in D, ‖h u‖ := by
  have hf' : ∀ u ∈ D, HasFDerivWithinAt Q ((fderiv ℂ Q u).restrictScalars ℝ) D u :=
    fun u hu => ((hQd u hu).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hJpos : ∀ u ∈ D, 0 < jacN Q u := fun u hu =>
    pow_pos (norm_pos_iff.mpr (hdet u hu)) 2
  have hval : ∀ u ∈ D, fibSum D Q h (Q u) = h u / jacN Q u := by
    intro u hu
    have : D ∩ Q ⁻¹' {Q u} = {u} := by
      ext v
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
      exact ⟨fun ⟨hv, hq⟩ => hinj hv hu hq, fun hv => by subst hv; exact ⟨hu, rfl⟩⟩
    simp only [fibSum, this, finsum_mem_singleton]
  have hzero : ∀ y, y ∉ Q '' D → fibSum D Q h y = 0 := by
    intro y hy
    have : D ∩ Q ⁻¹' {y} = ∅ := by
      ext v
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false,
        not_and]
      exact fun hv hq => hy ⟨v, hv, hq⟩
    simp [fibSum, this]
  have hdetJ : ∀ u, |((fderiv ℂ Q u).restrictScalars ℝ).det| = jacN Q u := fun u =>
    abs_det_restrictScalars _
  have hkey : EqOn (fun u => |((fderiv ℂ Q u).restrictScalars ℝ).det| • fibSum D Q h (Q u)) h D := by
    intro u hu
    simp only [hval u hu, hdetJ, smul_eq_mul]
    field_simp [(hJpos u hu).ne']
  have hkeyn : EqOn (fun u => |((fderiv ℂ Q u).restrictScalars ℝ).det| • ‖fibSum D Q h (Q u)‖)
      (fun u => ‖h u‖) D := by
    intro u hu
    simp only [hval u hu, hdetJ, smul_eq_mul, norm_div, Real.norm_of_nonneg (hJpos u hu).le]
    field_simp [(hJpos u hu).ne']
  have hint_on : IntegrableOn (fibSum D Q h) (Q '' D) := by
    rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hD hf' hinj]
    exact hh.congr_fun (fun u hu => (hkey hu).symm) hD
  have hint : Integrable (fibSum D Q h) := hint_on.integrable_of_forall_notMem_eq_zero hzero
  refine ⟨hint, ?_, ?_⟩
  · rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
      integral_image_eq_integral_abs_det_fderiv_smul volume hD hf' hinj]
    exact setIntegral_congr_fun hD hkey
  · rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Q '' D)
      (fun y hy => by rw [hzero y hy, norm_zero]),
      integral_image_eq_integral_abs_det_fderiv_smul volume hD hf' hinj]
    exact setIntegral_congr_fun hD hkeyn

theorem exists_inj_cover {O : Set (Fin e → ℂ)} {Q : (Fin e → ℂ) → (Fin e → ℂ)}
    (hQ : ∀ u ∈ O, AnalyticAt ℂ Q u ∧
      LinearMap.det (fderiv ℂ Q u : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0) (hO : IsOpen O) :
    ∃ W : ℕ → Set (Fin e → ℂ), (∀ n, IsOpen (W n)) ∧ (∀ n, W n ⊆ O) ∧ (∀ n, InjOn Q (W n)) ∧
      ⋃ n, W n = O := by
  classical
  set s : Set (Set (Fin e → ℂ)) :=
    insert ∅ {b | b ∈ TopologicalSpace.countableBasis (Fin e → ℂ) ∧ b ⊆ O ∧ InjOn Q b}
  have hs : s.Countable := by
    apply Set.Countable.insert
    apply (TopologicalSpace.countable_countableBasis (Fin e → ℂ)).mono
    intro b hb
    exact hb.1
  have hmem : ∀ n, Set.enumerateCountable hs ∅ n ∈ s := Set.enumerateCountable_mem hs
    (Set.mem_insert _ _)
  refine ⟨Set.enumerateCountable hs ∅, fun n => ?_, fun n => ?_, fun n => ?_, ?_⟩
  · rcases hmem n with h | h
    · rw [h]; exact isOpen_empty
    · exact TopologicalSpace.isOpen_of_mem_countableBasis h.1
  · rcases hmem n with h | h
    · rw [h]; exact empty_subset _
    · exact h.2.1
  · rcases hmem n with h | h
    · rw [h]; exact injOn_empty _
    · exact h.2.2
  · refine Subset.antisymm (iUnion_subset fun n => ?_) fun u hu => ?_
    · rcases hmem n with h | h
      · rw [h]; exact empty_subset _
      · exact h.2.1
    obtain ⟨hQa, hQd⟩ := hQ u hu
    set Ce := (fderiv ℂ Q u).toContinuousLinearEquivOfDetNeZero hQd
    have hCe : (Ce : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) = fderiv ℂ Q u :=
      ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ hQd
    have hstrict : HasStrictFDerivAt Q (Ce : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) u := by
      rw [hCe]; exact hQa.hasStrictFDerivAt
    set F := hstrict.toOpenPartialHomeomorph Q
    have hFc : (F : (Fin e → ℂ) → (Fin e → ℂ)) = Q := hstrict.toOpenPartialHomeomorph_coe
    have hus : u ∈ F.source := hstrict.mem_toOpenPartialHomeomorph_source
    obtain ⟨b, hbB, hub, hbsub⟩ := (TopologicalSpace.isBasis_countableBasis (Fin e → ℂ)).exists_subset_of_mem_open
      (⟨hus, hu⟩ : u ∈ F.source ∩ O) (F.open_source.inter hO)
    have hbs : b ∈ s := Or.inr ⟨hbB, fun v hv => (hbsub hv).2, by
      rw [← hFc]; exact F.injOn.mono fun v hv => (hbsub hv).1⟩
    obtain ⟨n, hn⟩ := Set.subset_range_enumerate hs ∅ hbs
    exact mem_iUnion.mpr ⟨n, hn ▸ hub⟩

theorem integrable_tsum_of_summable {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℕ → α → ℝ} (hF : ∀ n, Integrable (F n) μ) (hs : Summable fun n => ∫ y, ‖F n y‖ ∂μ) :
    Integrable (fun y => ∑' n, F n y) μ := by
  have hmeas : ∀ n, AEMeasurable (fun y => ‖F n y‖ₑ) μ := fun n => (hF n).aemeasurable.enorm
  have hlin : ∫⁻ y, ∑' n, ‖F n y‖ₑ ∂μ ≠ ⊤ := by
    rw [lintegral_tsum hmeas]
    have : ∀ n, ∫⁻ y, ‖F n y‖ₑ ∂μ = ENNReal.ofReal (∫ y, ‖F n y‖ ∂μ) := fun n =>
      (ofReal_integral_norm_eq_lintegral_enorm (hF n)).symm
    simp_rw [this]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg fun _ => norm_nonneg _) hs]
    exact ENNReal.ofReal_ne_top
  have hae : ∀ᵐ y ∂μ, ∑' n, ‖F n y‖ₑ < ⊤ := ae_lt_top' (AEMeasurable.tsum hmeas) hlin
  have hsum : ∀ᵐ y ∂μ, Summable fun n => F n y := by
    filter_upwards [hae] with y hy
    refine Summable.of_norm ?_
    have : (∑' n, (‖F n y‖₊ : ENNReal)) ≠ ⊤ := hy.ne
    exact NNReal.summable_coe.mpr (ENNReal.tsum_coe_ne_top_iff_summable.mp this)
  refine ⟨aestronglyMeasurable_of_tendsto_ae atTop (f := fun N y => ∑ n ∈ Finset.range N, F n y)
    (fun N => Finset.aestronglyMeasurable_fun_sum _ fun n _ => (hF n).1) ?_, ?_⟩
  · filter_upwards [hsum] with y hy
    exact hy.hasSum.tendsto_sum_nat
  · refine lt_of_le_of_lt (lintegral_mono fun y => enorm_tsum_le_tsum_enorm) ?_
    exact lt_top_iff_ne_top.mpr hlin

theorem tsum_finsum_disjointed {α : Type*} {D : ℕ → Set α} (hd : Pairwise (Disjoint on D))
    {O : Set α} (hU : ⋃ n, D n = O) {G : Set α} (hG : (O ∩ G).Finite) (f : α → ℝ) :
    ∑' n, ∑ᶠ u ∈ D n ∩ G, f u = ∑ᶠ u ∈ O ∩ G, f u := by
  classical
  have hsub : ∀ n, D n ⊆ O := fun n => hU ▸ subset_iUnion D n
  have hterm : ∀ n, ∑ᶠ u ∈ D n ∩ G, f u = ∑ u ∈ hG.toFinset, if u ∈ D n then f u else 0 := by
    intro n
    have hfin : (D n ∩ G).Finite := hG.subset fun u hu => ⟨hsub n hu.1, hu.2⟩
    rw [finsum_mem_eq_finite_toFinset_sum f hfin,
      Finset.sum_ite, Finset.sum_const_zero, add_zero]
    congr 1
    ext u
    simp only [Finite.mem_toFinset, Finset.mem_filter, mem_inter_iff]
    exact ⟨fun h => ⟨⟨hsub n h.1, h.2⟩, h.1⟩, fun h => ⟨h.2, h.1.2⟩⟩
  have hfun : ∀ u ∈ hG.toFinset, ∃ n0 : ℕ,
      (fun n => if u ∈ D n then f u else 0) = fun n => if n = n0 then f u else 0 := by
    intro u hu
    have huO : u ∈ O := (hG.mem_toFinset.mp hu).1
    obtain ⟨n0, hn0⟩ := mem_iUnion.mp (hU ▸ huO : u ∈ ⋃ n, D n)
    refine ⟨n0, funext fun n => ?_⟩
    by_cases hn : n = n0
    · subst hn; simp [hn0]
    · have : u ∉ D n := fun h => (hd hn).le_bot ⟨h, hn0⟩
      simp [this, hn]
  simp_rw [hterm]
  rw [Summable.tsum_finsetSum (fun u hu => ?_), finsum_mem_eq_finite_toFinset_sum f hG]
  · refine Finset.sum_congr rfl fun u hu => ?_
    obtain ⟨n0, h⟩ := hfun u hu
    rw [h, tsum_ite_eq]
  · obtain ⟨n0, h⟩ := hfun u hu
    rw [h]
    exact (hasSum_ite_eq n0 (f u)).summable

theorem area_open {O : Set (Fin e → ℂ)} (hO : IsOpen O) {Q : (Fin e → ℂ) → (Fin e → ℂ)}
    (hQ : ∀ u ∈ O, AnalyticAt ℂ Q u ∧
      LinearMap.det (fderiv ℂ Q u : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)
    {h : (Fin e → ℂ) → ℝ} (hh : IntegrableOn h O) (hfin : ∀ᵐ y, (O ∩ Q ⁻¹' {y}).Finite) :
    Integrable (fibSum O Q h) ∧ ∫ u in O, h u = ∫ y, fibSum O Q h y := by
  obtain ⟨W, hWo, hWO, hWinj, hWU⟩ := exists_inj_cover hQ hO
  set D := disjointed W with hDdef
  have hDm : ∀ n, MeasurableSet (D n) := MeasurableSet.disjointed fun n => (hWo n).measurableSet
  have hDsub : ∀ n, D n ⊆ W n := disjointed_subset W
  have hDU : ⋃ n, D n = O := iUnion_disjointed.trans hWU
  have hDd : Pairwise (Disjoint on D) := disjoint_disjointed W
  have hDO : ∀ n, D n ⊆ O := fun n => (hDsub n).trans (hWO n)
  have hp : ∀ n, Integrable (fibSum (D n) Q h) ∧ ∫ y, fibSum (D n) Q h y = ∫ u in D n, h u ∧
      ∫ y, ‖fibSum (D n) Q h y‖ = ∫ u in D n, ‖h u‖ := fun n =>
    piece_change (hDm n) (fun u hu => (hQ u (hDO n hu)).1.differentiableAt)
      (fun u hu => (hQ u (hDO n hu)).2) ((hWinj n).mono (hDsub n)) (hh.mono_set (hDO n))
  have hhO : IntegrableOn h (⋃ n, D n) := by rw [hDU]; exact hh
  have hs1 := hasSum_integral_iUnion hDm hDd hhO
  have hs2 := hasSum_integral_iUnion hDm hDd hhO.norm
  have hn2 : ∀ n, ∫ y, ‖fibSum (D n) Q h y‖ = ∫ u in D n, ‖h u‖ := fun n => (hp n).2.2
  have hn1 : ∀ n, ∫ y, fibSum (D n) Q h y = ∫ u in D n, h u := fun n => (hp n).2.1
  have hsumm : Summable fun n => ∫ y, ‖fibSum (D n) Q h y‖ := by
    simp_rw [hn2]; exact hs2.summable
  have htsum : ∫ y, ∑' n, fibSum (D n) Q h y = ∑' n, ∫ y, fibSum (D n) Q h y :=
    (integral_tsum_of_summable_integral_norm (fun n => (hp n).1) hsumm).symm
  have hae : (fun y => ∑' n, fibSum (D n) Q h y) =ᵐ[volume] fibSum O Q h := by
    filter_upwards [hfin] with y hy
    simp only [fibSum]
    exact tsum_finsum_disjointed hDd hDU hy (fun u => h u / jacN Q u)
  refine ⟨(integrable_tsum_of_summable (fun n => (hp n).1) hsumm).congr hae, ?_⟩
  rw [← integral_congr_ae hae, htsum]
  simp_rw [hn1]
  rw [hs1.tsum_eq, hDU]

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

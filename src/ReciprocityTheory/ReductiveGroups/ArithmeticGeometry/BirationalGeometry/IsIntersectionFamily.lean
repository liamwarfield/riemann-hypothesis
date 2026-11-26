module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial MeasureTheory Filter Topology

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

section Algebra

abbrev MRingOver (R : Type*) [CommRing R] (ι : K → Type*) := MvPolynomial (Σ k, ι k) R

abbrev MRing (ι : K → Type*) := MRingOver ℤ ι

variable {R : Type*} [CommRing R]

def IsMultiHomog (s : MRingOver R ι) (a : K → ℕ) : Prop :=
  ∀ m ∈ s.support, ∀ k, ∑ i, m ⟨k, i⟩ = a k

def IsMultiHomogIdeal (P : Ideal (MRingOver R ι)) : Prop :=
  ∃ S : Set (MRingOver R ι), (∀ f ∈ S, ∃ a, IsMultiHomog f a) ∧ P = Ideal.span S

def IsRelevant (W : Ideal (MRingOver R ι)) : Prop :=
  ∀ k, ∃ i, (X ⟨k, i⟩ : MRingOver R ι) ∉ W

def IsMultiProjPrime (P : Ideal (MRingOver R ι)) : Prop :=
  P.IsPrime ∧ IsMultiHomogIdeal P ∧ IsRelevant P

def IsHorizontal (P : Ideal (MRing ι)) : Prop :=
  P.comap (C : ℤ →+* MRing ι) = ⊥

def IsArithVar (P : Ideal (MRing ι)) (d : ℕ) : Prop :=
  Nonempty K ∧ IsMultiProjPrime P ∧ IsHorizontal P ∧
    ringKrullDim (MRing ι ⧸ P) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞)

def divSupp (P : Ideal (MRingOver R ι)) (s : MRingOver R ι) : Set (Ideal (MRingOver R ι)) :=
  {W | W ∈ (P ⊔ Ideal.span {s}).minimalPrimes ∧ IsRelevant W}


open scoped Classical in
open Classical in
def multAt (J W : Ideal (MRingOver R ι)) : ℕ :=
  if h : W.IsPrime then
    haveI := h
    (Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (MRingOver R ι ⧸ J))).toNat
  else 0

theorem divSupp_finite [IsNoetherianRing R] (P : Ideal (MRingOver R ι)) (s : MRingOver R ι) : (divSupp P s).Finite :=
  (Ideal.finite_minimalPrimes_of_isNoetherianRing _ (P ⊔ Ideal.span {s})).subset fun _ hW => hW.1

def divCycle [IsNoetherianRing R] (P : Ideal (MRingOver R ι)) (s : MRingOver R ι) :
    Ideal (MRingOver R ι) →₀ ℕ := by
  classical
  exact Finsupp.ofSupportFinite
    (fun W => if W ∈ divSupp P s then multAt (P ⊔ Ideal.span {s}) W else 0)
    ((divSupp_finite P s).subset fun W hW => by
      by_contra h
      exact hW (ite_eq_right h))

def charOf (W : Ideal (MRing ι)) : ℕ :=
  (Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι))).natAbs


open scoped Classical in
open Classical in
def geoNum : (n : ℕ) → Ideal (MRing ι) → (Fin n → K → ℤ) → ℤ
  | 0, V, _ =>
    if h : IsRelevant V then
      ((Module.length ℤ
        (MRing ι ⧸ (V ⊔ Ideal.span (Set.range fun k => (X ⟨k, (h k).choose⟩ : MRing ι) - 1)))).toNat : ℤ)
    else 0
  | n + 1, V, a =>
    if h : IsRelevant V then
      ∑ k, a (Fin.last n) k *
        ∑ᶠ W ∈ divSupp V (X ⟨k, (h k).choose⟩),
          (multAt (V ⊔ Ideal.span {(X ⟨k, (h k).choose⟩ : MRing ι)}) W : ℤ) * geoNum n W (Fin.init a)
    else 0

end Algebra

section Complex

def mcPts (P : Ideal (MRing ι)) : Set ((Σ k, ι k) → ℂ) :=
  {z | (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) ∧ ∀ f ∈ P, eval z (map (Int.castRingHom ℂ) f) = 0}


variable (ι) in
structure HermLine (ι : K → Type*) where

  a : K → ℤ

  h : ((Σ k, ι k) → ℂ) → ℝ
  pos : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → 0 < h z
  smul : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) →
    h (fun p => c p.1 * z p) = (∏ k, ‖c k‖ ^ a k) * h z

def IsSmoothHerm (A : HermLine ι) : Prop :=
  ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A.h {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}

def HermLine.tensor (A B : HermLine ι) : HermLine ι where
  a := A.a + B.a
  h z := A.h z * B.h z
  pos z hz := mul_pos (A.pos z hz) (B.pos z hz)
  smul c z hc := by
    rw [A.smul c z hc, B.smul c z hc]
    have : ∀ k, ‖c k‖ ^ (A.a + B.a) k = ‖c k‖ ^ A.a k * ‖c k‖ ^ B.a k := fun k =>
      zpow_add₀ (norm_ne_zero_iff.mpr (hc k)) _ _
    simp only [this, Finset.prod_mul_distrib]
    ring

def segre (z : (Σ k, ι k) → ℂ) : ((k : K) → ι k) → ℂ :=
  fun i => ∏ k, z ⟨k, i k⟩

variable {e : ℕ}

def fibre (P : Ideal (MRing ι)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (y : Fin e → ℂ) : Set (((k : K) → ι k) → ℂ) :=
  {w | ∃ z ∈ mcPts P, segre z = w ∧ Ψ w = Fin.cons 1 y}

def IsSheet (P : Ideal (MRing ι)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (y : Fin e → ℂ) (w : ((k : K) → ι k) → ℂ) (γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ) : Prop :=
  segre (γ y) = w ∧ ∀ᶠ y' in 𝓝 y,
    DifferentiableAt ℂ γ y' ∧ γ y' ∈ mcPts P ∧ Ψ (segre (γ y')) = Fin.cons 1 y'

def sheetDensity (P : Ideal (MRing ι)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) (y : Fin e → ℂ)
    (w : ((k : K) → ι k) → ℂ) : ℝ := by
  classical
  exact if hγ : ∃ γ, IsSheet P Ψ y w γ then
    g (hγ.choose y) * maDensity (fun j y' => φ j (hγ.choose y')) y
  else 0

def ptsIntegralAt (P : Ideal (MRing ι)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) : ℝ :=
  ∫ y, ∑ᶠ w ∈ fibre P Ψ y, sheetDensity P Ψ φ g y w

def IsGoodProj (P : Ideal (MRing ι)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) : Prop :=
  ∀ z ∈ mcPts P, Ψ (segre z) ≠ 0

def ptsIntegral (P : Ideal (MRing ι)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    (g : ((Σ k, ι k) → ℂ) → ℝ) : ℝ := by
  classical
  exact if hΨ : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P Ψ then
    ptsIntegralAt P hΨ.choose φ g
  else 0

def logNorm (A : HermLine ι) (s : MRing ι) (z : (Σ k, ι k) → ℂ) : ℝ :=
  Real.log (‖eval z (map (Int.castRingHom ℂ) s)‖ / A.h z)

def arInt (P : Ideal (MRing ι)) (s : MRing ι) (A : HermLine ι) (L : Fin e → HermLine ι) : ℝ :=
  ptsIntegral P (fun j z => Real.log ((L j).h z)) (logNorm A s)

end Complex

section Constructors

def HermLine.ofMetrics (m : ∀ k, ConeMetric (C := ℂ) (ι := ι k)) (a : K → ℤ) : HermLine ι where
  a := a
  h z := ∏ k, (m k).ρ (fun i => z ⟨k, i⟩) ^ a k
  pos z hz := Finset.prod_pos fun k _ => by
    obtain ⟨i, hi⟩ := hz k
    exact zpow_pos ((m k).pos _ fun h0 => hi (congrFun h0 i)) _
  smul c z hc := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    have : (fun i => c k * z ⟨k, i⟩) = c k • fun i => z ⟨k, i⟩ := rfl
    simp only [this, (m k).smul, mul_zpow]

def HermLine.ofWeight (u : ((Σ k, ι k) → ℂ) → ℝ)
    (hu : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → u (fun p => c p.1 * z p) = u z) : HermLine ι where
  a := 0
  h z := Real.exp (-u z)
  pos _ _ := Real.exp_pos _
  smul c z hc := by simp [hu c z hc]

end Constructors

section Family

def recR (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι)) {n : ℕ}
    (L : Fin n → HermLine ι) (A : HermLine ι) (s : MRing ι) : ℝ := by
  classical
  exact (∑ᶠ W ∈ divSupp P s, (multAt (P ⊔ Ideal.span {s}) W : ℝ) *
      (if IsHorizontal W then I W n L
        else (geoNum n W (fun j => (L j).a) : ℝ) * Real.log (charOf W))) -
    arInt P s A L

def IsIntersectionFamily (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) : Prop :=
  (∀ P n (L : Fin n → HermLine ι) (σ : Equiv.Perm (Fin n)), IsArithVar P n →
      (∀ j, IsSmoothHerm (L j)) → I P n (L ∘ σ) = I P n L) ∧
  (∀ P n (L : Fin n → HermLine ι) (A B : HermLine ι), IsArithVar P (n + 1) →
      (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm B →
      I P (n + 1) (Fin.snoc L (A.tensor B)) =
        I P (n + 1) (Fin.snoc L A) + I P (n + 1) (Fin.snoc L B)) ∧
  (∀ P n (L : Fin n → HermLine ι) (A : HermLine ι) (s : MRing ι) (a : K → ℕ),
      IsArithVar P (n + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A →
      (∀ k, A.a k = a k) → IsMultiHomog s a → s ∉ P →
      I P (n + 1) (Fin.snoc L A) = recR I P L A s)

end Family

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.LemCone
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

section Coord

variable (o : Type*) {Ω : Type*} [CommRing o] [CommRing Ω] [Algebra o Ω] {ι : Type*}

private theorem coneMap_monomial' (x : ι → Ω) (e : ι →₀ ℕ) (a : o) :
    coneMap o x (monomial e a) = Polynomial.C (aeval x (monomial e a)) * Polynomial.X ^ e.degree := by
  unfold coneMap
  rw [aeval_monomial, aeval_monomial, Polynomial.algebraMap_apply, map_mul, mul_assoc]
  congr 1
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, map_prod, Polynomial.C_pow,
    Finset.prod_pow_eq_pow_sum]
  congr 1

private theorem coeff_coneMap_eq_aeval_homogeneousComponent (x : ι → Ω) (f : MvPolynomial ι o) (d : ℕ) :
    (coneMap o x f).coeff d = aeval x (homogeneousComponent d f) := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [f.as_sum, map_sum]
  rw [Polynomial.finsetSum_coeff]
  simp only [coneMap_monomial', Polynomial.coeff_C_mul_X_pow]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [homogeneousComponent_apply, map_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun e _ => ?_
  rcases eq_or_ne e.degree d with h | h
  · simp [h]
  · rw [if_neg (Ne.symm h), if_neg h]

theorem coneMap_of_isHomogeneous (x : ι → Ω) {f : MvPolynomial ι o} {n : ℕ}
    (hf : f.IsHomogeneous n) :
    coneMap o x f = Polynomial.C (aeval x f) * Polynomial.X ^ n := by
  ext d
  rw [coeff_coneMap_eq_aeval_homogeneousComponent, Polynomial.coeff_C_mul_X_pow,
    homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 hf)]
  rcases eq_or_ne d n with rfl | h
  · simp
  · rw [if_neg h, if_neg h, map_zero]

theorem mem_coordIdeal_of_isHomogeneous (x : ι → Ω) {f : MvPolynomial ι o} {n : ℕ}
    (hf : f.IsHomogeneous n) (h : aeval x f = 0) : f ∈ coordIdeal o x := by
  rw [coordIdeal, RingHom.mem_ker, coneMap_of_isHomogeneous o x hf, h, map_zero, zero_mul]

theorem coeff_coneMap (x : ι → Ω) (f : MvPolynomial ι o) (d : ℕ) :
    (coneMap o x f).coeff d = aeval x (homogeneousComponent d f) := by
  exact coeff_coneMap_eq_aeval_homogeneousComponent o x f d

theorem coordIdeal_isHomogIdeal (x : ι → Ω) : IsHomogIdeal o (coordIdeal o x) := by
  intro f hf d
  rw [coordIdeal, RingHom.mem_ker] at hf ⊢
  rw [coneMap_of_isHomogeneous o x (homogeneousComponent_isHomogeneous d f), ← coeff_coneMap, hf,
    Polynomial.coeff_zero, map_zero, zero_mul]

end Coord

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

section Chart

variable (o : Type*) {Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω] {ι : Type*}

def chartRing (x : ι → Ω) (i : ι) : Subalgebra o Ω :=
  Algebra.adjoin o (Set.range fun j => x j / x i)

structure ChartBundle (x : ι → Ω) (r : ℕ) (E : Type*) [AddCommGroup E] [Module Ω E] where

  lat : ι → AddSubgroup E

  stable : ∀ i, ∀ a ∈ chartRing o x i, ∀ e ∈ lat i, a • e ∈ lat i

  frame : ∀ i, x i ≠ 0 → ∃ (k : ℕ) (f c : Fin k → Ω), (∀ l, f l ∈ chartRing o x i) ∧
    (∀ l, c l ∈ chartRing o x i) ∧ ∑ l, c l * f l = 1 ∧
    ∀ l, ∃ b : Fin r → E, LinearIndependent Ω b ∧ Submodule.span Ω (Set.range b) = ⊤ ∧
      ∀ e, (∃ n : ℕ, f l ^ n • e ∈ lat i) ↔
        ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, f l ^ n * a q ∈ chartRing o x i) ∧ e = ∑ q, a q • b q

  overlap : ∀ i j, x i ≠ 0 → x j ≠ 0 → ∀ e ∈ lat i, ∃ m : ℕ, (x i / x j) ^ m • e ∈ lat j

variable {o}

theorem div_mem_chartRing (x : ι → Ω) (i j : ι) :
    x j / x i ∈ chartRing o x i :=
  Algebra.subset_adjoin ⟨j, rfl⟩

theorem exists_pow_mul_mem_chartRing (x : ι → Ω) (i j : ι) (hi : x i ≠ 0)
    {a : Ω} (ha : a ∈ chartRing o x i) :
    ∃ m : ℕ, (x i / x j) ^ m * a ∈ chartRing o x j := by
  have hij : x i / x j ∈ chartRing o x j := div_mem_chartRing x j i
  induction ha using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨k, rfl⟩ := hy
    refine ⟨1, ?_⟩
    have : x i / x j * (x k / x i) = x k / x j := by field_simp
    rw [pow_one, this]
    exact div_mem_chartRing x j k
  | algebraMap r =>
    exact ⟨0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨n, hn⟩ := hz
    refine ⟨m + n, ?_⟩
    have : (x i / x j) ^ (m + n) * (y + z) =
        (x i / x j) ^ n * ((x i / x j) ^ m * y) + (x i / x j) ^ m * ((x i / x j) ^ n * z) := by
      ring
    rw [this]
    exact add_mem (mul_mem (pow_mem hij _) hm) (mul_mem (pow_mem hij _) hn)
  | mul y z _ _ hy hz =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨n, hn⟩ := hz
    refine ⟨m + n, ?_⟩
    have : (x i / x j) ^ (m + n) * (y * z) = ((x i / x j) ^ m * y) * ((x i / x j) ^ n * z) := by
      ring
    rw [this]
    exact mul_mem hm hn

variable (o)

def lineLat (x : ι → Ω) (d : ℕ) (i : ι) : AddSubgroup Ω :=
  ((Subalgebra.toSubmodule (chartRing o x i)).map (LinearMap.mulRight o (x i ^ d))).toAddSubgroup

variable {o}

theorem mem_lineLat (x : ι → Ω) (d : ℕ) (i : ι) (e : Ω) :
    e ∈ lineLat o x d i ↔ ∃ a ∈ chartRing o x i, a * x i ^ d = e := by
  simp [lineLat]

variable (o)

def lineBundle (x : ι → Ω) (d : ℕ) : ChartBundle o x 1 Ω where
  lat := lineLat o x d
  stable i a ha e he := by
    obtain ⟨c, hc, rfl⟩ := (mem_lineLat x d i e).1 he
    refine (mem_lineLat x d i _).2 ⟨a * c, mul_mem ha hc, ?_⟩
    rw [smul_eq_mul, mul_assoc]
  frame i hi := by
    refine ⟨1, fun _ => 1, fun _ => 1, fun _ => one_mem _, fun _ => one_mem _, by simp, fun _ => ?_⟩
    simp only [one_pow, one_smul, one_mul, exists_const]
    refine ⟨fun _ => x i ^ d, ?_, ?_, ?_⟩
    · rw [linearIndependent_unique_iff]
      exact pow_ne_zero _ hi
    · rw [Set.range_const]
      exact Ideal.span_singleton_eq_top.2 (isUnit_iff_ne_zero.2 (pow_ne_zero _ hi))
    · intro e
      rw [mem_lineLat]
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨fun _ => a, fun _ => ha, by simp⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨a 0, ha 0, by simp⟩
  overlap i j hi hj e he := by
    obtain ⟨a, ha, rfl⟩ := (mem_lineLat x d i e).1 he
    obtain ⟨m, hm⟩ := exists_pow_mul_mem_chartRing x i j hi ha
    refine ⟨m, (mem_lineLat x d j _).2 ⟨(x i / x j) ^ m * a * (x i / x j) ^ d,
      mul_mem hm (pow_mem (div_mem_chartRing x j i) _), ?_⟩⟩
    rw [smul_eq_mul, div_pow, div_pow]
    field_simp

end Chart

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterOsgood
namespace ReciprocityTheory.ChartRestriction.G.Geo

def OsgoodStatement : Prop :=
  ∀ (e : ℕ) (U : Set (Fin e → ℂ)) (f : (Fin e → ℂ) → ℂ), IsOpen U → DifferentiableOn ℂ f U →
    AnalyticOnNhd ℂ f U

theorem osgood : OsgoodStatement := by
  intro e U f hU hf z₀ hz₀
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU z₀ hz₀
  have hs : 0 < r / 2 := half_pos hr
  have hcl : Metric.closedBall z₀ (r / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (half_lt_self hr)).trans hball
  have hd : ∀ ζ ∈ Metric.closedBall z₀ (r / 2), DifferentiableAt ℂ f ζ :=
    fun ζ hζ => hf.differentiableAt (hU.mem_nhds (hcl hζ))
  set L := ReciprocityTheory.AnForm.Osgood.fctlCLM z₀ hs f hd
  have hg : AnalyticAt ℂ (fun z => ((2 * (Real.pi : ℂ) * Complex.I) ^ e)⁻¹ *
      L (ReciprocityTheory.AnForm.Osgood.kern z₀ (r / 2) z)) z₀ :=
    analyticAt_const.mul ((L.analyticAt _).comp (ReciprocityTheory.AnForm.Osgood.kern_analyticAt z₀ hs))
  refine hg.congr ?_
  filter_upwards [Metric.ball_mem_nhds z₀ hs] with z hz
  rw [ReciprocityTheory.AnForm.Osgood.fctlCLM_kern hs hd hz]
  exact inv_mul_cancel_left₀ (pow_ne_zero _ Complex.two_pi_I_ne_zero) _

end ReciprocityTheory.ChartRestriction.G.Geo
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFS
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem maDensity_congr_of_eventuallyEq {D : ℕ} {φ ψ : Fin D → (Fin D → ℂ) → ℝ} {y : Fin D → ℂ}
    (h : ∀ j, φ j =ᶠ[𝓝 y] ψ j) : maDensity φ y = maDensity ψ y := by
  have h2 : ∀ j, fderiv ℝ (fderiv ℝ (φ j)) y = fderiv ℝ (fderiv ℝ (ψ j)) y := fun j =>
    Filter.EventuallyEq.fderiv_eq (show fderiv ℝ (φ j) =ᶠ[𝓝 y] fderiv ℝ (ψ j) from
      (h j).eventuallyEq_nhds.mono fun _ h' => h'.fderiv_eq)
  have hH : ∀ k, cxHessian (φ k) y = cxHessian (ψ k) y := by
    intro k
    unfold cxHessian
    rw [h2 k]
  simp only [maDensity, hH]

theorem mixedDisc_one (A : Fin 1 → Matrix (Fin 1) (Fin 1) ℂ) : mixedDisc A = A 0 0 0 := by
  unfold mixedDisc
  rw [← Finset.powerset_univ, Finset.univ_unique, ← Finset.insert_empty,
    Finset.sum_powerset_insert (by simp)]
  simp [Matrix.det_unique]

theorem maDensity_one (f : (Fin 1 → ℂ) → ℝ) (y : Fin 1 → ℂ) :
    maDensity (fun _ => f) y = (fderiv ℝ (fderiv ℝ f) y (Pi.single 0 1) (Pi.single 0 1) +
      fderiv ℝ (fderiv ℝ f) y (Complex.I • Pi.single 0 1) (Complex.I • Pi.single 0 1)) /
        (2 * Real.pi) := by
  have hre : ∀ u v : ℝ, ((((u : ℂ) + Complex.I * (v : ℂ)) / 4).re) = u / 4 := by
    intro u v
    simp [Complex.div_ofNat_re]
  rw [maDensity, mixedDisc_one]
  simp only [cxHessian, hre]
  have := Real.pi_pos
  simp
  field_simp
  ring

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodB
namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

noncomputable section

variable {σ : Type}

abbrev qmap : MvPolynomial σ ℤ →+* MvPolynomial σ ℚ := MvPolynomial.map (Int.castRingHom ℚ)

def qIdeal (P : Ideal (MvPolynomial σ ℤ)) : Ideal (MvPolynomial σ ℚ) := P.map qmap

theorem qmap_injective : Function.Injective (qmap : MvPolynomial σ ℤ → MvPolynomial σ ℚ) := MvPolynomial.map_injective _ Int.cast_injective

theorem exists_int_mul_eq_qmap (q : MvPolynomial σ ℚ) :
    ∃ D : ℤ, D ≠ 0 ∧ ∃ q' : MvPolynomial σ ℤ, (D : MvPolynomial σ ℚ) * q = qmap q' := by
  induction q using MvPolynomial.induction_on' with
  | monomial u a =>
    refine ⟨a.den, by exact_mod_cast a.den_nz, MvPolynomial.monomial u a.num, ?_⟩
    rw [show ((a.den : ℤ) : MvPolynomial σ ℚ) = C ((a.den : ℤ) : ℚ) from (map_intCast (C : ℚ →+* MvPolynomial σ ℚ) _).symm,
      C_mul_monomial, MvPolynomial.map_monomial]
    congr 1
    push_cast
    exact Rat.den_mul_eq_num a
  | add p q hp hq =>
    obtain ⟨D₁, hD₁, p', hp'⟩ := hp
    obtain ⟨D₂, hD₂, q', hq'⟩ := hq
    refine ⟨D₁ * D₂, mul_ne_zero hD₁ hD₂, (D₂ : MvPolynomial σ ℤ) * p' + (D₁ : MvPolynomial σ ℤ) * q', ?_⟩
    rw [map_add (f := _), map_mul, map_mul, map_intCast, map_intCast, ← hp', ← hq']
    push_cast
    ring

theorem exists_int_mul_mem_of_mem_qIdeal (P : Ideal (MvPolynomial σ ℤ)) {g : MvPolynomial σ ℚ}
    (hg : g ∈ qIdeal P) :
    ∃ N : ℤ, N ≠ 0 ∧ ∃ h ∈ P, (N : MvPolynomial σ ℚ) * g = qmap h := by
  have hg' : g ∈ Submodule.span (MvPolynomial σ ℚ) (qmap '' (P : Set (MvPolynomial σ ℤ))) := hg
  clear hg
  induction hg' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, hh, rfl⟩ := hx
    exact ⟨1, one_ne_zero, h, hh, by simp⟩
  | zero => exact ⟨1, one_ne_zero, 0, P.zero_mem, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨N₁, hN₁, h₁, hh₁, e₁⟩ := hx
    obtain ⟨N₂, hN₂, h₂, hh₂, e₂⟩ := hy
    refine ⟨N₁ * N₂, mul_ne_zero hN₁ hN₂, (N₂ : MvPolynomial σ ℤ) * h₁ + (N₁ : MvPolynomial σ ℤ) * h₂,
      P.add_mem (P.mul_mem_left _ hh₁) (P.mul_mem_left _ hh₂), ?_⟩
    rw [map_add (f := _), map_mul, map_mul, map_intCast, map_intCast, ← e₁, ← e₂]
    push_cast
    ring
  | smul a x _ hx =>
    obtain ⟨N, hN, h, hh, e⟩ := hx
    obtain ⟨D, hD, a', ha'⟩ := exists_int_mul_eq_qmap a
    refine ⟨D * N, mul_ne_zero hD hN, a' * h, P.mul_mem_left _ hh, ?_⟩
    rw [map_mul, ← ha', ← e, smul_eq_mul]
    push_cast
    ring

theorem mem_of_qmap_mem_qIdeal (P : Ideal (MvPolynomial σ ℤ)) (hP : P.IsPrime)
    (hH : P.comap (C : ℤ →+* MvPolynomial σ ℤ) = ⊥) {f : MvPolynomial σ ℤ}
    (hf : qmap f ∈ qIdeal P) : f ∈ P := by
  obtain ⟨N, hN, h, hh, e⟩ := exists_int_mul_mem_of_mem_qIdeal P hf
  have hNf : (N : MvPolynomial σ ℤ) * f = h := by
    apply qmap_injective
    rw [map_mul, map_intCast, e]
  rw [← hNf, show (N : MvPolynomial σ ℤ) = C N from (map_intCast (C : ℤ →+* MvPolynomial σ ℤ) N).symm] at hh
  rcases hP.mem_or_mem hh with hC | hf'
  · have : N ∈ P.comap (C : ℤ →+* MvPolynomial σ ℤ) := hC
    rw [hH] at this
    exact absurd ((Submodule.mem_bot ℤ).mp this) hN
  · exact hf'

def ratHom (P : Ideal (MvPolynomial σ ℤ)) :
    MvPolynomial σ ℤ ⧸ P →+* MvPolynomial σ ℚ ⧸ qIdeal P :=
  Ideal.quotientMap (qIdeal P) qmap Ideal.le_comap_map

theorem ratHom_mk (P : Ideal (MvPolynomial σ ℤ)) (f : MvPolynomial σ ℤ) :
    ratHom P (Ideal.Quotient.mk P f) = Ideal.Quotient.mk (qIdeal P) (qmap f) := rfl

theorem ratHom_isLocalization (P : Ideal (MvPolynomial σ ℤ)) :
    (letI := (ratHom P).toAlgebra
     IsLocalization (Algebra.algebraMapSubmonoid (MvPolynomial σ ℤ ⧸ P) (nonZeroDivisors ℤ))
       (MvPolynomial σ ℚ ⧸ qIdeal P)) := by
  let _ := (ratHom P).toAlgebra
  have hcast : ∀ n : ℤ, algebraMap (MvPolynomial σ ℤ ⧸ P) (MvPolynomial σ ℚ ⧸ qIdeal P)
      (algebraMap ℤ (MvPolynomial σ ℤ ⧸ P) n) = algebraMap ℚ (MvPolynomial σ ℚ ⧸ qIdeal P) n := by
    intro n
    rw [eq_intCast, map_intCast, map_intCast]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨y, hy⟩
    obtain ⟨n, hn, rfl⟩ := Submonoid.mem_map.mp hy
    rw [hcast]
    exact (IsUnit.mk0 (n : ℚ) (by exact_mod_cast nonZeroDivisors.ne_zero hn)).map _
  · intro z
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨D, hD, q', hq'⟩ := exists_int_mul_eq_qmap q
    refine ⟨⟨Ideal.Quotient.mk P q', ⟨algebraMap ℤ _ D,
      Submonoid.mem_map.mpr ⟨D, mem_nonZeroDivisors_of_ne_zero hD, rfl⟩⟩⟩, ?_⟩
    change _ * algebraMap (MvPolynomial σ ℤ ⧸ P) _ (algebraMap ℤ _ D) = ratHom P (Ideal.Quotient.mk P q')
    rw [hcast, ratHom_mk, ← hq', mul_comm, map_mul]
    congr 1
  · intro x y hxy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    change ratHom P _ = ratHom P _ at hxy
    rw [ratHom_mk, ratHom_mk, Ideal.Quotient.eq, ← map_sub] at hxy
    obtain ⟨N, hN, h, hh, e⟩ := exists_int_mul_mem_of_mem_qIdeal P hxy
    have hNab : (N : MvPolynomial σ ℤ) * (a - b) = h := by
      apply qmap_injective
      rw [map_mul, map_intCast, e]
    refine ⟨⟨algebraMap ℤ _ N, Submonoid.mem_map.mpr ⟨N, mem_nonZeroDivisors_of_ne_zero hN, rfl⟩⟩, ?_⟩
    change algebraMap ℤ _ N * Ideal.Quotient.mk P a = algebraMap ℤ _ N * Ideal.Quotient.mk P b
    rw [← sub_eq_zero, ← mul_sub, ← map_sub, eq_intCast, ← map_intCast (Ideal.Quotient.mk P), ← map_mul,
      hNab, Ideal.Quotient.eq_zero_iff_mem]
    exact hh

theorem isDomain_qQuot (P : Ideal (MvPolynomial σ ℤ)) (hP : P.IsPrime)
    (hH : P.comap (C : ℤ →+* MvPolynomial σ ℤ) = ⊥) :
    IsDomain (MvPolynomial σ ℚ ⧸ qIdeal P) := by
  let _ := (ratHom P).toAlgebra
  have := ratHom_isLocalization P
  refine IsLocalization.isDomain_of_le_nonZeroDivisors (R := MvPolynomial σ ℤ ⧸ P)
    (M := Algebra.algebraMapSubmonoid (MvPolynomial σ ℤ ⧸ P) (nonZeroDivisors ℤ))
    (S := MvPolynomial σ ℚ ⧸ qIdeal P) ?_
  rintro _ ⟨n, hn, rfl⟩
  apply mem_nonZeroDivisors_of_ne_zero
  intro h0
  rw [eq_intCast, ← map_intCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem,
    show (n : MvPolynomial σ ℤ) = C n from (map_intCast (C : ℤ →+* MvPolynomial σ ℤ) n).symm] at h0
  have : n ∈ P.comap (C : ℤ →+* MvPolynomial σ ℤ) := h0
  rw [hH] at this
  exact nonZeroDivisors.ne_zero hn ((Submodule.mem_bot ℤ).mp this)

end

end ReciprocityTheory.ChartRestriction.G.Geo
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.LemSec
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

section LemSec

variable (o : Type*) {Ω : Type*} [CommRing o] [CommRing Ω] [Algebra o Ω] {ι : Type*}

theorem coordIdeal_isPrime [IsDomain Ω] (x : ι → Ω) : (coordIdeal o x).IsPrime :=
  RingHom.ker_isPrime _

end LemSec

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.FsMetricFinIsSemipositive
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

variable {ι : Type*} [Fintype ι]

def fsLp (ι : Type*) [Fintype ι] : (ι → ℂ) →L[ℝ] EuclideanSpace ℂ ι :=
  ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => ℂ)).symm :
    (ι → ℂ) →L[ℂ] EuclideanSpace ℂ ι).restrictScalars ℝ

lemma fsLp_apply (z : ι → ℂ) : fsLp ι z = WithLp.toLp 2 z := rfl

lemma fsLp_ne_zero {z : ι → ℂ} (hz : z ≠ 0) : fsLp ι z ≠ 0 := by
  rw [fsLp_apply]
  intro h
  apply hz
  have h2 := congrArg (WithLp.ofLp (p := 2)) h
  simpa using h2

lemma fsLp_smul_I (w : ι → ℂ) : fsLp ι (Complex.I • w) = Complex.I • fsLp ι w := rfl

lemma fsLp_normSq_ne_zero {z : ι → ℂ} (hz : z ≠ 0) : ‖fsLp ι z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 (fsLp_ne_zero hz))

def fsGrad (y : ι → ℂ) : (ι → ℂ) →L[ℝ] ℝ :=
  (‖fsLp ι y‖ ^ 2)⁻¹ • (innerSL ℝ (fsLp ι y)).comp (fsLp ι)

lemma fsGrad_apply (y v : ι → ℂ) :
    fsGrad y v = (‖fsLp ι y‖ ^ 2)⁻¹ * inner ℝ (fsLp ι y) (fsLp ι v) := rfl

lemma hasFDerivAt_logFs {y : ι → ℂ} (hy : y ≠ 0) :
    HasFDerivAt (fun z => Real.log ‖fsLp ι z‖) (fsGrad y) y := by
  have h0 : fsLp ι y ≠ 0 := fsLp_ne_zero hy
  have hL : HasFDerivAt (fsLp ι) (fsLp ι) y := (fsLp ι).hasFDerivAt
  have h1 := (HasFDerivAt.log (HasFDerivAt.norm_sq hL) (fsLp_normSq_ne_zero hy)).const_mul (1 / 2 : ℝ)
  have hfun : (fun z => Real.log ‖fsLp ι z‖) = fun z => 1 / 2 * Real.log (‖fsLp ι z‖ ^ 2) := by
    funext z
    rw [Real.log_pow]
    push_cast
    ring
  rw [hfun]
  refine h1.congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro v
  rw [fsGrad_apply]
  simp
  ring

lemma fderiv_logFs_eventuallyEq {z : ι → ℂ} (hz : z ≠ 0) :
    fderiv ℝ (fun z => Real.log ‖fsLp ι z‖) =ᶠ[nhds z] fsGrad := by
  filter_upwards [eventually_ne_nhds hz] with y hy using (hasFDerivAt_logFs hy).fderiv

lemma hess_logFs {z : ι → ℂ} (hz : z ≠ 0) (w : ι → ℂ) :
    fderiv ℝ (fderiv ℝ (fun z => Real.log ‖fsLp ι z‖)) z w w =
      ‖fsLp ι w‖ ^ 2 / ‖fsLp ι z‖ ^ 2 -
        2 * inner ℝ (fsLp ι z) (fsLp ι w) ^ 2 / (‖fsLp ι z‖ ^ 2) ^ 2 := by
  have hL : HasFDerivAt (fsLp ι) (fsLp ι) z := (fsLp ι).hasFDerivAt
  have h0 := fsLp_normSq_ne_zero hz
  have hc := (hasDerivAt_inv h0).comp_hasFDerivAt z (HasFDerivAt.norm_sq hL)
  have hT : HasFDerivAt (fun y => (innerSL ℝ (fsLp ι y)).comp (fsLp ι))
      (((ContinuousLinearMap.compL ℝ (ι → ℂ) (EuclideanSpace ℂ ι) ℝ).flip (fsLp ι)).comp
      ((innerSL ℝ).comp (fsLp ι))) z :=
    (((ContinuousLinearMap.compL ℝ (ι → ℂ) (EuclideanSpace ℂ ι) ℝ).flip (fsLp ι)).comp
      ((innerSL ℝ).comp (fsLp ι))).hasFDerivAt
  have hG := HasFDerivAt.smul hc hT
  rw [(fderiv_logFs_eventuallyEq hz).fderiv_eq]
  have hfG : (fsGrad (ι := ι)) = ((fun y : ℝ => y⁻¹) ∘ fun x => ‖fsLp ι x‖ ^ 2) •
      (fun y => (innerSL ℝ (fsLp ι y)).comp (fsLp ι)) := rfl
  rw [hfG, hG.fderiv]
  simp
  field_simp
  ring

lemma inner_sq_add_inner_I_sq (x y : EuclideanSpace ℂ ι) :
    inner ℝ x y ^ 2 + inner ℝ x (Complex.I • y) ^ 2 = ‖inner ℂ x y‖ ^ 2 := by
  have e0 : ∀ u v : EuclideanSpace ℂ ι, inner ℝ u v = (inner ℂ u v).re := by
    intro u v
    rw [PiLp.inner_apply, PiLp.inner_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    first
    | rfl
    | simp [Complex.inner, RCLike.inner_apply]
    | simp [Complex.inner, mul_comm]
  rw [e0, e0, inner_smul_right, Complex.sq_norm, Complex.normSq_apply, Complex.mul_re,
    Complex.I_re, Complex.I_im]
  ring

theorem fsMetric_isSmooth : IsSmoothMetric (fsMetric (ι := ι)) := by
  intro z hz
  change ContDiffWithinAt ℝ _ (fun z => ‖fsLp ι z‖) _ z
  have h0 : fsLp ι z ≠ 0 := fsLp_ne_zero hz
  have hn : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : EuclideanSpace ℂ ι => ‖u‖) (fsLp ι z) := by
    first
    | exact contDiffAt_norm ℝ h0
    | exact contDiffAt_norm h0
  exact (hn.comp z (fsLp ι).contDiff.contDiffAt).contDiffWithinAt

theorem leviForm_fsMetric {z : ι → ℂ} (hz : z ≠ 0) (w : ι → ℂ) :
    leviForm (fun z => Real.log ((fsMetric (ι := ι)).ρ z)) z w =
      (‖fsLp ι w‖ ^ 2 * ‖fsLp ι z‖ ^ 2 - ‖inner ℂ (fsLp ι z) (fsLp ι w)‖ ^ 2) /
        (2 * (‖fsLp ι z‖ ^ 2) ^ 2) := by
  change leviForm (fun z => Real.log ‖fsLp ι z‖) z w = _
  unfold leviForm
  rw [hess_logFs hz, hess_logFs hz, fsLp_smul_I, norm_smul, Complex.norm_I, one_mul,
    ← inner_sq_add_inner_I_sq]
  have h0 := fsLp_normSq_ne_zero hz
  field_simp
  ring

theorem fsMetric_isSemipositive : IsSemipositive (fsMetric (ι := ι)) := by
  refine ⟨fsMetric_isSmooth, fun z hz w => ?_⟩
  rw [leviForm_fsMetric hz]
  have hcs := norm_inner_le_norm (𝕜 := ℂ) (fsLp ι z) (fsLp ι w)
  have h2 := mul_self_le_mul_self (norm_nonneg _) hcs
  apply div_nonneg
  · nlinarith [h2]
  · positivity

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

module

public import Mathlib
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsPrecompleteFiniteModule

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA
namespace ReciprocityTheory.ChartRestriction.G.T0

open scoped TensorProduct BigOperators ComplexOrder
open NumberField

noncomputable def ratio {Ω V : Type*} [Field Ω] [AddCommGroup V] [Module Ω V] (f g : V) : Ω :=
  open Classical in if h : ∃ a : Ω, f = a • g then h.choose else 0

def IsNormDiscrete {Ω : Type*} [Field Ω] (v : AddValuation Ω (WithTop ℤ)) : Prop :=
  (∀ a : Ω, a ≠ 0 → v a ≠ ⊤) ∧ ∃ π : Ω, v π = 1

abbrev vRing {Ω : Type*} [Field Ω] (v : AddValuation Ω (WithTop ℤ)) : ValuationSubring Ω :=
  Valuation.valuationSubring v

def comapIncl {F Ω : Type*} [Field F] [Field Ω] (V : ValuationSubring Ω) (f : F →+* Ω) :
    V.comap f →+* V :=
  f.restrict (V.comap f) V fun _ hx => hx

instance comapIncl_isLocalHom {F Ω : Type*} [Field F] [Field Ω] (V : ValuationSubring Ω)
    (f : F →+* Ω) : IsLocalHom (comapIncl V f) := by
  constructor
  intro x hx
  obtain ⟨u, hu⟩ := isUnit_iff_exists_inv.mp hx
  have hu' : f (x : F) * (u : Ω) = 1 := congrArg Subtype.val hu
  have hx0 : (x : F) ≠ 0 := fun h => zero_ne_one (by rw [h, map_zero, zero_mul] at hu'; exact hu')
  have hinv : f ((x : F)⁻¹) = (u : Ω) := by rw [map_inv₀]; exact inv_eq_of_mul_eq_one_right hu'
  have hmem : (x : F)⁻¹ ∈ V.comap f := by rw [ValuationSubring.mem_comap, hinv]; exact u.2
  exact isUnit_iff_exists_inv.mpr ⟨⟨_, hmem⟩, Subtype.ext (mul_inv_cancel₀ hx0)⟩

noncomputable abbrev resAlg {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
    (v : AddValuation Ω (WithTop ℤ)) :
    Algebra (IsLocalRing.ResidueField ((vRing v).comap (algebraMap F Ω)))
      (IsLocalRing.ResidueField (vRing v)) :=
  (IsLocalRing.ResidueField.map (comapIncl (vRing v) (algebraMap F Ω))).toAlgebra

def IsOver {K Ω : Type*} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    (v : AddValuation Ω (WithTop ℤ)) (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : Prop :=
  ∀ a : 𝓞 K, (0 < v (algebraMap K Ω (a : K)) ↔ a ∈ la.asIdeal)

def IsTrivOn (K : Type*) {Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (v : AddValuation Ω (WithTop ℤ)) : Prop :=
  ∀ a : K, a ≠ 0 → v (algebraMap K Ω a) = 0

noncomputable def ramIdx {K Ω : Type*} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    (v : AddValuation Ω (WithTop ℤ)) (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : ℤ :=
  sInf {n : ℤ | ∃ a ∈ la.asIdeal, a ≠ 0 ∧ v (algebraMap K Ω (a : K)) = n}

noncomputable def logNorm {K : Type*} [Field K] [NumberField K]
    (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : ℝ :=
  Real.log (Ideal.absNorm la.asIdeal : ℝ)

def PT {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] (sg : K →+* ℂ) : Set (Ω →+* ℂ) :=
  {P | P.comp (algebraMap K Ω) = sg}

noncomputable def meanK {K : Type*} [Field K] [NumberField K] (F : (K →+* ℂ) → ℝ) : ℝ :=
  (∑ sg, F sg) / (Fintype.card (K →+* ℂ) : ℝ)

abbrev TVar (D N : ℕ) : Type := Fin (D + 1) × Fin (N + 1)

abbrev SVar (D N : ℕ) : Type := Unit ⊕ (Fin (D + 1) × Fin N)

abbrev OmS (Ω : Type) [Field Ω] (D N : ℕ) : Type := FractionRing (MvPolynomial (SVar D N) Ω)

noncomputable def sImg {Ω : Type} [Field Ω] {D N : ℕ} (j₀ : Fin (N + 1)) (x : Fin N → Ω)
    (p : TVar D N) : OmS Ω D N :=
  algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N)
    (Fin.succAboveCases (α := fun _ => MvPolynomial (SVar D N) Ω) j₀
      (if p.1 = 0 then MvPolynomial.X (Sum.inl ())
        else -∑ k, MvPolynomial.X (Sum.inr (p.1, k)) * MvPolynomial.C (x k))
      (fun k => MvPolynomial.X (Sum.inr (p.1, k))) p.2)

noncomputable def sHom {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}
    (j₀ : Fin (N + 1)) (x : Fin N → Ω) : MvPolynomial (TVar D N) K →ₐ[K] OmS Ω D N :=
  MvPolynomial.aeval (sImg j₀ x)

variable (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι]
  (Ω : ι → Type) [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  (WT : Type) [AddCommGroup WT]
  (A : ι → Type) [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c))

structure Data where

  D : ℕ

  N : ℕ

  T : ℕ

  i : ℕ
  g0 : ℕ

  cc : ℝ

  wL : WT
  wF : WT
  wde : WT

  ord : (c : ι) → AddValuation (Ω c) (WithTop ℤ) → WT → A c → ℤ

  nrm : (c : ι) → WT → A c → (Ω c →+* ℂ) → ℝ

  M : Submodule (𝓞 K) (∀ c, A c)
  WW : Submodule (𝓞 K) (∀ c, A c)
  Thp : Submodule (𝓞 K) (∀ c, A c)
  Th0 : Submodule (𝓞 K) (∀ c, A c)
  Thk : Submodule (𝓞 K) (∀ c, A c)

  w : Fin (N + 1) → ∀ c, A c

  jc : ι → Fin (N + 1)
  np : ℕ
  thp : Fin np → ∀ c, A c
  n0 : ℕ
  th0 : Fin n0 → ∀ c, A c
  nk : ℕ
  thk : Fin nk → ∀ c, A c

  et : ∀ c, A c
  ta1 : ∀ c, A c
  ta2 : ∀ c, A c

  nu : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ

  ip : (K →+* ℂ) → (∀ c, A c) → (∀ c, A c) → ℂ

  wsize : WT → ℝ

  DF : ℝ

  PN : ℝ
  PQ : ℝ
  tableDegreeThreeBase : ℝ
  PP0' : ℝ
  Pd : ℝ
  Gc : ℝ
  PI4 : ℝ
  Pet : ℝ
  tableLineDegreeFive : ℝ
  tableLineDegreeTwo : ℝ
  Prw : ℝ
  PO : ℝ
  f : ℝ
  r : ℝ

namespace Data

variable {K ι Ω WT A}
variable (d : Data K ι Ω WT A)

def G1 : WT := d.wL - d.wde

def G2 : WT := (d.D + 4 : ℕ) • d.wL - d.wF

def F0 : WT := d.wF + d.D • d.wL

def n1 : ℕ := d.i * d.g0

noncomputable def x (c : ι) (k : Fin d.N) : Ω c :=
  ratio (Ω := Ω c) (d.w ((d.jc c).succAbove k) c) (d.w (d.jc c) c)

def ResCond (c : ι) (v : AddValuation (Ω c) (WithTop ℤ)) (n : ℕ) : Prop :=
  letI := resAlg (F := K) v
  Algebra.trdeg (IsLocalRing.ResidueField ((vRing v).comap (algebraMap K (Ω c))))
      (IsLocalRing.ResidueField (vRing v)) = n ∧
  ∃ j0 : Fin (d.N + 1), d.w j0 c ≠ 0 ∧
    (∀ j, 0 ≤ v (ratio (Ω := Ω c) (d.w j c) (d.w j0 c))) ∧
    Algebra.trdeg (IsLocalRing.ResidueField ((vRing v).comap (algebraMap K (Ω c))))
      (IntermediateField.adjoin
        (IsLocalRing.ResidueField ((vRing v).comap (algebraMap K (Ω c))))
        {r | ∃ j, ∃ h : ratio (Ω := Ω c) (d.w j c) (d.w j0 c) ∈ vRing v,
          r = IsLocalRing.residue (vRing v) ⟨_, h⟩}) = n

def admitted (c : ι) (v : AddValuation (Ω c) (WithTop ℤ)) : Prop :=
  IsNormDiscrete v ∧
    ((∃ la, IsOver (K := K) v la ∧ d.ResCond c v d.D) ∨
      (IsTrivOn K v ∧ d.ResCond c v (d.D - 1)))

noncomputable def supN (sg : K →+* ℂ) (G : WT) (f : ∀ c, A c) : ℝ :=
  ⨆ p : (Σ c, PT (Ω := Ω c) sg), d.nrm p.1 G (f p.1) p.2

noncomputable def supNc (c : ι) (sg : K →+* ℂ) (G : WT) (fc : A c) : ℝ :=
  ⨆ P : PT (Ω := Ω c) sg, d.nrm c G fc P

noncomputable def be (c : ι) (P : Ω c →+* ℂ) : ℝ :=
  Real.sqrt (∑ j, d.nrm c d.wL (d.w j c) P ^ 2)

def ST (c : ι) (sg : K →+* ℂ) (t : Fin d.D → Fin (d.N + 1) → ℂ) : Set (Ω c →+* ℂ) :=
  {P | P ∈ PT sg ∧ ∀ i, ∑ j, t i j * P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c)) = 0}

noncomputable def sH (c : ι) : MvPolynomial (TVar d.D d.N) K →ₐ[K] OmS (Ω c) d.D d.N :=
  sHom (d.jc c) (d.x c)

noncomputable abbrev KT (c : ι) : IntermediateField K (OmS (Ω c) d.D d.N) :=
  IntermediateField.adjoin K (Set.range (sImg (D := d.D) (d.jc c) (d.x c)))

noncomputable def delc (c : ι) : ℕ := Module.finrank (d.KT c) (OmS (Ω c) d.D d.N)
noncomputable def del : ℕ := ∑ c, d.delc c

def a0 : ℕ := d.T - d.D

def PH : ℝ := d.PP0' + d.PN + d.tableLineDegreeFive + d.tableLineDegreeTwo + d.PI4 + d.Prw

noncomputable def n96 : ℕ :=
  8 * ((d.D + 2) * (d.N + 1)) ^ 2 * (d.D + 1) * d.del * (1 + ⌈d.PO⌉₊)

noncomputable def sphMeasure : MeasureTheory.Measure
    (Fin d.D → Metric.sphere (0 : EuclideanSpace ℂ (Fin (d.N + 1))) 1) :=
  MeasureTheory.Measure.pi fun _ => (MeasureTheory.volume :
    MeasureTheory.Measure (EuclideanSpace ℂ (Fin (d.N + 1)))).toSphere

end Data

namespace Data

variable {K ι Ω WT A}
variable (d : Data K ι Ω WT A)

end Data


end ReciprocityTheory.ChartRestriction.G.T0
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion

open IsLocalRing Polynomial

theorem isPrecomplete_finite_module {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] : IsPrecomplete I M := by
  first | exact UpperTheory.Reformulated.B.Qk17.isPrecomplete_finite_module .. | (apply UpperTheory.Reformulated.B.Qk17.isPrecomplete_finite_module <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qk17.isPrecomplete_finite_module <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk17.isPrecomplete_finite_module <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qk17.isPrecomplete_finite_module <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk17.isPrecomplete_finite_module <;> first | assumption | infer_instance)

theorem isAdicComplete_finite_algebra {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] (S : Type*) [CommRing S] [Algebra R S] [Module.Finite R S] :
    IsAdicComplete ((maximalIdeal R).map (algebraMap R S)) S := by
  rw [IsAdicComplete.map_algebraMap_iff]
  have := isPrecomplete_finite_module (maximalIdeal R) S
  exact ⟨⟩

theorem map_maximalIdeal_le_maximal {R : Type*} [CommRing R] [IsLocalRing R] (S : Type*) [CommRing S]
    [Algebra R S] [Module.Finite R S] (n : Ideal S) (hn : n.IsMaximal) :
    (maximalIdeal R).map (algebraMap R S) ≤ n := by
  rw [Ideal.map_le_iff_le_comap]
  have : (n.comap (algebraMap R S)).IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal n
  exact (IsLocalRing.eq_maximalIdeal this).ge

theorem finite_maximal_ideals_of_finite {R : Type*} [CommRing R] [IsLocalRing R] (S : Type*) [CommRing S]
    [Algebra R S] [Module.Finite R S] : {n : Ideal S | n.IsMaximal}.Finite := by
  let J := (maximalIdeal R).map (algebraMap R S)
  let : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  have : Module.Finite (R ⧸ maximalIdeal R) (S ⧸ J) := Module.Finite.of_restrictScalars_finite R _ _
  have : IsArtinianRing (S ⧸ J) := IsArtinianRing.of_finite (R ⧸ maximalIdeal R) (S ⧸ J)
  refine ((IsArtinianRing.setOfPred_isMaximal_finite (S ⧸ J)).image
    (Ideal.comap (Ideal.Quotient.mk J))).subset ?_
  intro n hn
  refine ⟨n.map (Ideal.Quotient.mk J), ?_, ?_⟩
  · have hJ : J ≤ n := map_maximalIdeal_le_maximal S n hn
    have : n.IsMaximal := hn
    exact Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective (by simpa using hJ)
  · have hJ : J ≤ n := map_maximalIdeal_le_maximal S n hn
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
    rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_eq_left.mpr hJ

theorem exists_pow_mem_map_maximalIdeal {R : Type*} [CommRing R] [IsLocalRing R] (S : Type*) [CommRing S]
    [Algebra R S] [Module.Finite R S] (b : S) (hb : ∀ n : Ideal S, n.IsMaximal → b ∈ n) :
    ∃ N : ℕ, 0 < N ∧ b ^ N ∈ (maximalIdeal R).map (algebraMap R S) := by
  let J := (maximalIdeal R).map (algebraMap R S)
  let : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  have : Module.Finite (R ⧸ maximalIdeal R) (S ⧸ J) := Module.Finite.of_restrictScalars_finite R _ _
  have : IsArtinianRing (S ⧸ J) := IsArtinianRing.of_finite (R ⧸ maximalIdeal R) (S ⧸ J)
  obtain ⟨k, hk⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := S ⧸ J)
  have hmem : Ideal.Quotient.mk J b ∈ (⊥ : Ideal (S ⧸ J)).jacobson := by
    rw [Ideal.jacobson, Ideal.mem_sInf]
    rintro q ⟨-, hq⟩
    have := Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective (K := q)
    exact hb _ this
  have h1 : Ideal.Quotient.mk J (b ^ (k + 1)) = 0 := by
    have := Ideal.pow_mem_pow hmem k
    rw [hk, Ideal.zero_eq_bot, Ideal.mem_bot] at this
    rw [pow_succ, map_mul, map_pow, this, zero_mul]
  exact ⟨k + 1, k.succ_pos, Ideal.Quotient.eq_zero_iff_mem.mp h1⟩

theorem exists_idempotent_henselian {S : Type*} [CommRing S] (J : Ideal S) [HenselianRing S J] (x : S) (N : ℕ)
    (hN : (x * x - x) ^ (N + 1) ∈ J) : ∃ e s : S, e * e = e ∧ e - x = s * (x * x - x) := by
  have hnil : (Ideal.Quotient.mk J x - Ideal.Quotient.mk J x ^ 2) ^ (N + 1) = 0 := by
    have : Ideal.Quotient.mk J x - Ideal.Quotient.mk J x ^ 2 = -(Ideal.Quotient.mk J (x * x - x)) := by
      simp only [map_sub, map_mul, pow_two, neg_sub]
    rw [this, neg_pow, ← map_pow, Ideal.Quotient.eq_zero_iff_mem.2 hN, mul_zero]
  have hid := isIdempotentElem_one_sub_one_sub_pow_pow _ (N + 1) hnil
  have hq : Ideal.Quotient.mk J (1 - (1 - x ^ (N + 1)) ^ (N + 1)) =
      1 - (1 - Ideal.Quotient.mk J x ^ (N + 1)) ^ (N + 1) := by simp
  have hid' : Ideal.Quotient.mk J (1 - (1 - x ^ (N + 1)) ^ (N + 1)) *
      Ideal.Quotient.mk J (1 - (1 - x ^ (N + 1)) ^ (N + 1)) =
      Ideal.Quotient.mk J (1 - (1 - x ^ (N + 1)) ^ (N + 1)) := by rw [hq]; exact hid.eq
  have hxW : IsIdempotentElem (Ideal.Quotient.mk (Ideal.span {x * x - x}) x) := by
    rw [IsIdempotentElem, ← map_mul, Ideal.Quotient.eq]
    exact Ideal.subset_span rfl
  have hqW : Ideal.Quotient.mk (Ideal.span {x * x - x}) (1 - (1 - x ^ (N + 1)) ^ (N + 1)) =
      Ideal.Quotient.mk (Ideal.span {x * x - x}) x := by
    simp only [map_sub, map_one, map_pow, hxW.pow_succ_eq, hxW.one_sub.pow_succ_eq, sub_sub_cancel]
  generalize 1 - (1 - x ^ (N + 1)) ^ (N + 1) = e0 at hid' hqW
  have h3 : e0 - x ∈ Ideal.span {x * x - x} := Ideal.Quotient.eq.1 hqW
  have h4 : e0 * e0 - e0 ∈ Ideal.span {x * x - x} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hqW, hxW.eq, sub_self]
  have h1 : (X ^ 2 - X : S[X]).eval e0 ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    rw [eval_sub, eval_pow, eval_X, map_sub, map_pow, pow_two, hid', sub_self]
  have hd : (X ^ 2 - X : S[X]).derivative.eval e0 = 2 * e0 - 1 := by
    simp; ring
  have h2 : IsUnit (Ideal.Quotient.mk J ((X ^ 2 - X : S[X]).derivative.eval e0)) := by
    rw [hd]
    refine isUnit_iff_exists_inv.2 ⟨Ideal.Quotient.mk J (2 * e0 - 1), ?_⟩
    simp only [map_sub, map_mul, map_ofNat, map_one]
    linear_combination 4 * hid'
  have hmon : (X ^ 2 - X : S[X]).Monic :=
    monic_X_pow_sub (lt_of_le_of_lt degree_X_le (by norm_num))
  obtain ⟨e, he, hee⟩ := HenselianRing.is_henselian _ hmon e0 h1 h2
  have hee' : e * e = e := by
    have := he.eq_zero
    simp only [eval_sub, eval_pow, eval_X] at this
    linear_combination this
  have hu2 : (2 * e - 1) * (2 * e - 1) = 1 := by linear_combination 4 * hee'
  have hdu : IsUnit (e - e0 - (2 * e - 1)) := by
    have : e - e0 - (2 * e - 1) = (-(2 * e - 1)) * ((e - e0) * (-(2 * e - 1)) + 1) := by
      linear_combination (-(e - e0)) * hu2
    rw [this]
    exact (isUnit_iff_exists_inv.2 ⟨-(2 * e - 1), by linear_combination hu2⟩).mul
      (Ring.mem_jacobson_iff.1 (HenselianRing.jac hee) _)
  have hdW : e - e0 ∈ Ideal.span {x * x - x} := by
    obtain ⟨v, hv⟩ := hdu.exists_left_inv
    have hdd : (e - e0) * (e - e0 - (2 * e - 1)) = e0 * e0 - e0 := by
      linear_combination (-1 : S) * hee'
    have : e - e0 = v * (e0 * e0 - e0) := by
      linear_combination (-(e - e0)) * hv + v * hdd
    rw [this]; exact Ideal.mul_mem_left _ _ h4
  have h5 : e - x ∈ Ideal.span {x * x - x} := by
    have : e - x = (e - e0) + (e0 - x) := by ring
    rw [this]; exact Ideal.add_mem _ hdW h3
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 h5
  exact ⟨e, s, hee', hs.symm⟩

theorem isLocalRing_finite_domain {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] (S : Type*) [CommRing S] [IsDomain S] [Algebra R S]
    [Module.Finite R S] : IsLocalRing S := by
  classical
  by_contra hloc
  obtain ⟨M1, hM1⟩ := Ideal.exists_maximal S
  have hex : ∃ M2 : Ideal S, M2.IsMaximal ∧ M2 ≠ M1 := by
    by_contra h
    push Not at h
    exact hloc (IsLocalRing.of_unique_max_ideal ⟨M1, hM1, fun M hM => h M hM⟩)
  obtain ⟨M2, hM2, h12⟩ := hex
  set F := (finite_maximal_ideals_of_finite (R := R) S).toFinset.filter (· ≠ M1) with hF
  have hmemF : ∀ N : Ideal S, N.IsMaximal → N ≠ M1 → N ∈ F := by
    intro N hN hN1
    rw [hF, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨hN, hN1⟩
  have hcop : M1 ⊔ F.inf id = ⊤ := by
    by_contra hne
    have hle : F.inf id ≤ M1 := by
      rw [hM1.eq_of_le hne le_sup_left]; exact le_sup_right
    obtain ⟨N, hN, hNle⟩ := (hM1.isPrime.inf_le').1 hle
    rw [hF, Finset.mem_filter, Set.Finite.mem_toFinset] at hN
    exact hN.2 ((hN.1 : N.IsMaximal).eq_of_le hM1.ne_top hNle)
  have h1 : (1 : S) ∈ M1 ⊔ F.inf id := by rw [hcop]; exact Submodule.mem_top
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 h1
  have hx1 : ∀ N : Ideal S, N.IsMaximal → N ≠ M1 → x - 1 ∈ N := by
    intro N hN hN1
    have : y ∈ N := Finset.inf_le (f := id) (hmemF N hN hN1) hy
    have : x - 1 = -y := by rw [← hxy]; ring
    rw [this]; exact N.neg_mem (by assumption)
  have hall : ∀ N : Ideal S, N.IsMaximal → x * x - x ∈ N := by
    intro N hN
    by_cases hN1 : N = M1
    · subst hN1; exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hx) hx
    · have := hx1 N hN hN1
      have e : x * x - x = x * (x - 1) := by ring
      rw [e]; exact Ideal.mul_mem_left _ _ this
  obtain ⟨k, hk, hkJ⟩ := exists_pow_mem_map_maximalIdeal (R := R) S _ hall
  have : IsAdicComplete ((maximalIdeal R).map (algebraMap R S)) S := isAdicComplete_finite_algebra S
  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  obtain ⟨e, s, hee, hes⟩ := exists_idempotent_henselian ((maximalIdeal R).map (algebraMap R S)) x k' hkJ
  have hxx1 : x * x - x ∈ M1 := hall M1 hM1
  have hxx2 : x * x - x ∈ M2 := hall M2 hM2
  rcases (IsIdempotentElem.iff_eq_zero_or_one.1 hee) with h0 | h0
  · apply hM2.ne_top
    rw [Ideal.eq_top_iff_one]
    have ha : -x ∈ M2 := by
      have : -x = s * (x * x - x) := by rw [← hes, h0]; ring
      rw [this]; exact Ideal.mul_mem_left _ _ hxx2
    have hb := hx1 M2 hM2 h12
    have : (1 : S) = -(x - 1) + -(-x) := by ring
    rw [this]; exact M2.add_mem (M2.neg_mem hb) (M2.neg_mem ha)
  · apply hM1.ne_top
    rw [Ideal.eq_top_iff_one]
    have : (1 : S) = s * (x * x - x) + x := by rw [← hes, h0]; ring
    rw [this]; exact M1.add_mem (Ideal.mul_mem_left _ _ hxx1) hx

section

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (L : Type*) [Field L] [Algebra R L] [FaithfulSMul R L] [Module.Finite R (integralClosure R L)]

theorem cl_inj : Function.Injective (algebraMap R (integralClosure R L)) := by
  intro x y h
  apply FaithfulSMul.algebraMap_injective R L
  exact congrArg Subtype.val h

theorem cl_isLocalRing [IsAdicComplete (maximalIdeal R) R] : IsLocalRing (integralClosure R L) :=
  isLocalRing_finite_domain (R := R) (integralClosure R L)

theorem cl_isLocalHom : IsLocalHom (algebraMap R (integralClosure R L)) :=
  RingHom.IsIntegral.isLocalHom (fun x => (Algebra.IsIntegral.isIntegral x : IsIntegral R x))
    (cl_inj R L)

end

section

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
  (L : Type*) [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [FiniteDimensional K L]

include K

theorem cl_faithful : FaithfulSMul R L :=
  (faithfulSMul_iff_algebraMap_injective R L).2 (by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K))

variable [Module.Finite R (integralClosure R L)]

theorem cl_dvr [IsAdicComplete (maximalIdeal R) R] :
    IsDiscreteValuationRing (integralClosure R L) := by
  have := cl_faithful R K L
  have : IsLocalRing (integralClosure R L) := cl_isLocalRing R L
  have : IsFractionRing (integralClosure R L) L := integralClosure.isFractionRing_of_finite_extension K L
  have : Algebra.IsIntegral R (integralClosure R L) := IsIntegralClosure.isIntegral_algebra R L
  have : IsNoetherianRing (integralClosure R L) :=
    isNoetherianRing_iff.mpr (isNoetherian_of_tower R inferInstance)
  have hD : IsDedekindDomain (integralClosure R L) :=
    { ‹IsNoetherianRing (integralClosure R L)›,
      Ring.DimensionLEOne.of_isIntegral R (integralClosure R L),
      (isIntegrallyClosed_iff L).mpr fun {x} hx =>
        ⟨IsIntegralClosure.mk' (integralClosure R L) x (isIntegral_trans (R := R) _ hx),
          IsIntegralClosure.algebraMap_mk' _ _ _⟩ with : IsDedekindDomain (integralClosure R L) }
  have hnf : ¬ IsField (integralClosure R L) := fun h =>
    (isField_iff_maximalIdeal_eq.not.mpr IsDiscreteValuationRing.not_a_field')
      (isField_of_isIntegral_of_isField (cl_inj R L) h)
  exact ((IsDiscreteValuationRing.TFAE (integralClosure R L) hnf).out 1 3).mpr hD

end

end ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.RegKrull
namespace ReciprocityTheory.ChartRestriction.G.T0

namespace KrullColonIdeal

variable {R : Type*} [CommRing R]

def colonI (s c : R) : Ideal R where
  carrier := {r | r * c ∈ Ideal.span {s}}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq] at *
    rw [add_mul]
    exact Ideal.add_mem _ hx hy
  zero_mem' := by simp
  smul_mem' := by
    intro r x hx
    simp only [Set.mem_ofPred_eq, smul_eq_mul] at *
    rw [mul_assoc]
    exact Ideal.mul_mem_left _ _ hx

theorem mem_colonI {s c r : R} : r ∈ colonI s c ↔ r * c ∈ Ideal.span {s} := Iff.rfl

theorem exists_prime_colon [IsNoetherianRing R] (s a : R) (ha : a ∉ Ideal.span {s}) :
    ∃ b : R, b ∉ Ideal.span {s} ∧ colonI s a ≤ colonI s b ∧
      ∀ q1 q2 : R, q1 * q2 ∈ colonI s b → q1 ∈ colonI s b ∨ q2 ∈ colonI s b := by
  classical
  have hS : ({J : Ideal R | ∃ b : R, b ∉ Ideal.span {s} ∧ colonI s a ≤ colonI s b ∧
      colonI s b = J} : Set (Ideal R)).Nonempty := ⟨colonI s a, a, ha, le_rfl, rfl⟩
  obtain ⟨M, hM, hmax⟩ : ∃ M ∈ ({J : Ideal R | ∃ b : R, b ∉ Ideal.span {s} ∧
      colonI s a ≤ colonI s b ∧ colonI s b = J} : Set (Ideal R)),
      ∀ I ∈ ({J : Ideal R | ∃ b : R, b ∉ Ideal.span {s} ∧
      colonI s a ≤ colonI s b ∧ colonI s b = J} : Set (Ideal R)), ¬ M < I := by
    first
    | exact set_has_maximal_iff_noetherian.mpr inferInstance _ hS
    | exact WellFounded.has_min (wellFounded_submodule_gt R R) _ hS
  obtain ⟨b, hb, hab, rfl⟩ := hM
  refine ⟨b, hb, hab, fun q1 q2 h => ?_⟩
  by_cases h1 : q1 ∈ colonI s b
  · exact Or.inl h1
  · right

    have hle : colonI s b ≤ colonI s (q1 * b) := by
      intro r hr
      rw [mem_colonI] at hr ⊢
      have e : r * (q1 * b) = q1 * (r * b) := by ring
      rw [e]
      exact Ideal.mul_mem_left _ q1 hr
    have hnot : q1 * b ∉ Ideal.span {s} := fun h' => h1 (mem_colonI.2 h')
    have heq : colonI s b = colonI s (q1 * b) := by
      by_contra hne
      exact hmax _ ⟨q1 * b, hnot, hab.trans hle, rfl⟩ (lt_of_le_of_ne hle hne)
    rw [heq, mem_colonI]
    have h' := mem_colonI.1 h
    have e : q2 * (q1 * b) = q1 * q2 * b := by ring
    rw [e]
    exact h'

end KrullColonIdeal


open KrullColonIdeal in
theorem mem_of_mem_heightOne_localizations {R K : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K] (x : K)
    (hx : ∀ p : Ideal R, p.IsPrime → p.height = 1 →
      ∃ a s : R, s ∉ p ∧ x * algebraMap R K s = algebraMap R K a) :
    ∃ r : R, algebraMap R K r = x := open KrullColonIdeal in by
  classical

  obtain ⟨a, b, hb0, hxab⟩ : ∃ a b : R, b ≠ 0 ∧ x * algebraMap R K b = algebraMap R K a := by
    obtain ⟨⟨a, ⟨b, hb⟩⟩, hx'⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) x
    refine ⟨a, b, nonZeroDivisors.ne_zero hb, ?_⟩
    rw [← hx']
    exact IsLocalization.mk'_spec K a ⟨b, hb⟩
  have hbK : algebraMap R K b ≠ 0 := by
    intro h
    apply hb0
    apply IsFractionRing.injective R K
    rw [h, map_zero]
  by_contra hne
  have ha : a ∉ Ideal.span {b} := by
    intro h
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 h
    apply hne
    refine ⟨r, ?_⟩
    apply mul_right_cancel₀ hbK
    rw [hxab, ← hr, map_mul]
  obtain ⟨c, hc, hac, hprime⟩ := exists_prime_colon b a ha
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hc (Ideal.zero_mem _)
  have hbP : b ∈ colonI b c := mem_colonI.2 (Ideal.mul_mem_right c _ (Ideal.mem_span_singleton_self b))
  have hPne : colonI b c ≠ ⊥ := by
    intro h
    have hb' := hbP
    rw [h, Ideal.mem_bot] at hb'
    exact hb0 hb'
  have hPprime : (colonI b c).IsPrime := by
    refine ⟨?_, fun h => hprime _ _ h⟩
    refine (Ideal.ne_top_iff_one _).2 (fun h1 => hc ?_)
    have h1' := mem_colonI.1 h1
    rwa [one_mul] at h1'

  have key : ∃ q0 ∈ colonI b c, ∃ u : R, u ∉ colonI b c ∧ u * b = q0 * c := by
    by_contra hcon
    push_neg at hcon
    apply hc
    have hint : IsIntegral R (algebraMap R K c / algebraMap R K b) := by
      refine isIntegral_of_smul_mem_submodule
        (Submodule.map (Algebra.linearMap R K) (colonI b c)) ?_ ?_ _ ?_
      · intro hbot
        have hmem : algebraMap R K b ∈ Submodule.map (Algebra.linearMap R K) (colonI b c) :=
          Submodule.mem_map_of_mem hbP
        rw [hbot, Submodule.mem_bot] at hmem
        exact hbK hmem
      · exact (IsNoetherian.noetherian (colonI b c)).map _
      · intro n hn
        obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.1 hn
        obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 (mem_colonI.1 hq)
        have hvP : v ∈ colonI b c := by
          by_contra hv'
          exact hcon q hq v hv' hv
        refine Submodule.mem_map.2 ⟨v, hvP, ?_⟩
        have hv2 : algebraMap R K v * algebraMap R K b = algebraMap R K q * algebraMap R K c := by
          rw [← map_mul, ← map_mul, hv]
        simp only [Algebra.linearMap_apply, smul_eq_mul]
        first
        | (rw [div_mul_eq_mul_div, eq_div_iff hbK]; linear_combination hv2)
        | (field_simp; linear_combination hv2)
        | (field_simp; linear_combination -hv2)
    obtain ⟨r, hr⟩ : ∃ r : R, algebraMap R K r = algebraMap R K c / algebraMap R K b := by
      first
      | exact IsIntegrallyClosed.isIntegral_iff.1 hint
      | exact IsIntegrallyClosed.algebraMap_eq_of_integral hint
    have hrc : r * b = c := by
      apply IsFractionRing.injective R K
      rw [map_mul, hr]
      first
      | exact div_mul_cancel₀ _ hbK
      | field_simp
    exact Ideal.mem_span_singleton'.2 ⟨r, hrc⟩
  obtain ⟨q0, hq0, u, hu, huq⟩ := key
  have huP : ∀ q ∈ colonI b c, u * q ∈ Ideal.span {q0} := by
    intro q hq
    obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 (mem_colonI.1 hq)
    refine Ideal.mem_span_singleton'.2 ⟨v, ?_⟩
    apply mul_right_cancel₀ hc0
    linear_combination (-v) * huq + u * hv

  have hmin : colonI b c ∈ (Ideal.span {q0}).minimalPrimes := by
    refine ⟨⟨hPprime, ?_⟩, fun Q hQ hQP => ?_⟩
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact hq0
    · intro q hq
      have huq' : u * q ∈ Q := hQ.2 (huP q hq)
      rcases hQ.1.mem_or_mem huq' with h | h
      · exact absurd (hQP h) hu
      · exact h
  haveI : Submodule.IsPrincipal (Ideal.span {q0}) := ⟨⟨q0, rfl⟩⟩
  have hle1 : (colonI b c).height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {q0}) _ hmin
  have hge1 : (1 : ℕ∞) ≤ (colonI b c).height := by
    rw [ENat.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
    exact hPne
  have hheight : (colonI b c).height = 1 := le_antisymm hle1 hge1
  obtain ⟨a', s', hs', hs'x⟩ := hx (colonI b c) hPprime hheight
  apply hs'
  apply hac
  rw [mem_colonI]
  refine Ideal.mem_span_singleton'.2 ⟨a', ?_⟩
  apply IsFractionRing.injective R K
  rw [map_mul, map_mul, ← hs'x, ← hxab]
  ring

end ReciprocityTheory.ChartRestriction.G.T0
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.PTNonempty
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField Cardinal

private lemma countable_of_intermediateField_fg {K Ω : Type} [Field K] [Countable K] [Field Ω] [Algebra K Ω]
    (hfg : (⊤ : IntermediateField K Ω).FG) : Countable Ω := by
  obtain ⟨S, hS⟩ := hfg
  haveI : Countable (MvPolynomial (S : Set Ω) K) := by
    first
    | infer_instance
    | exact Cardinal.mk_le_aleph0_iff.mp (MvPolynomial.cardinal_mk_le_max.trans
        (max_le (max_le Cardinal.mk_le_aleph0 Cardinal.mk_le_aleph0) le_rfl))
    | exact Cardinal.mk_le_aleph0_iff.mp (MvPolynomial.cardinalMk_le_max_lift.trans
        (max_le (max_le (Cardinal.lift_le_aleph0.mpr Cardinal.mk_le_aleph0)
          (Cardinal.lift_le_aleph0.mpr Cardinal.mk_le_aleph0)) le_rfl))
    | exact Cardinal.mk_le_aleph0_iff.mp (MvPolynomial.cardinalMk_le_max.trans
        (max_le (max_le Cardinal.mk_le_aleph0 Cardinal.mk_le_aleph0) le_rfl))
  let f : MvPolynomial (S : Set Ω) K × MvPolynomial (S : Set Ω) K → Ω := fun pq =>
    MvPolynomial.aeval (fun x : (S : Set Ω) => (x : Ω)) pq.1 /
      MvPolynomial.aeval (fun x : (S : Set Ω) => (x : Ω)) pq.2
  have hf : Function.Surjective f := by
    intro x
    have hx : x ∈ IntermediateField.adjoin K (S : Set Ω) := by
      rw [hS]; exact IntermediateField.mem_top
    obtain ⟨r, hr, t, ht, rfl⟩ := (IntermediateField.mem_adjoin_iff_div).mp hx
    rw [Algebra.adjoin_eq_range] at hr ht
    obtain ⟨p, rfl⟩ := hr
    obtain ⟨q, rfl⟩ := ht
    exact ⟨(p, q), rfl⟩
  exact hf.countable

theorem exists_embedding_over {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    (hfg : (⊤ : IntermediateField K Ω).FG) (sg : K →+* ℂ) :
    ∃ P : Ω →+* ℂ, P.comp (algebraMap K Ω) = sg := by
  haveI hKc : Countable K := by
    first
    | infer_instance
    | exact (Module.finBasis ℚ K).equivFun.injective.countable
  haveI hΩc : Countable Ω := countable_of_intermediateField_fg hfg
  letI : Algebra K ℂ := sg.toAlgebra
  haveI : FaithfulSMul K ℂ := by
    first
    | infer_instance
    | exact (faithfulSMul_iff_algebraMap_injective K ℂ).mpr sg.injective
  haveI : FaithfulSMul K Ω := by
    first
    | infer_instance
    | exact (faithfulSMul_iff_algebraMap_injective K Ω).mpr (algebraMap K Ω).injective
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K Ω
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis K ℂ
  have hC : Cardinal.aleph0 < Cardinal.mk ℂ := by
    rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum
  have hKle : Cardinal.mk K ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0
  have htt : Cardinal.aleph0 < Cardinal.mk t := by
    first
    | (by_contra hle
       have h := IsAlgClosed.cardinal_le_max_transcendence_basis _ ht
       exact absurd (h.trans (max_le (max_le hKle (not_lt.mp hle)) le_rfl)) (not_le.mpr hC))
    | (have h := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _ ht hKle hC
       rw [Cardinal.lift_inj] at h
       rw [h] at hC
       exact hC)
  have hst : Cardinal.mk s ≤ Cardinal.mk t := Cardinal.mk_le_aleph0.trans htt.le
  obtain ⟨e⟩ := (Cardinal.le_def _ _).mp hst
  let u : s → ℂ := fun i => ((e i : t) : ℂ)
  have hu : AlgebraicIndependent K u := ht.1.comp e e.injective
  let E := hs.1.aevalEquiv.symm.trans hu.aevalEquiv
  let φ : Algebra.adjoin K (Set.range (Subtype.val : s → Ω)) →ₐ[K] ℂ :=
    (Algebra.adjoin K (Set.range u)).val.comp E.toAlgHom
  have hφ : Function.Injective φ := Subtype.val_injective.comp E.injective
  letI : Algebra (Algebra.adjoin K (Set.range (Subtype.val : s → Ω))) ℂ := φ.toRingHom.toAlgebra
  haveI : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range (Subtype.val : s → Ω))) Ω :=
    hs.isAlgebraic
  try haveI : NoZeroSMulDivisors (Algebra.adjoin K (Set.range (Subtype.val : s → Ω))) ℂ :=
    NoZeroSMulDivisors.of_algebraMap_injective hφ
  try haveI : FaithfulSMul (Algebra.adjoin K (Set.range (Subtype.val : s → Ω))) ℂ :=
    (faithfulSMul_iff_algebraMap_injective _ ℂ).mpr hφ
  try haveI : NoZeroSMulDivisors (Algebra.adjoin K (Set.range (Subtype.val : s → Ω))) Ω :=
    NoZeroSMulDivisors.of_algebraMap_injective Subtype.val_injective
  try haveI : FaithfulSMul (Algebra.adjoin K (Set.range (Subtype.val : s → Ω))) Ω :=
    (faithfulSMul_iff_algebraMap_injective _ Ω).mpr Subtype.val_injective
  let g : Ω →ₐ[Algebra.adjoin K (Set.range (Subtype.val : s → Ω))] ℂ := IsAlgClosed.lift
  refine ⟨g.toRingHom, ?_⟩
  ext k
  have h1 : algebraMap K Ω k = algebraMap (Algebra.adjoin K (Set.range (Subtype.val : s → Ω))) Ω
      (algebraMap K (Algebra.adjoin K (Set.range (Subtype.val : s → Ω))) k) := by
    first
    | rfl
    | exact IsScalarTower.algebraMap_apply _ _ _ k
  show g (algebraMap K Ω k) = sg k
  rw [h1, g.commutes]
  exact φ.commutes k

end ReciprocityTheory.ChartRestriction.G.T0
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.RegLaw
namespace ReciprocityTheory.ChartRestriction.G.T0

def RegLaw {Λ Wt : Type*} (Forms : Wt → Type*) (Pt Pt' : Λ → Type*)
    (emb : ∀ la, Pt la → Pt' la) (v : ∀ la, Pt' la → ∀ {w : Wt}, Forms w → EReal)
    (Q : Type*) (ord : Q → ∀ {w : Wt}, Forms w → EReal)
    (NoZero : ∀ {w : Wt} {n : ℕ}, (Fin n → Forms w) → Prop) : Prop :=

  (∀ (w : Wt) (F : Forms w),
    (∀ la (y : Pt la), 0 ≤ v la (emb la y) F) →
      (∀ la (y' : Pt' la), 0 ≤ v la y' F) ∧ ∀ q : Q, 0 ≤ ord q F) ∧

  (∀ (wL wE : Wt) (n : ℕ) (ws : Fin n → Forms wL) (et : Forms wE) (nu : Λ → ℝ) (c' : ℝ),
    0 ≤ c' → NoZero ws →
    (∀ la (y : Pt la), 0 ≤ v la (emb la y) et ∧ (v la (emb la y) et ≠ ⊤ →
      (⨅ k, v la (emb la y) (ws k)) ≤ (nu la : EReal) + (c' : EReal) * v la (emb la y) et)) →
    (∀ la (y' : Pt' la), 0 ≤ v la y' et ∧ (v la y' et ≠ ⊤ →
      (⨅ k, v la y' (ws k)) ≤ (nu la : EReal) + (c' : EReal) * v la y' et)) ∧
    ∀ q : Q, 0 ≤ ord q et ∧ (ord q et ≠ ⊤ → (⨅ k, ord q (ws k)) ≤ (c' : EReal) * ord q et))

end ReciprocityTheory.ChartRestriction.G.T0
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.BinomRatio
namespace ReciprocityTheory.ChartRestriction.G.T0

private theorem choose_succ_mul_succ_eq_choose_mul_sub (n k : ℕ) (h : k ≤ n) :
    ((n.choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) = ((n.choose k : ℕ) : ℝ) * ((n : ℝ) - k) := by
  have h1 := Nat.choose_succ_right_eq n k
  have h2 : ((n - k : ℕ) : ℝ) = (n : ℝ) - k := Nat.cast_sub h
  rw [← h2]
  exact_mod_cast h1

theorem sub_mul_choose_le_mul_choose (T D : ℕ) (hT : D * (2 * D + 7) ≤ T) :
    ∀ k ≤ D, ((T : ℝ) - k * (2 * D + 7)) * (((T + 2 * D + 6).choose k : ℕ) : ℝ) ≤
      (T : ℝ) * (((T - 1).choose k : ℕ) : ℝ) := by
  intro k hk
  induction k with
  | zero => simp
  | succ k ih =>
    have ih := ih (by omega)
    have h7 : 7 * D ≤ T := by nlinarith [Nat.zero_le (D * D)]
    have hA := choose_succ_mul_succ_eq_choose_mul_sub (T + 2 * D + 6) k (by omega)
    have hB := choose_succ_mul_succ_eq_choose_mul_sub (T - 1) k (by omega)
    have ha : ((T + 2 * D + 6 : ℕ) : ℝ) = (T : ℝ) + 2 * D + 6 := by push_cast; ring
    have hT1 : ((T - 1 : ℕ) : ℝ) = (T : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [ha] at hA
    rw [hT1] at hB
    have hkT : ((k : ℝ) + 2) ≤ T := by exact_mod_cast (show k + 2 ≤ T by omega)
    have hb : (0 : ℝ) ≤ (T : ℝ) - 1 - k := by linarith
    have hCA : (0 : ℝ) ≤ (((T + 2 * D + 6).choose k : ℕ) : ℝ) := Nat.cast_nonneg _
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hdiff : (0 : ℝ) ≤ ((T : ℝ) - k * (2 * D + 7)) * ((T : ℝ) - 1 - k) -
        ((T : ℝ) - ((k : ℝ) + 1) * (2 * D + 7)) * ((T : ℝ) + 2 * D + 6 - k) := by
      have e : ((T : ℝ) - k * (2 * D + 7)) * ((T : ℝ) - 1 - k) -
          ((T : ℝ) - ((k : ℝ) + 1) * (2 * D + 7)) * ((T : ℝ) + 2 * D + 6 - k) =
          (2 * (D : ℝ) + 7) * ((k : ℝ) + 1) * (2 * (D : ℝ) + 6) := by ring
      rw [e]; positivity
    have P := mul_le_mul_of_nonneg_right ih hb
    have Q := mul_nonneg hCA hdiff
    have key : ((T : ℝ) - ((k : ℝ) + 1) * (2 * D + 7)) *
        (((T + 2 * D + 6).choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) ≤
        (T : ℝ) * (((T - 1).choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) := by
      have e1 : ((T : ℝ) - ((k : ℝ) + 1) * (2 * D + 7)) *
          (((T + 2 * D + 6).choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) =
          ((T : ℝ) - ((k : ℝ) + 1) * (2 * D + 7)) *
          ((((T + 2 * D + 6).choose k : ℕ) : ℝ) * ((T : ℝ) + 2 * D + 6 - k)) := by
        linear_combination ((T : ℝ) - ((k : ℝ) + 1) * (2 * D + 7)) * hA
      have e2 : (T : ℝ) * (((T - 1).choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) =
          (T : ℝ) * ((((T - 1).choose k : ℕ) : ℝ) * ((T : ℝ) - 1 - k)) := by
        linear_combination (T : ℝ) * hB
      rw [e1, e2]
      nlinarith [P, Q]
    push_cast
    exact le_of_mul_le_mul_right key hk1

end ReciprocityTheory.ChartRestriction.G.T0
end

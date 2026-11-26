module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedFDerivWordEqCoeff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineH2SmallCoverBijective
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsSmulPtSmulPt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicCompleteOfFiniteBasis
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CuspValueComparison
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicPointExtOfIsSeparated
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicPointExtOfIsSeparated
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.AnPer

theorem point_hol_ext_of_isSeparated : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Opens E) {X : Scheme.{0}}, X.IsSeparated → ∀ x x' : Sp (Hol W) ⟶ X, (∀ (p : E) (hp : p ∈ W), spMap (Hol.ev p hp).toRingHom ≫ x = spMap (Hol.ev p hp).toRingHom ≫ x') → x = x' := by
  intro E _ _ W X hX x x' h
  have : IsSeparated (terminal.from X) := hX.isSeparated_terminal_from
  exact point_hol_ext E W X (⊤_ Scheme) (terminal.from X) x x' (terminal.hom_ext _ _) h

end GlobalTheory.AnPer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicPointExtOfIsSeparatedStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphicPoint_ext_of_isSeparated : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Opens E) {X : Scheme.{0}}, X.IsSeparated → ∀ x x' : Sp (Hol W) ⟶ X, (∀ (p : E) (hp : p ∈ W), spMap (Hol.ev p hp).toRingHom ≫ x = spMap (Hol.ev p hp).toRingHom ≫ x') → x = x' := by
  first | exact @GlobalTheory.AnPer.point_hol_ext_of_isSeparated | exact GlobalTheory.AnPer.point_hol_ext_of_isSeparated | (intros; apply GlobalTheory.AnPer.point_hol_ext_of_isSeparated <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClosureThetaRatiosOfIsCl
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH

namespace GlobalTheory.ZH

theorem RatModel.IsCl.subfield_eq_top_of_ratios {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]
    {M : RatModel o Ω} {J : Type} {t : J → Ω} (h : M.IsCl t) (K : Subfield Ω)
    (hc : ∀ a, algebraMap o Ω a ∈ K) (hr : ∀ i j, t j / t i ∈ K) : K = ⊤ := by
  obtain ⟨i, hi⟩ := h.1 (genericPoint M.Z)
  obtain ⟨U, hU, hD, hR⟩ := h.2 i hi.1
  have hne : (U : Set M.Z).Nonempty := ⟨genericPoint M.Z, by rw [hD]; exact hi⟩
  let A : Subalgebra o Ω := { K.toSubring with algebraMap_mem' := hc }
  have hle : M.ringOn U ≤ A := by
    rw [hR]
    refine Algebra.adjoin_le ?_
    rintro _ ⟨j, rfl⟩
    exact hr i j
  refine top_unique fun x _ => ?_
  obtain ⟨a, b, -, rfl⟩ := RatModel.exists_eq_div hU hne x
  exact div_mem (hle ((RatModel.mem_ringOn_iff_exists hne).2 ⟨a, rfl⟩))
    (hle ((RatModel.mem_ringOn_iff_exists hne).2 ⟨b, rfl⟩))

theorem finite_closure_theta_ratios_of_isCl (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω)
    (M : RatModel o Ω) (J : Type) (t : J → Ω) (h : M.IsCl t) :
    Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪
      {x | ∃ i j : S.Gam × J, x = S.th j.1 * t j.2 / (S.th i.1 * t i.2)})) Ω := by
  obtain ⟨x, hx⟩ := S.th_ne
  have htop := h.subfield_eq_top_of_ratios (Subfield.closure (Set.range (algebraMap o Ω) ∪
      {x | ∃ i j : S.Gam × J, x = S.th j.1 * t j.2 / (S.th i.1 * t i.2)}))
    (fun a => Subfield.subset_closure (Or.inl ⟨a, rfl⟩))
    (fun i j => Subfield.subset_closure (Or.inr ⟨(x, i), (x, j), (mul_div_mul_left _ _ hx).symm⟩))
  refine Module.Finite.of_surjective (Algebra.linearMap _ Ω) fun y => ⟨⟨y, ?_⟩, rfl⟩
  rw [htop]
  exact Subfield.mem_top y

end GlobalTheory.ZH
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorPolynomialEvalAlgebraMulOfProdEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorPolynomialEvalAlgebraMulOfProdEqZero
open Filter Topology

namespace GlobalTheory.PeriodFamily

section

variable {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D]

theorem exists_prod_dvd_monomial (t : I → D) (k : ℕ) :
    ∀ m : I →₀ ℕ, k ≤ m.degree → ∃ s : Fin k → I, ∏ a, t (s a) ∣ ∏ i, t i ^ m i := by
  induction k with
  | zero => intro m _; exact ⟨Fin.elim0, by simp⟩
  | succ k ih =>
    intro m hm
    have h : m ≠ 0 := by rintro rfl; simp at hm
    obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by simpa using Finsupp.ne_iff.1 h
    have hle : Finsupp.single i 1 ≤ m := by
      rw [Finsupp.single_le_iff]; omega
    obtain ⟨m', rfl⟩ := exists_add_of_le hle
    obtain ⟨s, hs⟩ := ih m' (by rw [map_add (f := _), Finsupp.degree_single] at hm; omega)
    refine ⟨Fin.cons i s, ?_⟩
    have h1 : ∏ j, t j ^ (Finsupp.single i 1 : I →₀ ℕ) j = t i := by
      rw [Finset.prod_eq_single i] <;> simp +contextual [Finsupp.single_apply, eq_comm]
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Finsupp.add_apply, pow_add,
      Finset.prod_mul_distrib, h1]
    exact mul_dvd_mul_left _ hs

variable [Algebra ℂ D]

theorem aeval_eq_zero_of_coeff_eq_zero {N : ℕ} {t : I → D}
    (ht : ∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) (P : MvPolynomial I ℂ)
    (hP : ∀ m : I →₀ ℕ, m.degree < N + 1 → P.coeff m = 0) : MvPolynomial.aeval t P = 0 := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
  refine Finset.sum_eq_zero fun m hm => ?_
  have h : N + 1 ≤ m.degree := by
    by_contra h
    exact MvPolynomial.mem_support_iff.1 hm (hP m (by omega))
  obtain ⟨s, hs⟩ := exists_prod_dvd_monomial t (N + 1) m h
  rw [ht, zero_dvd_iff] at hs
  rw [hs, mul_zero]


omit [Algebra ℂ D] [CommRing D] in
theorem coeff_sum_monomial_finsuppAntidiag (N : ℕ) (F : MvPowerSeries I ℂ) (n : I →₀ ℕ)
    (hn : n.degree < N + 1) :
    AddMonoidAlgebra.coeff (∑ k ∈ Finset.range (N + 1),
      ∑ m ∈ Finset.finsuppAntidiag (Finset.univ : Finset I) k,
        MvPolynomial.monomial m (MvPowerSeries.coeff m F)) n = MvPowerSeries.coeff n F := by
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Finset.sum_ite_eq',
    Finset.mem_finsuppAntidiag, Finset.subset_univ, and_true]
  rw [← Finsupp.degree_eq_sum, Finset.sum_ite_eq, if_pos (Finset.mem_range.2 hn)]

theorem aeval_sum_monomial_finsuppAntidiag (N : ℕ) (t : I → D) (F : MvPowerSeries I ℂ) :
    MvPolynomial.aeval t (∑ k ∈ Finset.range (N + 1),
      ∑ m ∈ Finset.finsuppAntidiag (Finset.univ : Finset I) k,
        MvPolynomial.monomial m (MvPowerSeries.coeff m F)) =
      ∑ k ∈ Finset.range (N + 1), ∑ m ∈ Finset.finsuppAntidiag (Finset.univ : Finset I) k,
        MvPowerSeries.coeff m F • ∏ i, t i ^ m i := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, MvPolynomial.aeval_monomial, Algebra.smul_def,
    Finsupp.prod_fintype _ _ (fun i => pow_zero (t i))]

end

theorem taylor_mul_of_prod_eq_zero : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type}
    [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) →
    ∀ f g : (I → ℂ) → ℂ, AnalyticAt ℂ f 0 → AnalyticAt ℂ g 0 →
      GlobalTheory.PeriodFamily.taylor N t (fun z ↦ f z * g z) =
        GlobalTheory.PeriodFamily.taylor N t f * GlobalTheory.PeriodFamily.taylor N t g := by
  intro I _ _ D _ _ N t ht f g hf hg
  change GlobalTheory.PeriodFamily.taylor N t (f * g) = _
  rw [GlobalTheory.PeriodFamily.taylor_eq_sum_coeff_taylor N t _ (hf.mul hg), GlobalTheory.PeriodFamily.taylor_eq_sum_coeff_taylor N t _ hf, GlobalTheory.PeriodFamily.taylor_eq_sum_coeff_taylor N t _ hg,
    GlobalTheory.taylor_mul hf hg, ← aeval_sum_monomial_finsuppAntidiag,
    ← aeval_sum_monomial_finsuppAntidiag, ← aeval_sum_monomial_finsuppAntidiag, ← map_mul,
    ← sub_eq_zero, ← map_sub]
  refine aeval_eq_zero_of_coeff_eq_zero ht _ fun m hm => ?_
  rw [MvPolynomial.coeff_sub, coeff_sum_monomial_finsuppAntidiag _ _ _ hm, MvPolynomial.coeff_mul,
    MvPowerSeries.coeff_mul, sub_eq_zero]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [← hp, map_add (f := _)] at hm
  rw [coeff_sum_monomial_finsuppAntidiag _ _ _ (by omega),
    coeff_sum_monomial_finsuppAntidiag _ _ _ (by omega)]

end GlobalTheory.PeriodFamily
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorPolynomialEvalAlgebraMulOfProdEqZeroStatement
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.taylorPolynomialEvalAlgebra_mul_of_prod_eq_zero : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ f g : (I → ℂ) → ℂ, AnalyticAt ℂ f 0 → AnalyticAt ℂ g 0 → GlobalTheory.PeriodFamily.taylor N t (fun z ↦ f z * g z) = GlobalTheory.PeriodFamily.taylor N t f * GlobalTheory.PeriodFamily.taylor N t g := by
  first | exact @GlobalTheory.PeriodFamily.taylor_mul_of_prod_eq_zero | exact GlobalTheory.PeriodFamily.taylor_mul_of_prod_eq_zero | (intros; apply GlobalTheory.PeriodFamily.taylor_mul_of_prod_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallChartPairAlongLinearMap
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallChartPairAlongLinearMap
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer.ChartPair

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
  {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V}

theorem exists_affine_pt (y : Sp ℂ ⟶ X) : ∃ U : X.Opens, IsAffineOpen U ∧ ⊤ ≤ y ⁻¹ᵁ U := by
  obtain ⟨U, hU, hy, -⟩ := exists_isAffineOpen_mem_and_subset (x := y (default : PrimeSpectrum ℂ)) (U := ⊤) trivial
  refine ⟨U, hU, fun p _ ↦ ?_⟩
  have : p = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  subst this
  exact hy

theorem isOpen_dom (u : Unif F s σ) (U : X.Opens) : IsOpen {p : Tot I g | p.1 ∈ F.V ∧ ⊤ ≤ u.E p ⁻¹ᵁ U} :=
  (u.hol U 0).1

def Good (u : Unif F s σ) (W : Opens (Tot I g)) : Prop :=
  (∀ p ∈ W, p.1 ∈ F.V) ∧ ∃ U : X.Opens, IsAffineOpen U ∧ ∀ p ∈ W, ⊤ ≤ u.E p ⁻¹ᵁ U

def charts (u : Unif F s σ) : Charts F where
  K := {W : Opens (Tot I g) // Good u W}
  W k := k.1
  base k := k.2.1
  le l k' k := ∀ p ∈ k'.1, F.shift l p ∈ k.1
  le_refl k p hp := by rwa [F.shift_zero]
  le_trans {l m k k' k''} h h' p hp := by rw [F.shift_add]; exact h _ (h' p hp)
  maps h := h

end GlobalTheory.AnPer.ChartPair

namespace GlobalTheory.AnPer.ChartPair

variable {I₁ : Type} [Fintype I₁] {g₁ : ℕ} {Λ₁ : Type} [AddCommGroup Λ₁] {F₁ : Fam I₁ g₁ Λ₁}
  {B₁ : Type} [CommRing B₁] {X₁ : Scheme.{0}} {s₁ : X₁ ⟶ Sp B₁} {σ₁ : B₁ →+* Hol F₁.V}
  {I₂ : Type} [Fintype I₂] {g₂ : ℕ} {Λ₂ : Type} [AddCommGroup Λ₂] {F₂ : Fam I₂ g₂ Λ₂}
  {B₂ : Type} [CommRing B₂] {X₂ : Scheme.{0}} {s₂ : X₂ ⟶ Sp B₂} {σ₂ : B₂ →+* Hol F₂.V}

def pairCharts (u₁ : Unif F₁ s₁ σ₁) (u₂ : Unif F₂ s₂ σ₂) (b : (I₁ → ℂ) → I₂ → ℂ)
    (M : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ)) (A : Λ₁ →+ Λ₂) : Charts F₁ where
  K := {q : Opens (Tot I₁ g₁) × Opens (Tot I₂ g₂) //
    Good u₁ q.1 ∧ Good u₂ q.2 ∧ ∀ p ∈ q.1, ((b p.1, M p.2) : Tot I₂ g₂) ∈ q.2}
  W k := k.1.1
  base k := k.2.1.1
  le l k' k := (∀ p ∈ k'.1.1, F₁.shift l p ∈ k.1.1) ∧ ∀ p ∈ k'.1.2, F₂.shift (A l) p ∈ k.1.2
  le_refl k := ⟨fun p hp ↦ by rwa [F₁.shift_zero], fun p hp ↦ by rwa [map_zero, F₂.shift_zero]⟩
  le_trans {l m k k' k''} h h' := ⟨fun p hp ↦ by rw [F₁.shift_add]; exact h.1 _ (h'.1 p hp),
    fun p hp ↦ by rw [map_add (f := _), F₂.shift_add]; exact h.2 _ (h'.2 p hp)⟩
  maps h := h.1

theorem exists_pair (u₁ : Unif F₁ s₁ σ₁) (u₂ : Unif F₂ s₂ σ₂) (b : (I₁ → ℂ) → I₂ → ℂ)
    (hb : AnalyticOnNhd ℂ b F₁.V) (hbV : ∀ z ∈ F₁.V, b z ∈ F₂.V)
    (M : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ)) (A : Λ₁ →+ Λ₂)
    (hτ : ∀ l, ∀ z ∈ F₁.V, F₂.τ (A l) (b z) = M (F₁.τ l z)) :
    ∃ (K₁ : Charts F₁) (K₂ : Charts F₂) (κ : K₁.K → K₂.K), K₁.Rich ∧
      (∀ k, ∃ U, IsAffineOpen U ∧ ∀ p ∈ K₁.W k, ⊤ ≤ u₁.E p ⁻¹ᵁ U) ∧
      (∀ k, ∃ U, IsAffineOpen U ∧ ∀ p ∈ K₂.W k, ⊤ ≤ u₂.E p ⁻¹ᵁ U) ∧
      (∀ k, ∀ p ∈ K₁.W k, ((b p.1, M p.2) : Tot I₂ g₂) ∈ K₂.W (κ k)) ∧
      ∀ l k' k, K₁.le l k' k → K₂.le (A l) (κ k') (κ k) := by
  let Φ : Tot I₁ g₁ → Tot I₂ g₂ := fun p ↦ (b p.1, M p.2)
  have hΦ : ∀ l (p : Tot I₁ g₁), p.1 ∈ F₁.V → Φ (F₁.shift l p) = F₂.shift (A l) (Φ p) := by
    intro l p hp
    simp only [Φ, Fam.shift, map_add (f := _), hτ l p.1 hp]
  have hcont : ContinuousOn Φ {p : Tot I₁ g₁ | p.1 ∈ F₁.V} :=
    (hb.continuousOn.comp continuous_fst.continuousOn fun p hp ↦ hp).prodMk
      (M.continuous_of_finiteDimensional.comp continuous_snd).continuousOn
  refine ⟨pairCharts u₁ u₂ b M A, charts u₂, fun k ↦ ⟨k.1.2, k.2.2.1⟩, ⟨?_, ?_⟩,
    fun k ↦ k.2.1.2, fun k ↦ k.2.2, fun k ↦ k.2.2.2, fun l k' k h ↦ h.2⟩
  · intro p hp
    obtain ⟨U₁, hU₁, h₁⟩ := exists_affine_pt (u₁.E p)
    obtain ⟨U₂, hU₂, h₂⟩ := exists_affine_pt (u₂.E (Φ p))
    let O₁ := {q : Tot I₁ g₁ | q.1 ∈ F₁.V ∧ ⊤ ≤ u₁.E q ⁻¹ᵁ U₁}
    let O₂ := {q : Tot I₂ g₂ | q.1 ∈ F₂.V ∧ ⊤ ≤ u₂.E q ⁻¹ᵁ U₂}
    have hO₂ : IsOpen O₂ := isOpen_dom u₂ U₂
    have hO₁ : IsOpen (O₁ ∩ Φ ⁻¹' O₂) :=
      (hcont.mono fun (q : Tot I₁ g₁) (hq : q ∈ O₁) ↦ hq.1).isOpen_inter_preimage (isOpen_dom u₁ U₁) hO₂
    refine ⟨⟨(⟨O₁ ∩ Φ ⁻¹' O₂, hO₁⟩, ⟨O₂, hO₂⟩),
      ⟨fun q hq ↦ hq.1.1, U₁, hU₁, fun q hq ↦ hq.1.2⟩, ⟨fun q hq ↦ hq.1, U₂, hU₂, fun q hq ↦ hq.2⟩,
      fun q hq ↦ hq.2⟩, ?_⟩
    exact ⟨⟨hp, h₁⟩, hbV _ hp, h₂⟩
  · intro l k₁ k₂ p hp hp'
    have hb₁ := k₁.2.1.1
    have hb₂ := k₁.2.2.1.1
    have o₁ : IsOpen ((k₁.1.1 : Set (Tot I₁ g₁)) ∩ F₁.shift l ⁻¹' k₂.1.1) :=
      (F₁.shift_analytic l hb₁).continuousOn.isOpen_inter_preimage k₁.1.1.isOpen k₂.1.1.isOpen
    have o₂ : IsOpen ((k₁.1.2 : Set (Tot I₂ g₂)) ∩ F₂.shift (A l) ⁻¹' k₂.1.2) :=
      (F₂.shift_analytic (A l) hb₂).continuousOn.isOpen_inter_preimage k₁.1.2.isOpen k₂.1.2.isOpen
    obtain ⟨U₁, hU₁, h₁⟩ := k₁.2.1.2
    obtain ⟨U₂, hU₂, h₂⟩ := k₁.2.2.1.2
    refine ⟨⟨(⟨_, o₁⟩, ⟨_, o₂⟩), ⟨fun q hq ↦ hb₁ q hq.1, U₁, hU₁, fun q hq ↦ h₁ q hq.1⟩,
      ⟨fun q hq ↦ hb₂ q hq.1, U₂, hU₂, fun q hq ↦ h₂ q hq.1⟩, fun q hq ↦ ⟨k₁.2.2.2 q hq.1, ?_⟩⟩,
      ⟨hp, hp'⟩, ⟨fun q hq ↦ ?_, fun q hq ↦ ?_⟩, ⟨fun q hq ↦ hq.2, fun q hq ↦ hq.2⟩⟩
    · show F₂.shift (A l) (Φ q) ∈ k₂.1.2
      rw [← hΦ l q (hb₁ q hq.1)]
      exact k₂.2.2.2 _ hq.2
    · rw [F₁.shift_zero]; exact hq.1
    · rw [map_zero, F₂.shift_zero]; exact hq.1

end GlobalTheory.AnPer.ChartPair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallChartPairAlongLinearMapStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_small_chart_pair_along_linear_map : ∀ {I₁ : Type} [Fintype I₁] {g₁ : ℕ} {Λ₁ : Type} [AddCommGroup Λ₁] {F₁ : Fam I₁ g₁ Λ₁} {B₁ : Type} [CommRing B₁] {X₁ : Scheme.{0}} {s₁ : X₁ ⟶ Sp B₁} {σ₁ : B₁ →+* Hol F₁.V} {I₂ : Type} [Fintype I₂] {g₂ : ℕ} {Λ₂ : Type} [AddCommGroup Λ₂] {F₂ : Fam I₂ g₂ Λ₂} {B₂ : Type} [CommRing B₂] {X₂ : Scheme.{0}} {s₂ : X₂ ⟶ Sp B₂} {σ₂ : B₂ →+* Hol F₂.V} (u₁ : Unif F₁ s₁ σ₁) (u₂ : Unif F₂ s₂ σ₂) (b : (I₁ → ℂ) → I₂ → ℂ) (hb : AnalyticOnNhd ℂ b F₁.V) (hbV : ∀ z ∈ F₁.V, b z ∈ F₂.V) (M : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ)) (A : Λ₁ →+ Λ₂), (∀ l, ∀ z ∈ F₁.V, F₂.τ (A l) (b z) = M (F₁.τ l z)) → ∃ (K₁ : Charts F₁) (K₂ : Charts F₂) (κ : K₁.K → K₂.K), K₁.Rich ∧ (∀ k, ∃ U, IsAffineOpen U ∧ ∀ p ∈ K₁.W k, ⊤ ≤ u₁.E p ⁻¹ᵁ U) ∧ (∀ k, ∃ U, IsAffineOpen U ∧ ∀ p ∈ K₂.W k, ⊤ ≤ u₂.E p ⁻¹ᵁ U) ∧ (∀ k, ∀ p ∈ K₁.W k, ((b p.1, M p.2) : Tot I₂ g₂) ∈ K₂.W (κ k)) ∧ ∀ l k' k, K₁.le l k' k → K₂.le (A l) (κ k') (κ k) := by
  first | exact @GlobalTheory.AnPer.ChartPair.exists_pair | exact GlobalTheory.AnPer.ChartPair.exists_pair | (intros; apply GlobalTheory.AnPer.ChartPair.exists_pair <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsolutelyIntegrallyClosedDomainTateTwistAcyclic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShEqvTw
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShEqvTw
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem sh_eqv_tw : ∀ (q : ℕ) (i : ℤ) (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B), SH A → SH B → IsUnit (q : A) → Eqv _ (spMap φ) (tw q i) := by
  intro q i A B _ _ φ hA hB hq
  obtain ⟨hAl, _⟩ := hA
  obtain ⟨hBl, _⟩ := hB
  obtain ⟨ζ⟩ := GlobalTheory.T.nonempty_cyclotomicPrimitiveRoots_of_strictlyHenselian q A ⟨hAl, ‹_›⟩ hq
  let S : Scheme.{0} := Spec (CommRingCat.of A)
  let ζS : Prim q Γ(S, ⊤) := Prim.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ζ
  have hgen := GlobalTheory.T.tateTwist_isFreeRankOne_on_generatorSection q i S ζS
  have hac : ∀ (C : Type) [CommRing C], SH C → AcycF (ZMod q) (sch.obj (Spec (CommRingCat.of C))) (tw q i) :=
    fun C _ hC n hn => GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf (ZMod q) C hC (tw q i) n hn
  refine GlobalTheory.T.etaleCohomologyEquiv_of_locallyConstant_bijective (ZMod q) (tw q i) S (twGen i ζS) hgen S (Spec (CommRingCat.of B)) (𝟙 S)
    (Spec.map (CommRingCat.ofHom φ)) (hac A ⟨hAl, ‹_›⟩) (hac B ⟨hBl, ‹_›⟩) ?_
  have cA := GlobalTheory.T.locallyConstant_spec_localRing_const_bijective (ZMod q) A
  have cB := GlobalTheory.T.locallyConstant_spec_localRing_const_bijective (ZMod q) B
  have hcomp : (fun φ' : LocallyConstant S (ZMod q) => φ'.comap (Spec.map (CommRingCat.ofHom φ)).base.hom) ∘
      (fun c : ZMod q => LocallyConstant.const S c) = fun c => LocallyConstant.const _ c := by
    funext c; ext x; rfl
  refine (Function.Bijective.of_comp_iff _ cA).1 ?_
  rw [hcomp]
  exact cB
end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShEqvTwStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eqv_spMap_tw_of_isUnit : ∀ (q : ℕ) (i : ℤ) (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B), SH A → SH B → IsUnit (q : A) → Eqv _ (spMap φ) (tw q i) := by
  first | (exact @GlobalTheory.EtC.sh_eqv_tw) | (exact GlobalTheory.EtC.sh_eqv_tw) | (intros; apply GlobalTheory.EtC.sh_eqv_tw  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStrictlyHenselianOfIsFieldMonicRoots
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStrictlyHenselianOfIsFieldMonicRoots
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem isField_aic_sh : ∀ (T : Type) [CommRing T], IsField T → AIC T → SH T := by
  intro T _ hF hA
  letI : Field T := hF.toField
  refine ⟨Field.henselian T, ?_⟩
  haveI hT : IsAlgClosed T := by
    refine IsAlgClosed.of_exists_root T ?_
    intro p hm hirr
    obtain ⟨a, ha⟩ := hA p hm (Polynomial.natDegree_pos_iff_degree_pos.mpr (Polynomial.degree_pos_of_irreducible hirr))
    exact ⟨a, by simpa [Polynomial.IsRoot] using ha⟩
  have hinj : Function.Injective (IsLocalRing.residue T) := (IsLocalRing.residue T).injective
  have hbij : Function.Bijective (IsLocalRing.residue T) := ⟨hinj, IsLocalRing.residue_surjective⟩
  haveI : IsAlgClosed (IsLocalRing.ResidueField T) :=
    IsAlgClosed.of_ringEquiv T _ (RingEquiv.ofBijective _ hbij)
  infer_instance

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStrictlyHenselianOfIsFieldMonicRootsStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isStrictlyHenselian_of_isField_monicRoots : ∀ (T : Type) [CommRing T], IsField T → AIC T → SH T := by
  first | (exact @GlobalTheory.EtC.isField_aic_sh) | (exact GlobalTheory.EtC.isField_aic_sh) | (intros; apply GlobalTheory.EtC.isField_aic_sh  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsolutelyIntegrallyClosedDomainTateTwistAcyclic
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.AicAcyc

theorem aic_of_isAlgClosed (K : Type) [Field K] [IsAlgClosed K] : AIC K := by
  intro p hp hdeg
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root p (by
    rw [Polynomial.degree_eq_natDegree hp.ne_zero]; exact_mod_cast hdeg.ne')
  exact ⟨a, ha⟩

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]

theorem isIso_spMap {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) : IsIso (spMap (e : A →+* B)) := by
  haveI : IsIso (CommRingCat.ofHom (e : A →+* B)) := (RingEquiv.toCommRingCatIso e).isIso_hom
  unfold spMap
  infer_instance

end GlobalTheory.EtC.AicAcyc

namespace GlobalTheory.EtC


open GlobalTheory.EtC.AicAcyc in
theorem b5 : B5 := by
  intro q A _ _ hA hq n i hn
  haveI := GlobalTheory.T.isAlgClosed_fractionRing_of_monic_polynomials_have_roots A hA
  have hK : SH (FractionRing A) :=
    GlobalTheory.T.isStrictlyHenselian_of_isField_monicRoots (FractionRing A) (Field.toIsField _) (aic_of_isAlgClosed _)
  have hE := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties (ZMod q) (tw q i)
  have heqv : Eqv (ZMod q) (spMap (algebraMap A (FractionRing A))) (tw q i) := by
    refine GlobalTheory.T.etaleCohomology_local_to_global_ringMap_indEtale (ZMod q) (tw q i) (GlobalTheory.T.tateTwist_finitary q i) A A (FractionRing A)
      (Algebra.ofId A (FractionRing A)) ?_
    intro O _ _ hO hOind
    obtain ⟨hfield, haic⟩ := GlobalTheory.T.isField_monicRoots_tensor_fractionRing_strictlyHenselian A O hA hO hOind
    have hSH : SH (O ⊗[A] FractionRing A) := GlobalTheory.T.isStrictlyHenselian_of_isField_monicRoots _ hfield haic
    have hqO : IsUnit (q : O) := by
      simpa using hq.map (algebraMap A O)
    let e := Algebra.TensorProduct.rid A A O
    let j : O →ₐ[A] O ⊗[A] FractionRing A := Algebra.TensorProduct.includeLeft
    have hψ : (Algebra.TensorProduct.map (AlgHom.id A O) (Algebra.ofId A (FractionRing A))) =
        j.comp e.toAlgHom := by
      apply Algebra.TensorProduct.ext'
      intro o a
      simp [j, e, Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    rw [hψ]
    have h1 : Eqv (ZMod q) (spMap (j : O →+* O ⊗[A] FractionRing A)) (tw q i) :=
      GlobalTheory.T.eqv_spMap_tw_of_isUnit q i O _ (j : O →+* O ⊗[A] FractionRing A) hO hSH hqO
    have h2 : Eqv (ZMod q) (spMap ((e : O ⊗[A] A ≃+* O) : O ⊗[A] A →+* O)) (tw q i) := by
      haveI := isIso_spMap (e : O ⊗[A] A ≃+* O)
      exact hE.1 _ _ _ inferInstance
    have h3 := (hE.2.1 _ _ _ _ _).1 h1 h2
    rw [← spMap_comp] at h3
    exact h3
  have hacK : AcycF (ZMod q) (sp (FractionRing A)) (tw q i) :=
    fun m hm => GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf (ZMod q) (FractionRing A) hK (tw q i) m hm
  exact (hE.2.2.2 _ _ _ heqv).1 hacK n hn

end GlobalTheory.EtC

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsolutelyIntegrallyClosedDomainTateTwistAcyclicStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absolutelyIntegrallyClosed_domain_tateTwistAcyclic : GlobalTheory.EtC.B5 := by
  first | (exact @GlobalTheory.EtC.b5) | (exact GlobalTheory.EtC.b5) | (intros; apply GlobalTheory.EtC.b5  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelKlingenDeligneRibetOfBoth
namespace GlobalTheory

theorem siegelKlingenDeligneRibet_of_both :
    GlobalTheory.Published.SiegelKlingen → GlobalTheory.Published.DeligneRibet → GlobalTheory.Published.SiegelKlingenDeligneRibet :=
  fun a b => ⟨a, b⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpGLiAddSmul
noncomputable section

open NumberField

namespace GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E]

def expGLi (a : ℕ) (X : Matrix (Fin a) (Fin a) (Cinf E)) : GL (Fin a) (Cinf E) :=
  (Matrix.isUnit_exp X).unit

@[simp] theorem val_expGLi (a : ℕ) (X : Matrix (Fin a) (Fin a) (Cinf E)) :
    (expGLi a X).val = NormedSpace.exp X := rfl

theorem expGLi_add_smul (a : ℕ) (X : Matrix (Fin a) (Fin a) (Cinf E)) (s t : ℝ) :
    expGLi a ((s + t) • X) = expGLi a (s • X) * expGLi a (t • X) :=
  Units.ext (by
    rw [Units.val_mul, val_expGLi, val_expGLi, val_expGLi, add_smul]
    exact Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left s).smul_right t))

@[simp] theorem expGLi_zero (a : ℕ) : expGLi a (0 : Matrix (Fin a) (Fin a) (Cinf E)) = 1 :=
  Units.ext (by rw [val_expGLi, NormedSpace.exp_zero, Units.val_one])

end GlobalTheory.CuspRep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPureBCId
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PureLift

def IsPure {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] (W : A ⟶ A) [IsMonHom W] (r s : R) : Prop :=
  (∀ x ∈ Fil A, push (dp0 R) (𝟙 _) W x = r • x) ∧ ∀ y : HdR A, push (dp0 R) (𝟙 _) W y - s • y ∈ Fil A

def IsPureBC {S : Type} [CommRing S] (G : Over (Sp S)) [GrpObj G] (W : G ⟶ G) (r s : S) : Prop :=
  ∀ (R : Type) [CommRing R] (f : S →+* R) (A : Over (Sp R)) [GrpObj A] (φ : A.left ⟶ G.left),
    IsGrpPullback A G (spMap f) φ → ∀ (W' : A ⟶ A) [IsMonHom W'], W'.left ≫ φ = φ ≫ W.left → IsPure A W' (f r) (f s)

theorem IsPure.mem_Fil {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {W : A ⟶ A} [IsMonHom W] {r r' s : R}
    (h : IsPure A W r' s) (hu : IsUnit (r - s)) {y : HdR A} (hy : push (dp0 R) (𝟙 _) W y = r • y) : y ∈ Fil A := by
  have hm := h.2 y
  rw [hy, ← sub_smul] at hm
  obtain ⟨u, hu'⟩ := hu
  have hv := (Fil A).smul_mem (↑u⁻¹ : R) hm
  rwa [smul_smul, ← hu', Units.inv_mul, one_smul] at hv

end GlobalTheory.PureLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPermMatrixRepParabolicDoubleCoset
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPermMatrixRepParabolicDoubleCoset
open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism

namespace GlobalTheory.FinGL.Bruhat

theorem exists_perm_rep_blockTri : ∀ (F : Type) [Field F] (r : ℕ) (b b' : Fin r → ℕ), Monotone b → Monotone b' → ∀ g : GL (Fin r) F, ∃ (w : Equiv.Perm (Fin r)) (p' : blockTri (κ := F) b') (p : blockTri (κ := F) b), g = (p' : GL (Fin r) F) * permGL F w * (p : GL (Fin r) F) := by
  intro F _ r b b' hb hb' g
  have hle : ∀ (c : Fin r → ℕ), Monotone c → ∀ u ∈ unip F r, u ∈ blockTri (κ := F) c := by
    intro c hc u hu
    rw [mem_blockTri]
    intro i j hij
    exact unip_lower hu (lt_of_not_ge fun h => absurd (hc h) (not_le.2 hij))
  obtain ⟨m, u, hu, u', hu', h⟩ := exists_decomp g
  have hdet : (Matrix.diagonal fun c => (m.2 c : F)).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun c _ => (m.2 c).ne_zero
  let d : GL (Fin r) F := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet
  have hdv : (d : Matrix (Fin r) (Fin r) F) = Matrix.diagonal fun c => (m.2 c : F) := rfl
  have hd : d ∈ blockTri (κ := F) b := by
    rw [mem_blockTri]
    intro i j hij
    rw [hdv]
    exact Matrix.diagonal_apply_ne _ (fun e => by rw [e] at hij; exact lt_irrefl _ hij)
  have hm : mono m = (permGL F m.1 : Matrix (Fin r) (Fin r) F) * (d : Matrix (Fin r) (Fin r) F) := by
    ext a c
    rw [hdv, Matrix.mul_diagonal, permGL_apply]
    by_cases e : a = m.1 c <;> simp [mono, e]
  refine ⟨m.1, ⟨u, hle b' hb' u hu⟩, ⟨d * u', Subgroup.mul_mem _ hd (hle b hb u' hu')⟩, Units.ext ?_⟩
  rw [h, hm]
  simp only [Units.val_mul, Matrix.mul_assoc]

end GlobalTheory.FinGL.Bruhat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPermMatrixRepParabolicDoubleCosetStatement
open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_permMatrix_rep_parabolic_doubleCoset : ∀ (F : Type) [Field F] (r : ℕ) (b b' : Fin r → ℕ), Monotone b → Monotone b' → ∀ g : GL (Fin r) F, ∃ (w : Equiv.Perm (Fin r)) (p' : blockTri (κ := F) b') (p : blockTri (κ := F) b), g = (p' : GL (Fin r) F) * permGL F w * (p : GL (Fin r) F) := by
  first | exact @GlobalTheory.FinGL.Bruhat.exists_perm_rep_blockTri | exact GlobalTheory.FinGL.Bruhat.exists_perm_rep_blockTri | (intros; apply GlobalTheory.FinGL.Bruhat.exists_perm_rep_blockTri <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueOfIsAdicColimit
open CategoryTheory AlgebraicGeometry Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AdicColimit

namespace GlobalTheory.FinitePointLimit

theorem existsUnique_of_isAdicColimit {B : Type} [CommRing B] (J : Ideal B)
    (h : IsAdicColimit J (Over.mk (𝟙 (Sp B)))) (X : Scheme.{0}) (z : ∀ e : ℕ, Sp (B ⧸ J ^ (e + 1)) ⟶ X)
    (hz : ∀ e : ℕ, Out.thickTrans B J e ≫ z (e + 1) = z e) :
    ∃! x : Sp B ⟶ X, ∀ e : ℕ, Out.thick B J e ≫ x = z e := by
  have hι : ∀ e : ℕ, thickι J e (Over.mk (𝟙 (Sp B))) =
      pullback.snd (Over.mk (𝟙 (Sp B))).hom (Out.thick B J e) ≫ Out.thick B J e := by
    intro e
    have hc := pullback.condition (f := (Over.mk (𝟙 (Sp B))).hom) (g := Out.thick B J e)
    show pullback.fst _ _ = _
    simpa using hc
  have hiso : ∀ e : ℕ, IsIso (pullback.snd (Over.mk (𝟙 (Sp B))).hom (Out.thick B J e)) := by
    intro e
    have : IsIso (Over.mk (𝟙 (Sp B))).hom := by
      show IsIso (𝟙 _)
      infer_instance
    infer_instance
  have hmap : ∀ e : ℕ, Out.thickMap B J e (Over.mk (𝟙 (Sp B))) ≫
      pullback.snd (Over.mk (𝟙 (Sp B))).hom (Out.thick B J (e + 1)) =
      pullback.snd (Over.mk (𝟙 (Sp B))).hom (Out.thick B J e) ≫ Out.thickTrans B J e := by
    intro e
    rw [← cancel_mono (Out.thick B J (e + 1)), Category.assoc, Category.assoc,
      Out.thickTrans_comp, ← hι, ← hι, thickMap_ι]
  obtain ⟨g, hg, hu⟩ := h X
    (fun e => pullback.snd (Over.mk (𝟙 (Sp B))).hom (Out.thick B J e) ≫ z e) (by
      intro e
      rw [← Category.assoc, hmap, Category.assoc, hz])
  refine ⟨g, fun e => ?_, fun x hx => hu x fun e => ?_⟩
  · have he := hg e
    rw [hι, Category.assoc] at he
    have := hiso e
    exact (cancel_epi _).mp he
  · rw [hι, Category.assoc, hx]

end GlobalTheory.FinitePointLimit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamStructureToFree
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem allPrim_of_abelianDeRhamFree (h : GlobalTheory.Published.AbelianDeRhamFree) (R : Type) [CommRing R]
    (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) : AllPrim (dp0 R) (𝟙 _) A := by
  have hdim : SmoothOfRelativeDimension (g + g) (A ⊗ A).hom := by
    haveI := hg
    haveI : SmoothOfRelativeDimension g (pullback.fst A.hom A.hom) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
        (IsPullback.of_hasPullback _ _).flip hg
    exact inferInstanceAs (SmoothOfRelativeDimension (g + g) (pullback.fst A.hom A.hom ≫ A.hom))
  obtain ⟨f1, p1, r1, -⟩ := h R A g hA hg
  obtain ⟨f2, p2, r2, -⟩ := h R (A ⊗ A) (g + g)
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA) hdim
  have one0 : ∀ c, pullOver (dp0 R) (𝟙 _) (1 : A ⟶ A) c = 0 := fun c => by
    haveI : IsIso ((𝟙_ (Over (Sp R))).hom ≫ 𝟙 _) := inferInstanceAs (IsIso (𝟙 (Sp R) ≫ 𝟙 _))
    rw [Hom.one_def, ← pullOver_pullOver, firstDeRham_base_eq_zero _ (pullOver (dp0 R) (𝟙 _) η[A] c), map_zero]
  have id0 : ∀ c, pullOver (dp0 R) (𝟙 _) (𝟙 A) c = c := fun c => IsMor.pullCohomologyOne_id _ c
  let Ψ := (pullOver (dp0 R) (𝟙 _) (lift (𝟙 A) (1 : A ⟶ A))).prod
    (pullOver (dp0 R) (𝟙 _) (lift (1 : A ⟶ A) (𝟙 A)))
  have hs : Function.Surjective Ψ := fun ⟨a, b⟩ =>
    ⟨pullOver (dp0 R) (𝟙 _) (fst A A) a + pullOver (dp0 R) (𝟙 _) (snd A A) b, by
    refine Prod.ext ?_ ?_
    · change pullOver _ _ _ _ = a
      rw [map_add (f := _), pullOver_pullOver, pullOver_pullOver, lift_fst, lift_snd, one0, id0, add_zero]
    · change pullOver _ _ _ _ = b
      rw [map_add (f := _), pullOver_pullOver, pullOver_pullOver, lift_fst, lift_snd, one0, id0, zero_add]⟩
  have hb : Function.Bijective Ψ := Module.bijective_of_surjective_of_rankAtStalk_eq hs (by
    intro m hm
    rw [Module.rankAtStalk_prod, Pi.add_apply, r1, r2]; ring)
  refine eq_top_iff.2 fun c _ => (mem_prim_iff _ _ _ _).2 (hb.1 ?_)
  have e1 : lift (𝟙 A) (1 : A ⟶ A) ≫ μ[A] = 𝟙 A := by rw [← Hom.mul_def, _root_.mul_one]
  have e2 : lift (1 : A ⟶ A) (𝟙 A) ≫ μ[A] = 𝟙 A := by rw [← Hom.mul_def, _root_.one_mul]
  refine Prod.ext ?_ ?_
  · change pullOver _ _ _ _ = pullOver _ _ _ _
    rw [map_add (f := _), pullOver_pullOver, pullOver_pullOver, pullOver_pullOver, lift_fst, lift_snd, e1,
      one0, id0, add_zero]
  · change pullOver _ _ _ _ = pullOver _ _ _ _
    rw [map_add (f := _), pullOver_pullOver, pullOver_pullOver, pullOver_pullOver, lift_fst, lift_snd, e2,
      one0, id0, zero_add]

theorem abelianDeRhamFree_toFree (h : GlobalTheory.Published.AbelianDeRhamFree) :
    GlobalTheory.Published.AbelianDeRham.Free := fun R _ A _ g hA hg =>
  ⟨allPrim_of_abelianDeRhamFree h R A g hA hg, h R A g hA hg⟩

theorem abelianDeRhamStructure_toFree (h : GlobalTheory.Published.AbelianDeRhamStructure) :
    GlobalTheory.Published.AbelianDeRham.Free :=
  abelianDeRhamFree_toFree h.1

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalIdempotentCharacters
noncomputable section

namespace GlobalTheory.CuspidalIdempotentCharacters

open Formalism.L2.DIV GlobalTheory.FinGL NumberField

theorem isIndCuspChar_iff {E : Type} [Field E] [NumberField E] (Pg : Finset (Pl E)) (r : ℕ) {K : Type} [Field K]
    (s : K →+* ℂ) (χ : G0 Pg r → K) :
    GlobalTheory.IndefiniteRowSideFullHecke.GenericMultiplicityOne.IsIndCuspChar Pg r s χ ↔ GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.IsCuspIndProdChar Pg r s χ := by
  constructor
  · rintro ⟨b, V, i1, i2, i3, σ, hc, hχ⟩
    exact ⟨_, fun PP => ⟨b PP, V PP, i1 PP, i2 PP, i3 PP, σ PP, hc PP, fun _ => rfl⟩, hχ⟩
  · rintro ⟨θ, hθ, hχ⟩
    choose b V i1 i2 i3 σ hc ht using hθ
    exact ⟨b, V, i1, i2, i3, σ, hc, fun g => (hχ g).trans (Finset.prod_congr rfl fun PP _ => ht PP (g PP))⟩

theorem sum_eq_lvlSum {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ} {K : Type} [Field K]
    (P : LevelP Pg r K) (χ : G0 Pg r → K) (i : Fintype P.H) :
    ∑ h : P.H, χ (h : G0 Pg r) * (((P.chi h)⁻¹ : Kˣ) : K) = GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.lvlSum P χ := by
  obtain rfl : i = GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.fintypeH P := Subsingleton.elim _ _
  rfl

theorem genericMultOne_iff : GlobalTheory.IndefiniteRowSideFullHecke.GenericMultiplicityOne.GenericMultOne ↔ GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.OneWhittakerVector := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.GenericMultiplicityOne.GenericMultOne GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.OneWhittakerVector
  refine forall_congr' fun E => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun Pg =>
    forall_congr' fun r => forall_congr' fun K => forall_congr' fun _ => forall_congr' fun _ =>
    forall_congr' fun s => forall_congr' fun ψ => forall_congr' fun _ => forall_congr' fun χ =>
    imp_congr (isIndCuspChar_iff Pg r s χ) ?_
  rw [← sum_eq_lvlSum (P0 Pg r ψ) χ]

section Idem

variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]

theorem eps_eq_lvlIdem (H : Subgroup G) (ψ : H →* Kˣ) :
    Formalism.MainNotions.PrimeDegreeVariant.eps (⟨H, ψ⟩ : Formalism.MainNotions.PrimeDegreeVariant.Pair K G) = lvlIdem H ψ := by
  classical
  unfold Formalism.MainNotions.PrimeDegreeVariant.eps lvlIdem
  rw [Finset.smul_sum]
  symm
  refine Fintype.sum_of_injective (fun h : H => (h : G)) Subtype.val_injective _ _ ?_ ?_
  · intro x hx
    have : x ∉ H := fun h => hx ⟨⟨x, h⟩, rfl⟩
    simp [this]
  · intro h
    simp [map_inv]

variable {W : Type} [AddCommGroup W] [Module K W]

theorem asAlgebraHom_lvlIdem (τ : Representation K G W) (H : Subgroup G) (ψ : H →* Kˣ) [Fintype H] :
    τ.asAlgebraHom (lvlIdem H ψ) = (Nat.card H : K)⁻¹ • ∑ h : H, (((ψ h)⁻¹ : Kˣ) : K) • τ (h : G) := by
  unfold lvlIdem
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr (by congr!) fun h _ => ?_
  rw [Representation.asAlgebraHom_single, smul_smul, map_inv]

theorem isIdempotentElem_lvlIdem [CharZero K] (τ : Representation K G W) (H : Subgroup G) (ψ : H →* Kˣ) :
    IsIdempotentElem (τ.asAlgebraHom (lvlIdem H ψ)) := by
  classical
  have hc : (Nat.card H : K) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := H)).ne'
  set T : Module.End K W := ∑ h : H, (((ψ h)⁻¹ : Kˣ) : K) • τ (h : G) with hT
  have h1 : ∀ a : H, ((((ψ a)⁻¹ : Kˣ) : K) • τ (a : G)) * T = T := by
    intro a
    rw [hT, Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft a) _ _ fun h => ?_
    simp [smul_smul, mul_comm]
  have h2 : T * T = (Nat.card H : K) • T := by
    conv_lhs => rw [hT, Finset.sum_mul, ← hT]
    rw [Finset.sum_congr rfl fun a _ => h1 a]
    simp [Nat.card_eq_fintype_card, Nat.cast_smul_eq_nsmul]
  rw [IsIdempotentElem, asAlgebraHom_lvlIdem, ← hT, smul_mul_smul_comm, h2, smul_smul, mul_assoc,
    inv_mul_cancel₀ hc, mul_one]

theorem finrank_eq_one_iff [CharZero K] [FiniteDimensional K W] (τ : Representation K G W) (H : Subgroup G)
    (ψ : H →* Kˣ) [Fintype H] :
    Module.finrank K (LinearMap.range (τ.asAlgebraHom (lvlIdem H ψ))) = 1 ↔
      ∑ h : H, LinearMap.trace K W (τ (h : G)) * (((ψ h)⁻¹ : Kˣ) : K) = (Nat.card H : K) := by
  have hc : (Nat.card H : K) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := H)).ne'
  have h := (LinearMap.IsIdempotentElem.isProj_range _ (isIdempotentElem_lvlIdem τ H ψ)).trace
  have e : LinearMap.trace K W (τ.asAlgebraHom (lvlIdem H ψ)) =
      (Nat.card H : K)⁻¹ * ∑ h : H, LinearMap.trace K W (τ (h : G)) * (((ψ h)⁻¹ : Kˣ) : K) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [asAlgebraHom_lvlIdem, map_smul, map_sum, smul_eq_mul]
    simp [mul_comm]
  rw [← Nat.cast_eq_one (R := K), ← h, e, inv_mul_eq_one₀ hc, eq_comm]

end Idem

end GlobalTheory.CuspidalIdempotentCharacters
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockDiagActEq
open GlobalTheory.FinGL Formalism.L2.DIV Module

namespace GlobalTheory.FinGL

theorem IsCuspDatum.exists_blockDiag_act_eq (F : Type) [Field F] (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V) (hσ : IsCuspDatum b σ)
    (p : blockTri (κ := F) b) :
    ∃ m : blockTri (κ := F) b, σ m = σ p ∧ ∀ i k : Fin r, ((m : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i k =
      if b i = b k then ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i k else 0 := by
  refine ⟨Subgroup.inclusion (GlobalTheory.Parabolic.levi_le_blockTri b) (GlobalTheory.Parabolic.leviProj b p), ?_,
    fun i k => GlobalTheory.Parabolic.leviProj_apply b p i k⟩
  set m := Subgroup.inclusion (GlobalTheory.Parabolic.levi_le_blockTri b) (GlobalTheory.Parabolic.leviProj b p) with hm
  have h1 : GlobalTheory.Parabolic.leviProj b (m⁻¹ * p) = 1 := by
    rw [map_mul, map_inv, hm, GlobalTheory.Parabolic.leviProj_inclusion, inv_mul_cancel]
  have h2 : σ (m⁻¹ * p) = 1 := by
    refine hσ.infl _ fun i j hij => ?_
    have e := GlobalTheory.Parabolic.leviProj_apply b (m⁻¹ * p) i j
    rw [h1, if_pos hij] at e
    rw [← e]
    simp
  calc σ m = σ m * σ (m⁻¹ * p) := by rw [h2, mul_one]
    _ = σ p := by rw [← map_mul, mul_inv_cancel_left]

end GlobalTheory.FinGL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalAtFnEqValAt
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AnPer

theorem evalAt_fn_eq_valAt' {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Opens E) {X : Scheme.{0}}
    (x : Sp (Hol W) ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) (p : E) (hp : p ∈ W) :
    ⊤ ≤ (spMap (Hol.ev p hp).toRingHom ≫ x) ⁻¹ᵁ U ∧
      (evalAt x U h f).fn p = valAt' (spMap (Hol.ev p hp).toRingHom ≫ x) U f := by
  set φ : Hol W →+* ℂ := (Hol.ev p hp).toRingHom
  have h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U := fun q _ ↦ h (Set.mem_univ ((spMap φ) q))
  refine ⟨h', ?_⟩
  have e : (spMap φ ≫ x).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom =
      x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of (Hol W))).hom ≫ CommRingCat.ofHom φ := by
    rw [← Scheme.ΓSpecIso_naturality, ← Category.assoc,
      ← Scheme.Hom.appLE_comp_appLE (spMap φ) x U ⊤ ⊤ h le_rfl]
    congr 2
  have e2 := congrArg (fun t ↦ t.hom f) e
  rw [valAt', dite_eq_left h', valAt, ← Hol.ev_apply p hp]
  exact e2.symm

end GlobalTheory.AnPer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeIsSeparatedOfAffineBase
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeIsSeparatedOfAffineBase
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem abelianScheme_left_isSeparated_of_affine :
    ∀ {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → A.left.IsSeparated := by
  intro R _ A _ h
  haveI : IsProper A.hom := h.proper
  refine ⟨?_⟩
  rw [← terminal.comp_from A.hom]
  infer_instance

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeIsSeparatedOfAffineBaseStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_isSeparated_of_affine_base : ∀ {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → A.left.IsSeparated := by
  first | exact @GlobalTheory.abelianScheme_left_isSeparated_of_affine | exact GlobalTheory.abelianScheme_left_isSeparated_of_affine | (intros; apply GlobalTheory.abelianScheme_left_isSeparated_of_affine <;> assumption)
end
end

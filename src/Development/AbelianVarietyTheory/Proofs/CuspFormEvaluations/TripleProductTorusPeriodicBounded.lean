module

public import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.AppellHumbertDataOfIsoCube
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.JetSubstPCompJetBC
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBPrim

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.TripleProductTorusPeriodicBounded
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε zero2)
open GlobalTheory.JetSer (IsNormRos primφ primε)
open GlobalTheory.CubeValues GlobalTheory.AppellHumbertTrivial
open scoped BigOperators Real

noncomputable section

namespace GlobalTheory.FrameUnits

section Analysis

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

theorem exists_le_of_periodic {S : Set E} {R : ℝ} (hS : ∀ z, ∃ l ∈ S, ‖z + l‖ ≤ R) (φ : E → ℝ)
    (hφ : Continuous φ) (hp : ∀ l ∈ S, ∀ z, φ (z + l) = φ z) : ∃ C, ∀ z, φ z ≤ C := by
  haveI := FiniteDimensional.proper ℂ E
  obtain ⟨C, hC⟩ := ((isCompact_closedBall (0 : E) R).image hφ).bddAbove
  refine ⟨C, fun z => ?_⟩
  obtain ⟨l, hl, h⟩ := hS z
  rw [← hp l hl z]
  exact hC ⟨_, mem_closedBall_zero_iff.2 h, rfl⟩

theorem weight_nonneg_of_periodic {S : Set E} {R : ℝ} (hS : ∀ z, ∃ l ∈ S, ‖z + l‖ ≤ R)
    (r : E → ℂ) (hr : Differentiable ℂ r) (h0 : r 0 ≠ 0)
    (q : E → ℝ) (hq : Continuous q) (hs : ∀ (t : ℂ) v, q (t • v) = ‖t‖ ^ 2 * q v)
    (hp : ∀ l ∈ S, ∀ z, ‖r (z + l)‖ * Real.exp (-q (z + l)) = ‖r z‖ * Real.exp (-q z))
    (v : E) : 0 ≤ q v := by
  by_contra hneg
  rw [not_le] at hneg
  obtain ⟨C, hC⟩ := exists_le_of_periodic hS (fun z => ‖r z‖ * Real.exp (-q z))
    (hr.continuous.norm.mul (Real.continuous_exp.comp hq.neg)) hp
  have := eq_zero_of_gaussian_decay (fun t => r (t • v))
    (hr.comp (differentiable_id.smul_const v)) C (q v) hneg fun t => by
      have h1 := hC (t • v)
      simp only [hs, Real.exp_neg] at h1
      rwa [← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)] at h1
  simp at this
  exact h0 this

theorem form_eq_zero_and_const {S : Set E} {R : ℝ} (hS : ∀ z, ∃ l ∈ S, ‖z + l‖ ≤ R)
    (ψ : E → ℂ) (hψ : Differentiable ℂ ψ) (h0 : ∀ z, ψ z ≠ 0)
    (D : E → E → ℂ) (hc : Continuous fun z => D z z)
    (hadd : ∀ z z' w, D (z + z') w = D z w + D z' w)
    (hsm : ∀ (t : ℂ) z w, D (t • z) w = t * D z w)
    (hst : ∀ z w, D w z = star (D z w))
    (hper : ∀ l ∈ S, ∃ ρ : ℂ, ‖ρ‖ = 1 ∧ ∀ z, ψ (z + l) = ρ * cexp (π * D z l + π / 2 * D l l) * ψ z) :
    (∀ z w, D z w = 0) ∧ ∀ z, ψ z = ψ 0 := by
  have hre : ∀ z w, (D w z).re = (D z w).re := fun z w => by rw [hst z w]; simp
  have hsq : ∀ z l, (D (z + l) (z + l)).re = (D z z).re + 2 * (D z l).re + (D l l).re := by
    intro z l
    rw [hadd, Complex.add_re, hre (z + l) z, hre (z + l) l, hadd, hadd, Complex.add_re,
      Complex.add_re, hre z l]
    ring
  let q : E → ℝ := fun z => π / 2 * (D z z).re
  have hq : Continuous q := continuous_const.mul (Complex.continuous_re.comp hc)
  have hs : ∀ (t : ℂ) w, q (t • w) = ‖t‖ ^ 2 * q w := fun t w => by
    have : D (t • w) (t • w) = ((‖t‖ ^ 2 : ℝ) : ℂ) * D w w := by
      rw [hsm, hst (t • w) w, hsm, star_mul', ← hst w w, ← _root_.mul_assoc, Complex.star_def,
        Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [q]
    rw [this, Complex.re_ofReal_mul]
    ring
  have hn : ∀ l ∈ S, ∀ z, ‖ψ (z + l)‖ = Real.exp (q (z + l) - q z) * ‖ψ z‖ := fun l hl z => by
    obtain ⟨ρ, hρ, h⟩ := hper l hl
    rw [h, norm_mul, norm_mul, hρ, _root_.one_mul, Complex.norm_exp]
    congr 2
    simp only [q, hsq]
    have e : (π : ℂ) / 2 = ((π / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    ring
  have h1 := weight_nonneg_of_periodic hS ψ hψ (h0 0) q hq hs (fun l hl z => by
    rw [hn l hl z, mul_right_comm, ← Real.exp_add, mul_comm]
    congr 2
    ring)
  have h2 := weight_nonneg_of_periodic hS (fun z => (ψ z)⁻¹) (hψ.inv h0) (inv_ne_zero (h0 0))
    (fun z => -q z) hq.neg (fun t w => by rw [hs]; ring) (fun l hl z => by
    rw [norm_inv, norm_inv, hn l hl z, mul_inv, mul_right_comm, ← Real.exp_neg, ← Real.exp_add,
      mul_comm]
    congr 2
    ring)
  have h3 : ∀ z, (D z z).re = 0 := fun z => by
    have : q z = 0 := le_antisymm (by linarith [h2 z]) (h1 z)
    simpa [q, Real.pi_ne_zero] using this
  have h4 : ∀ z w, (D z w).re = 0 := fun z w => by
    have := hsq z w
    rw [h3, h3, h3] at this
    linarith
  refine ⟨fun z w => ?_, fun z => ?_⟩
  · refine Complex.ext (h4 z w) ?_
    have := h4 (I • z) w
    rw [hsm] at this
    simpa using this
  · obtain ⟨C, hC⟩ := exists_le_of_periodic hS (fun z => ‖ψ z‖) hψ.continuous.norm
      (fun l hl z => by simp [hn l hl z, q, h3])
    refine hψ.apply_eq_apply_of_bounded (isBounded_iff_forall_norm_le.2 ⟨C, ?_⟩) z 0
    rintro _ ⟨z, rfl⟩
    exact hC z

omit [FiniteDimensional ℂ E] in
theorem differentiableOn_fun_prod {α : Type*} {f : α → E → ℂ} {S : Set E}
    (s : Finset α) (hf : ∀ i, DifferentiableOn ℂ (f i) S) :
    DifferentiableOn ℂ (fun z => ∏ i ∈ s, f i z) S := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (hf a).mul ih

end Analysis

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem exists_period_norm_le : ∃ R : ℝ, ∀ z : Fin g → ℂ, ∃ l ∈ u.Λ, ‖z + l‖ ≤ R := by
  haveI := u.discrete
  haveI : IsZLattice ℝ u.Λ := ⟨u.full⟩
  let b := (Module.Free.chooseBasis ℤ u.Λ).ofZLatticeBasis ℝ u.Λ
  refine ⟨∑ i, ‖b i‖, fun z => ⟨-(ZSpan.floor b z : Fin g → ℂ), u.Λ.neg_mem ?_, ?_⟩⟩
  · exact ((Module.Free.chooseBasis ℤ u.Λ).ofZLatticeBasis_span ℝ u.Λ).le (ZSpan.floor b z).2
  · rw [← sub_eq_add_neg, ← ZSpan.fract_apply]
    exact ZSpan.norm_fract_le b z

theorem gen_linComb_in_frame (hL : L.IsLB) {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (hu : u.IsAH Hm χ)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {Y : Scheme.{0}} (p : E → (Sp ℂ ⟶ Y))
    (hp : ∀ (U : Y.Opens) (f : Γ(Y, U)), IsOpen {z | ⊤ ≤ p z ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun z => valAt' (p z) U f) {z | ⊤ ≤ p z ⁻¹ᵁ U})
    (hS : ∃ R : ℝ, ∀ z : E, ∃ l, (∀ w, p (w + l) = p w) ∧ ‖z + l‖ ≤ R)
    {K : Type} [Fintype K] (φ : K → (Y ⟶ A.left)) (ε : K → ℤ) (lam : K → E →ₗ[ℂ] (Fin g → ℂ))
    (hlam : ∀ k z, p z ≫ φ k = (u.ex (lam k z)).left)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    (∀ z w, ∑ k, (ε k : ℂ) * hermForm Hm (lam k z) (lam k w) = 0) ∧
      ∃ κ : ℂ, κ ≠ 0 ∧ ∀ (j : K → L.ι) (z : E), (∀ k, ⊤ ≤ (u.ex (lam k z)).left ⁻¹ᵁ L.U (j k)) →
        valAt' (p z) (L.wchart φ j) (t.s j).val = κ * ∏ k, u.fr (j k) (lam k z) ^ ε k := by
  have hv : ValueRules := valAt'_rules
  obtain ⟨R, hS⟩ := hS
  have hld : ∀ k, Differentiable ℂ (lam k) := fun k =>
    (LinearMap.toContinuousLinearMap (lam k)).differentiable
  let D : (K → L.ι) → Set E := fun j => {z | ⊤ ≤ p z ⁻¹ᵁ L.wchart φ j}
  have hD : ∀ j z, z ∈ D j ↔ ∀ k, ⊤ ≤ (u.ex (lam k z)).left ⁻¹ᵁ L.U (j k) := fun j z => by
    refine (le_preimage_wchart (p z) L φ j).trans ?_
    simp only [hlam]
  have hcov : ∀ z, ∃ j, z ∈ D j := fun z => by
    choose c hc using SelfCube.exists_chart hv hL u
    exact ⟨fun k => c (lam k z), (hD _ _).2 fun k => hc _⟩
  let T : (K → L.ι) → E → ℂ := fun j z => valAt' (p z) (L.wchart φ j) (t.s j).val
  let F : (K → L.ι) → E → ℂ := fun j z => ∏ k, u.fr (j k) (lam k z) ^ ε k
  have hF0 : ∀ j z, z ∈ D j → F j z ≠ 0 := fun j z hz =>
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (u.fr_ne _ _ ((hD j z).1 hz k))
  obtain ⟨ψ, hψ, hG⟩ := PullHermitian.exists_glue D (fun j => (hp _ 0).1) hcov
    (fun j z => T j z * (F j z)⁻¹)
    (fun j => by
      have dF : DifferentiableOn ℂ (fun z => ∏ k, u.fr (j k) (lam k z) ^ ε k) (D j) :=
        differentiableOn_fun_prod _ fun k => DifferentiableOn.zpow
          ((u.fr_hol (j k)).comp (hld k).differentiableOn fun z hz => (hD j z).1 hz k)
          (Or.inl fun z hz => u.fr_ne _ _ ((hD j z).1 hz k))
      exact (hp _ (t.s j).val).2.mul (dF.inv (hF0 j)))
    (fun j j' z hz hz' => by
      have e1 : T j z = _ * T j' z := val_gen (p z) hv t ht j j' hz hz'
      have e2 := val_linComb (p z) hv L φ ε j j' hz hz'
      simp only [hlam] at e2
      have e3 : T j z = (∏ k, valAt' (u.ex (lam k z)).left (L.U (j k) ⊓ L.U (j' k))
          (L.g (j k) (j' k)).val ^ ε k) * T j' z := e1.trans (congrArg (· * T j' z) e2)
      have c1 : F j z = (∏ k, valAt' (u.ex (lam k z)).left (L.U (j k) ⊓ L.U (j' k))
          (L.g (j k) (j' k)).val ^ ε k) * F j' z := by
        simp only [F]
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [u.fr_compat _ _ _ ((le_preimage_inf _ _ _).2 ⟨(hD j z).1 hz k, (hD j' z).1 hz' k⟩), mul_zpow]
      rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff (hF0 _ _ hz) (hF0 _ _ hz'), e3, c1]
      ring)
  have hψ0 : ∀ z, ψ z ≠ 0 := fun z => by
    obtain ⟨j, hj⟩ := hcov z
    rw [hG j z hj]
    exact mul_ne_zero (val_unit_ne_zero _ hv hj _) (inv_ne_zero (hF0 j z hj))
  obtain ⟨h1, h2⟩ := form_eq_zero_and_const (S := {l | ∀ w, p (w + l) = p w}) hS ψ hψ hψ0
    (fun z w => ∑ k, (ε k : ℂ) * hermForm Hm (lam k z) (lam k w))
    (continuous_finsetSum _ fun k _ => continuous_const.mul
      ((continuous_hermForm_self Hm).comp (hld k).continuous))
    (fun z z' w => by simp only [map_add (f := _), hermForm_add_left, mul_add, Finset.sum_add_distrib])
    (fun c z w => by
      simp only [map_smul, hermForm_smul_left, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring)
    (fun z w => by
      simp only [star_sum, star_mul', star_intCast]
      exact Finset.sum_congr rfl fun k _ => by rw [hermForm_swap hu.1])
    (fun l hl => by
      have hΛ : ∀ k, lam k l ∈ u.Λ := fun k => by
        rw [← u.ker, ← ex_zero u]
        apply Over.OverMorphism.ext
        rw [← hlam, ← map_zero (lam k), ← hlam, ← hl 0, zero_add]
      refine ⟨∏ k, χ ⟨lam k l, hΛ k⟩ ^ ε k, by simp [norm_prod, norm_zpow, hu.2.2.1], fun z => ?_⟩
      obtain ⟨j, hj⟩ := hcov z
      have hj' : z + l ∈ D j := by
        simp only [D, Set.mem_setOf_eq, hl z]
        exact hj
      have eT : T j (z + l) = T j z := by simp only [T, hl z]
      have c1 : F j z = (∏ k, χ ⟨lam k l, hΛ k⟩ ^ ε k) *
          cexp (π * ∑ k, (ε k : ℂ) * hermForm Hm (lam k z) (lam k l) +
            π / 2 * ∑ k, (ε k : ℂ) * hermForm Hm (lam k l) (lam k l)) * F j (z + l) := by
        simp only [F]
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Complex.exp_sum,
          ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [hu.2.2.2 ⟨lam k l, hΛ k⟩ (j k) (lam k z) ((hD j z).1 hj k), map_add (f := _), mul_zpow, mul_zpow,
          ← Complex.exp_int_mul]
        congr 3
        simp only [hermForm]
        ring
      rw [hG j z hj, hG j _ hj', eT]
      have n1 := hF0 j z hj
      have n2 := hF0 j _ hj'
      have key : ∀ a b c d : ℂ, b ≠ 0 → c ≠ 0 → b = a * c → d * c⁻¹ = a * (d * b⁻¹) := by
        rintro a _ c d h1 h2 rfl
        have := left_ne_zero_of_mul h1
        field_simp
      exact key _ _ _ _ n1 n2 c1)
  refine ⟨h1, ψ 0, hψ0 0, fun j z hz => ?_⟩
  have hz' := (hD j z).2 hz
  rw [← h2 z, hG j z hz', inv_mul_cancel_right₀ (hF0 j z hz')]

theorem val_eq_one_of_corr {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (h : Z ⟶ Y)
    (hc : LB.Gen.Corr L _ _ _ _ (LB.pullGen L φ ε t h) (LB.oneGen L)) (x : Sp ℂ ⟶ Z) (j : L.ι)
    (hx : ∀ k, ⊤ ≤ ((x ≫ h) ≫ φ k) ⁻¹ᵁ L.U j) :
    valAt' (x ≫ h) (L.wchart φ fun _ => j) (t.s fun _ => j).val = 1 := by
  have hv : ValueRules := valAt'_rules
  have e := hc (fun _ => j) PEmpty.elim (fun _ _ _ => rfl) (fun k => k.elim) (fun _ k => k.elim)
  have h1 : ⊤ ≤ x ⁻¹ᵁ L.wchart (fun k => h ≫ φ k) (fun _ => j) :=
    (le_preimage_wchart x L _ _).2 fun k => by simpa only [Category.assoc] using hx k
  have h2 : ⊤ ≤ x ⁻¹ᵁ L.wchart (Y := Z) (K := PEmpty) PEmpty.elim PEmpty.elim :=
    (le_preimage_wchart x L _ _).2 fun k => k.elim
  have h3 := (le_preimage_inf x _ _).2 ⟨h1, h2⟩
  have e' := (val_res x hv inf_le_left h3 _).symm.trans
    ((congrArg (fun f : Γ(Z, _)ˣ => valAt' x _ f.val) e).trans (val_res x hv inf_le_right h3 _))
  refine ((val_res x hv _ h1 _).trans (val_pullU x hv h _ _)).symm.trans (e'.trans ?_)
  exact valAt'_one x h2

theorem prod_zpow_eq_zpow_sum {K : Type} (s : Finset K) {a : ℂ} (ha : a ≠ 0) (ε : K → ℤ) :
    ∏ k ∈ s, a ^ ε k = a ^ ∑ k ∈ s, ε k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert b s hb ih => rw [Finset.prod_insert hb, Finset.sum_insert hb, zpow_add₀ ha, ih]

end GlobalTheory.FrameUnits
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RawChartBaseChangeRigGerm
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RawChartBaseChangeRigGerm
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RawChartGermBC

section Alg

variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S')

theorem map_psTrunc {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (f : MvPowerSeries κ S) :
    MvPolynomial.map ψ (psTrunc m f) = psTrunc m (MvPowerSeries.map ψ f) := by
  unfold psTrunc
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [MvPolynomial.map_monomial, MvPowerSeries.coeff_map]

theorem map_psIn (d : ℕ) {n n' : ℕ} (m : ℕ) (r : Fin n → Fin n') (f : MvPowerSeries (Fin n × Fin d) S) :
    MvPolynomial.map ψ (psIn d m r f) = psIn d m r (MvPowerSeries.map ψ f) := by
  unfold psIn
  rw [MvPolynomial.map_rename, map_psTrunc]

theorem spMap_comp_eq {A B C D : Type} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (f : A →+* B) (g : B →+* D) (f' : A →+* C) (g' : C →+* D) (h : g.comp f = g'.comp f') :
    (spMap g ≫ spMap f : Sp D ⟶ Sp A) = spMap g' ≫ spMap f' := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

theorem appTop_toΓ_spMap (a : S) : (spMap ψ).appTop.hom (toΓ S a) = toΓ S' (ψ a) := by
  unfold toΓ
  have h2 := congrArg (fun g => CommRingCat.Hom.hom g a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ψ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  exact h2.symm

end Alg

section Pull

variable {S0 : Scheme.{0}} (A : Over S0) [GrpObj A] (L : LB A.left)

set_option maxHeartbeats 1000000 in
theorem isPullSec_whisker_comp (a : ℤ) {T1 T2 T3 : Over S0} (h1 : T2 ⟶ T1) (h2 : T3 ⟶ T2)
    {s1 : LB.Sec (LPow A L a T1)} {s2 : LB.Sec (LPow A L a T2)} {s3 : LB.Sec (LPow A L a T3)}
    (e1 : IsPullSec A L a (h1 ▷ A) (whiskerRight_snd _ _) s1 s2)
    (e2 : IsPullSec A L a (h2 ▷ A) (whiskerRight_snd _ _) s2 s3) :
    IsPullSec A L a ((h2 ≫ h1) ▷ A) (whiskerRight_snd _ _) s1 s3 :=
  (LBPull.isPullSec_congr A L a (MonoidalCategory.comp_whiskerRight h2 h1 A) _ _ s1 s3).2
    (LBPull.isPullSec_comp A L a e1 e2)

end Pull

section Geo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ Xo.X) (d : ℕ)

theorem subst_rjBC (m n n' : ℕ) (φ : Fin n × Fin d → MvPolynomial (Fin n' × Fin d) S)
    (φ' : Fin n × Fin d → MvPolynomial (Fin n' × Fin d) S') (h : ∀ p, φ' p = MvPolynomial.map ψ (φ p)) :
    (Formalism.L2.Pj.homAt (spMap ψ ≫ x0) (jetSubstP m φ')).left ≫ (rjBC ψ x0 d m n).left =
      (rjBC ψ x0 d m n').left ≫ (Formalism.L2.Pj.homAt x0 (jetSubstP m φ)).left := by
  have hφ : φ' = fun p => MvPolynomial.map ψ (φ p) := funext h
  subst hφ
  unfold rjBC Formalism.L2.Pj.homAt
  simp only [Over.homMk_left]
  exact spMap_comp_eq _ _ _ _ (PullbackSections.jetSubstP_comp_jetBC ψ m φ)

theorem aug_rjBC (m n : ℕ) :
    (Formalism.L2.Pj.homAt (spMap ψ ≫ x0) (jetAug : Jet S' (Fin n × Fin d) m →ₐ[S'] S')).left ≫ (rjBC ψ x0 d m n).left =
      spMap ψ ≫ (Formalism.L2.Pj.homAt x0 (jetAug : Jet S (Fin n × Fin d) m →ₐ[S] S)).left := by
  unfold rjBC Formalism.L2.Pj.homAt
  simp only [Over.homMk_left]
  exact spMap_comp_eq _ _ _ _ (PullbackSections.jetAug_comp_jetBC ψ (Fin n × Fin d) m)

theorem base_rjBC (m n : ℕ) :
    rjBase (spMap ψ ≫ x0) d m n ≫ ptBC ψ x0 = rjBC ψ x0 d m n ≫ rjBase x0 d m n := by
  apply Over.OverMorphism.ext
  unfold rjBC ptBC rjBase
  simp only [Over.comp_left, Over.homMk_left]
  refine spMap_comp_eq _ _ _ _ (RingHom.ext fun a => ?_)
  simp only [RingHom.comp_apply]
  rw [show algebraMap S (Jet S (Fin n × Fin d) m) a = Ideal.Quotient.mk _ (MvPolynomial.C a) from rfl,
    PullbackSections.jetBC_mk, MvPolynomial.map_C]
  rfl

theorem overAt_hom_bc :
    (overAt (spMap ψ ≫ x0) S').hom = spMap ψ ≫ (overAt x0 S).hom := by
  unfold overAt
  simp [spMap]

theorem val_genPow {Y Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ Xo.univ.t.G.left)) (ε : K → ℤ)
    (g : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε)) (k : ℕ) (r : Z ⟶ Y) (z : Z) (J) :
    val (genPow φ ε g k) r z J = val g r z J ^ k := by
  unfold genPow val
  exact map_pow _ _ _

theorem val_reL_bc (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S)
    (x : ∀ m, rjO x0 d m 1 ⟶ Xo.univ.t.G) (x' : ∀ m, rjO (spMap ψ ≫ x0) d m 1 ⟶ Xo.univ.t.G)
    (hx : ∀ m, x' m = rjBC ψ x0 d m 1 ≫ x m)
    (e : ∀ m, RFrTy x0 d x m) (e' : ∀ m, RFrTy (spMap ψ ≫ x0) d x' m)
    (he : ∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e' m) (LB.pullGen Xo.univ.t.PP.L
      (cφ ![rjpt x0 d x m (0 : Fin 2), rjpt x0 d x m (1 : Fin 2)]) (cε 2) (e m) (rjBC ψ x0 d m 2).left))
    (wP : PrimTy H Xo) (m : ℕ) {Z : Scheme.{0}} (r : Z ⟶ (rjO (spMap ψ ≫ x0) d m 1).left) (z : Z) {J}
    (hJ : Good Xo.univ.t.PP.L z J) :
    val (reL (spMap ψ ≫ x0) d x' (fun a i => MvPowerSeries.map ψ (act a i)) e' wP m) r z J =
      val (reL x0 d x act e wP m) (r ≫ (rjBC ψ x0 d m 1).left) z J := by
  have hφ : ∀ p : Fin 2 × Fin d,
      (![fun j => MvPolynomial.X ((0 : Fin 1), j), fun j => psIn d m ![0] (MvPowerSeries.map ψ (act H.w0 j))] :
        Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) S') p.1 p.2 =
      MvPolynomial.map ψ ((![fun j => MvPolynomial.X ((0 : Fin 1), j), fun j => psIn d m ![0] (act H.w0 j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) S) p.1 p.2) := by
    rintro ⟨i, j⟩
    fin_cases i <;> simp [map_psIn]
  have hxl : (x' m).left = (rjBC ψ x0 d m 1).left ≫ (x m).left := by
    rw [hx m]
    rfl
  unfold reL rpe
  simp only [val_mul hJ, val_pull hJ]
  congr 1
  · rw [hxl, Category.assoc]
  · refine (val_pull hJ _ _ r).trans ?_
    refine (val_corr hJ (he m) _).trans ?_
    refine (val_pull hJ _ _ _).trans ?_
    refine Eq.trans ?_ (val_pull hJ _ _ _).symm
    simp only [Category.assoc]
    rw [subst_rjBC ψ x0 d m 2 1 _ _ hφ]

end Geo

end GlobalTheory.RawChartGermBC

namespace GlobalTheory


open RawChartGermBC in
theorem rawChart_baseChange_rig_germ :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S S' : Type) [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ Xo.X) (d : ℕ) (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (x : ∀ m, rjO x0 d m 1 ⟶ Xo.univ.t.G) (x' : ∀ m, rjO (spMap ψ ≫ x0) d m 1 ⟶ Xo.univ.t.G), (∀ m, x' m = rjBC ψ x0 d m 1 ≫ x m) → ∀ (e : ∀ m, RFrTy x0 d x m) (e' : ∀ m, RFrTy (spMap ψ ≫ x0) d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e' m) (LB.pullGen Xo.univ.t.PP.L (cφ ![rjpt x0 d x m (0 : Fin 2), rjpt x0 d x m (1 : Fin 2)]) (cε 2) (e m) (rjBC ψ x0 d m 2).left)) → ∀ (wP : PrimTy H Xo), wP.IsGen → (LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ (reL x0 d x act e wP 0) (homAt x0 (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S)).left) (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt x0 S) 1) → LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ (reL (spMap ψ ≫ x0) d x' (fun a i => MvPowerSeries.map ψ (act a i)) e' wP 0) (homAt (spMap ψ ≫ x0) (jetAug : Jet S' (Fin 1 × Fin d) 0 →ₐ[S'] S')).left) (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt (spMap ψ ≫ x0) S') 1)) ∧ ∀ (k : ℕ) (Fs : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo x0))) (Fs' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo (spMap ψ ≫ x0)))) (f : MvPowerSeries (Fin 1 × Fin d) S), IsPullSec Xo.univ.t.G Xo.univ.t.PP.L k (ptBC ψ x0 ▷ Xo.univ.t.G) (whiskerRight_snd _ _) Fs Fs' → RIsGerm x0 d x act e wP k Fs f → RIsGerm (spMap ψ ≫ x0) d x' (fun a i => MvPowerSeries.map ψ (act a i)) e' wP k Fs' (MvPowerSeries.map ψ f) := by
  intro E _ _ _ H Dw l Xo S S' _ _ ψ x0 d _ act x x' hx e e' hge hge' he wP hwP
  obtain rfl : x' = fun m => rjBC ψ x0 d m 1 ≫ x m := funext hx
  refine ⟨fun hrig => ?_, fun k Fs Fs' f hpull hgerm => ?_⟩
  · refine corr_of_val Xo.univ.t.PP.isLB (fun y J hJ => ?_)
    refine (val_pull hJ _ _ _).trans ?_
    refine (val_reL_bc ψ x0 d act x _ (fun _ => rfl) e e' he wP 0 _ y hJ).trans ?_
    rw [Category.assoc, aug_rjBC ψ x0 d 0 1, ← Category.assoc]
    refine (val_pull hJ _ _ _).symm.trans ?_
    refine (val_corr hJ hrig _).trans ?_
    rw [GermB.val_rigT _ _ _ _ _ _ _ hJ, GermB.val_rigT _ _ _ _ _ _ _ hJ, overAt_hom_bc ψ x0]
    simp only [Category.id_comp]
  · intro m
    obtain ⟨F0, τ0, hF0, hτ0, hv0⟩ := hgerm m
    obtain ⟨F1, hF1⟩ := GermD.exists_pullSec Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ)
      (rjBase (spMap ψ ≫ x0) d m 1 ▷ Xo.univ.t.G) (whiskerRight_snd _ _) Fs'
    obtain ⟨F2, hF2⟩ := GermD.exists_pullSec Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ)
      (rjBC ψ x0 d m 1 ▷ Xo.univ.t.G) (whiskerRight_snd _ _) F0
    have hA := isPullSec_whisker_comp _ _ (k : ℤ) (rjBase x0 d m 1) (rjBC ψ x0 d m 1) hF0 hF2
    have hB := isPullSec_whisker_comp _ _ (k : ℤ) (ptBC ψ x0) (rjBase (spMap ψ ≫ x0) d m 1) hpull hF1
    have hB' := (LBPull.isPullSec_congr Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ)
      (congrArg (· ▷ Xo.univ.t.G) (base_rjBC ψ x0 d m 1)) _ (whiskerRight_snd _ _) Fs F1).1 hB
    have h12 : F1 = F2 := LBPull.isPullSec_unique _ _ _ hB' hA
    subst h12
    have hv := LBPull.isValueAt_pull Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (rjBC ψ x0 d m 1) (x m) hF2 hv0
    have hvb : (rjBC ψ x0 d m 1).left.appTop.hom (toΓ _ (psJet m f)) =
        toΓ _ (psJet m (MvPowerSeries.map ψ f)) := by
      rw [← PullbackSections.jetBC_psJet]
      exact appTop_toΓ_spMap (jetBC ψ (Fin 1 × Fin d) m) (psJet m f)
    rw [hvb] at hv
    refine ⟨F1, LB.pullGen Xo.univ.t.PP.L _ _ τ0 (rjBC ψ x0 d m 1).left, hF1, ?_, hv⟩
    refine corr_of_val Xo.univ.t.PP.isLB (fun y J hJ => ?_)
    refine (val_pull hJ _ _ _).trans ?_
    refine (val_corr hJ hτ0 _).trans ?_
    rw [val_genPow, val_genPow, val_reL_bc ψ x0 d act x _ (fun _ => rfl) e e' he wP m _ y hJ]

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RawChartBaseChangeRigGermStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rawChart_baseChange_rig_germ_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S S' : Type) [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ Xo.X) (d : ℕ) (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (x : ∀ m, rjO x0 d m 1 ⟶ Xo.univ.t.G) (x' : ∀ m, rjO (spMap ψ ≫ x0) d m 1 ⟶ Xo.univ.t.G), (∀ m, x' m = rjBC ψ x0 d m 1 ≫ x m) → ∀ (e : ∀ m, RFrTy x0 d x m) (e' : ∀ m, RFrTy (spMap ψ ≫ x0) d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e' m) (LB.pullGen Xo.univ.t.PP.L (cφ ![rjpt x0 d x m (0 : Fin 2), rjpt x0 d x m (1 : Fin 2)]) (cε 2) (e m) (rjBC ψ x0 d m 2).left)) → ∀ (wP : PrimTy H Xo), wP.IsGen → (LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ (reL x0 d x act e wP 0) (homAt x0 (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S)).left) (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt x0 S) 1) → LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ (reL (spMap ψ ≫ x0) d x' (fun a i => MvPowerSeries.map ψ (act a i)) e' wP 0) (homAt (spMap ψ ≫ x0) (jetAug : Jet S' (Fin 1 × Fin d) 0 →ₐ[S'] S')).left) (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt (spMap ψ ≫ x0) S') 1)) ∧ ∀ (k : ℕ) (Fs : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo x0))) (Fs' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo (spMap ψ ≫ x0)))) (f : MvPowerSeries (Fin 1 × Fin d) S), IsPullSec Xo.univ.t.G Xo.univ.t.PP.L k (ptBC ψ x0 ▷ Xo.univ.t.G) (whiskerRight_snd _ _) Fs Fs' → RIsGerm x0 d x act e wP k Fs f → RIsGerm (spMap ψ ≫ x0) d x' (fun a i => MvPowerSeries.map ψ (act a i)) e' wP k Fs' (MvPowerSeries.map ψ f) := by
  first | exact @GlobalTheory.rawChart_baseChange_rig_germ | exact GlobalTheory.rawChart_baseChange_rig_germ | (intros; apply GlobalTheory.rawChart_baseChange_rig_germ <;> assumption)
end
end

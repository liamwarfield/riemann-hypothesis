module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.WickOperatorVanishing
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesInChartRingHomLaws

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffDmonOfSubMem
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.EigenCongruence

variable {R : Type} [CommRing R] {d : ℕ}

def coeffIdeal {σ : Type} (I : Ideal R) : Ideal (MvPowerSeries σ R) where
  carrier := {g | ∀ mo, coeff mo g ∈ I}
  add_mem' := by
    intro a b ha hb mo
    rw [map_add (f := _)]
    exact I.add_mem (ha mo) (hb mo)
  zero_mem' := by
    intro mo
    rw [map_zero]
    exact I.zero_mem
  smul_mem' := by
    classical
    intro c x hx mo
    rw [smul_eq_mul, coeff_mul]
    exact I.sum_mem fun p _ => I.mul_mem_left _ (hx p.2)

theorem pderiv_mem_coeffIdeal {σ : Type} {I : Ideal R} {g : MvPowerSeries σ R}
    (hg : g ∈ coeffIdeal I) (s : σ) : pderiv s g ∈ coeffIdeal I := by
  intro mo
  rw [coeff_pderiv]
  exact I.mul_mem_right _ (hg _)

theorem dof_mem_coeffIdeal (F : Fin d → PS R 2 d) (v : Fin d → R) {I : Ideal R} {g : PS R 1 d}
    (hg : g ∈ coeffIdeal I) : Dof F v g ∈ coeffIdeal I :=
  Ideal.sum_mem _ fun _ _ => Ideal.mul_mem_left _ _ (pderiv_mem_coeffIdeal hg _)

theorem dof_step (F : Fin d → PS R 2 d) (v : Fin d → R) (y c : R) {I : Ideal R} {f g : PS R 1 d}
    (hf : Dof F v f - C y * f ∈ coeffIdeal I) (hg : g - C c * f ∈ coeffIdeal I) :
    Dof F v g - C (y * c) * f ∈ coeffIdeal I := by
  have h1 : Dof F v g = Dof F v (g - C c * f) + C c * Dof F v f := by
    rw [← GE.dof_C_mul, ← GE.dof_add, sub_add_cancel]
  have h2 : Dof F v g - C (y * c) * f =
      Dof F v (g - C c * f) + C c * (Dof F v f - C y * f) := by
    rw [h1, map_mul]; ring
  rw [h2]
  exact Ideal.add_mem _ (dof_mem_coeffIdeal F v hg) (Ideal.mul_mem_left _ _ hf)

theorem dof_iterate (F : Fin d → PS R 2 d) (v : Fin d → R) (y c : R) {I : Ideal R}
    {f g : PS R 1 d} (hf : Dof F v f - C y * f ∈ coeffIdeal I) (hg : g - C c * f ∈ coeffIdeal I)
    (n : ℕ) : (Dof F v)^[n] g - C (y ^ n * c) * f ∈ coeffIdeal I := by
  induction n with
  | zero => simpa using hg
  | succ n ih =>
    rw [Function.iterate_succ_apply', pow_succ', mul_assoc]
    exact dof_step F v y _ hf ih

theorem foldr_sub_mem (F : Fin d → PS R 2 d) {I : Ideal R} {ι : Type} (u : ι → Fin d → R)
    (y : ι → R) (f : PS R 1 d) (hf : ∀ l, Dof F (u l) f - C (y l) * f ∈ coeffIdeal I)
    (m : ι → ℕ) (L : List ι) :
    L.foldr (fun l g => (Dof F (u l))^[m l] g) f - C (L.map fun l => y l ^ m l).prod * f ∈
      coeffIdeal I := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.foldr_cons, List.map_cons, List.prod_cons]
    exact dof_iterate F (u a) (y a) _ (hf a) ih (m a)

theorem dmonOf_sub_mem (F : Fin d → PS R 2 d) {I : Ideal R} {ι : Type} [Fintype ι]
    (u : ι → Fin d → R) (y : ι → R) (f : PS R 1 d)
    (hf : ∀ l, Dof F (u l) f - C (y l) * f ∈ coeffIdeal I) (m : ι →₀ ℕ) :
    DmonOf F u m f - C (∏ l, y l ^ m l) * f ∈ coeffIdeal I := by
  have h := foldr_sub_mem F u y f hf m (Finset.univ : Finset ι).toList
  rwa [Finset.prod_map_toList] at h

end GlobalTheory.EigenCongruence

namespace GlobalTheory

theorem constantCoeff_dmonOf_sub_mem :
    ∀ (R : Type) [CommRing R] (d : ℕ) (F : Fin d → PS R 2 d) (I : Ideal R) (ι : Type) [Fintype ι]
      (u : ι → Fin d → R) (y : ι → R) (f : PS R 1 d),
      (∀ l mo, coeff mo (Dof F (u l) f - C (y l) * f) ∈ I) →
      ∀ m : ι →₀ ℕ, constantCoeff (DmonOf F u m f) - (∏ l, y l ^ m l) * constantCoeff f ∈ I := by
  intro R _ d F I ι _ u y f hf m
  have h := EigenCongruence.dmonOf_sub_mem F u y f hf m 0
  rwa [coeff_zero_eq_constantCoeff, map_sub, map_mul, constantCoeff_C] at h

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CoeffProdLeadingMinors
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.LeadingMinors

theorem _root_.GlobalTheory.LeadingMinors.isHomogeneous_det_X {k σ ι : Type*} [CommRing k] [Fintype ι]
    [DecidableEq ι] (v : ι → ι → σ) :
    (Matrix.of fun a i : ι => (MvPolynomial.X (v a i) : MvPolynomial σ k)).det.IsHomogeneous
      (Fintype.card ι) := by
  rw [← MvPolynomial.mem_homogeneousSubmodule, Matrix.det_apply]
  refine Submodule.sum_mem _ fun e _ => ?_
  rw [Units.smul_def]
  refine zsmul_mem ?_ _
  rw [MvPolynomial.mem_homogeneousSubmodule]
  have h := MvPolynomial.IsHomogeneous.prod Finset.univ
    (fun i => (Matrix.of fun a i : ι => (MvPolynomial.X (v a i) : MvPolynomial σ k)) (e i) i)
    (fun _ => 1) fun i _ => MvPolynomial.isHomogeneous_X k _
  simpa using h

theorem _root_.GlobalTheory.LeadingMinors.det_X_mem_supported {k σ ι : Type*} [CommRing k] [Fintype ι]
    [DecidableEq ι] (v : ι → ι → σ) (S : Set σ) (hS : ∀ a i, v a i ∈ S) :
    (Matrix.of fun a i : ι => (MvPolynomial.X (v a i) : MvPolynomial σ k)).det ∈
      MvPolynomial.supported k S := by
  rw [Matrix.det_apply]
  refine Subalgebra.sum_mem _ fun e _ => ?_
  rw [Units.smul_def]
  refine zsmul_mem (Subalgebra.prod_mem _ fun i _ => ?_) _
  exact Algebra.subset_adjoin (Set.mem_image_of_mem MvPolynomial.X (hS (e i) i))

theorem _root_.GlobalTheory.LeadingMinors.killCompl_det_X {k σ ρ ι : Type*} [CommRing k] [Fintype ι]
    [DecidableEq ι] {f : ρ → σ} (hf : Function.Injective f) (v : ι → ι → σ) (u : ι → ρ)
    (hd : ∀ a, v a a = f (u a)) (ho : ∀ a i, a ≠ i → v a i ∉ Set.range f) :
    MvPolynomial.killCompl hf
      (Matrix.of fun a i : ι => (MvPolynomial.X (v a i) : MvPolynomial σ k)).det =
      MvPolynomial.monomial (∑ a, Finsupp.single (u a) 1) 1 := by
  rw [AlgHom.map_det]
  have hM : (MvPolynomial.killCompl hf).mapMatrix
      (Matrix.of fun a i : ι => (MvPolynomial.X (v a i) : MvPolynomial σ k)) =
      Matrix.diagonal fun a => MvPolynomial.X (u a) := by
    ext a i
    rw [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.diagonal_apply]
    split_ifs with h
    · subst h
      rw [hd, ← MvPolynomial.rename_X f, MvPolynomial.killCompl_rename_app]
    · rw [MvPolynomial.killCompl, MvPolynomial.aeval_X, dite_eq_right (ho a i h)]
  rw [hM, Matrix.det_diagonal, MvPolynomial.monomial_sum_one]
  rfl

theorem _root_.GlobalTheory.LeadingMinors.coeff_prod_leading_minors : ∀ (k : Type) [CommRing k] (T : Type) [Fintype T] [DecidableEq T] (r : T → ℕ) (n : ℕ) (col : ∀ τ, Fin (r τ) → Fin n) (m : ∀ τ, Fin (r τ) → ℕ), (∀ τ, Function.Injective (col τ)) → ∀ (P : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k) (al : (Σ τ : T, Fin (r τ)) × Fin n →₀ ℕ), P = (∏ τ, ∏ s : Fin (r τ), (Matrix.of fun a i : Fin (s.val + 1) => (MvPolynomial.X ((⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (r τ)), col τ (Fin.castLE s.isLt i)) : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k)).det ^ m τ s) → al = ∑ τ, ∑ s : Fin (r τ), m τ s • ∑ a : Fin (s.val + 1), Finsupp.single ((⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (r τ)), col τ (Fin.castLE s.isLt a)) 1 → P.coeff al = 1 ∧ P.IsHomogeneous al.degree ∧ al.degree = ∑ τ, ∑ s : Fin (r τ), m τ s * (s.val + 1) ∧ ∀ mo ∈ P.support, ∀ l b, mo (l, b) ≠ 0 → ∃ i, col l.1 i = b := by
  intro k _ T _ _ r n col m hcol P al hP hal
  have hf : Function.Injective
      (fun l : Σ τ : T, Fin (r τ) => ((l, col l.1 l.2) : (Σ τ : T, Fin (r τ)) × Fin n)) :=
    fun a b h => congrArg Prod.fst h
  have hblock : ∀ τ (s : Fin (r τ)), MvPolynomial.killCompl hf
      (Matrix.of fun a i : Fin (s.val + 1) =>
        (MvPolynomial.X ((⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (r τ)),
          col τ (Fin.castLE s.isLt i)) : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k)).det =
      MvPolynomial.monomial
        (∑ a : Fin (s.val + 1), Finsupp.single (⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (r τ)) 1)
        1 := fun τ s =>
    _root_.GlobalTheory.LeadingMinors.killCompl_det_X hf _ (fun a => ⟨τ, Fin.castLE s.isLt a⟩)
      (fun _ => rfl) (by
        rintro a i hai ⟨l, hl⟩
        simp only [Prod.mk.injEq] at hl
        obtain ⟨rfl, h⟩ := hl
        exact hai (Fin.castLE_injective _ (hcol τ h)))
  set B : (Σ τ : T, Fin (r τ)) →₀ ℕ := ∑ τ, ∑ s : Fin (r τ), m τ s •
    ∑ a : Fin (s.val + 1), Finsupp.single (⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (r τ)) 1
    with hBdef
  have hkill : MvPolynomial.killCompl hf P = MvPolynomial.monomial B 1 := by
    rw [hP, hBdef, map_prod, MvPolynomial.monomial_sum_one]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_prod, MvPolynomial.monomial_sum_one]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [map_pow, hblock, MvPolynomial.monomial_pow, one_pow]
  have hmap : Finsupp.mapDomain
      (fun l : Σ τ : T, Fin (r τ) => ((l, col l.1 l.2) : (Σ τ : T, Fin (r τ)) × Fin n)) B = al := by
    rw [hal, hBdef]
    simp [Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_smul, Finsupp.mapDomain_single]
  have hdeg : al.degree = ∑ τ, ∑ s : Fin (r τ), m τ s * (s.val + 1) := by
    rw [hal]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, Finsupp.degree_single]
  have hhom : P.IsHomogeneous (∑ τ, ∑ s : Fin (r τ), m τ s * (s.val + 1)) := by
    rw [hP]
    refine MvPolynomial.IsHomogeneous.prod _ _ _ fun τ _ =>
      MvPolynomial.IsHomogeneous.prod _ _ _ fun s _ => ?_
    have h := (_root_.GlobalTheory.LeadingMinors.isHomogeneous_det_X (k := k)
      (fun a i : Fin (s.val + 1) => ((⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (r τ)),
        col τ (Fin.castLE s.isLt i)))).pow (m τ s)
    rw [Fintype.card_fin] at h
    rwa [mul_comm] at h
  have hsupp : P ∈ MvPolynomial.supported k
      {x : (Σ τ : T, Fin (r τ)) × Fin n | ∃ i, col x.1.1 i = x.2} := by
    rw [hP]
    exact Subalgebra.prod_mem _ fun τ _ => Subalgebra.prod_mem _ fun s _ =>
      Subalgebra.pow_mem _ (_root_.GlobalTheory.LeadingMinors.det_X_mem_supported
        (fun a i : Fin (s.val + 1) => ((⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (r τ)),
          col τ (Fin.castLE s.isLt i)))
        {x : (Σ τ : T, Fin (r τ)) × Fin n | ∃ i, col x.1.1 i = x.2}
        fun a i => ⟨Fin.castLE s.isLt i, rfl⟩) _
  refine ⟨?_, by rw [hdeg]; exact hhom, hdeg, fun mo hmo l b hlb => ?_⟩
  · rw [← hmap, ← MvPolynomial.coeff_killCompl hf, hkill, MvPolynomial.coeff_monomial, if_pos rfl]
  · have hv : (l, b) ∈ P.vars :=
      (MvPolynomial.mem_vars_iff_mem_support _).2 ⟨mo, hmo, Finsupp.mem_support_iff.2 hlb⟩
    exact MvPolynomial.mem_supported.1 hsupp hv

end GlobalTheory.LeadingMinors
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TwistedMeasureMomentsEqShiftedSeriesJets
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TwistedMeasureMomentsEqShiftedSeriesJets
noncomputable section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.TwistMom
open GlobalTheory.MomOne.Shift
variable {q : ℕ} [Fact q.Prime]

theorem norm_zc (a : ℤ_[q]) : ‖zc a‖ = ‖a‖ := by
  have h := PadicComplex.norm_extends' q (a : ℚ_[q])
  simpa [zc] using h

theorem zc_natCast (m : ℕ) : zc (m : ℤ_[q]) = (m : ℂ_[q]) := by simp [zc]

theorem continuous_zc : Continuous (zc : ℤ_[q] → ℂ_[q]) := by
  refine (Isometry.of_dist_eq fun a b => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm, ← norm_zc]
  simp [zc]

theorem norm_sub_one_lt_of_root {ζ : ℂ_[q]} {n : ℕ} (h : ζ ^ (q ^ n) = 1) : ‖ζ - 1‖ < 1 := by
  have hp : q.Prime := Fact.out
  have hn : q ^ n ≠ 0 := pow_ne_zero _ hp.ne_zero
  have h1 : ‖ζ‖ = 1 := by
    have := congrArg norm h
    rw [norm_pow, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).mp this
  let O : Subring ℂ_[q] :=
    { carrier := {x | ‖x‖ ≤ 1}
      mul_mem' := fun {a b} ha hb => by
        show ‖a * b‖ ≤ 1
        rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hb
      one_mem' := by simp
      add_mem' := fun {a b} ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by simpa using ha }
  have hz : ζ ∈ O := h1.le
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hp ((⟨ζ, hz⟩ : O) - 1) 1 n
  have hr' := congrArg (fun x : O => (x : ℂ_[q])) hr
  simp only [sub_add_cancel] at hr'
  push_cast at hr'
  have hq : ‖(q : ℂ_[q])‖ < 1 := by
    rw [← zc_natCast, norm_zc]; exact Padic.norm_p_lt_one
  have e : (ζ - 1) ^ q ^ n = -((q : ℂ_[q]) * ((ζ - 1) * r)) := by
    rw [h, one_pow] at hr'
    linear_combination -hr'
  have hm : ‖(ζ - 1) * r‖ ≤ 1 := O.mul_mem (O.sub_mem hz O.one_mem) r.2
  have : ‖ζ - 1‖ ^ q ^ n < 1 := by
    rw [← norm_pow, e, norm_neg, norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) hm).trans_lt hq
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) hn).mp this

theorem continuous_redFun (r : ℕ) (g : ZMod (q ^ r) → ℂ_[q]) :
    Continuous fun a : ℤ_[q] => g (PadicInt.toZModPow r a) := by
  have hl : q.Prime := Fact.out
  rw [continuous_iff_continuousAt]
  intro x
  refine (continuousAt_const (y := g (PadicInt.toZModPow r x))).congr ?_
  have hpos : (0 : ℝ) < (q : ℝ) ^ (-(r : ℤ)) := zpow_pos (by exact_mod_cast hl.pos) _
  filter_upwards [Metric.closedBall_mem_nhds x hpos] with y hy
  rw [Metric.mem_closedBall, dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow,
    ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero] at hy
  rw [hy]

theorem hasSum_coeff_iter {ζ : ℂ_[q]} (h : ‖ζ - 1‖ < 1) {S : ℂ_[q]⟦X⟧} (hS : Bdd S) (k : ℕ) :
    ∀ n, HasSum (fun m => coeff m S * coeff n (DT^[k] (sS ζ ^ m)))
      (coeff n (DT^[k] (shiftS ζ S))) := by
  obtain ⟨B, hB⟩ := hS
  induction k with
  | zero =>
    intro n
    simp only [Function.iterate_zero, id]
    rw [coeff_shiftS]
    exact (summable_term h hB n).hasSum
  | succ k ih =>
    intro n
    simp only [Function.iterate_succ_apply', coeff_DT]
    have := ((ih (n + 1)).mul_right ((n : ℂ_[q]) + 1)).add ((ih n).mul_right (n : ℂ_[q]))
    simpa only [mul_add, mul_assoc] using this

theorem DT_one_add_pow (c : ℂ_[q]) (j : ℕ) :
    DT (C c * (1 + X) ^ j) = C (c * j) * (1 + X) ^ j := by
  have hDT (f : ℂ_[q]⟦X⟧) : DT f = (1 + X) * PowerSeries.derivative f := by
    ext n
    rw [coeff_DT, add_mul, one_mul, map_add, coeff_derivative]
    cases n with
    | zero => simp
    | succ n => rw [coeff_succ_X_mul, coeff_derivative]; simp
  cases j with
  | zero => simp [hDT]
  | succ j =>
    have hd : PowerSeries.derivative (1 + X : ℂ_[q]⟦X⟧) = 1 := by
      rw [map_add, derivative_one, derivative_X, zero_add]
    rw [hDT, Derivation.leibniz]
    simp only [derivative_C, smul_eq_mul]
    rw [derivative_pow (1 + X : ℂ_[q]⟦X⟧) (j + 1), hd]
    simp only [Nat.add_sub_cancel, mul_one, map_mul, map_natCast, pow_succ]
    ring

theorem DT_iter_sum (s : Finset ℕ) (c : ℕ → ℂ_[q]) (k : ℕ) :
    DT^[k] (∑ j ∈ s, C (c j) * (1 + X) ^ j) = ∑ j ∈ s, C (c j * (j : ℂ_[q]) ^ k) * (1 + X) ^ j := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hsum (f : ℕ → ℂ_[q]⟦X⟧) : DT (∑ j ∈ s, f j) = ∑ j ∈ s, DT (f j) := by
      ext n
      simp only [map_sum, coeff_DT, Finset.sum_mul, Finset.sum_add_distrib]
    rw [Function.iterate_succ_apply', ih, hsum]
    exact Finset.sum_congr rfl fun j _ => by rw [DT_one_add_pow, pow_succ, mul_assoc]

theorem sS_pow_eq (ζ : ℂ_[q]) (m : ℕ) :
    sS ζ ^ m = ∑ j ∈ Finset.range (m + 1),
      C ((-1) ^ (m - j) * (m.choose j : ℂ_[q]) * ζ ^ j) * (1 + X) ^ j := by
  rw [sS, sub_eq_add_neg, add_pow]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [map_mul, map_pow, map_neg, map_one, map_natCast, mul_pow]
  ring

theorem twisted_moments : ∀ (q : ℕ) [Fact q.Prime] (S : ℂ_[q]⟦X⟧) (ζ : ℂ_[q]) (n k : ℕ), Bdd S → ζ ^ (q ^ n) = 1 → ∃ f : C(ℤ_[q], ℂ_[q]), (∀ a, f a = ζ ^ (PadicInt.toZModPow n a).val * zc a ^ k) ∧ HasSum (fun m : ℕ => coeff m S * (fwdDiff (1 : ℤ_[q]))^[m] f 0) (constantCoeff (DT^[k] (shiftS ζ S))) := by
  intro q _ S ζ n k hS h
  have hζ := norm_sub_one_lt_of_root h
  refine ⟨⟨fun a => ζ ^ (PadicInt.toZModPow n a).val * zc a ^ k,
    (continuous_redFun n fun x => ζ ^ x.val).mul (continuous_zc.pow k)⟩, fun _ => rfl, ?_⟩
  have := hasSum_coeff_iter hζ hS k 0
  rw [coeff_zero_eq_constantCoeff] at this
  convert this using 3 with m
  set_option synthInstance.maxHeartbeats 100000 in
    rw [fwdDiff_iter_eq_sum_shift, sS_pow_eq, DT_iter_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : (0 : ℤ_[q]) + j • (1 : ℤ_[q]) = (j : ℤ_[q]) := by simp
  rw [e]
  simp only [ContinuousMap.coe_mk, map_natCast, ZMod.val_natCast, zc_natCast]
  rw [← pow_eq_pow_mod j h]
  simp
  ring

end GlobalTheory.MomOne.TwistMom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TwistedMeasureMomentsEqShiftedSeriesJetsStatement
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_measure_moments_eq_shifted_series_jets : ∀ (q : ℕ) [Fact q.Prime] (S : ℂ_[q]⟦X⟧) (ζ : ℂ_[q]) (n k : ℕ), Bdd S → ζ ^ (q ^ n) = 1 → ∃ f : C(ℤ_[q], ℂ_[q]), (∀ a, f a = ζ ^ (PadicInt.toZModPow n a).val * zc a ^ k) ∧ HasSum (fun m : ℕ => coeff m S * (fwdDiff (1 : ℤ_[q]))^[m] f 0) (constantCoeff (DT^[k] (shiftS ζ S))) := by
  first | exact @GlobalTheory.MomOne.TwistMom.twisted_moments | exact GlobalTheory.MomOne.TwistMom.twisted_moments | (intros; apply GlobalTheory.MomOne.TwistMom.twisted_moments <;> assumption)
end
end

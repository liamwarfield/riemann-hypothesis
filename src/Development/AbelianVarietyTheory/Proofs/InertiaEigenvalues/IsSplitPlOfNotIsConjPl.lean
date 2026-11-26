module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientPow
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotentiallyCrystallineModuleEqCrystallineRestric
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NilpotentOfNotIsUnit
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.SharpRestriction.LevelLetterCocycles.SecondPropositionEveryLocalisation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalMapSurjective

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfNotIsConjPl
open GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders Polynomial NumberField
open scoped Classical

namespace GlobalTheory.FixedPlaceSplit

theorem host_conj_conj (D : Formalism.BasicNotions.D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  apply D.host.φ₀.injective
  rw [D.host.toHostAx.conjE_apply, D.host.toHostAx.conjE_apply]
  simp

theorem isSplitPl_of_not_isConjPl (D : Formalism.BasicNotions.D7) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E))
    (h : ¬ Formalism.BasicNotions.IsConjPl D.host w w) : Formalism.BasicNotions.IsSplitPl D.host w := by
  by_contra hs
  apply h
  have key : ∀ x y : 𝓞 D.host.E, (y : D.host.E) = D.host.conj (x : D.host.E) →
      x ∈ w.asIdeal → y ∈ w.asIdeal := by
    intro x y hxy hx
    by_contra hy
    apply hs
    refine ⟨x, hx, fun y' hy' => ?_⟩
    have : y' = y := by
      apply RingOfIntegers.ext
      exact hy'.trans hxy.symm
    rwa [this]
  intro x y hxy
  refine ⟨key x y hxy, key y x ?_⟩
  rw [hxy, host_conj_conj]

theorem isSplitPl_plGw : ∀ (D : Formalism.BasicNotions.D7) (k : Fin 2) (v : D.nd.PlG k),
    Formalism.BasicNotions.IsSplitPl D.host (D.naut.plGw k v) :=
  fun D k v => isSplitPl_of_not_isConjPl D _ (D.naut.plGw_nconj k v v)

end GlobalTheory.FixedPlaceSplit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFilPIffEvPt
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.TiedUnif

theorem zpow_form {R : Type} [CommRing R] (u : Rˣ) (a : ℤ) (x w : R) :
    x * (u : R) ^ (-a).toNat = (u : R) ^ a.toNat * w ↔ x = ((u ^ a : Rˣ) : R) * w := by
  rcases le_total 0 a with h | h
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h
    simp
  · obtain ⟨n, rfl⟩ := Int.exists_eq_neg_ofNat h
    simp only [neg_neg, Int.toNat_natCast, Int.toNat_neg_natCast, pow_zero, one_mul, zpow_neg,
      zpow_natCast]
    rw [Units.eq_inv_mul_iff_mul_eq, Units.val_pow_eq_pow_val, mul_comm]

variable {l : ℕ} [Fact l.Prime]

def piOne (e : Per.Fl l) : Per.Ainf l := Per.tm ((frobeniusEquiv (Per.Fl l) l).symm e) - 1

theorem mu_eq (e : Per.Fl l) : mu e = xi e * piOne e := by
  have h : (Per.tm ((frobeniusEquiv (Per.Fl l) l).symm e)) ^ l = Per.tm e := by
    rw [← map_pow, frobeniusEquiv_symm_pow_p]
  rw [mu, piOne, xi, geom_sum_mul, h]

theorem theta_piOne {e : Per.Fl l} (he : IsEps e) : Per.θD l (aDp l (piOne e)) ≠ 0 := by
  rw [(thetaD_props l).2.2.2.1]
  intro h
  apply he.2
  have h' : Per.θ l (piOne e) = 0 := Subtype.ext h
  rw [piOne, map_sub, map_one, WittVector.fontaineTheta_teichmuller, sub_eq_zero] at h'
  exact h'

theorem theta_xi {e : Per.Fl l} (he : IsEps e) : Per.θD l (aDp l (xi e)) = 0 := by
  rw [(thetaD_props l).2.2.2.1, (theta_eq_zero_iff_xi_dvd l e he _).2 dvd_rfl]
  rfl

theorem ev_aDp (n : ℕ) (a : Per.Ainf l) :
    Per.ev l n (aDp l a) = Ideal.Quotient.mk _ (algebraMap (Per.Ainf l) (Per.AinfP l) a) := by
  rw [aDp, RingHom.comp_apply, GlobalTheory.RingIface.ev_alg]

theorem mem_filtration_iff_eval_eq_zero' {e : Per.Fl l} (he : IsEps e) (n : ℕ) (y : Per.BdRp l) :
    y ∈ Per.FilP l n ↔ Per.ev l n y = 0 := by
  obtain ⟨E, hE, hev⟩ := GlobalTheory.RingIface.exists_bdRp_equiv l
  rw [(filtration_eq_xi_pow l e he).1, ← hev, FilPrincipal.evalₐ_eq_zero_iff (GlobalTheory.T.kerThetaLocalized_eq_span_fontaineXiElement l e he), ← hE,
    ← map_pow E, map_dvd_iff E, aDp, RingHom.comp_apply]

theorem mu_sub_log {e : Per.Fl l} (he : IsEps e) {y : Per.BdRp l} (hy : Per.IsLog l e y) :
    aDp l (mu e) - y ∈ Per.FilP l 2 := by
  have h2 := GlobalTheory.CrisIncl.factorial_mul_ev l e y he.1 hy 2
  have hsq : Per.ev l 2 (aDp l (mu e ^ 2)) = 0 := by
    refine (mem_filtration_iff_eval_eq_zero' he 2 _).1 (((filtration_eq_xi_pow l e he).1 2 _).2 ?_)
    rw [mu_eq, map_pow, map_mul, mul_pow]
    exact dvd_mul_right _ _
  rw [ev_aDp, map_pow, map_pow] at hsq
  have hu : IsUnit (((2 : ℕ) : Per.AinfP l ⧸ Per.kerP l ^ 2)) := by
    have := (GlobalTheory.RingBasics.isUnit_nat l 2 two_ne_zero).map (Ideal.Quotient.mk (Per.kerP l ^ 2))
    rwa [map_natCast] at this
  rw [mem_filtration_iff_eval_eq_zero' he, map_sub, ev_aDp, sub_eq_zero]
  apply hu.mul_left_cancel
  have hf : Nat.factorial 2 = 2 := rfl
  rw [hf] at h2
  rw [h2]
  change _ = Ideal.Quotient.mk _ (∑ k ∈ Finset.range 2, (-1) ^ k * ((2 / (k + 1) : ℕ) : Per.AinfP l) *
      (algebraMap (Per.Ainf l) (Per.AinfP l) (mu e)) ^ (k + 1))
  rw [Finset.sum_range_succ, Finset.sum_range_one, map_add (f := _), map_mul _ _ (_ ^ (1 + 1)), map_pow _ _ (1 + 1),
    show (1 + 1 : ℕ) = 2 from rfl, hsq]
  simp [map_ofNat]

theorem log_eq_xi_mul {e : Per.Fl l} (he : IsEps e) {y : Per.BdRp l} (hy : Per.IsLog l e y) :
    ∃ v : Per.BdRp l, IsUnit v ∧ y = aDp l (xi e) * v := by
  obtain ⟨w, hw⟩ := ((filtration_eq_xi_pow l e he).1 2 _).1 (mu_sub_log he hy)
  refine ⟨aDp l (piOne e) - aDp l (xi e) * w, (thetaD_props l).2.2.1 _ ?_, ?_⟩
  · rw [map_sub, map_mul, theta_xi he, zero_mul, sub_zero]
    exact theta_piOne he
  · rw [mu_eq, map_mul] at hw
    linear_combination -hw

theorem isUnit_xi {e : Per.Fl l} (he : IsEps e) :
    IsUnit (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (xi e))) := by
  obtain ⟨hd, hinj, hF, -⟩ := BdRField.bdR_isField l
  have h0 : algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (xi e)) ≠ 0 := by
    intro h
    have h1 : aDp l (xi e) = 0 := hinj (by rw [h, map_zero])
    exact one_ne_zero ((filtration_eq_xi_pow l e he).2.1 1 (by rw [h1, zero_mul]))
  obtain ⟨b, hb⟩ := hF.mul_inv_cancel h0
  exact IsUnit.of_mul_eq_one b hb

theorem mem_FilD_iff {e : Per.Fl l} (he : IsEps e) (a : ℤ) (x : Per.BdR l) :
    x ∈ Per.FilD l a ↔ ∃ w : Per.BdRp l,
      x = (((isUnit_xi he).unit ^ a : (Per.BdR l)ˣ) : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) w := by
  rw [mem_FilD_iff_xi_pow l e he]
  refine exists_congr fun w => ?_
  rw [← zpow_form, IsUnit.unit_spec, map_mul, map_pow]

theorem filD_succ {e : Per.Fl l} (he : IsEps e) {y : Per.BdRp l} (hy : Per.IsLog l e y) (a : ℤ)
    (x : Per.BdR l) : x ∈ Per.FilD l (a + 1) ↔
      ∃ z ∈ Per.FilD l a, x = algebraMap (Per.BdRp l) (Per.BdR l) y * z := by
  obtain ⟨v, hv, rfl⟩ := log_eq_xi_mul he hy
  obtain ⟨v', hv'⟩ := hv.exists_right_inv
  have hv2 := congrArg (algebraMap (Per.BdRp l) (Per.BdR l)) hv'
  rw [map_mul, map_one] at hv2
  rw [mem_FilD_iff he, zpow_add_one, Units.val_mul, IsUnit.unit_spec, map_mul]
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨_, (mem_FilD_iff he a _).2 ⟨v' * w, rfl⟩, ?_⟩
    rw [map_mul]
    linear_combination (-((((isUnit_xi he).unit ^ a : (Per.BdR l)ˣ) : Per.BdR l) *
      algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (xi e)) * algebraMap (Per.BdRp l) (Per.BdR l) w)) * hv2
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨w, rfl⟩ := (mem_FilD_iff he a _).1 hz
    exact ⟨v * w, by rw [map_mul]; ring⟩

theorem alg_mem_FilD (n : ℕ) {z : Per.BdRp l} (hz : z ∈ Per.FilP l n) :
    algebraMap (Per.BdRp l) (Per.BdR l) z ∈ Per.FilD l n :=
  GlobalTheory.RingIface.alg_mem_FilD_nat l hz

theorem exists_isEps_pt (l : ℕ) [Fact l.Prime] : ∃ e : Per.Fl l, IsEps e := by
  obtain ⟨ζ, ε, h0, -, h1, h⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  refine ⟨ε, ?_, fun hh => h1 ?_⟩
  · have := h 0
    rw [h0, map_one] at this
    exact Subtype.ext this
  · apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← h 1, map_one]
    exact congrArg Subtype.val hh

theorem alg_mem_FilD_zero (z : Per.BdRp l) :
    algebraMap (Per.BdRp l) (Per.BdR l) z ∈ Per.FilD l 0 := by
  obtain ⟨e, he⟩ := exists_isEps_pt l
  exact alg_mem_FilD 0 (((filtration_eq_xi_pow l e he).1 0 z).2 (by rw [pow_zero]; exact one_dvd z))

theorem eD_ιA {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (a : Ainf l) :
    T.eD (P.ιB (AI.ιA a)) = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l a) := by
  have h := GlobalTheory.CrisIncl.incl_aB l _ T.incl a
  rw [← T.ιA] at h
  have h2 : T.eD (P.ιB (T.eB.symm (T.eB (AI.ιA a)))) = _ := h
  rw [RingEquiv.symm_apply_apply] at h2
  exact h2

theorem tied_uniformiser : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → (∀ K : FinExt l, P.ιB (AI.ιA AI.μ) - P.ιB P.tB ∈ (P.PD K).Fil 2) ∧ (∀ K : FinExt l, ∃ u ∈ (P.PD K).Fil 0, P.ιB (AI.ιA AI.π₁) * u = 1) ∧ ∀ (K : FinExt l) (a : ℤ) (x : P.R.BdR), x ∈ (P.PD K).Fil (a + 1) ↔ ∃ y ∈ (P.PD K).Fil a, x = P.ιB P.tB * y := by
  intro l _ P AI T
  obtain ⟨C, hC⟩ := FitsEx.exists_fits l P AI T
  have he : IsEps AI.ε := hC.ε ▸ core_isEps l C
  obtain ⟨y, hy, ht⟩ := T.t
  refine ⟨fun K => ?_, fun K => ?_, fun K a x => ?_⟩
  · rw [T.fil, map_sub, eD_ιA T, ht, ← map_sub]
    exact alg_mem_FilD 2 (mu_sub_log he hy)
  · obtain ⟨v, hv⟩ := ((thetaD_props l).2.2.1 _ (theta_piOne he)).exists_right_inv
    refine ⟨T.eD.symm (algebraMap (Per.BdRp l) (Per.BdR l) v), ?_, T.eD.injective ?_⟩
    · rw [T.fil, RingEquiv.apply_symm_apply]
      exact alg_mem_FilD_zero v
    · rw [map_mul, RingEquiv.apply_symm_apply, eD_ιA T, ← map_mul, map_one]
      exact (congrArg _ hv).trans (map_one _)
  · rw [T.fil, filD_succ he hy]
    constructor
    · rintro ⟨z, hz, e⟩
      refine ⟨T.eD.symm z, ?_, T.eD.injective ?_⟩
      · rwa [T.fil, RingEquiv.apply_symm_apply]
      · rw [map_mul, RingEquiv.apply_symm_apply, ht, e]
    · rintro ⟨z, hz, rfl⟩
      exact ⟨T.eD z, (T.fil K a z).1 hz, by rw [map_mul, ht]⟩

end GlobalTheory.MemLoc.TiedUnif
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrComplete
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory.FinExtIntegers

theorem dvr_complete : ∀ {l : ℕ} [Fact l.Prime] (LL : FinExt l), ∃ _ : IsDiscreteValuationRing ↥(OL LL), IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) ∧ ¬ IsUnit ((l : ℕ) : ↥(OL LL)) := by
  intro l _ LL
  unfold OL
  have hfd : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have : IsScalarTower ℤ_[l] ℚ_[l] ↥LL.1 := inferInstance
  have hfin : Module.Finite ℤ_[l] ↥(integralClosure ℤ_[l] ↥LL.1) :=
    IsIntegralClosure.finite ℤ_[l] ℚ_[l] ↥LL.1 ↥(integralClosure ℤ_[l] ↥LL.1)
  have : FaithfulSMul ℤ_[l] ↥LL.1 := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_faithful ℤ_[l] ℚ_[l] ↥LL.1
  have hdvr : IsDiscreteValuationRing ↥(integralClosure ℤ_[l] ↥LL.1) :=
    ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_dvr ℤ_[l] ℚ_[l] ↥LL.1
  have hloc : IsLocalHom (algebraMap ℤ_[l] ↥(integralClosure ℤ_[l] ↥LL.1)) :=
    ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_isLocalHom ℤ_[l] ↥LL.1
  refine ⟨hdvr, GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local ℤ_[l] _, ?_⟩
  intro hu
  have hl : ¬IsUnit (l : ℤ_[l]) := by
    rw [PadicInt.not_isUnit_iff, PadicInt.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  apply hl
  apply (isUnit_map_iff (algebraMap ℤ_[l] ↥(integralClosure ℤ_[l] ↥LL.1)) _).mp
  simpa using hu

end GlobalTheory.FinExtIntegers
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankLeOfSubsetClosureRange
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.HubLoc Module

namespace GlobalTheory

theorem finrank_le_of_subset_closure_range {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E]
    (J : E →+* PadicAlgCl l) (K : IntermediateField ℚ_[l] (PadicAlgCl l))
    (hdense : (K : Set (PadicAlgCl l)) ⊆ closure (Set.range J)) :
    finrank ℚ_[l] ↥K ≤ finrank ℚ E := by
  classical
  let b := Module.finBasis ℚ E
  let S : Submodule ℚ_[l] (PadicAlgCl l) := Submodule.span ℚ_[l] (Set.range fun k => J (b k))
  have hfd : FiniteDimensional ℚ_[l] S := FiniteDimensional.span_of_finite _ (Set.finite_range _)
  have hcl : IsClosed (S : Set (PadicAlgCl l)) := Submodule.closed_of_finiteDimensional S
  have hsub : Set.range J ⊆ S := by
    rintro _ ⟨x, rfl⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr x, map_sum]
    refine S.sum_mem fun k _ => ?_
    have e : J (b.repr x k • b k) = ((b.repr x k : ℚ) : ℚ_[l]) • J (b k) := by
      rw [Rat.smul_def, map_mul, map_ratCast, Algebra.smul_def, map_ratCast]
    rw [e]
    exact S.smul_mem _ (Submodule.subset_span ⟨k, rfl⟩)
  have hle : K.toSubalgebra.toSubmodule ≤ S := fun x hx => closure_minimal hsub hcl (hdense hx)
  have h1 : finrank ℚ_[l] ↥K.toSubalgebra.toSubmodule ≤ finrank ℚ_[l] S := Submodule.finrank_mono hle
  have h2 : finrank ℚ_[l] S ≤ finrank ℚ E := by
    have := finrank_range_le_card (R := ℚ_[l]) (fun k => J (b k))
    simpa [Set.finrank] using this
  exact le_trans h1 h2

theorem bridge_finrank_le (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    finrank ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1 ≤ 4 * D.R.n := by
  have h1 : finrank ℚ D.host.E = 4 * D.R.ord := D.host.finrank_cmField
  have h2 := finrank_le_of_subset_closure_range
    ((D.nbr i w hw).j.comp (algebraMap D.host.E D.nd.Om)) (D.nbr i w hw).Kw.1 (D.nbr i w hw).j_dense
  have h3 : D.R.n = D.R.ord := rfl
  have h4 : finrank ℚ D.host.E = 4 * D.R.n := by rw [h1, h3]
  exact le_trans h2 h4.le

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConcretePeriodDeRhamModuleFinrankLe
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConcretePeriodDeRhamModuleFinrankLe
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.Per.TiedDdR

theorem ddR_finrank_le : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
      [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V),
      FiniteDimensional ↥LL.1 ↥(DdR (P.PD K) ρ) ∧
        Module.finrank ↥LL.1 ↥(DdR (P.PD K) ρ) ≤ Module.finrank ℚ_[l] ↥K.1 * Module.finrank ↥LL.1 V := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ
  haveI := LL.2
  exact GlobalTheory.Per.FontaineBound.ddR_finite_le (P.PD K) (GlobalTheory.Per.FontaineBound.isField_of_tied T) ρ

end GlobalTheory.Per.TiedDdR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConcretePeriodDeRhamModuleFinrankLeStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.concretePeriod_deRham_module_finrank_le : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), FiniteDimensional ↥LL.1 ↥(DdR (P.PD K) ρ) ∧ Module.finrank ↥LL.1 ↥(DdR (P.PD K) ρ) ≤ Module.finrank ℚ_[l] ↥K.1 * Module.finrank ↥LL.1 V := by
  first | exact @GlobalTheory.Per.TiedDdR.ddR_finrank_le | exact GlobalTheory.Per.TiedDdR.ddR_finrank_le | (intros; apply GlobalTheory.Per.TiedDdR.ddR_finrank_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltWittEqZeroOfPrimeMulEqZero
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.Decompl

namespace GlobalTheory.HWL.TensorWitt

section Coord

variable {Z O : Type} [CommRing Z] [CommRing O] [Algebra Z O] {I : Type} [Fintype I]
  (b : Module.Basis I Z O) {W : Type} [CommRing W] [Algebra Z W]

private theorem crd_tmul_lemma (i : I) (o : O) (v : W) :
    crd b i (o ⊗ₜ[Z] v) = b.coord i o • v := by
  simp only [crd, TensorProduct.lift.tmul, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.lsmul_apply]

private theorem crd_mul_lemma_2 (i : I) (c : W) (y : O ⊗[Z] W) :
    crd b i ((1 : O) ⊗ₜ[Z] c * y) = c * crd b i y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul o v =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, crd_tmul_lemma, crd_tmul_lemma]
    exact (mul_smul_comm _ _ _).symm
  | add y z hy hz => rw [mul_add, map_add (f := _), map_add (f := _), hy, hz, mul_add]

private theorem sum_basis_tmul_crd_eq (y : O ⊗[Z] W) : ∑ i, b i ⊗ₜ[Z] crd b i y = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul o v =>
    simp_rw [crd_tmul_lemma, Module.Basis.coord_apply, ← TensorProduct.smul_tmul,
      ← TensorProduct.sum_tmul, Module.Basis.sum_repr]
  | add y z hy hz =>
    simp_rw [map_add (f := _), TensorProduct.tmul_add, Finset.sum_add_distrib, hy, hz]

private theorem crd_sum_lemma_4 (j : I) (v : I → W) : crd b j (∑ i, b i ⊗ₜ[Z] v i) = v j := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, crd_tmul_lemma, Module.Basis.coord_apply, Finsupp.single_apply]

theorem mem_pow_iff (w : W) (n : ℕ) (x : O ⊗[Z] W) :
    x ∈ Ideal.span {((1 : O) ⊗ₜ[Z] w) ^ n} ↔ ∀ i, crd b i x ∈ Ideal.span {w ^ n} := by
  rw [Algebra.TensorProduct.tmul_pow, one_pow, Ideal.mem_span_singleton]
  simp_rw [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨y, rfl⟩ i
    exact ⟨crd b i y, crd_mul_lemma_2 b i _ y⟩
  · intro h
    choose c hc using h
    refine ⟨∑ i, b i ⊗ₜ[Z] c i, ?_⟩
    conv_lhs => rw [← sum_basis_tmul_crd_eq b x]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hc i, Algebra.TensorProduct.tmul_mul_tmul, one_mul]


include b in
theorem complete_tensor (w : W) [h : IsAdicComplete (Ideal.span {w}) W] :
    IsAdicComplete (Ideal.span {(1 : O) ⊗ₜ[Z] w}) (O ⊗[Z] W) := by
  have key : ∀ (n : ℕ) (x : O ⊗[Z] W),
      x ∈ (Ideal.span {(1 : O) ⊗ₜ[Z] w} ^ n • ⊤ : Submodule (O ⊗[Z] W) (O ⊗[Z] W)) ↔
        ∀ i, crd b i x ∈ (Ideal.span {w} ^ n • ⊤ : Submodule W W) := by
    intro n x
    simp only [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
    exact mem_pow_iff b w n x
  have H1 : IsHausdorff (Ideal.span {(1 : O) ⊗ₜ[Z] w}) (O ⊗[Z] W) := by
    refine ⟨fun x hx => ?_⟩
    have hi : ∀ i, crd b i x = 0 := fun i =>
      IsHausdorff.haus h.toIsHausdorff _ fun n => by
        rw [SModEq.sub_mem, sub_zero]
        exact (key n x).1 (by simpa [SModEq.sub_mem] using hx n) i
    rw [← sum_basis_tmul_crd_eq b x]
    simp [hi]
  have H2 : IsPrecomplete (Ideal.span {(1 : O) ⊗ₜ[Z] w}) (O ⊗[Z] W) := by
    refine ⟨fun f hf => ?_⟩
    have hfi : ∀ i, ∃ L : W, ∀ n,
        crd b i (f n) ≡ L [SMOD (Ideal.span {w} ^ n • ⊤ : Submodule W W)] := fun i =>
      IsPrecomplete.prec h.toIsPrecomplete fun {m n} hmn => by
        rw [SModEq.sub_mem, ← map_sub]
        exact (key m _).1 (SModEq.sub_mem.1 (hf hmn)) i
    choose L hL using hfi
    refine ⟨∑ i, b i ⊗ₜ[Z] L i, fun n => ?_⟩
    rw [SModEq.sub_mem, key]
    intro i
    rw [map_sub, crd_sum_lemma_4]
    exact SModEq.sub_mem.1 (hL i n)
  exact { toIsHausdorff := H1, toIsPrecomplete := H2 }

end Coord

variable {l : ℕ} [Fact l.Prime]

theorem inclW_injective : Function.Injective (inclW l) := by
  unfold inclW
  exact WittVector.map_injective _ (IsFractionRing.injective (OCb l) (Cb l))

theorem tiltWitt_eq_zero_of_prime_mul_eq_zero (x : WCb l) (h : ((l : ℕ) : WCb l) * x = 0) : x = 0 := by
  haveI : CharP (Cb l) l :=
    charP_of_injective_algebraMap (IsFractionRing.injective (OCb l) (Cb l)) l
  ext n
  have h1 := WittVector.mul_charP_coeff_succ (p := l) x n
  rw [mul_comm, h, WittVector.zero_coeff] at h1
  rw [WittVector.zero_coeff]
  exact (pow_eq_zero_iff (Fact.out : l.Prime).ne_zero).1 h1.symm

theorem ainf_saturated_in_tiltWitt_prime (a : Loc.Ainf l) (w : WCb l) (h : inclW l a = ((l : ℕ) : WCb l) * w) :
    ∃ a', inclW l a' = w := by
  haveI : CharP (Cb l) l :=
    charP_of_injective_algebraMap (IsFractionRing.injective (OCb l) (Cb l)) l
  refine ⟨WittVector.mk l fun n => (frobeniusEquiv (OCb l) l).symm (a.coeff (n + 1)), ?_⟩
  ext n
  have h1 := congrArg (fun z : WCb l => z.coeff (n + 1)) h
  simp only [inclW, WittVector.map_coeff] at h1
  rw [mul_comm, WittVector.mul_charP_coeff_succ] at h1
  apply frobenius_inj (Cb l) l
  simp only [inclW, WittVector.map_coeff, WittVector.coeff_mk]
  rw [← RingHom.map_frobenius, frobenius_apply_frobeniusEquiv_symm, h1, frobenius_def]

theorem not_isUnit_teich (e : OCb l) (he : ¬ IsUnit (e - 1)) :
    ¬ IsUnit (WittVector.teichmuller l e - 1 : Loc.Ainf l) := by
  intro hu
  apply he
  have h1 := hu.map (WittVector.constantCoeff : WittVector l (OCb l) →+* OCb l)
  rwa [map_sub, map_one, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero] at h1

private theorem crd_tensorProduct_map_eq {Z O I W W' : Type} [CommRing Z] [CommRing O] [Algebra Z O]
    [Fintype I] (b : Module.Basis I Z O) [CommRing W] [Algebra Z W] [CommRing W'] [Algebra Z W']
    (f : W →ₐ[Z] W') (i : I) (y : O ⊗[Z] W) :
    crd b i (Algebra.TensorProduct.map (AlgHom.id O O) f y) = f (crd b i y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul o v =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, crd_tmul_lemma, crd_tmul_lemma, map_smul]
  | add y z hy hz => rw [map_add (f := _), map_add (f := _), hy, hz, map_add (f := _), map_add (f := _)]

private theorem tensor_eq_of_crd_eq {Z O I W : Type} [CommRing Z] [CommRing O] [Algebra Z O]
    [Fintype I] (b : Module.Basis I Z O) [CommRing W] [Algebra Z W] {y y' : O ⊗[Z] W}
    (h : ∀ i, crd b i y = crd b i y') : y = y' := by
  rw [← sum_basis_tmul_crd_eq b y, ← sum_basis_tmul_crd_eq b y']
  simp_rw [h]

private theorem exists_basis_padicInt_OL (l : ℕ) [Fact l.Prime] (LL : FinExt l) :
    ∃ (I : Type) (_ : Fintype I), Nonempty (Module.Basis I ℤ_[l] ↥(OL LL)) := by
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  haveI : IsIntegralClosure ↥(OL LL) ℤ_[l] ↥LL.1 := integralClosure.isIntegralClosure _ _
  haveI : Module.Finite ℤ_[l] ↥(OL LL) := IsIntegralClosure.finite ℤ_[l] ℚ_[l] ↥LL.1 ↥(OL LL)
  haveI : Module.IsTorsionFree ℤ_[l] ↥LL.1 := .of_smul_eq_zero fun r x h => by
    rw [Algebra.smul_def, mul_eq_zero] at h
    refine h.imp (fun h => ?_) id
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] ↥LL.1, RingHom.comp_apply,
      map_eq_zero_iff _ (algebraMap ℚ_[l] ↥LL.1).injective] at h
    exact (map_eq_zero_iff _ (IsFractionRing.injective ℤ_[l] ℚ_[l])).1 h
  haveI : Module.Free ℤ_[l] ↥(OL LL) := IsIntegralClosure.module_free ℤ_[l] ℚ_[l] ↥LL.1 ↥(OL LL)
  exact ⟨_, inferInstance, ⟨Module.Free.chooseBasis ℤ_[l] ↥(OL LL)⟩⟩

theorem main : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l),
    IsAdicComplete (Ideal.span {((l : ℕ) : RW LL)}) (RW LL) ∧
    (∀ x : RW LL, ((l : ℕ) : RW LL) * x = 0 → x = 0) ∧ Function.Injective (inclR LL) ∧
    (∀ (y : RA LL) (x : RW LL), inclR LL y = ((l : ℕ) : RW LL) * x → ∃ y', inclR LL y' = x) ∧
    ∀ e : OCb l, ¬ IsUnit (e - 1) →
      IsAdicComplete (Ideal.span {(1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l e - 1)})
        (RA LL) := by
  intro l _ LL
  obtain ⟨I, _, ⟨b⟩⟩ := exists_basis_padicInt_OL l LL
  haveI : CharP (Cb l) l :=
    charP_of_injective_algebraMap (IsFractionRing.injective (OCb l) (Cb l)) l
  have hl : ((l : ℕ) : RW LL) = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] ((l : ℕ) : WCb l) := by
    rw [← Algebra.TensorProduct.includeRight_apply, map_natCast]
  have hl' : ∀ i (x : RW LL), crd b i (((l : ℕ) : RW LL) * x) = ((l : ℕ) : WCb l) * crd b i x := by
    intro i x
    rw [hl]
    exact crd_mul_lemma_2 b i _ x
  have hinc : ∀ (y : RA LL) i, crd b i (inclR LL y) = inclW l (crd b i y) := fun y i =>
    crd_tensorProduct_map_eq b (inclWA l) i y
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hl]
    haveI : IsAdicComplete (Ideal.span {((l : ℕ) : WCb l)}) (WCb l) :=
      (GlobalTheory.Per.AinfComplete.witt_complete (p := l) (R := Cb l) ((l : ℕ) : WCb l)
        (fun c => ⟨c, fun n => by simp⟩)
        (fun x hx => by simpa using hx 1)).2
    exact complete_tensor b _
  · intro x hx
    refine tensor_eq_of_crd_eq b fun i => ?_
    rw [map_zero]
    exact tiltWitt_eq_zero_of_prime_mul_eq_zero _ (by rw [← hl', hx, map_zero])
  · intro y y' h
    exact tensor_eq_of_crd_eq b fun i => inclW_injective (by rw [← hinc, ← hinc, h])
  · intro y x hyx
    have hi : ∀ i, ∃ a' : Loc.Ainf l, inclW l a' = crd b i x := fun i =>
      ainf_saturated_in_tiltWitt_prime (crd b i y) (crd b i x)
        ((hinc y i).symm.trans ((congrArg (crd b i) hyx).trans (hl' i x)))
    choose a' ha' using hi
    refine ⟨∑ i, b i ⊗ₜ[ℤ_[l]] a' i, tensor_eq_of_crd_eq b fun i => ?_⟩
    exact (hinc _ i).trans ((congrArg (inclW l) (crd_sum_lemma_4 b i a')).trans (ha' i))
  · intro e he
    haveI : IsAdicComplete (Ideal.span {(WittVector.teichmuller l e - 1 : Ainf l)}) (Ainf l) :=
      (GlobalTheory.Per.AinfComplete.main l _ (not_isUnit_teich e he)).2
    exact complete_tensor b _

end GlobalTheory.HWL.TensorWitt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodCoefficientRingPadicIntegersFinExt
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodCoefficientRingPadicIntegersFinExt
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.LocalIntegers

theorem goodO_integers : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l), GoodO (Qp := ℚ_[l]) ↥LL.1 ↥(OL LL) :=
  fun l _ LL => (good_integers l LL).1

end GlobalTheory.LocalIntegers
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodCoefficientRingPadicIntegersFinExtStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodCoefficientRing_padicIntegers_finExt : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l), GoodO (Qp := ℚ_[l]) ↥LL.1 ↥(OL LL) := by
  first | exact @GlobalTheory.LocalIntegers.goodO_integers | exact GlobalTheory.LocalIntegers.goodO_integers | (intros; apply GlobalTheory.LocalIntegers.goodO_integers <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussGLZero
noncomputable section

open Matrix

namespace GlobalTheory.FlatConj

def gaussGL {k : Type} [Field k] [Fintype k] [DecidableEq k] (ψ : AddChar k ℂ) (ξ : kˣ →* ℂˣ) (r : ℕ) : ℂ :=
  ∑ x : GL (Fin r) k, (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ) * ψ (Matrix.trace (x : Matrix (Fin r) (Fin r) k))

variable {E : Type} [Field E] [NumberField E]

def resField (PP : Formalism.L2.DIV.Pl E) : Field (Formalism.L2.DIV.kP PP) :=
  haveI := PP.isMaximal
  Ideal.Quotient.field PP.asIdeal

def resFintype (PP : Formalism.L2.DIV.Pl E) : Fintype (Formalism.L2.DIV.kP PP) :=
  haveI : Finite (Formalism.L2.DIV.kP PP) := Ideal.finiteQuotientOfFreeOfNeBot PP.asIdeal PP.ne_bot
  Fintype.ofFinite _

def gaussP (PP : Formalism.L2.DIV.Pl E) (ψ : AddChar (Formalism.L2.DIV.kP PP) ℂ) (ξ : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (r : ℕ) : ℂ :=
  @gaussGL (Formalism.L2.DIV.kP PP) (resField PP) (resFintype PP) (Classical.decEq _) ψ ξ r

end GlobalTheory.FlatConj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodORingOfIntegers
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.Pass

theorem goodO_ringOfIntegers :
    ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l), GoodO (Qp := ℚ_[l]) ↥LL.1 ↥(OL LL) :=
  fun l _ LL => (GlobalTheory.LocalIntegers.good_integers l LL).1

end GlobalTheory.Pass
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusSubOneWittTensorLatticeSurjectiveFixed
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusSubOneWittTensorLatticeSurjectiveFixed
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.WittTensorFixed

theorem tensor_flat {R W T : Type} [CommRing R] [CommRing W] [Algebra R W] [AddCommGroup T]
    [Module R T] [Module.Flat R T] (f : W →ₐ[R] W) (hs : ∀ y, ∃ b, f b - b = y)
    (hk : ∀ b, f b = b → ∃ z, b = algebraMap R W z)
    (hi : Function.Injective (algebraMap R W)) :
    (∀ y : W ⊗[R] T, ∃ b, TensorProduct.map f.toLinearMap LinearMap.id b - b = y) ∧
    (∀ b : W ⊗[R] T, TensorProduct.map f.toLinearMap LinearMap.id b = b ↔
      ∃ t : T, b = (1 : W) ⊗ₜ[R] t) ∧
    Function.Injective (fun t : T => (1 : W) ⊗ₜ[R] t) := by

  let g : W →ₗ[R] W := f.toLinearMap - LinearMap.id
  let i : R →ₗ[R] W := Algebra.linearMap R W
  have key : ∀ b : W ⊗[R] T,
      TensorProduct.map f.toLinearMap LinearMap.id b - b = g.rTensor T b := by
    intro b
    simp only [g, LinearMap.rTensor_sub, LinearMap.rTensor_id, LinearMap.sub_apply,
      LinearMap.id_apply]
    rfl
  have gsurj : Function.Surjective g := fun y => by
    obtain ⟨b, hb⟩ := hs y
    exact ⟨b, by simpa [g] using hb⟩
  have hex : Function.Exact i g := by
    intro y
    constructor
    · intro hy
      have hfy : f y = y := by
        have h2 : f y - y = 0 := by simpa [g] using hy
        exact sub_eq_zero.mp h2
      obtain ⟨z, rfl⟩ := hk y hfy
      exact ⟨z, rfl⟩
    · rintro ⟨z, rfl⟩
      simp [g, i]
  have hexT := rTensor_exact T hex gsurj
  have emb : ∀ t : T, (1 : W) ⊗ₜ[R] t = i.rTensor T ((1 : R) ⊗ₜ[R] t) := by
    intro t
    simp [i]
  have hrange : ∀ x : R ⊗[R] T, i.rTensor T x = (1 : W) ⊗ₜ[R] TensorProduct.lid R T x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r t =>
      simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, i, Algebra.linearMap_apply]
      rw [Algebra.algebraMap_eq_smul_one (A := W) r, TensorProduct.smul_tmul]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, TensorProduct.tmul_add]
  refine ⟨fun y => ?_, fun b => ?_, ?_⟩
  · obtain ⟨b, hb⟩ := LinearMap.rTensor_surjective T gsurj y
    exact ⟨b, by rw [key]; exact hb⟩
  · have hiff : TensorProduct.map f.toLinearMap LinearMap.id b = b ↔ g.rTensor T b = 0 := by
      rw [← key, sub_eq_zero]
    rw [hiff, hexT]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨TensorProduct.lid R T x, hrange x⟩
    · rintro ⟨t, rfl⟩
      exact ⟨(1 : R) ⊗ₜ t, (emb t).symm⟩
  · have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := T) i hi
    intro t t' h
    have h' : i.rTensor T ((1 : R) ⊗ₜ[R] t) = i.rTensor T ((1 : R) ⊗ₜ[R] t') := by
      rw [← emb, ← emb]
      exact h
    simpa using congrArg (TensorProduct.lid R T) (hinj h')

theorem baseChange_flat {R W O : Type} [CommRing R] [CommRing W] [Algebra R W] [CommRing O]
    [Algebra R O] [Module.Flat R O] (f : W →ₐ[R] W) (hs : ∀ y, ∃ b, f b - b = y)
    (hk : ∀ b, f b = b → ∃ z, b = algebraMap R W z)
    (hi : Function.Injective (algebraMap R W)) :
    (∀ y : O ⊗[R] W, ∃ b, Algebra.TensorProduct.map (AlgHom.id O O) f b - b = y) ∧
    (∀ b : O ⊗[R] W, Algebra.TensorProduct.map (AlgHom.id O O) f b = b →
      ∃ z, b = algebraMap O (O ⊗[R] W) z) ∧
    Function.Injective (algebraMap O (O ⊗[R] W)) := by

  let g : W →ₗ[R] W := f.toLinearMap - LinearMap.id
  let i : R →ₗ[R] W := Algebra.linearMap R W
  have key : ∀ b : O ⊗[R] W,
      Algebra.TensorProduct.map (AlgHom.id O O) f b - b = g.lTensor O b := by
    intro b
    induction b using TensorProduct.induction_on with
    | zero => simp
    | tmul o w => simp [g, TensorProduct.tmul_sub]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), ← hx, ← hy]; abel
  have gsurj : Function.Surjective g := fun y => by
    obtain ⟨b, hb⟩ := hs y
    exact ⟨b, by simpa [g] using hb⟩
  have hex : Function.Exact i g := by
    intro y
    constructor
    · intro hy
      have hfy : f y = y := by
        have h2 : f y - y = 0 := by simpa [g] using hy
        exact sub_eq_zero.mp h2
      obtain ⟨z, rfl⟩ := hk y hfy
      exact ⟨z, rfl⟩
    · rintro ⟨z, rfl⟩
      simp [g, i]
  have hexT := lTensor_exact O hex gsurj
  have emb : ∀ z : O, algebraMap O (O ⊗[R] W) z = i.lTensor O (z ⊗ₜ[R] (1 : R)) := by
    intro z
    simp [i]
  have hrange : ∀ x : O ⊗[R] R,
      i.lTensor O x = algebraMap O (O ⊗[R] W) (TensorProduct.rid R O x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul o r =>
      simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, i, Algebra.linearMap_apply,
        Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]
      rw [Algebra.algebraMap_eq_smul_one (A := W) r, ← TensorProduct.smul_tmul]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]
  refine ⟨fun y => ?_, fun b hb => ?_, ?_⟩
  · obtain ⟨b, hb⟩ := LinearMap.lTensor_surjective O gsurj y
    exact ⟨b, by rw [key]; exact hb⟩
  · have h0 : g.lTensor O b = 0 := by rw [← key, hb, sub_self]
    obtain ⟨x, rfl⟩ := (hexT b).mp h0
    exact ⟨TensorProduct.rid R O x, hrange x⟩
  · have hinj := Module.Flat.lTensor_preserves_injective_linearMap (M := O) i hi
    intro z z' h
    rw [emb, emb] at h
    simpa using congrArg (TensorProduct.rid R O) (hinj h)

theorem algebraMap_WCb_injective (l : ℕ) [Fact l.Prime] :
    Function.Injective (algebraMap ℤ_[l] (WCb l)) := by

  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hne
  have hker : RingHom.ker (algebraMap ℤ_[l] (WCb l)) ≠ ⊥ := by
    intro h
    apply hne
    have hxk : x ∈ RingHom.ker (algebraMap ℤ_[l] (WCb l)) := hx
    rw [h] at hxk
    exact (Submodule.mem_bot _).mp hxk
  obtain ⟨n, hn⟩ := PadicInt.ideal_eq_span_pow_p hker
  have hmem : (l : ℤ_[l]) ^ n ∈ RingHom.ker (algebraMap ℤ_[l] (WCb l)) := by
    rw [hn]
    exact Ideal.subset_span (Set.mem_singleton _)
  rw [RingHom.mem_ker, map_pow, map_natCast] at hmem
  exact pow_ne_zero n (WittVector.p_nonzero l (Cb l)) hmem

theorem flat_lattice {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp]
    [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] [IsDomain O]
    [IsBezout O] (hO : Function.Injective (algebraMap O LL)) (T : LocLat G Qp LL O) :
    Module.Flat O ↥T.L.T := by

  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  intro x hx
  rw [Submodule.mem_torsion_iff] at hx
  obtain ⟨⟨a, ha⟩, hax⟩ := hx
  have hax' : a • x = 0 := hax
  rw [Submodule.mem_bot]
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have hLL : algebraMap O LL a ≠ 0 := fun h => ha0 (hO (by rw [h, map_zero]))
  have hx0 : (algebraMap O LL a) • (x : T.V) = 0 := by
    rw [algebraMap_smul, ← Submodule.coe_smul, hax']
    rfl
  exact Subtype.ext ((smul_eq_zero.mp hx0).resolve_left hLL)

theorem lattice_fixed {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp]
    [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] [IsDomain O]
    [IsBezout O] (hO : Function.Injective (algebraMap O LL)) (T : LocLat G Qp LL O)
    {R : Type} [CommRing R] [Algebra O R] (f : R →ₐ[O] R) (hs : ∀ y, ∃ b, f b - b = y)
    (hk : ∀ b, f b = b → ∃ z, b = algebraMap O R z)
    (hi : Function.Injective (algebraMap O R)) :
    (∀ y : TW R T, ∃ b, TWmap f T b - b = y) ∧
    (∀ b : TW R T, TWmap f T b = b ↔ ∃ t : ↥T.L.T, b = (1 : R) ⊗ₜ[O] t) ∧
    Function.Injective (fun t : ↥T.L.T => (1 : R) ⊗ₜ[O] t) := by
  haveI := flat_lattice hO T
  unfold TW TWmap
  exact tensor_flat f hs hk hi

theorem ring_fixed (l : ℕ) [Fact l.Prime] (LL : FinExt l) :
    (∀ y : RW LL, ∃ b, φRW LL b - b = y) ∧
    (∀ b : RW LL, φRW LL b = b → ∃ z, b = algebraMap ↥(OL LL) (RW LL) z) ∧
    Function.Injective (algebraMap ↥(OL LL) (RW LL)) := by
  obtain ⟨_, -, -, -, hfree, -, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
  haveI : Module.Flat ℤ_[l] ↥(OL LL) := Module.Flat.of_free
  obtain ⟨hs, hk, -⟩ := GlobalTheory.ArtinSchreierWitt.main l
  unfold RW φRW
  exact baseChange_flat (frobW l) hs hk (algebraMap_WCb_injective l)


set_option maxHeartbeats 1600000 in
theorem main : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), (∀ y : TW (RW LL) T, ∃ b, TWmap (φRW LL) T b - b = y) ∧ (∀ b : TW (RW LL) T, TWmap (φRW LL) T b = b ↔ ∃ t : ↥T.L.T, b = (1 : RW LL) ⊗ₜ[↥(OL LL)] t) ∧ Function.Injective (fun t : ↥T.L.T => (1 : RW LL) ⊗ₜ[↥(OL LL)] t) := by
  intro l _ K LL T
  obtain ⟨hdvr, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
  have hO : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := fun a b h => Subtype.ext h
  obtain ⟨hs, hk, hi⟩ := ring_fixed l LL
  exact lattice_fixed hO T (φRW LL) hs hk hi

end GlobalTheory.WittTensorFixed
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusSubOneWittTensorLatticeSurjectiveFixedStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_sub_one_wittTensorLattice_surjective_fixed : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), (∀ y : TW (RW LL) T, ∃ b, TWmap (φRW LL) T b - b = y) ∧ (∀ b : TW (RW LL) T, TWmap (φRW LL) T b = b ↔ ∃ t : ↥T.L.T, b = (1 : RW LL) ⊗ₜ[↥(OL LL)] t) ∧ Function.Injective (fun t : ↥T.L.T => (1 : RW LL) ⊗ₜ[↥(OL LL)] t) := by
  first | exact @GlobalTheory.WittTensorFixed.main | exact GlobalTheory.WittTensorFixed.main | (intros; apply GlobalTheory.WittTensorFixed.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolySpanAndHomRelationsOfAdmissible
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory

theorem charpoly_span_and_hom_relations_of_admissible : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), TruncatedSeriesCountingIdentities.admG1 i r → LargeLevelLemmas.CharpolyCoeffsLemmaFamily i r ∧ LargeLevelLemmas.SpanQuotientLemma i r ρ π ∧ LargeLevelLemmas.HomRelationsLemmaAllChoices i r ρ π :=
  fun _ i r ρ π h => ⟨LargeLevelLemmas.span_lemma_clause i r h, LargeLevelLemmas.eigenspace_lemma_clause i r ρ π, LargeLevelLemmas.relation_lemma_clause i r ρ π⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUntiltToComplexPAdicBasicLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUntiltToComplexPAdicBasicLaws
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer.Laws

variable (l : ℕ) [Fact l.Prime]

theorem untilt_zero : (0 : Fl l).untilt = 0 :=
  Perfection.teichmuller_zero

theorem sh_laws : ∀ (l : ℕ) [Fact l.Prime], sh (1 : Fl l) = 1 ∧ sh (0 : Fl l) = 0 ∧
    (∀ x y : Fl l, sh (x * y) = sh x * sh y) ∧ (∀ (x : Fl l) (n : ℕ), sh (x ^ n) = sh x ^ n) ∧
    (∀ x : Fl l, ‖sh x‖ ≤ 1) ∧ (∀ c : ℂ_[l], ‖c‖ ≤ 1 → ∃ x : Fl l, sh x = c) ∧
    (∀ x y : Fl l, ‖sh (x + y) - sh x - sh y‖ ≤ ‖(l : ℂ_[l])‖) ∧ (∀ x : Fl l, ‖sh (-x)‖ = ‖sh x‖) := by
  intro l _
  have hmul : ∀ x y : Fl l, sh (x * y) = sh x * sh y := fun x y => by
    simp only [sh, map_mul]; rfl
  have hpow : ∀ (x : Fl l) (n : ℕ), sh (x ^ n) = sh x ^ n := fun x n => by
    simp only [sh, map_pow]; norm_cast
  refine ⟨by simp [sh], by simp [sh, untilt_zero], hmul, hpow, fun x => (GlobalTheory.RingBasics.mem_OC _).1 (x.untilt).2,
    fun c hc => ?_, fun x y => ?_, fun x => ?_⟩
  · obtain ⟨x, hx⟩ := GlobalTheory.MemLoc.FundOnto.untilt_surjective l ⟨c, (GlobalTheory.RingBasics.mem_OC c).2 hc⟩
    exact ⟨x, by simp [sh, hx]⟩
  · have hm : (x + y).untilt - x.untilt - y.untilt ∈ Ideal.span {(l : OC l)} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sub, PreTilt.mk_untilt_eq_coeff_zero,
        PreTilt.mk_untilt_eq_coeff_zero, PreTilt.mk_untilt_eq_coeff_zero, map_add]
      ring
    have := (GlobalTheory.RingBasics.mem_span_pow_OC 1 _).1 (by rw [pow_one]; exact hm)
    simpa [sh] using this
  · have h2 : sh (-x) ^ 2 = sh x ^ 2 := by rw [← hpow, ← hpow, neg_sq]
    have h3 : ‖sh (-x)‖ ^ 2 = ‖sh x‖ ^ 2 := by rw [← norm_pow, ← norm_pow, h2]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h3

end GlobalTheory.PSer.Laws
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUntiltToComplexPAdicBasicLawsStatement
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tiltUntiltToComplexPAdic_basic_laws : ∀ (l : ℕ) [Fact l.Prime], sh (1 : Fl l) = 1 ∧ sh (0 : Fl l) = 0 ∧ (∀ x y : Fl l, sh (x * y) = sh x * sh y) ∧ (∀ (x : Fl l) (n : ℕ), sh (x ^ n) = sh x ^ n) ∧ (∀ x : Fl l, ‖sh x‖ ≤ 1) ∧ (∀ c : ℂ_[l], ‖c‖ ≤ 1 → ∃ x : Fl l, sh x = c) ∧ (∀ x y : Fl l, ‖sh (x + y) - sh x - sh y‖ ≤ ‖(l : ℂ_[l])‖) ∧ (∀ x : Fl l, ‖sh (-x)‖ = ‖sh x‖) := by
  first | exact @GlobalTheory.PSer.Laws.sh_laws | exact GlobalTheory.PSer.Laws.sh_laws | (intros; apply GlobalTheory.PSer.Laws.sh_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankKsEq
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.HubLoc Module

namespace GlobalTheory.HubLoc

theorem finrank_Ks_eq : ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l) (s : ℕ), 0 < s → finrank ℚ_[l] ↥(Loc.Ks K s) = finrank ℚ_[l] ↥(Loc.K0 K) * (l ^ (s - 1) * (l - 1)) := by
  intro l _ K s hs
  rw [GlobalTheory.Cyc.finrank_Ks K s hs, mul_comm (l - 1)]

end GlobalTheory.HubLoc
end

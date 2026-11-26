module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemXSmulOfProjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleOfSurjective
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NearPiSepComplete

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DenseFrobeniusSplitPlaces
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual

namespace GlobalTheory.FrobDense

theorem conj_ne {R : Ranks} (H : Host R) :
    starRingEnd ℂ (Complex.I * (Real.sqrt H.d : ℂ)) ≠ Complex.I * (Real.sqrt H.d : ℂ) := by
  intro h
  have h1 := congrArg Complex.im h
  have : 0 < Real.sqrt H.d := Real.sqrt_pos.2 (by exact_mod_cast H.hyp.2.1.pos)
  simp at h1
  linarith

theorem sqrt_sq {R : Ranks} (H : Host R) : H.sqrtMinusD ^ 2 = -(H.d : H.E) := by
  have h0 : (Complex.I * (Real.sqrt H.d : ℂ)) ^ 2 = -(H.d : ℂ) := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp
  have h3 : H.φ₀ H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ) := H.φ₀_mem
  apply H.φ₀.injective
  rw [map_pow, h3, h0]
  simp

theorem exists_finite_split {R : Ranks} (H : Host R) :
    ∃ A : Set (HeightOneSpectrum (𝓞 H.E)), A.Finite ∧
    ∀ v, v ∉ A → v.asIdeal.inertiaDeg ℤ = 1 → IsSplitPl H v := by
  have hint : IsIntegral ℤ H.sqrtMinusD := by
    apply IsIntegral.of_pow (n := 2) (by norm_num)
    rw [sqrt_sq]
    have := (isIntegral_algebraMap (R := ℤ) (A := H.E) (x := (H.d : ℤ))).neg
    simpa using this
  let c : 𝓞 H.E →+* 𝓞 H.E := RingOfIntegers.mapRingHom (H.conj : H.E →+* H.E)
  let b : 𝓞 H.E := ⟨_, hint⟩
  have hb : c b - b ≠ 0 := by
    intro h
    have h1 : H.conj H.sqrtMinusD = H.sqrtMinusD := congrArg (fun y : 𝓞 H.E => (y : H.E)) (sub_eq_zero.1 h)
    have h2 := H.conjE_apply H.φ₀ H.sqrtMinusD
    have h3 : H.φ₀ H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ) := H.φ₀_mem
    have h4 : H.φ₀ (H.conj H.sqrtMinusD) = starRingEnd ℂ (H.φ₀ H.sqrtMinusD) := h2
    rw [h1, h3] at h4
    exact conj_ne H h4.symm
  refine ⟨{v | v.asIdeal ∣ Ideal.span {c b - b}},
    Ideal.finite_factors (by simpa [Ideal.span_singleton_eq_bot] using hb), fun v hv hd => ?_⟩
  by_contra hs
  apply hv
  have hp := ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified H.E).1 v).2 hd
  have hst : ∀ x ∈ v.asIdeal, c x ∈ v.asIdeal := by
    intro x hx
    by_contra hx'
    refine hs ⟨x, hx, fun y hy => ?_⟩
    have : y = c x := RingOfIntegers.ext hy
    rwa [this]
  have : Fact (Ideal.absNorm v.asIdeal).Prime := ⟨hp⟩
  have hcard : Nat.card (𝓞 H.E ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal :=
    (Ideal.absNorm_eq_natCard v.asIdeal).symm
  have := v.isPrime
  have htop : AddSubgroup.zmultiples (1 : 𝓞 H.E ⧸ v.asIdeal) = ⊤ :=
    zmultiples_eq_top_of_prime_card hcard one_ne_zero
  have hmem : Ideal.Quotient.mk v.asIdeal b ∈ AddSubgroup.zmultiples (1 : 𝓞 H.E ⧸ v.asIdeal) := by
    rw [htop]; trivial
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 hmem
  have h1 : b - (n : 𝓞 H.E) ∈ v.asIdeal := by
    rw [← Ideal.Quotient.eq, ← hn]; simp
  have h2 := hst _ h1
  rw [map_sub, map_intCast] at h2
  show v.asIdeal ∣ _
  rw [Ideal.dvd_span_singleton]
  have := v.asIdeal.sub_mem h2 h1
  simpa using this

end GlobalTheory.FrobDense
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntSubMem
open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.SplitFrobDense

theorem exists_conj_ne {R : Ranks} (H : Host R) :
    ∃ x y : 𝓞 H.E, (y : H.E) = H.conj (x : H.E) ∧ y - x ≠ 0 := by
  by_contra hc
  push Not at hc
  have h1 : ∀ x : 𝓞 H.E, H.conj (x : H.E) = x := fun x => by
    have := hc x ⟨H.conj x, (RingOfIntegers.isIntegral_coe x).map (H.conj.toAlgHom.restrictScalars ℤ)⟩ rfl
    exact congrArg (fun z : 𝓞 H.E => (z : H.E)) (sub_eq_zero.1 this)
  have h2 : ∀ z : H.E, H.conj z = z := fun z => by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 H.E) z
    rw [map_div₀]
    exact congrArg₂ (· / ·) (h1 a) (h1 b)
  have := H.isCMField_hostE
  refine IsTotallyComplex.complexEmbedding_not_isReal H.φ₀ (ComplexEmbedding.isReal_iff.2 ?_)
  ext z
  exact (H.conjE_apply H.φ₀ z).symm.trans (congrArg H.φ₀ (h2 z))

theorem exists_int_sub_mem {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E))
    (hv : v.asIdeal.inertiaDeg ℤ = 1) (x : 𝓞 E) : ∃ n : ℤ, x - n ∈ v.asIdeal := by
  have := v.isPrime
  have : NeZero v.asIdeal := ⟨v.ne_bot⟩
  have hp := Nat.absNorm_under_prime v.asIdeal
  have h := Ideal.absNorm_pow_inertiaDeg (v.asIdeal.under ℤ) v.asIdeal
  rw [hv, pow_one] at h
  rw [h] at hp
  have : Fact (Ideal.absNorm v.asIdeal).Prime := ⟨hp⟩
  have hc : Nat.card (𝓞 E ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal :=
    (Ideal.absNorm_eq_natCard v.asIdeal).symm
  have : Nontrivial (𝓞 E ⧸ v.asIdeal) := Ideal.Quotient.nontrivial_iff.2 v.isPrime.ne_top
  have hm := mem_zmultiples_of_prime_card hc (g := (1 : 𝓞 E ⧸ v.asIdeal)) (g' := Ideal.Quotient.mk _ x)
    one_ne_zero
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 hm
  refine ⟨n, Ideal.Quotient.eq.1 ?_⟩
  rw [← hn]
  simp

theorem frobDense : ∀ D : D7, GlobalTheory.TwSys.Cheb → FrobDense D := by
  classical
  intro D hC T hT
  rw [dense_iff_inter_open]
  rintro V hV ⟨g, hg⟩
  have : IsGalois D.host.E D.nd.Om := {}
  have hn : (fun u : G D.host.E D.nd.Om => u * g) ⁻¹' V ∈ nhds (1 : G D.host.E D.nd.Om) :=
    (hV.preimage (continuous_mul_const g)).mem_nhds (by simpa using hg)
  obtain ⟨L, hfd, hN, hL⟩ := (krullTopology_mem_nhds_one_iff_of_normal D.host.E D.nd.Om _).1 hn
  have hgal : IsGalois D.host.E L := {}
  obtain ⟨x, y, hxy, hne⟩ := exists_conj_ne D.host
  have f1 : {v : PlE D.host | v.asIdeal ∣ Ideal.span {y - x}}.Finite :=
    Ideal.finite_factors (by simpa using hne)
  obtain ⟨v, hv, hf, -, B, hB, -, σ, hσ, hU⟩ := hC D.host.E D.nd.Om L.fixingSubgroup L.fixingSubgroup_isOpen
    ((InfiniteGalois.normal_iff_isGalois L).2 hgal) g (f1.toFinset ∪ hT.toFinset)
  simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton,
    not_or] at hv
  obtain ⟨h1, h2⟩ := hv
  obtain ⟨n, hx⟩ := exists_int_sub_mem v hf x
  have hsplit : IsSplitPl D.host v := by
    refine ⟨x - n, hx, fun z hz hzv => h1 ?_⟩
    have hz' : z = y - n := by
      apply RingOfIntegers.ext
      rw [hz]
      simp [hxy]
    have := v.asIdeal.sub_mem hzv hx
    rwa [hz', sub_sub_sub_cancel_right] at this
  have := hL hU
  simp only [Set.mem_preimage, inv_mul_cancel_right] at this
  exact ⟨σ, this, v, h2, hsplit, B, hB, hσ⟩

end GlobalTheory.SplitFrobDense
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WildEqOneOfCharpolyUnipotentModL
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WildEqOneOfCharpolyUnipotentModL
open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.WildKill

theorem not_lt_one_of_coprime {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {a b : ℕ} (hab : a.Coprime b)
    (hb : A.valuation (b : Ω) < 1) : ¬ A.valuation (a : Ω) < 1 := by
  intro ha
  obtain ⟨u, v, huv⟩ : IsCoprime (a : ℤ) (b : ℤ) := Nat.isCoprime_iff_coprime.2 hab
  have h1 : (u : Ω) * (a : Ω) + (v : Ω) * (b : Ω) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) huv
  have hu : ∀ w : ℤ, A.valuation (w : Ω) ≤ 1 := fun w => (A.valuation_le_one_iff _).2 (intCast_mem A w)
  have h2 : A.valuation ((u : Ω) * (a : Ω) + (v : Ω) * (b : Ω)) < 1 := by
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hu u)) ha
    · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hu v)) hb
  rw [h1, map_one] at h2
  exact lt_irrefl _ h2

theorem mem_of_wild {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (H : Subgroup (G E Ω)) (ho : IsOpen (H : Set (G E Ω))) (σ : G E Ω) (n : ℕ)
    (hn : ¬ A.valuation (n : Ω) < 1) (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) (hH : σ ^ n ∈ H) :
    σ ∈ H := by
  have : IsGalois E Ω := {}
  let C : ClosedSubgroup (G E Ω) := ⟨H, H.isClosed_of_isOpen ho⟩
  have hC : (IntermediateField.fixedField H).fixingSubgroup = H :=
    InfiniteGalois.fixingSubgroup_fixedField C
  rw [← hC, IntermediateField.mem_fixingSubgroup_iff]
  intro y hy
  have hy' : (σ ^ n) y = y := (IntermediateField.mem_fixedField_iff H y).1 hy _ hH
  by_contra hne
  have hx : σ y - y ≠ 0 := sub_ne_zero.2 hne
  have hsum : ∑ i ∈ Finset.range n, (σ ^ i) (σ y - y) = 0 := by
    have : ∀ i, (σ ^ i) (σ y - y) = (σ ^ (i + 1)) y - (σ ^ i) y := by
      intro i
      rw [map_sub, pow_succ, AlgEquiv.mul_apply]
    simp_rw [this]
    rw [Finset.sum_range_sub (fun i => (σ ^ i) y), hy']
    simp
  have hlt : A.valuation (∑ i ∈ Finset.range n, ((σ ^ i) (σ y - y) / (σ y - y) - 1)) < 1 :=
    Valuation.map_sum_lt _ one_ne_zero fun i _ =>
      GlobalTheory.valuation_pow_apply_div_sub_one_lt A σ hσ _ hx i
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, hsum] at hlt
  apply hn
  simpa using hlt

theorem eq_one_of_wild_of_unipotent :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (g l n : ℕ) [Fact g.Prime] [Fact l.Prime], l ≠ g → A.valuation (g : Ω) < 1 → ∀ (K : Type) [Field K] [CharP K l] (rb : G E Ω →* GL (Fin n) K), IsOpen (rb.ker : Set (G E Ω)) → ∀ s : G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (s y / y - 1) < 1) → ((rb s : GL _ _) : Matrix (Fin n) (Fin n) K).charpoly = (X - 1) ^ n → rb s = 1 := by
  intro E Ω _ _ _ _ _ A g l n hg hl hne hA K _ _ rb ho s hs hc
  refine mem_of_wild A rb.ker ho s (l ^ n)
    (not_lt_one_of_coprime A (Nat.Coprime.pow_left n ((Nat.coprime_primes hl.out hg.out).2 hne)) hA) hs ?_
  rw [MonoidHom.mem_ker, map_pow, Units.ext_iff, Units.val_pow_eq_pow_val]
  exact GlobalTheory.TameLabels.pow_eq_one_of_charpoly _ hc

end GlobalTheory.WildKill
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WildEqOneOfCharpolyUnipotentModLStatement
open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wild_eq_one_of_charpoly_unipotent_mod_l : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (g l n : ℕ) [Fact g.Prime] [Fact l.Prime], l ≠ g → A.valuation (g : Ω) < 1 → ∀ (K : Type) [Field K] [CharP K l] (rb : G E Ω →* GL (Fin n) K), IsOpen (rb.ker : Set (G E Ω)) → ∀ s : G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (s y / y - 1) < 1) → ((rb s : GL _ _) : Matrix (Fin n) (Fin n) K).charpoly = (X - 1) ^ n → rb s = 1 := by
  first | exact @GlobalTheory.WildKill.eq_one_of_wild_of_unipotent | exact GlobalTheory.WildKill.eq_one_of_wild_of_unipotent | (intros; apply GlobalTheory.WildKill.eq_one_of_wild_of_unipotent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeFreeOfCrystalline
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeFreeOfCrystalline
open PowerSeries Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.HWL

theorem _root_.GlobalTheory.HWL.mem_smul_of_projective_comp {D A M : Type} [CommRing D] [IsDomain D] [CommRing A]
    [AddCommGroup M] [Module A M] (f : D⟦X⟧ →+* A)
    (hp : @Module.Projective D⟦X⟧ _ M _ (Module.compHom _ f)) (c : D) (hc : c ≠ 0) {a b : A}
    (ha : f (C c) = a) (hb : f X = b) (x y : M) (h : a • x = b • y) : ∃ z : M, x = b • z := by
  letI : Module D⟦X⟧ M := Module.compHom M f
  obtain ⟨z, hz⟩ := _root_.GlobalTheory.WachFree.mem_X_smul_of_projective c hc x y (by
    change f (C c) • x = f X • y
    rw [ha, hb]
    exact h)
  refine ⟨z, ?_⟩
  rw [hz]
  change f X • z = b • z
  rw [hb]

private theorem isSMulRegular_of_projective_powerSeries_comp_lemma {D A M : Type} [CommRing D]
    [IsDomain D] [CommRing A] [AddCommGroup M] [Module A M] (f : D⟦X⟧ →+* A)
    (hp : @Module.Projective D⟦X⟧ _ M _ (Module.compHom _ f)) {b : A} (hb : f X = b) :
    IsSMulRegular M b := by
  letI : Module D⟦X⟧ M := Module.compHom M f
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (R := D⟦X⟧) (M := M)
    (mem_nonZeroDivisors_of_ne_zero (X_ne_zero : (X : D⟦X⟧) ≠ 0))
  intro x y h
  apply hreg
  change f X • x = f X • y
  rw [hb]
  exact h

set_option maxHeartbeats 8000000 in
theorem _root_.GlobalTheory.HWL.lattice_free : ∀ (l : ℕ) [Fact l.Prime] (P : _root_.Formalism.BasicNotions.LocPrime l) (AI : _root_.Formalism.BasicNotions.LocAinf l P) (K : _root_.Formalism.BasicNotions.Loc.FinExt l) (s : ℕ) (LL : _root_.Formalism.BasicNotions.Loc.FinExt l), _root_.Formalism.BasicNotions.Loc.Good K s LL → ∀ (Γ : _root_.GlobalTheory.HWL.GamS P K s LL) (R : _root_.GlobalTheory.HWL.WSer Γ) (I : _root_.GlobalTheory.HWL.IoS AI R), _root_.GlobalTheory.HWL.IoW I → ∀ (E : _root_.GlobalTheory.HWL.WEt I) (Mo : _root_.GlobalTheory.HWL.NS E) (T : _root_.Formalism.BasicNotions.LocLat ↥(_root_.Formalism.BasicNotions.Loc.GK K) ℚ_[l] ↥LL.1 ↥(_root_.Formalism.BasicNotions.Loc.OL LL)), _root_.Formalism.WeaklyAdmissibleFiltrations.IsCrys (P.PD K) T.ρ → Nonempty (Module.Basis (Fin (Module.finrank ↥(_root_.Formalism.BasicNotions.Loc.OL LL) ↥T.L.T)) (_root_.Formalism.BasicNotions.LetA ↥(_root_.Formalism.BasicNotions.Loc.OL LL) (Module.finrank ℚ_[l] ↥(_root_.Formalism.BasicNotions.Loc.K0 K))) ↥(Mo.N T)) := by
  set_option synthInstance.maxHeartbeats 400000 in
    intro l _ P AI K s LL _ Γ R I _ E Mo T hc
    obtain ⟨_, -, hl⟩ := _root_.GlobalTheory.FinExtIntegers.dvr_complete LL
    have hfree := E.DD_free T
    haveI := hfree.1
    haveI : FiniteDimensional ℚ_[l] ↥(_root_.Formalism.BasicNotions.Loc.K0 K) := by
      haveI := K.2
      have hle : _root_.Formalism.BasicNotions.Loc.K0 K ≤ ↑K := inf_le_left
      exact Module.Finite.of_injective (IntermediateField.inclusion hle).toLinearMap
        (IntermediateField.inclusion hle).toRingHom.injective
    haveI : NeZero (Module.finrank ℚ_[l] ↥(_root_.Formalism.BasicNotions.Loc.K0 K)) := ⟨Module.finrank_pos.ne'⟩
    haveI : Module.Finite _ (Mo.N T) :=
      Module.Finite.iff_fg.mpr (Mo.N_fg T)
    have hl0 : (l : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
    have hzX : _root_.Formalism.BasicNotions.Loc.zlA LL (Module.finrank ℚ_[l] ↥(_root_.Formalism.BasicNotions.Loc.K0 K)) X = fun _ => X := by
      ext1; simp [_root_.Formalism.BasicNotions.Loc.zlA]
    have hzC : _root_.Formalism.BasicNotions.Loc.zlA LL (Module.finrank ℚ_[l] ↥(_root_.Formalism.BasicNotions.Loc.K0 K)) (C (l : ℤ_[l])) =
        fun _ => C (l : _root_.Formalism.BasicNotions.Loc.OL LL) := by
      ext1; simp [_root_.Formalism.BasicNotions.Loc.zlA]
    have key := _root_.GlobalTheory.WachFree.basis_of_regular
      (ι := ZMod (Module.finrank ℚ_[l] ↥(_root_.Formalism.BasicNotions.Loc.K0 K)))
      (O := ↥(_root_.Formalism.BasicNotions.Loc.OL LL))
      (N := ↥(Mo.N T)) (E := R.EE) (D := E.DD T) R.EE_inj
      (Mo.N T).subtype (Mo.N_base T hc) (l : _root_.Formalism.BasicNotions.Loc.OL LL) ?_ hl ?_ ?_
    · rwa [hfree.2] at key
    · intro h0
      haveI : CharZero ↥LL.1 :=
        charZero_of_injective_algebraMap (algebraMap ℚ_[l] ↥LL.1).injective
      have hcast : ((l : _root_.Formalism.BasicNotions.Loc.OL LL) : ↥LL.1) = 0 := by rw [h0]; rfl
      push_cast at hcast
      exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast hcast)
    · exact isSMulRegular_of_projective_powerSeries_comp_lemma _ (Mo.N_proj T) hzX
    · intro x y h
      exact _root_.GlobalTheory.HWL.mem_smul_of_projective_comp (_root_.Formalism.BasicNotions.Loc.zlA LL _) (Mo.N_proj T)
        (l : ℤ_[l]) hl0 hzC hzX x y h

end GlobalTheory.HWL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeFreeOfCrystallineStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wach_lattice_free_of_crystalline : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ (E : WEt I) (Mo : NS E) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys (P.PD K) T.ρ → Nonempty (Module.Basis (Fin (Module.finrank ↥(OL LL) ↥T.L.T)) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥(Mo.N T)) := by
  first | exact @GlobalTheory.HWL.lattice_free | exact GlobalTheory.HWL.lattice_free | (intros; apply GlobalTheory.HWL.lattice_free <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalExactSequenceContinuityAllTheories
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage Filter Topology

namespace GlobalTheory.FundCont

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)

theorem l_ne : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero

theorem small_mul_mem (T : LocTied l P AI) {M n k : ℕ} {c : ℚ_[l]} {b : P.R.BdR}
    (hc : ‖c‖ ≤ (l : ℝ) ^ (-(k : ℤ))) (hb : (l : P.R.BdR) ^ k * b ∈ Lat AI M n) :
    qB P c * b ∈ Lat AI M n := by
  have h0 : (0 : ℝ) < (l : ℝ) ^ (-(k : ℤ)) := by
    have := (Fact.out : l.Prime).pos
    positivity
  have hz : ‖c / (l : ℚ_[l]) ^ k‖ ≤ 1 := by
    rw [norm_div, Padic.norm_p_pow, div_le_one h0]
    exact hc
  have := qB_mul_mem_Lat AI T ⟨_, hz⟩ hb
  convert this using 1
  rw [← mul_assoc, ← map_natCast (qB P), ← map_pow, ← map_mul]
  congr 2
  exact (div_mul_cancel₀ _ (pow_ne_zero _ l_ne)).symm

theorem large_mul_mem (T : LocTied l P AI) {M n k : ℕ} {c : ℚ_[l]} {b : P.R.BdR}
    (hc : ‖(l : ℚ_[l]) ^ k * c‖ ≤ 1) (hb : b ∈ Lat AI M (k + n)) :
    qB P c * b ∈ Lat AI M n := by
  rw [← pow_mul_mem_Lat_iff AI (k := k)]
  have := qB_mul_mem_Lat AI T ⟨_, hc⟩ hb
  convert this using 1
  simp only [map_mul, map_pow, map_natCast, mul_assoc]

theorem exists_pow_lt {ε : ℝ} (hε : 0 < ε) : ∃ k : ℕ, (l : ℝ) ^ (-(k : ℤ)) < ε :=
  PadicInt.exists_pow_neg_lt l hε

theorem exists_mul_le_one (c : ℚ_[l]) : ∃ k : ℕ, ‖(l : ℚ_[l]) ^ k * c‖ ≤ 1 := by
  obtain ⟨k, hk⟩ := exists_pow_lt (l := l) (ε := (‖c‖ + 1)⁻¹) (by positivity)
  refine ⟨k, ?_⟩
  rw [norm_mul, Padic.norm_p_pow]
  calc _ ≤ (‖c‖ + 1)⁻¹ * (‖c‖ + 1) := by gcongr; linarith
    _ = 1 := inv_mul_cancel₀ (by positivity)

variable {X : Type} [TopologicalSpace X]

theorem eventually_orbit (T : LocTied l P AI) {b : P.R.BdR} (hb : b ∈ FilB P 0) (M n : ℕ)
    {c : X → ℚ_[l]} (hc : Continuous c) {γ : X → GQ l} (hγ : Continuous γ) (x₀ : X) :
    ∀ᶠ x in 𝓝 x₀, qB P (c x) * P.actQdR (γ x) b - qB P (c x₀) * P.actQdR (γ x₀) b ∈ Lat AI M n := by
  obtain ⟨⟨k, hk⟩, -⟩ := bounded_and_eventually_sub_mem_Lat l P AI T b hb M n
  obtain ⟨j, hj⟩ := exists_mul_le_one (c x₀)
  obtain ⟨-, he⟩ := bounded_and_eventually_sub_mem_Lat l P AI T b hb M (j + n)
  have h0 : (0 : ℝ) < (l : ℝ) ^ (-(k : ℤ)) := by
    have := (Fact.out : l.Prime).pos
    positivity
  have t1 : Tendsto (fun x => (γ x₀)⁻¹ * γ x) (𝓝 x₀) (𝓝 1) := by
    have : Continuous fun x => (γ x₀)⁻¹ * γ x := continuous_const.mul hγ
    simpa using this.tendsto x₀
  filter_upwards [t1.eventually he, Metric.tendsto_nhds.1 (hc.tendsto x₀) _ h0] with x h1 h2
  rw [dist_eq_norm] at h2
  have h3 := act_mem_Lat AI (γ x) hk
  rw [map_mul, map_pow, map_natCast] at h3
  have h4 := small_mul_mem AI T h2.le h3
  have h5 := act_mem_Lat AI (γ x₀) h1
  rw [map_sub, ← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel_left] at h5
  have h6 := large_mul_mem AI T hj h5
  convert add_mem h4 h6 using 1
  rw [map_sub]
  ring

def LatCont (h : X → P.R.BdR) : Prop :=
  ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (n : ℕ) (x₀ : X), ∀ᶠ x in 𝓝 x₀, tD P ^ N * (h x - h x₀) ∈ Lat AI (N + 1) n

theorem latCont_const (b : P.R.BdR) : LatCont AI (fun _ : X => b) :=
  ⟨0, fun N _ n x₀ => Eventually.of_forall fun x => by simp⟩

theorem LatCont.add {h h' : X → P.R.BdR} (H : LatCont AI h) (H' : LatCont AI h') :
    LatCont AI (fun x => h x + h' x) := by
  obtain ⟨N₀, H⟩ := H
  obtain ⟨N₁, H'⟩ := H'
  refine ⟨max N₀ N₁, fun N hN n x₀ => ?_⟩
  filter_upwards [H N (le_of_max_le_left hN) n x₀, H' N (le_of_max_le_right hN) n x₀] with x a b
  convert add_mem a b using 1
  ring

theorem LatCont.sum {ι : Type} (s : Finset ι) (h : ι → X → P.R.BdR) (H : ∀ i, LatCont AI (h i)) :
    LatCont AI (fun x => ∑ i ∈ s, h i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using latCont_const AI 0
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (H i).add AI ih

theorem continuous_chi : Continuous fun g : GQ l => (P.χQ g : ℚ_[l]) := by
  obtain ⟨χ, h1, h2, -⟩ := exists_integral_cyclotomicChar l P
  simp only [← h1]
  have h3 : Continuous fun g => (χ g : ℤ_[l]) := Units.continuous_val.comp h2
  exact continuous_subtype_val.comp h3

theorem latCont_orbit (T : LocTied l P AI) (b : P.R.BdR)
    {c : X → ℚ_[l]} (hc : Continuous c) {γ : X → GQ l} (hγ : Continuous γ) :
    LatCont AI (fun x => qB P (c x) * P.actQdR (γ x) b) := by
  obtain ⟨a, ha⟩ := (P.PD (botExt l)).Fil_exh b
  refine ⟨(-a).toNat, fun N hN n x₀ => ?_⟩
  have hb : tD P ^ N * b ∈ FilB P 0 :=
    FilB_anti (by omega) (FilB_mul (FilB_pow tD_mem N) ha)
  have hc' : Continuous fun x => c x * ((P.χQ (γ x) : ℚ_[l]) ^ N)⁻¹ :=
    hc.mul (((continuous_chi.comp hγ).pow N).inv₀ fun x => pow_ne_zero _ (Units.ne_zero _))
  have e : ∀ x, qB P (c x * ((P.χQ (γ x) : ℚ_[l]) ^ N)⁻¹) * P.actQdR (γ x) (tD P ^ N * b) =
      tD P ^ N * (qB P (c x) * P.actQdR (γ x) b) := by
    intro x
    have h1 : qB P ((P.χQ (γ x) : ℚ_[l]) ^ N)⁻¹ * qB P (P.χQ (γ x) : ℚ_[l]) ^ N = 1 := by
      rw [← map_pow, ← map_mul, inv_mul_cancel₀ (pow_ne_zero _ (Units.ne_zero _)), map_one]
    rw [map_mul, map_mul, map_pow, act_tD, mul_pow]
    linear_combination (tD P ^ N * (qB P (c x) * P.actQdR (γ x) b)) * h1
  filter_upwards [eventually_orbit AI T hb (N + 1) n hc' hγ x₀] with x hx
  rwa [e, e, ← mul_sub] at hx

theorem tD_pow_not_mem (T : LocTied l P AI) (N : ℕ) : tD P ^ N ∉ FilB P ((N : ℤ) + 1) := by
  have hu : IsUnit (tD P) := by
    have := (P.PD (botExt l)).t_unit
    rw [P.period_datum_t_eq] at this
    exact this.map P.ιB
  induction N with
  | zero =>
    intro h
    apply (P.PD (botExt l)).not_mem_filtration_two
    rw [P.PD_ι, P.period_datum_t_eq]
    simpa using FilB_mul (tD_mem (P := P)) h
  | succ N ih =>
    intro h
    obtain ⟨y, hy, e⟩ := ((GlobalTheory.MemLoc.TiedUnif.tied_uniformiser l P AI T).2.2 (botExt l) _ _).1 h
    rw [pow_succ'] at e
    apply ih
    rw [hu.mul_left_cancel e]
    exact_mod_cast hy

theorem continuous_of_latCont (T : LocTied l P AI) {c : X → ℚ_[l]}
    (H : LatCont AI (fun x => qB P (c x))) : Continuous c := by
  obtain ⟨N, H⟩ := H
  obtain ⟨n, hn⟩ : ∃ n, tD P ^ N ∉ Lat AI (N + 1) n := by
    by_contra h
    push Not at h
    exact tD_pow_not_mem AI T N (by exact_mod_cast mem_FilB_of_forall_Lat l P AI T (N + 1) _ h)
  refine continuous_iff_continuousAt.2 fun x₀ => Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨k, hk⟩ := exists_pow_lt (l := l) hε
  filter_upwards [H N le_rfl (k + n) x₀] with x hx
  rw [dist_eq_norm]
  by_contra hlt
  push Not at hlt
  have h0 : 0 < ‖c x - c x₀‖ := hε.trans_le hlt
  apply hn
  have := large_mul_mem AI T (c := (c x - c x₀)⁻¹) (by
    rw [norm_mul, Padic.norm_p_pow, norm_inv, ← div_eq_mul_inv, div_le_one h0]
    exact hk.le.trans hlt) hx
  rwa [← map_sub, mul_left_comm, ← map_mul, inv_mul_cancel₀ (norm_pos_iff.1 h0), map_one,
    mul_one] at this

theorem contCore_of_tied (T : LocTied l P AI) (K : FinExt l) : contCore (P.PD K) := by
  intro LL _ _ _ O _ _ hO A k x β hβ x' f hf
  obtain ⟨-, hfd, hmt, htr, -⟩ := hO
  have hLL : ∀ (φ : A.V →ₗ[ℚ_[l]] ℚ_[l]) (v : A.V), Continuous fun c : LL => φ (c • v) := fun φ v =>
    IsModuleTopology.continuous_of_linearMap
      (φ ∘ₗ (LinearMap.toSpanSingleton LL A.V v).restrictScalars ℚ_[l])
  have hV : ∀ φ : A.V →ₗ[ℚ_[l]] ℚ_[l], Continuous φ := by
    intro φ
    let b := Module.finBasis LL A.V
    have : (φ : A.V → ℚ_[l]) = fun v => ∑ j, φ (b.coord j v • b j) := by
      funext v
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum]
      simp [b.sum_repr]
    rw [this]
    exact continuous_finsetSum _ fun j _ =>
      (hLL φ (b j)).comp (IsModuleTopology.continuous_of_linearMap (b.coord j))
  have key : ∀ φ : A.V →ₗ[ℚ_[l]] ℚ_[l], Continuous fun g => φ (f g) := by
    intro φ
    let Φ : A.V ⊗[ℚ_[l]] P.R.B →ₗ[ℚ_[l]] P.R.BdR :=
      (TensorProduct.lid ℚ_[l] P.R.BdR).toLinearMap ∘ₗ TensorProduct.map φ P.ιB.toLinearMap
    have hΦ : ∀ v b, Φ (v ⊗ₜ b) = qB P (φ v) * P.ιB b := by
      intro v b
      simp [Φ, Algebra.smul_def]
    have h1 : ∀ (y : A.V ⊗[ℚ_[l]] P.R.B) (i : Fin k), LatCont AI fun g => Φ (β i g • y) := by
      intro y i
      induction y using TensorProduct.induction_on with
      | zero => simpa using latCont_const AI 0
      | tmul v b =>
        simp only [TensorProduct.smul_tmul', hΦ]
        simpa using latCont_orbit AI T (P.ιB b) ((hLL φ v).comp (hβ i))
          (γ := fun _ => 1) continuous_const
      | add y y' ih ih' =>
        simp only [smul_add, map_add (f := _)]
        exact ih.add AI ih'
    have h2 : ∀ y : A.V ⊗[ℚ_[l]] P.R.B, LatCont AI fun g => Φ (actVB (P.PD K) A.ρ g y) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simpa using latCont_const AI 0
      | tmul v b =>
        have e : ∀ g : ↥(GK K), Φ (actVB (P.PD K) A.ρ g (v ⊗ₜ b)) =
            qB P (φ (A.ρ g v)) * P.actQdR (g : GQ l) (P.ιB b) := by
          intro g
          rw [← ιB_act, ← hΦ, ← P.PD_actB]
          rfl
        simp only [e]
        exact latCont_orbit AI T (P.ιB b) ((hV φ).comp (A.cont v)) continuous_subtype_val
      | add y y' ih ih' =>
        simp only [map_add (f := _)]
        exact ih.add AI ih'
    apply continuous_of_latCont AI T
    have e : ∀ g, qB P (φ (f g)) =
        ∑ i, Φ (β i g • x i) + (Φ (actVB (P.PD K) A.ρ g x') + -Φ x') := by
      intro g
      have := congrArg Φ (hf g)
      rwa [hΦ, map_one, mul_one, map_add, map_sum, map_sub, sub_eq_add_neg] at this
    simp only [e]
    exact (LatCont.sum AI _ _ fun i => h1 (x i) i).add AI ((h2 x').add AI (latCont_const AI _))
  haveI : Module.Finite ℚ_[l] A.V := Module.Finite.trans LL A.V
  let b := Module.finBasis ℚ_[l] A.V
  have : f = fun g => ∑ j, algebraMap ℚ_[l] LL (b.coord j (f g)) • b j := by
    funext g
    simp [b.sum_repr]
  rw [this]
  haveI : ContinuousSMul LL A.V := IsModuleTopology.toContinuousSMul LL A.V
  haveI : ContinuousSMul ℚ_[l] LL := IsModuleTopology.toContinuousSMul ℚ_[l] LL
  exact continuous_finsetSum _ fun j _ =>
    ((continuous_algebraMap ℚ_[l] LL).comp (key (b.coord j))).smul continuous_const

theorem fundamentalExactSequence_continuity_all_theories : ∀ D : D7, Formalism.MainNotions.LocalSituation.adm6 D := fun D l _ K =>
  contCore_of_tied (D.locA l) (D.locT l) K

end GlobalTheory.FundCont
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicIntegersFiniteExtGoodCoefficientRing
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicIntegersFiniteExtGoodCoefficientRing
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.LitGood

theorem litGoodO : LitGoodO :=
  fun l _ LL => GlobalTheory.Pass.goodO_ringOfIntegers l LL

end GlobalTheory.LitGood
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicIntegersFiniteExtGoodCoefficientRingStatement
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicIntegers_finiteExt_goodCoefficientRing : LitGoodO := by
  first | exact @GlobalTheory.LitGood.litGoodO | exact GlobalTheory.LitGood.litGoodO | (intros; apply GlobalTheory.LitGood.litGoodO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WildLowerRamificationGroupAntitoneEventuallyBot
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WildLowerRamificationGroupAntitoneEventuallyBot
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem wild_antitone_and_eventually_bot :
    ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L], Antitone (wild K L) ∧ ∃ m, wild K L m = ⊥ := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ _
  refine ⟨fun i j hij ↦ ?_, ?_⟩
  · exact lowerRamificationGroup_antitone K L (by simp only [add_le_add_iff_right, Nat.cast_le]; exact hij)
  · obtain ⟨n, hn⟩ := exists_lowerRamificationGroup_eq_bot K L
    exact ⟨n, hn _ (by omega)⟩

end GlobalTheory.PMon.Ram
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WildLowerRamificationGroupAntitoneEventuallyBotStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wildLowerRamificationGroup_antitone_eventually_bot : ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L], Antitone (wild K L) ∧ ∃ m, wild K L m = ⊥ := by
  first | exact @GlobalTheory.PMon.Ram.wild_antitone_and_eventually_bot | exact GlobalTheory.PMon.Ram.wild_antitone_and_eventually_bot | (intros; apply GlobalTheory.PMon.Ram.wild_antitone_and_eventually_bot <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisGroupFixedFieldBaseChangeLocalField
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisGroupFixedFieldBaseChangeLocalField
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem baseChange_fixedField :
    ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] (A : Subgroup (L ≃ₐ[K] L)), ∃ j : (L ≃ₐ[↥(IntermediateField.fixedField A)] L) →* (L ≃ₐ[K] L), Function.Injective j ∧ j.range = A ∧ (∀ σ x, j σ x = σ x) ∧ ∀ i : ℤ, lowerRamificationGroup ↥(IntermediateField.fixedField A) L i = (lowerRamificationGroup K L i).comap j := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ _ A
  refine ⟨AlgEquiv.restrictScalarsHom K, AlgEquiv.restrictScalarsHom_injective K, ?_, ?_, ?_⟩
  · rw [GroundTheory.LocalField.range_restrictScalarsHom, IntermediateField.fixingSubgroup_fixedField]
  · intro σ x
    rfl
  · intro i
    exact (lowerRamificationGroup_comap_restrictScalars (IntermediateField.fixedField A) i).symm

end GlobalTheory.PMon.Ram
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisGroupFixedFieldBaseChangeLocalFieldStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisGroup_fixedField_baseChange_localField : ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] (A : Subgroup (L ≃ₐ[K] L)), ∃ j : (L ≃ₐ[↥(IntermediateField.fixedField A)] L) →* (L ≃ₐ[K] L), Function.Injective j ∧ j.range = A ∧ (∀ σ x, j σ x = σ x) ∧ ∀ i : ℤ, lowerRamificationGroup ↥(IntermediateField.fixedField A) L i = (lowerRamificationGroup K L i).comap j := by
  first | exact @GlobalTheory.PMon.Ram.baseChange_fixedField | exact GlobalTheory.PMon.Ram.baseChange_fixedField | (intros; apply GlobalTheory.PMon.Ram.baseChange_fixedField <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInitialSegmentNotInfLeFiltration
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInitialSegmentNotInfLeFiltration
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem exists_initialSegment_not_inf_le :
    ∀ (G : Type) [Group G] (R : ℕ → Subgroup G) (A B : Subgroup G), Antitone R →
      (∃ m, R m = ⊥) → ∃ n : ℕ, ∀ t, t < n ↔ ¬ A ⊓ R t ≤ B := by
  intro G _ R A B hR hm
  classical
  obtain ⟨m, hm⟩ := hm
  have h : ∃ t, A ⊓ R t ≤ B := ⟨m, by rw [hm]; simp⟩
  refine ⟨Nat.find h, fun t => ⟨fun ht => Nat.find_min h ht, fun hn => ?_⟩⟩
  by_contra hc
  push_neg at hc
  exact hn (le_trans (inf_le_inf_left A (hR hc)) (Nat.find_spec h))

end GlobalTheory.PMon.Ram
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInitialSegmentNotInfLeFiltrationStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_initialSegment_not_inf_le_filtration : ∀ (G : Type) [Group G] (R : ℕ → Subgroup G) (A B : Subgroup G), Antitone R → (∃ m, R m = ⊥) → ∃ n : ℕ, ∀ t, t < n ↔ ¬ A ⊓ R t ≤ B := by
  first | exact @GlobalTheory.PMon.Ram.exists_initialSegment_not_inf_le | exact GlobalTheory.PMon.Ram.exists_initialSegment_not_inf_le | (intros; apply GlobalTheory.PMon.Ram.exists_initialSegment_not_inf_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationJumpSumEqSumRange
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationJumpSumEqSumRange
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem jumpSum_eq_sum_range : ∀ (G : Type) [Group G] (R : ℕ → Subgroup G) (A B : Subgroup G) (n : ℕ), Antitone R →
    (∀ t, t < n ↔ ¬ A ⊓ R t ≤ B) → jumpSum R A B = ∑ t ∈ Finset.range n, Nat.card ↥(A ⊓ R t) := by
  intro G _ R A B n _ h
  classical
  unfold jumpSum
  rw [finsum_eq_sum_of_support_subset (s := Finset.range n)]
  · refine Finset.sum_congr rfl fun t ht => ?_
    rw [if_neg ((h t).1 (Finset.mem_range.1 ht))]
  · intro t ht
    rw [Function.mem_support] at ht
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hn
    exact ht (if_pos (not_not.1 (mt (h t).2 hn)))

end GlobalTheory.PMon.Ram
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationJumpSumEqSumRangeStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramificationJumpSum_eq_sum_range : ∀ (G : Type) [Group G] (R : ℕ → Subgroup G) (A B : Subgroup G) (n : ℕ), Antitone R → (∀ t, t < n ↔ ¬ A ⊓ R t ≤ B) → jumpSum R A B = ∑ t ∈ Finset.range n, Nat.card ↥(A ⊓ R t) := by
  first | exact @GlobalTheory.PMon.Ram.jumpSum_eq_sum_range | exact GlobalTheory.PMon.Ram.jumpSum_eq_sum_range | (intros; apply GlobalTheory.PMon.Ram.jumpSum_eq_sum_range <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationJumpSumComapInjective
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationJumpSumComapInjective
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem jumpSum_comap_injective :
    ∀ (G G' : Type) [Group G] [Group G'] (j : G' →* G) (R : ℕ → Subgroup G) (B : Subgroup G), Function.Injective j →
      jumpSum (fun t => (R t).comap j) ⊤ (B.comap j) = jumpSum R j.range B := by
  intro G G' _ _ j R B hj
  unfold jumpSum
  apply finsum_congr
  intro t
  have h1 : (⊤ ⊓ (R t).comap j ≤ B.comap j) ↔ (j.range ⊓ R t ≤ B) := by
    rw [top_inf_eq]
    constructor
    · rintro h x ⟨⟨y, rfl⟩, hy⟩
      exact h (show y ∈ (R t).comap j from hy)
    · intro h y hy
      exact h ⟨⟨y, rfl⟩, hy⟩
  have h2 : Nat.card ↥(⊤ ⊓ (R t).comap j) = Nat.card ↥(j.range ⊓ R t) := by
    rw [top_inf_eq, ← Subgroup.map_comap_eq, Subgroup.card_map_of_injective hj]
  rw [h2]
  by_cases h : j.range ⊓ R t ≤ B
  · rw [if_pos (h1.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (h1.mp h')), if_neg h]

end GlobalTheory.PMon.Ram
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationJumpSumComapInjectiveStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramificationJumpSum_comap_injective : ∀ (G G' : Type) [Group G] [Group G'] (j : G' →* G) (R : ℕ → Subgroup G) (B : Subgroup G), Function.Injective j → jumpSum (fun t => (R t).comap j) ⊤ (B.comap j) = jumpSum R j.range B := by
  first | exact @GlobalTheory.PMon.Ram.jumpSum_comap_injective | exact GlobalTheory.PMon.Ram.jumpSum_comap_injective | (intros; apply GlobalTheory.PMon.Ram.jumpSum_comap_injective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitVectorOfUnitFor
noncomputable section

namespace GlobalTheory.WachUnit

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

theorem unitVector_of_unitFor (E : EtTie W RA RW inclR φR gR πA)
    (hU : GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts.UnitFor E) :
    ∃ (e : W.DD W.one) (e₀ : ↥W.one.L.T), Submodule.span O {e₀} = ⊤ ∧
      W.one.L.T = Submodule.span O {(e₀ : W.one.V)} ∧
      E.jD W.one e = (1 : RW) ⊗ₜ[O] e₀ ∧
      W.N W.one = Submodule.span (LetA O n) {e} ∧
      Submodule.span W.EE {e} = (⊤ : Submodule W.EE (W.DD W.one)) ∧
      W.φD W.one e = e ∧ (∀ g, W.γD W.one g e = e) ∧
      ∀ a : LetA O n, a • e = 0 → a = 0 := by
  obtain ⟨-, e₀, h₀, -, -⟩ := E.one_e
  obtain ⟨e, hj, hbij, hφ, hγ, hN⟩ := hU e₀ h₀
  refine ⟨e, e₀, h₀, ?_, hj, hN, ?_, hφ, hγ, fun a ha => ?_⟩
  · have h1 := congrArg (Submodule.map W.one.L.T.subtype) h₀
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, Set.image_singleton] at h1
    exact h1.symm
  · rw [eq_top_iff]
    rintro z -
    exact Submodule.mem_span_singleton.2 (hbij.2 z)
  · apply W.EE_inj
    apply hbij.1
    simp only
    rw [algebraMap_smul, algebraMap_smul, ha, zero_smul]

end Generic

open Formalism.MainNotions.N Formalism.MainNotions.LocalSituation

theorem unitVector : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; ∃ (e : W.DD W.one) (e₀ : ↥W.one.L.T), Submodule.span ↥(OL LL) {e₀} = ⊤ ∧ W.one.L.T = Submodule.span ↥(OL LL) {(e₀ : W.one.V)} ∧ E.jD W.one e = (1 : RW LL) ⊗ₜ[↥(OL LL)] e₀ ∧ W.N W.one = Submodule.span (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) {e} ∧ Submodule.span W.EE {e} = (⊤ : Submodule W.EE (W.DD W.one)) ∧ W.φD W.one e = e ∧ (∀ g, W.γD W.one g e = e) ∧ ∀ a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)), a • e = 0 → a = 0 := by
  intro D HW F l _ K s LL h
  exact unitVector_of_unitFor _ (unitPart l (D.loc l) (D.locA l) (HW l) (F l) K s LL h)

end GlobalTheory.WachUnit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InjectiveTensorBcrisToBdR
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.LocTensorK

private theorem ιB_algebraMap_Kur {l : ℕ} [Fact l.Prime] (P : LocPrime l) (c : ↥(MaximalUnramifiedExtension l)) :
    P.ιB (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) = algebraMap (Om l) P.R.BdR (c : Om l) := by
  have hint : IsIntegral ℚ_[l] (c : Om l) := Algebra.IsIntegral.isIntegral _
  obtain ⟨K, hc⟩ : ∃ K : FinExt l, (c : Om l) ∈ K0 K :=
    ⟨⟨IntermediateField.adjoin ℚ_[l] {(c : Om l)},
      IntermediateField.adjoin.finiteDimensional hint⟩,
      IntermediateField.mem_adjoin_simple_self ℚ_[l] (c : Om l), c.2⟩
  have h := (P.PD K).ι.commutes (⟨c, hc⟩ : ↥(K0 K))
  rw [P.PD_ι] at h
  exact h

private theorem indep_of_frac {k Ω B D : Type} [Field k] [Field Ω] [CommRing B] [CommRing D] [Algebra k Ω]
    [IsGalois k Ω] (hD : IsField D) (o : Ω →+* D) (ι : B →+* D) (hι : Function.Injective ι)
    (hk : ∀ c : k, ∃ a : B, ι a = o (algebraMap k Ω c))
    (hfrac : ∀ (a b : B) (x : Ω), b ≠ 0 → ι a = o x * ι b → x ∈ (algebraMap k Ω).range)
    (m : ℕ) (x : Fin m → Ω) (hx : LinearIndependent k x) (b : Fin m → B)
    (hb : ∑ i, o (x i) * ι (b i) = 0) : ∀ i, b i = 0 := by
  letI : Field D := hD.toField
  have hcl : ∀ y : D, y ∈ Subring.closure (Set.range ι) ↔ ∃ a, ι a = y := by
    intro y
    have : Subring.closure (Set.range ι) = ι.range := by
      rw [← RingHom.coe_range, Subring.closure_eq]
    rw [this]; rfl
  have key := GlobalTheory.T.eq_zero_of_sum_map_mul_eq_zero_of_linearIndependent k Ω D o (Subfield.closure (Set.range ι)) (by
    intro y
    constructor
    · intro hy
      obtain ⟨u, hu, v, hv, huv⟩ := Subfield.mem_closure_iff.1 hy
      obtain ⟨a, rfl⟩ := (hcl u).1 hu
      obtain ⟨c, rfl⟩ := (hcl v).1 hv
      by_cases hc : c = 0
      · subst hc
        rw [map_zero, div_zero] at huv
        have : y = 0 := o.injective (by rw [map_zero]; exact huv.symm)
        rw [this]; exact zero_mem _
      · have hc' : ι c ≠ 0 := fun h => hc (hι (by rw [h, map_zero]))
        refine hfrac a c y hc ?_
        rw [← huv, div_mul_cancel₀ _ hc']
    · rintro ⟨c, rfl⟩
      obtain ⟨a, ha⟩ := hk c
      exact Subfield.subset_closure ⟨a, ha⟩) m x hx (fun i => ι (b i))
    (fun i => Subfield.subset_closure ⟨b i, rfl⟩) hb
  intro i
  exact hι (by rw [map_zero]; exact key i)

private theorem tied_tensor_inj : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (m : ℕ) (x : Fin m → Om l), LinearIndependent ↥(MaximalUnramifiedExtension l) x → ∀ b : Fin m → P.R.B, ∑ i, algebraMap (Om l) P.R.BdR (x i) * P.ιB (b i) = 0 → ∀ i, b i = 0 := by
  intro l _ P AI T m x hx b hb
  obtain ⟨hD, -, hι, -⟩ := GlobalTheory.Per.TiedField.tied_field l P AI T
  haveI : IsGalois ℚ_[l] (Om l) := inferInstance
  haveI : IsGalois ↥(MaximalUnramifiedExtension l) (Om l) := inferInstance
  refine indep_of_frac (k := ↥(MaximalUnramifiedExtension l)) hD (algebraMap (Om l) P.R.BdR) (P.ιB : P.R.B →+* P.R.BdR) hι
    (fun c => ⟨algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c, ιB_algebraMap_Kur P c⟩) ?_ m x hx b hb
  intro a c y hc h
  exact ⟨⟨y, GlobalTheory.T.mem_maxUnramified_of_crystallineRatio l P AI T a c y hc h⟩, rfl⟩

end GlobalTheory.LocTensorK

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_tensor_Bcris_to_BdR : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (m : ℕ) (x : Fin m → ↥K.1), LinearIndependent ↥(K0 K) x → ∀ b : Fin m → P.R.B, ∑ i, algebraMap ↥K.1 P.R.BdR (x i) * P.ιB (b i) = 0 → ∀ i, b i = 0 := by
  intro l _ P AI hT K m x hx b hb
  refine GlobalTheory.LocTensorK.tied_tensor_inj l P AI hT m (fun i => (x i : Om l))
    (GlobalTheory.UnramDisjoint.linearIndependent_Kur l K m x hx) b ?_
  exact hb
end

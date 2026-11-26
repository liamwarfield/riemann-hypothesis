module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsBlockProd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.JetSubstPCompJetBC

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AdmissibleColumnsLeAndHarmonicMapCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory


open MvPolynomial in
theorem map_lap_one {T : Type} (r : T → ℕ) (n : ℕ) {k k' : Type} [Field k] [Field k'] (f : k →+* k')
    (τ τ' : T) (a : Fin (r τ)) (a' : Fin (r τ')) (P : MvPolynomial (Letter T r n) k) :
    lap r n k' 1 τ τ' a a' (MvPolynomial.map f P) = MvPolynomial.map f (lap r n k 1 τ τ' a a' P) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [lap, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_sum,
    Derivation.coeFn_coe, MvPolynomial.smul_eq_C_mul, map_mul, map_C, pderiv_map]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  congr 2
  by_cases h : b = b' <;> simp [Matrix.one_apply, h]


open MvPolynomial in
theorem map_rowShift {T : Type} (r : T → ℕ) (n : ℕ) {k k' : Type} [Field k] [Field k'] (f : k →+* k')
    (σ : T) (i i' : Fin (r σ)) (t : k) (P : MvPolynomial (Letter T r n) k) :
    rowShift r n k' σ i i' (f t) (MvPolynomial.map f P) = MvPolynomial.map f (rowShift r n k σ i i' t P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [rowShift]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p s hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    simp only [rowShift, aeval_X]
    split_ifs <;> simp

theorem map_mem_HHa {T : Type} (r : T → ℕ) (n : ℕ) {k k' : Type} [Field k] [Field k'] (f : k →+* k')
    (hf : Function.Surjective f) (cc : T → T) (isX : T → Prop) (a : T → ℕ → ℕ)
    (P : MvPolynomial (Letter T r n) k) (hP : P ∈ HHa r n k cc isX a) :
    MvPolynomial.map f P ∈ HHa r n k' cc isX a := by
  obtain ⟨h1, h2, h3⟩ := hP
  refine ⟨?_, ?_, ?_⟩
  · simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker] at h1 ⊢
    intro τ hτ b b'
    rw [map_lap_one, h1 τ hτ b b', map_zero]
  · intro σ i i' hi t
    obtain ⟨s, rfl⟩ := hf t
    rw [map_rowShift, h2 σ i i' hi s]
  · intro m hm
    exact h3 m (MvPolynomial.support_map_subset f P hm)

theorem finrank_le_of_span_sup_smul_top {R M : Type} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] {n : ℕ} (x : Fin n → M) (I : Ideal R) (hI : I ≠ ⊤)
    (h : Submodule.span R (Set.range x) ⊔ (I • ⊤ : Submodule R M) = ⊤) : Module.finrank R M ≤ n := by
  set N := Submodule.span R (Set.range x) with hN
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup
    (N := N) (N' := ⊤) (P := ⊤) (I := I) Module.Finite.fg_top le_rfl (by rw [h])
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply hI
    rw [Ideal.eq_top_iff_one]
    simpa using I.neg_mem hr1
  have hmem : ∀ m : M, (r • (LinearMap.id : M →ₗ[R] M)) m ∈ N := fun m =>
    hr (Submodule.smul_mem_pointwise_smul m r ⊤ Submodule.mem_top)
  have hinj : Function.Injective ((r • (LinearMap.id : M →ₗ[R] M)).codRestrict N hmem) := by
    intro u v huv
    have : r • u = r • v := congrArg Subtype.val huv
    exact smul_right_injective M hr0 this
  haveI : Module.Finite R N := Module.Finite.span_of_finite R (Set.finite_range x)
  have h1 := LinearMap.finrank_le_finrank_of_injective hinj
  have h2 : Module.finrank R N ≤ n := by
    simpa [Set.finrank] using finrank_range_le_card (R := R) x
  exact h1.trans h2

theorem Mfr_ne_top {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) :
    Mfr l ≠ ⊤ := by
  intro h
  have hb : l.Mb = ⊤ := by
    rw [Ideal.eq_top_iff_one] at h ⊢
    obtain ⟨y, hy, hy1⟩ := (Ideal.mem_map_iff_of_surjective (H.bar : 𝓞 E →+* 𝓞 E) H.bar.surjective).1 h
    have : y = 1 := H.bar.injective (by simpa using hy1)
    exact this ▸ hy
  have hp := l.prod
  rw [hb, Ideal.map_top, Ideal.top_mul] at hp
  have hn := congrArg Ideal.absNorm hp
  rw [Ideal.absNorm_top, Ideal.absNorm_span_natCast] at hn
  have h3 := l.three_le
  have hpos : 0 < Module.finrank ℤ (𝓞 E) := Module.finrank_pos
  rcases Nat.pow_eq_one.1 hn.symm with h' | h' <;> omega

theorem admissible_columns_le_and_harmonic_map_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), (∀ (rk : Bool) (x0 : Fin n → Dw.La), AdmX (l := l) rk x0 → Dw.p + Dw.q ≤ n) ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P ∈ HHa Dw.mult n d.c₂.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) := by
  intro E _ _ _ H Dw l Xo c n d
  refine ⟨fun rk x0 hx => ?_, fun a P hP => ?_⟩
  swap
  · have hs : Function.Surjective (d.eF : c.F →+* d.c₂.F) := fun y => ⟨d.eF.symm y, d.eF.apply_symm_apply y⟩
    generalize (d.eF : c.F →+* d.c₂.F) = f at hs ⊢
    exact map_mem_HHa Dw.mult n f hs _ _ _ P hP
  haveI := Dw.fin
  haveI := Dw.proj
  rw [← Dw.rank]
  refine finrank_le_of_span_sup_smul_top x0 (Mfr l) (Mfr_ne_top l) ?_
  unfold AdmX at hx
  refine top_le_iff.1 (hx.ge.trans ?_)
  exact sup_le_sup_right (Submodule.span_mono (Set.image_subset_range _ _)) _

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardLevGrpAndSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.TwoMulPowFourDvdCardGeneralLinearGroup
open Matrix

namespace GlobalTheory

def transvectionUnit {R : Type} [CommRing R] {r : ℕ} {i j : Fin r} (h : i ≠ j) : GL (Fin r) R :=
  ⟨transvection i j (1 : R), transvection i j (-1 : R),
    by rw [transvection_mul_transvection_same _ _ h]; simp,
    by rw [transvection_mul_transvection_same _ _ h]; simp⟩

theorem transvectionUnit_pow_val {R : Type} [CommRing R] {r : ℕ} {i j : Fin r} (h : i ≠ j)
    (n : ℕ) :
    ((transvectionUnit (R := R) h ^ n : GL (Fin r) R) : Matrix (Fin r) (Fin r) R)
      = transvection i j (n : R) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Units.val_mul, ih]
    change transvection i j (n : R) * transvection i j (1 : R) = _
    rw [transvection_mul_transvection_same _ _ h]
    simp

theorem orderOf_transvectionUnit {R : Type} [CommRing R] (q : ℕ) [CharP R q] {r : ℕ}
    {i j : Fin r} (h : i ≠ j) : orderOf (transvectionUnit (R := R) h) = q := by
  have key : ∀ n : ℕ, orderOf (transvectionUnit (R := R) h) ∣ n ↔ q ∣ n := by
    intro n
    rw [orderOf_dvd_iff_pow_eq_one, ← CharP.cast_eq_zero_iff R q n, Units.ext_iff,
      transvectionUnit_pow_val, Units.val_one]
    constructor
    · intro hn
      have := congrFun (congrFun hn i) j
      simpa [transvection, one_apply_ne h] using this
    · intro hn
      rw [hn, transvection_zero]
  exact Nat.dvd_antisymm ((key q).2 dvd_rfl) ((key _).1 dvd_rfl)

theorem two_mul_pow_four_dvd_card_generalLinearGroup :
    ∀ (R : Type) [CommRing R] [Finite R] (p : ℕ), Odd p → CharP R (p ^ 4) → 1 < p →
      ∀ r : ℕ, 2 ≤ r → 2 * p ^ 4 ∣ Nat.card (GL (Fin r) R) := by
  intro R _ _ p hp hchar h1 r hr
  have hij : (⟨0, by omega⟩ : Fin r) ≠ ⟨1, by omega⟩ := by simp
  have hq : p ^ 4 ∣ Nat.card (GL (Fin r) R) := by
    rw [← orderOf_transvectionUnit (R := R) (p ^ 4) hij]
    exact orderOf_dvd_natCard _
  have h2 : (2 : R) ≠ 0 := by
    intro h
    have hd : p ^ 4 ∣ 2 := (CharP.cast_eq_zero_iff R (p ^ 4) 2).1 (by exact_mod_cast h)
    have hle := Nat.le_of_dvd (by norm_num) hd
    have : 2 ^ 4 ≤ p ^ 4 := Nat.pow_le_pow_left h1 4
    omega
  have hneg : orderOf (-1 : GL (Fin r) R) = 2 := by
    apply orderOf_eq_prime
    · simp
    · intro h
      have h' := congrArg (fun u : GL (Fin r) R =>
        (u : Matrix (Fin r) (Fin r) R) ⟨0, by omega⟩ ⟨0, by omega⟩) h
      simp only [Units.val_neg, Units.val_one, Matrix.neg_apply, Matrix.one_apply_eq] at h'
      apply h2
      linear_combination -h'
  have h2d : 2 ∣ Nat.card (GL (Fin r) R) := by
    rw [← hneg]
    exact orderOf_dvd_natCard _
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd
    (Nat.Coprime.pow_right 4 ((Nat.coprime_two_left).2 hp)) h2d hq

end GlobalTheory
end

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.EtaForm
attribute [local instance] Over.cartesianMonoidalCategory
open scoped TensorProduct

namespace GlobalTheory.EtaCard

theorem finrank_fibre (O M k : Type) [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M]
    [Module.Finite O M] [Module.Projective O M] [Field k] [Algebra O k] :
    Module.finrank k (k ⊗[O] M) = Module.finrank O M := by
  have : Module.FinitePresentation O M := Module.finitePresentation_of_projective O M
  have key : ∀ (K : Type) [Field K] [Algebra O K], Module.finrank K (K ⊗[O] M) =
      Module.rankAtStalk M (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum O) := fun K _ _ => by
    have h := Module.rankAtStalk_baseChange (R := O) (M := M) (S := K) ⟨⊥, Ideal.isPrime_bot⟩
    rw [Module.rankAtStalk_eq_finrank_of_free] at h
    exact h.trans ((Module.isLocallyConstant_rankAtStalk (R := O) (M := M)).apply_eq_of_preconnectedSpace _ _)
  rw [key k, ← key (FractionRing O), (TensorProduct.isBaseChange O M (FractionRing O)).finrank_eq]

theorem nonempty_equiv_mod (O M : Type) [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M]
    [Module.Finite O M] [Module.Projective O M] (I : Ideal O) [Finite (O ⧸ I)] (r : ℕ)
    (hr : Module.finrank O M = r) :
    Nonempty ((M ⧸ (I • ⊤ : Submodule O M)) ≃ₗ[O] (Fin r → O ⧸ I)) := by
  have : Finite (Ideal (O ⧸ I)) := Finite.of_injective _ SetLike.coe_injective
  have : Finite (MaximalSpectrum (O ⧸ I)) :=
    Finite.of_injective (fun P => P.asIdeal) fun _ _ h => MaximalSpectrum.ext h
  obtain ⟨B⟩ := Module.nonempty_basis_of_flat_of_finrank_eq (O ⧸ I) ((O ⧸ I) ⊗[O] M) r fun P => by
    let := P.isMaximal
    let := Ideal.Quotient.field P.asIdeal
    rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange O (O ⧸ I) ((O ⧸ I) ⧸ P.1) ((O ⧸ I) ⧸ P.1) M).finrank_eq,
      finrank_fibre, hr]
  exact ⟨(TensorProduct.quotTensorEquivQuotSMul M I).symm ≪≫ₗ B.equivFun.restrictScalars O⟩

theorem nonempty_aut_equiv (O N : Type) [CommRing O] [AddCommGroup N] [Module O N] (I : Ideal O) (r : ℕ)
    (e : N ≃ₗ[O] (Fin r → O ⧸ I)) : Nonempty ((N ≃ₗ[O] N) ≃ GL (Fin r) (O ⧸ I)) := by
  have hs : Function.Surjective (algebraMap O (O ⧸ I)) := Ideal.Quotient.mk_surjective
  let e1 : (N ≃ₗ[O] N) ≃ ((Fin r → O ⧸ I) ≃ₗ[O ⧸ I] (Fin r → O ⧸ I)) :=
    { toFun := fun g => (e.symm ≪≫ₗ g ≪≫ₗ e).extendScalarsOfSurjective hs
      invFun := fun g => e ≪≫ₗ g.restrictScalars O ≪≫ₗ e.symm
      left_inv := fun g => by ext x; simp
      right_inv := fun g => by ext x; simp }
  exact ⟨e1.trans ((LinearMap.GeneralLinearGroup.generalLinearEquiv _ _).symm.toEquiv.trans
    Matrix.GeneralLinearGroup.toLin.symm.toEquiv)⟩

theorem span_sup_pow (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (a : O) (S : Submodule O M)
    (h : S ⊔ Ideal.span {a} • ⊤ = ⊤) (k : ℕ) : S ⊔ Ideal.span {a ^ k} • ⊤ = ⊤ := by
  induction k with
  | zero => simp
  | succ k ih =>
    refine eq_top_iff.2 (ih.ge.trans (sup_le le_sup_left ?_))
    have h2 := congrArg (fun T : Submodule O M => Ideal.span {a ^ k} • T) h
    simp only [Submodule.smul_sup, ← Submodule.mul_smul, Ideal.span_singleton_mul_span_singleton,
      ← pow_succ] at h2
    exact h2.ge.trans (sup_le_sup_right Submodule.smul_le_right _)

variable (E : Type) [Field E] [NumberField E]

theorem finite_quot (k : ℕ) (hk : k ≠ 0) : Finite (𝓞 E ⧸ Ideal.span {(k : 𝓞 E)}) :=
  Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hk)

theorem card_quot (k : ℕ) : Nat.card (𝓞 E ⧸ Ideal.span {(k : 𝓞 E)}) = k ^ Module.finrank ℚ E := by
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_natCast, RingOfIntegers.rank]

theorem charP_quot (k : ℕ) : CharP (𝓞 E ⧸ Ideal.span {(k : 𝓞 E)}) k := by
  refine ⟨fun n => ?_⟩
  rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  refine ⟨fun h => ?_, fun h => Nat.cast_dvd_cast h⟩
  have h2 := map_dvd (Algebra.norm ℤ) h
  rw [← map_natCast (algebraMap ℤ (𝓞 E)), ← map_natCast (algebraMap ℤ (𝓞 E)), Algebra.norm_algebraMap,
    Algebra.norm_algebraMap, Int.pow_dvd_pow_iff Module.finrank_pos.ne'] at h2
  exact_mod_cast h2

theorem finrank_eq [IsCMField E] : Module.finrank ℚ E = 2 * FD.fdeg E := by
  rw [FD.fdeg, IsTotallyComplex.finrank E]
  omega

theorem card_levGrp_and_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (R : ℕ), 1 < R → Finite (LevGrp Dw (R ^ 4)) ∧ Finite (LatMod Dw R) ∧ Nat.card (LatMod Dw R) = R ^ (2 * FD.fdeg E * (Dw.p + Dw.q)) ∧ Nat.card (LevGrp Dw (R ^ 4)) ≤ R ^ (8 * FD.fdeg E * (Dw.p + Dw.q) ^ 2) ∧ (Odd R → 2 ≤ Dw.p + Dw.q → 2 * R ^ 4 ∣ Nat.card (LevGrp Dw (R ^ 4))) ∧ (∃ x₀ : Fin (Dw.p + Dw.q) → Dw.La, Submodule.span (𝓞 E) (Set.range x₀) ⊔ (Ideal.span {(R : 𝓞 E)} • ⊤) = ⊤) ∧ ∀ (n : ℕ) (x₀ : Fin n → Dw.La), Submodule.span (𝓞 E) (Set.range x₀) ⊔ (Ideal.span {(R : 𝓞 E)} • ⊤) = ⊤ → ∀ (y : Fin n → LatMod Dw R) (g : LevGrp Dw (R ^ 4)), Submodule.span (𝓞 E) (Set.range fun b => g (shiftFam R x₀ y b)) = ⊤ := by
  intro E _ _ _ H Dw R hR
  have := Dw.fin
  have := Dw.proj
  have hR0 : R ≠ 0 := by omega
  have := finite_quot E R hR0
  have := finite_quot E (R ^ 4) (pow_ne_zero _ hR0)
  obtain ⟨e1⟩ := nonempty_equiv_mod (𝓞 E) Dw.La (Ideal.span {(R : 𝓞 E)}) _ Dw.rank
  obtain ⟨e4⟩ := nonempty_equiv_mod (𝓞 E) Dw.La (Ideal.span {((R ^ 4 : ℕ) : 𝓞 E)}) _ Dw.rank
  obtain ⟨g4⟩ := nonempty_aut_equiv _ _ _ _ e4
  refine ⟨Finite.of_equiv _ g4.symm, Finite.of_equiv _ e1.symm.toEquiv, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Nat.card_congr e1.toEquiv, Nat.card_fun, Nat.card_fin, card_quot, finrank_eq, ← pow_mul]
  · rw [Nat.card_congr g4]
    refine (Nat.card_le_card_of_injective _ Units.val_injective).trans (le_of_eq ?_)
    change Nat.card (Fin (Dw.p + Dw.q) → Fin (Dw.p + Dw.q) → _) = _
    rw [Nat.card_fun, Nat.card_fun, Nat.card_fin, card_quot, finrank_eq, ← pow_mul, ← pow_mul, ← pow_mul]
    congr 1
    ring
  · intro ho h2
    rw [Nat.card_congr g4]
    exact two_mul_pow_four_dvd_card_generalLinearGroup _ R ho (charP_quot E _) hR _ h2
  · choose x₀ hx using fun i => Submodule.Quotient.mk_surjective _ (e1.symm (Pi.single i 1))
    refine ⟨x₀, ?_⟩
    rw [sup_comm, ← Submodule.map_mkQ_eq_top, eq_top_iff]
    intro z _
    choose c hc using fun i => Ideal.Quotient.mk_surjective (e1 z i)
    refine ⟨∑ i, c i • x₀ i, Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩), e1.injective ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Submodule.mkQ_apply, hx, LinearEquiv.apply_symm_apply]
    ext j
    rw [Finset.sum_apply, Finset.sum_eq_single j (fun i _ hi => by simp [hi.symm]) (by simp), ← hc]
    simp [Algebra.smul_def]
  · intro n x₀ hx y g
    have h1 : Submodule.span (𝓞 E) (Set.range fun b => x₀ b + R • qRep (y b)) ⊔
        Ideal.span {(R : 𝓞 E)} • ⊤ = ⊤ := by
      refine eq_top_iff.2 (hx.ge.trans (sup_le (Submodule.span_le.2 ?_) le_sup_right))
      rintro _ ⟨b, rfl⟩
      have : x₀ b = (x₀ b + R • qRep (y b)) - (R : 𝓞 E) • qRep (y b) := by
        rw [Nat.cast_smul_eq_nsmul, add_sub_cancel_right]
      rw [this]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.subset_span ⟨b, rfl⟩))
        (Submodule.mem_sup_right (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) trivial))
    have h2 := span_sup_pow _ _ _ _ h1 4
    rw [← Nat.cast_pow, sup_comm, ← Submodule.map_mkQ_eq_top, Submodule.map_span, ← Set.range_comp] at h2
    have h3 := congrArg (Submodule.map g.toLinearMap) h2
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, LinearEquiv.range] at h3
    exact h3

end GlobalTheory.EtaCard
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NotIsBlockProdZero
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BlockThInhab
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.BlockTh

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) (n : ℕ)

theorem poly_ne_zero (K : Type) [Field K] (B : Bk Dw n) : B.poly K ≠ 0 := by
  classical
  unfold Bk.poly
  refine pow_ne_zero _ ?_
  intro h
  let v : LtN Dw n → K := fun l => if ∃ a : Fin B.i, l = ⟨B.τ, Fin.castLE B.hi a, B.col a⟩ then 1 else 0
  have h2 := congrArg (MvPolynomial.eval v) h
  rw [RingHom.map_det, map_zero] at h2
  have : (MvPolynomial.eval v).mapMatrix (Matrix.of fun a b : Fin B.i => MvPolynomial.X (⟨B.τ, Fin.castLE B.hi a, B.col b⟩ : LtN Dw n)) = 1 := by
    ext a b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, MvPolynomial.eval_X, v, Matrix.one_apply]
    by_cases hab : a = b
    · subst hab; rw [if_pos ⟨a, rfl⟩, if_pos rfl]
    · rw [if_neg hab, if_neg]
      rintro ⟨d, hd⟩
      simp only [Sigma.mk.injEq, heq_eq_eq, true_and, Prod.mk.injEq] at hd
      have h1 : a = d := Fin.castLE_injective _ hd.1
      have h3 : b = d := B.col_inj hd.2
      exact hab (h1.trans h3.symm)
  rw [this, Matrix.det_one] at h2
  exact one_ne_zero h2

theorem not_isBlockProd_zero (K : Type) [Field K] : ¬ IsBlockProd (0 : MvPolynomial (LtN Dw n) K) := by
  rintro ⟨nb, bs, -, h⟩
  exact Finset.prod_ne_zero_iff.2 (fun j _ => poly_ne_zero Dw n K (bs j)) h.symm

end GlobalTheory.BlockThInhab
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsRawChartBaseChangeJetPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsRawChartBaseChangeJetPoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.RawChartBC

open ReciprocityTheory.ChartRestriction.G.PullbackSections

theorem spMap_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'')
    (g : R →+* R') : spMap f ≫ spMap g = spMap (f.comp g) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem dualMap_alg {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) :
    (dualMap ψ).comp (algebraMap S (DualNumber S)) = (algebraMap T (DualNumber T)).comp ψ := by
  ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_epsMul {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (a : S) :
    (dualMap ψ).comp (epsMul a) = (epsMul (ψ a)).comp (dualMap ψ) := by
  ext s <;> simp [dualMap, epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem psTrunc_map {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') {κ : Type} [Fintype κ] [DecidableEq κ]
    (m : ℕ) (f : MvPowerSeries κ S) :
    psTrunc m (MvPowerSeries.map ψ f) = MvPolynomial.map ψ (psTrunc m f) := by
  unfold psTrunc
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [MvPolynomial.map_monomial, MvPowerSeries.coeff_map]

theorem basis_map {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') {σ κ : Type} [Fintype σ] [Fintype κ]
    (U : σ → κ → S) (h : ∀ v : κ → S, ∃! a : σ → S, ∀ j, ∑ ℓ, a ℓ * U ℓ j = v j) (v : κ → S') :
    ∃! a : σ → S', ∀ j, ∑ ℓ, a ℓ * ψ (U ℓ j) = v j := by
  classical
  choose N hN hNu using fun k : κ => h (Pi.single k 1)
  let M : Matrix σ κ S := Matrix.of U
  let P : Matrix κ σ S := Matrix.of N
  have h1 : P * M = 1 := by
    ext k j
    rw [Matrix.mul_apply, Matrix.one_apply]
    refine (hN k j).trans ?_
    simp [Pi.single_apply, eq_comm]
  have h2 : M * P = 1 := by
    ext ℓ ℓ'
    have e : (fun i => (M * P) ℓ i) = fun i => (1 : Matrix σ σ S) ℓ i := by
      refine (h (U ℓ)).unique (fun j => ?_) (fun j => ?_)
      · have : (M * P * M) ℓ j = M ℓ j := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
        rw [Matrix.mul_apply] at this
        exact this
      · have : ((1 : Matrix σ σ S) * M) ℓ j = M ℓ j := by rw [Matrix.one_mul]
        rw [Matrix.mul_apply] at this
        exact this
    exact congrFun e ℓ'
  have h1' : P.map ψ * M.map ψ = 1 := by rw [← Matrix.map_mul, h1]; simp
  have h2' : M.map ψ * P.map ψ = 1 := by rw [← Matrix.map_mul, h2]; simp
  have key : ∀ a : σ → S', (∀ j, ∑ ℓ, a ℓ * ψ (U ℓ j) = v j) ↔ Matrix.vecMul a (M.map ψ) = v := by
    intro a
    rw [funext_iff]
    rfl
  refine ⟨Matrix.vecMul v (P.map ψ), (key _).2 ?_, fun a ha => ?_⟩
  · rw [Matrix.vecMul_vecMul, h1', Matrix.vecMul_one]
  · rw [← (key a).1 ha, Matrix.vecMul_vecMul, h2', Matrix.vecMul_one]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

section Maps

variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ Xo.X)

def baseMap : overAt (spMap ψ ≫ x0) S' ⟶ overAt x0 S :=
  Over.homMk (spMap ψ) (by
    show spMap ψ ≫ spMap (algebraMap S S) ≫ x0 = spMap (algebraMap S' S') ≫ spMap ψ ≫ x0
    rw [← Category.assoc, ← Category.assoc, spMap_spMap, spMap_spMap])

def dualPtMap : overAt (spMap ψ ≫ x0) (DualNumber S') ⟶ overAt x0 (DualNumber S) :=
  Over.homMk (spMap (dualMap ψ)) (by
    show spMap (dualMap ψ) ≫ spMap (algebraMap S (DualNumber S)) ≫ x0 =
      spMap (algebraMap S' (DualNumber S')) ≫ spMap ψ ≫ x0
    rw [← Category.assoc, ← Category.assoc, spMap_spMap, spMap_spMap, dualMap_alg])

theorem sq_aug (d m : ℕ) :
    homAt (spMap ψ ≫ x0) (jetAug : Jet S' (Fin 1 × Fin d) m →ₐ[S'] S') ≫ rjBC ψ x0 d m 1 =
      baseMap ψ x0 ≫ homAt x0 (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) := by
  apply Over.OverMorphism.ext
  show spMap _ ≫ spMap (jetBC ψ _ m) = spMap ψ ≫ spMap _
  rw [spMap_spMap, spMap_spMap]
  exact congrArg spMap (jetAug_comp_jetBC ψ _ m)

theorem sq_trunc (d m : ℕ) :
    homAt (spMap ψ ≫ x0) (jetTrunc : Jet S' (Fin 1 × Fin d) (m + 1) →ₐ[S'] Jet S' (Fin 1 × Fin d) m) ≫
        rjBC ψ x0 d (m + 1) 1 =
      rjBC ψ x0 d m 1 ≫ homAt x0 (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin d) m) := by
  apply Over.OverMorphism.ext
  show spMap _ ≫ spMap (jetBC ψ _ (m + 1)) = spMap (jetBC ψ _ m) ≫ spMap _
  rw [spMap_spMap, spMap_spMap]
  exact congrArg spMap (jetTrunc_comp_jetBC ψ _ m)

theorem sq_subst {n n' d : ℕ} (m : ℕ) (φ : Fin n × Fin d → MvPolynomial (Fin n' × Fin d) S) :
    homAt (spMap ψ ≫ x0) (jetSubstP m (fun i => MvPolynomial.map ψ (φ i)) :
        Jet S' (Fin n × Fin d) m →ₐ[S'] Jet S' (Fin n' × Fin d) m) ≫ rjBC ψ x0 d m n =
      rjBC ψ x0 d m n' ≫ homAt x0 (jetSubstP m φ : Jet S (Fin n × Fin d) m →ₐ[S] Jet S (Fin n' × Fin d) m) := by
  apply Over.OverMorphism.ext
  show spMap _ ≫ spMap (jetBC ψ _ m) = spMap (jetBC ψ _ m) ≫ spMap _
  rw [spMap_spMap, spMap_spMap]
  exact congrArg spMap (jetSubstP_comp_jetBC ψ m φ)

theorem sq_tan (d : ℕ) (ℓ : Fin 1 × Fin d) :
    homAt (spMap ψ ≫ x0) (jetTan ℓ : Jet S' (Fin 1 × Fin d) (0 + 1) →ₐ[S'] DualNumber S') ≫ rjBC ψ x0 d 1 1 =
      dualPtMap ψ x0 ≫ homAt x0 (jetTan ℓ : Jet S (Fin 1 × Fin d) (0 + 1) →ₐ[S] DualNumber S) := by
  apply Over.OverMorphism.ext
  show spMap _ ≫ spMap (jetBC ψ _ (0 + 1)) = spMap (dualMap ψ) ≫ spMap _
  rw [spMap_spMap, spMap_spMap]
  have evalTan (T : Type) [CommRing T] (P : MvPolynomial (Fin 1 × Fin d) T) :
      (jetTan ℓ : Jet T (Fin 1 × Fin d) (0 + 1) →ₐ[T] DualNumber T)
          (Ideal.Quotient.mk (orig T (Fin 1 × Fin d) ^ (0 + 1 + 1)) P) =
        MvPolynomial.aeval (fun i => if i = ℓ then (DualNumber.eps : DualNumber T) else 0) P := rfl
  have hcomp :
      (jetTan ℓ : Jet S' (Fin 1 × Fin d) (0 + 1) →ₐ[S'] DualNumber S').toRingHom.comp
          (jetBC ψ (Fin 1 × Fin d) (0 + 1)) =
        (dualMap ψ).comp (jetTan ℓ : Jet S (Fin 1 × Fin d) (0 + 1) →ₐ[S] DualNumber S).toRingHom := by
    refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_))
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, jetBC_mk, evalTan,
        MvPolynomial.aeval_C, MvPolynomial.map_C]
      ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, jetBC_mk, evalTan,
        MvPolynomial.aeval_X, MvPolynomial.map_X]
      split_ifs <;> ext <;> simp [dualMap]
  exact congrArg spMap hcomp

theorem jetMap_congr_fun {R κ κ' : Type} [CommRing R] {m : ℕ} {f g : κ → MvPolynomial κ' R} (e : f = g)
    (hf : ∀ i, f i ∈ orig R κ') (hg : ∀ i, g i ∈ orig R κ') : jetMap (m := m) f hf = jetMap (m := m) g hg := by
  subst e
  rfl

theorem sq_copy (d m n : ℕ) (i : Fin n) :
    homAt (spMap ψ ≫ x0) (jetCopy d m i : Jet S' (Fin 1 × Fin d) m →ₐ[S'] Jet S' (Fin n × Fin d) m) ≫
        rjBC ψ x0 d m 1 =
      rjBC ψ x0 d m n ≫ homAt x0 (jetCopy d m i : Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S (Fin n × Fin d) m) := by
  apply Over.OverMorphism.ext
  show spMap _ ≫ spMap (jetBC ψ _ m) = spMap (jetBC ψ _ m) ≫ spMap _
  rw [spMap_spMap, spMap_spMap]
  have e := jetMap_comp_jetBC ψ m
    (fun p : Fin 1 × Fin d => (MvPolynomial.X (i, p.2) : MvPolynomial (Fin n × Fin d) S))
    (fun _ => X_mem_orig _) (fun p => by rw [MvPolynomial.map_X]; exact X_mem_orig _)
  rw [jetMap_congr_fun (show (fun p : Fin 1 × Fin d =>
      MvPolynomial.map ψ (MvPolynomial.X (i, p.2) : MvPolynomial (Fin n × Fin d) S)) =
    fun p => MvPolynomial.X (i, p.2) from funext fun p => MvPolynomial.map_X ψ _) _ (fun _ => X_mem_orig _)] at e
  exact congrArg spMap e

theorem list_prod_comp {T T' : Over Xo.X} (f : T' ⟶ T) (L : List (T ⟶ Xo.univ.t.G)) :
    (L.map (f ≫ ·)).prod = f ≫ L.prod := by
  induction L with
  | nil => simp [Hom.one_def]
  | cons a L ih => simp only [List.map_cons, List.prod_cons, ih, Hom.mul_def, comp_lift_assoc]

theorem isCombAt_map {k : ℕ} {v : Fin k → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} {cf : Fin k → S}
    {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (h : IsCombAt x0 v cf w) :
    IsCombAt (spMap ψ ≫ x0) (fun i => spMap (dualMap ψ) ≫ v i) (fun i => ψ (cf i)) (spMap (dualMap ψ) ≫ w) := by
  obtain ⟨u, hu, hp⟩ := h
  refine ⟨fun i => dualPtMap ψ x0 ≫ u i, fun i => ?_, ?_⟩
  · show spMap (dualMap ψ) ≫ (u i).left = _
    rw [hu i, ← Category.assoc, spMap_spMap, dualMap_epsMul, ← spMap_spMap, Category.assoc]
  · have e : List.ofFn (fun i => dualPtMap ψ x0 ≫ u i) = (List.ofFn u).map (dualPtMap ψ x0 ≫ ·) := by
      rw [List.map_ofFn]
      rfl
    rw [e, list_prod_comp, Over.comp_left, hp]
    rfl

end Maps

theorem rIsChart_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S S' : Type) [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ Xo.X) (d : ℕ) (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (x : ∀ m, rjO x0 d m 1 ⟶ Xo.univ.t.G) (x' : ∀ m, rjO (spMap ψ ≫ x0) d m 1 ⟶ Xo.univ.t.G), (∀ m, x' m = rjBC ψ x0 d m 1 ≫ x m) → ∀ (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (uvec : Lt1 Dw → Fin d → S), RIsChart x0 u d F act uvec x → RIsChart (spMap ψ ≫ x0) (fun τ i => spMap (dualMap ψ) ≫ u τ i) d (fun i => MvPowerSeries.map ψ (F i)) (fun a i => MvPowerSeries.map ψ (act a i)) (fun ℓ j => ψ (uvec ℓ j)) x' := by
  intro E _ _ _ H Dw l Xo S S' _ _ ψ x0 d F act x x' hx' u uvec hX
  obtain rfl : x' = fun m => rjBC ψ x0 d m 1 ≫ x m := funext hx'
  refine ⟨fun m => ?_, fun m => ?_, fun m => ?_, fun m a => ?_, fun ℓ => ?_, basis_map ψ uvec hX.basis⟩
  · rw [← Category.assoc, sq_aug, Category.assoc, hX.zero m]
    simp [Hom.one_def]
  · rw [← Category.assoc, sq_trunc, Category.assoc, hX.trunc m]
  · simp only [psTrunc_map]
    rw [← Category.assoc, sq_subst, Category.assoc, hX.law m]
    simp only [rjpt, Hom.mul_def, comp_lift_assoc]
    rw [← Category.assoc (homAt _ _) (rjBC _ _ _ _ _), ← Category.assoc (homAt _ _) (rjBC _ _ _ _ _), sq_copy,
      sq_copy, Category.assoc, Category.assoc]
  · simp only [psTrunc_map]
    rw [← Category.assoc (homAt _ _), sq_subst, Category.assoc, Category.assoc, hX.act m a]
  · have hv : (fun j : Fin d => (homAt (spMap ψ ≫ x0) (jetTan ((0 : Fin 1), j) :
        Jet S' (Fin 1 × Fin d) (0 + 1) →ₐ[S'] DualNumber S') ≫ (rjBC ψ x0 d 1 1 ≫ x 1)).left) =
        fun j => spMap (dualMap ψ) ≫ (homAt x0 (jetTan ((0 : Fin 1), j) :
          Jet S (Fin 1 × Fin d) (0 + 1) →ₐ[S] DualNumber S) ≫ x 1).left := by
      funext j
      rw [← Category.assoc, sq_tan, Category.assoc]
      rfl
    have := isCombAt_map ψ x0 (hX.tan ℓ)
    rw [← hv] at this
    exact this

end GlobalTheory.RawChartBC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsRawChartBaseChangeJetPointsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRawChart_baseChange_jetPoints : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S S' : Type) [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ Xo.X) (d : ℕ) (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (x : ∀ m, rjO x0 d m 1 ⟶ Xo.univ.t.G) (x' : ∀ m, rjO (spMap ψ ≫ x0) d m 1 ⟶ Xo.univ.t.G), (∀ m, x' m = rjBC ψ x0 d m 1 ≫ x m) → ∀ (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (uvec : Lt1 Dw → Fin d → S), RIsChart x0 u d F act uvec x → RIsChart (spMap ψ ≫ x0) (fun τ i => spMap (dualMap ψ) ≫ u τ i) d (fun i => MvPowerSeries.map ψ (F i)) (fun a i => MvPowerSeries.map ψ (act a i)) (fun ℓ j => ψ (uvec ℓ j)) x' := by
  first | exact @GlobalTheory.RawChartBC.rIsChart_baseChange | exact GlobalTheory.RawChartBC.rIsChart_baseChange | (intros; apply GlobalTheory.RawChartBC.rIsChart_baseChange <;> assumption)
end
end

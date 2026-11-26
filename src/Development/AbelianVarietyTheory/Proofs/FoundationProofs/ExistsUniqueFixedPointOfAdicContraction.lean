module

public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PredMulSumPadicValNatFactorialAddCardLe
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueAlgEquivOfCompatibleQuotient
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIdealInClassOfNormLeSqrtDiscr
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueFixedPointOfAdicContraction
noncomputable section

namespace GlobalTheory

open MvPowerSeries

section Eval

variable {A S σ : Type*} [CommRing A] [CommRing S] [Algebra A S]

theorem aeval_mem_pow_of_mem_idealOfVars {J : Ideal S} {x : σ → S} (hx : ∀ i, x i ∈ J) {n : ℕ}
    {p : MvPolynomial σ A} (hp : p ∈ MvPolynomial.idealOfVars σ A ^ n) :
    MvPolynomial.aeval x p ∈ J ^ n := by
  have h : (MvPolynomial.idealOfVars σ A).map (MvPolynomial.aeval x : _ →ₐ[A] S) ≤ J := by
    rw [MvPolynomial.idealOfVars, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    simpa using hx i
  have := Ideal.mem_map_of_mem (MvPolynomial.aeval x : _ →ₐ[A] S) hp
  rw [Ideal.map_pow] at this
  exact Ideal.pow_right_mono h n this

theorem eq_of_forall_sub_mem_ideal_pow (J : Ideal S) [IsHausdorff J S] {x y : S}
    (h : ∀ n, x - y ∈ J ^ n) : x = y := by
  rw [← sub_eq_zero]
  refine IsHausdorff.haus' (I := J) _ fun n => ?_
  rw [SModEq.zero]
  simpa using h n

variable [Finite σ]

def mvEvalMod (A : Type*) [CommRing A] [Algebra A S] (J : Ideal S) (x : σ → S)
    (hx : ∀ i, x i ∈ J) (n : ℕ) : MvPowerSeries σ A →ₐ[A] S ⧸ J ^ n :=
  (Ideal.Quotient.liftₐ (MvPolynomial.idealOfVars σ A ^ n)
    ((Ideal.Quotient.mkₐ A (J ^ n)).comp (MvPolynomial.aeval x)) fun _ hp =>
      Ideal.Quotient.eq_zero_iff_mem.2 (aeval_mem_pow_of_mem_idealOfVars hx hp)).comp
    ((truncTotalAlgHom σ A n).restrictScalars A)

theorem factor_comp_mvEvalMod (J : Ideal S) (x : σ → S) (hx : ∀ i, x i ∈ J) {m n : ℕ}
    (hle : m ≤ n) :
    (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hle)).comp (mvEvalMod A J x hx n) =
      mvEvalMod A J x hx m := by
  refine AlgHom.ext fun f => ?_
  change Ideal.Quotient.mk _ (MvPolynomial.aeval x (truncTotal n f)) =
    Ideal.Quotient.mk _ (MvPolynomial.aeval x (truncTotal m f))
  rw [Ideal.Quotient.eq, ← map_sub]
  exact aeval_mem_pow_of_mem_idealOfVars hx
    (truncTotal_sub_truncTotal_mem_pow_idealOfVars hle le_rfl f)

def mvEvalAdic (A : Type*) [CommRing A] [Algebra A S] (J : Ideal S) [IsAdicComplete J S]
    (x : σ → S) (hx : ∀ i, x i ∈ J) : MvPowerSeries σ A →ₐ[A] S :=
  IsAdicComplete.liftAlgHom J (mvEvalMod A J x hx) (factor_comp_mvEvalMod J x hx)

theorem mvEvalAdic_sub_aeval_truncTotal_mem (J : Ideal S) [IsAdicComplete J S] (x : σ → S)
    (hx : ∀ i, x i ∈ J) (n : ℕ) (f : MvPowerSeries σ A) :
    mvEvalAdic A J x hx f - MvPolynomial.aeval x (truncTotal n f) ∈ J ^ n := by
  rw [← Ideal.Quotient.eq]
  exact IsAdicComplete.mk_liftAlgHom J (mvEvalMod A J x hx) (factor_comp_mvEvalMod J x hx) n f

@[simp] theorem mvEvalAdic_coe (J : Ideal S) [IsAdicComplete J S] (x : σ → S)
    (hx : ∀ i, x i ∈ J) (p : MvPolynomial σ A) :
    mvEvalAdic A J x hx p = MvPolynomial.aeval x p := by
  refine eq_of_forall_sub_mem_ideal_pow J fun n => ?_
  have h1 := mvEvalAdic_sub_aeval_truncTotal_mem J x hx n (p : MvPowerSeries σ A)
  have h2 : MvPolynomial.aeval x (truncTotal n (p : MvPowerSeries σ A) - p) ∈ J ^ n := by
    refine aeval_mem_pow_of_mem_idealOfVars hx ?_
    rw [MvPolynomial.mem_pow_idealOfVars_iff']
    intro d hd
    rw [MvPolynomial.coeff_sub, coeff_truncTotal _ hd, MvPolynomial.coeff_coe, sub_self]
  simpa using add_mem h1 h2

@[simp] theorem mvEvalAdic_X (J : Ideal S) [IsAdicComplete J S] (x : σ → S)
    (hx : ∀ i, x i ∈ J) (i : σ) : mvEvalAdic A J x hx (X i) = x i := by
  simpa using mvEvalAdic_coe (A := A) J x hx (MvPolynomial.X i)

@[simp] theorem mvEvalAdic_C (J : Ideal S) [IsAdicComplete J S] (x : σ → S)
    (hx : ∀ i, x i ∈ J) (a : A) : mvEvalAdic A J x hx (C a) = algebraMap A S a :=
  (mvEvalAdic A J x hx).commutes a

theorem algHom_mem_pow_of_le_order (φ : MvPowerSeries σ A →ₐ[A] S) {K : Ideal S}
    (hφ : ∀ i, φ (X i) ∈ K) {n : ℕ} {g : MvPowerSeries σ A} (hg : (n : ℕ∞) ≤ g.order) :
    φ g ∈ K ^ n := by
  have h : (germIdeal σ A).map φ ≤ K := by
    rw [germIdeal_eq_span, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact hφ i
  have := Ideal.mem_map_of_mem φ (mem_germIdeal_pow_iff_le_order.2 hg)
  rw [Ideal.map_pow] at this
  exact Ideal.pow_right_mono h n this

theorem algHom_sub_constantCoeff_mem (φ : MvPowerSeries σ A →ₐ[A] S) {K : Ideal S}
    (hφ : ∀ i, φ (X i) ∈ K) (g : MvPowerSeries σ A) :
    φ g - algebraMap A S (constantCoeff g) ∈ K := by
  have h : φ (g - C (constantCoeff g)) ∈ K ^ 1 :=
    algHom_mem_pow_of_le_order φ hφ (mem_germIdeal_pow_iff_le_order.1 (by simp [RingHom.mem_ker]))
  rw [pow_one, map_sub] at h
  rwa [← φ.commutes]

omit [Finite σ] in
theorem algHom_coe_mvPolynomial (φ : MvPowerSeries σ A →ₐ[A] S) (p : MvPolynomial σ A) :
    φ p = MvPolynomial.aeval (fun i => φ (X i)) p := by
  have : φ.comp (MvPolynomial.coeToMvPowerSeries.algHom A) =
      MvPolynomial.aeval (fun i => φ (X i)) := by
    ext; simp
  simpa using DFunLike.congr_fun this p

theorem algHom_sub_aeval_truncTotal_mem (φ : MvPowerSeries σ A →ₐ[A] S) {J : Ideal S}
    (hφ : ∀ i, φ (X i) ∈ J) (n : ℕ) (g : MvPowerSeries σ A) :
    φ g - MvPolynomial.aeval (fun i => φ (X i)) (truncTotal n g) ∈ J ^ n := by
  rw [← algHom_coe_mvPolynomial, ← map_sub]
  refine algHom_mem_pow_of_le_order φ hφ (nat_le_order fun d hd => ?_)
  rw [map_sub, MvPolynomial.coeff_coe, coeff_truncTotal _ hd, sub_self]

theorem algHom_sub_mem_pow (φ ψ : MvPowerSeries σ A →ₐ[A] S) {J : Ideal S}
    (hφ : ∀ i, φ (X i) ∈ J) (hψ : ∀ i, ψ (X i) ∈ J) {n : ℕ}
    (h : ∀ i, φ (X i) - ψ (X i) ∈ J ^ n) (g : MvPowerSeries σ A) : φ g - ψ g ∈ J ^ n := by
  have h1 := algHom_sub_aeval_truncTotal_mem φ hφ n g
  have h2 := algHom_sub_aeval_truncTotal_mem ψ hψ n g
  have h3 : MvPolynomial.aeval (fun i => φ (X i)) (truncTotal n g) -
      MvPolynomial.aeval (fun i => ψ (X i)) (truncTotal n g) ∈ J ^ n := by
    have : (Ideal.Quotient.mkₐ A (J ^ n)).comp (MvPolynomial.aeval (fun i => φ (X i))) =
        (Ideal.Quotient.mkₐ A (J ^ n)).comp (MvPolynomial.aeval (fun i => ψ (X i))) := by
      ext i
      simpa [Ideal.Quotient.eq] using h i
    rw [← Ideal.Quotient.eq]
    exact DFunLike.congr_fun this _
  have := sub_mem (add_mem h1 h3) h2
  convert this using 1
  ring

theorem mvPowerSeries_algHom_ext_of_isHausdorff (J : Ideal S) [IsHausdorff J S]
    {φ ψ : MvPowerSeries σ A →ₐ[A] S} (hφ : ∀ i, φ (X i) ∈ J) (h : ∀ i, φ (X i) = ψ (X i)) :
    φ = ψ :=
  AlgHom.ext fun g => eq_of_forall_sub_mem_ideal_pow J fun n =>
    algHom_sub_mem_pow φ ψ hφ (fun i => h i ▸ hφ i) (fun i => by simp [h i]) g

end Eval

section Contraction

variable {A S τ ι : Type*} [CommRing A] [CommRing S] [Algebra A S]

end Contraction

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEquivalenceFiniteEtaleBaseChangeResidueField
noncomputable section

namespace GlobalTheory

open IsLocalRing Polynomial TensorProduct

theorem ker_includeRight_residueField_le_jacobson (R B : Type*) [CommRing R] [IsLocalRing R]
    [CommRing B] [Algebra R B] [Module.Finite R B] :
    RingHom.ker (Algebra.TensorProduct.includeRight : B →ₐ[R] ResidueField R ⊗[R] B) ≤
      (⊥ : Ideal B).jacobson := by
  intro x hx
  apply mem_jacobson_bot_of_forall_isMaximal
  intro n hn
  haveI := hn
  have hc := comap_eq_maximalIdeal_of_finite (R := R) n
  let φ : ResidueField R →ₐ[R] B ⧸ n :=
    Ideal.Quotient.liftₐ (maximalIdeal R) (Algebra.ofId R (B ⧸ n)) fun a ha => by
      rw [Algebra.ofId_apply, ← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem,
        ← Ideal.mem_comap, hc]
      exact ha
  let ψ := Algebra.TensorProduct.lift φ (Ideal.Quotient.mkₐ R n) fun _ _ => Commute.all _ _
  have h1 : ψ ((1 : ResidueField R) ⊗ₜ[R] x) = Ideal.Quotient.mk n x := by
    simp [ψ]
  have h0 : (1 : ResidueField R) ⊗ₜ[R] x = 0 := by
    simpa using RingHom.mem_ker.mp hx
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← h1, h0, map_zero]

theorem includeRight_residueField_surjective (R B : Type*) [CommRing R] [IsLocalRing R]
    [CommRing B] [Algebra R B] :
    Function.Surjective (Algebra.TensorProduct.includeRight : B →ₐ[R] ResidueField R ⊗[R] B) := by
  have hs : Function.Surjective (algebraMap R (ResidueField R)) := IsLocalRing.residue_surjective
  exact Algebra.TensorProduct.includeRight_surjective B hs

theorem isUnit_of_isUnit_one_tmul_residueField (R : Type*) {B : Type*} [CommRing R]
    [IsLocalRing R] [CommRing B] [Algebra R B] [Module.Finite R B] {x : B}
    (hx : IsUnit ((1 : ResidueField R) ⊗ₜ[R] x)) : IsUnit x := by
  apply isUnit_of_isUnit_mk_of_le_jacobson (ker_includeRight_residueField_le_jacobson R B)
  let e := Ideal.quotientKerAlgEquivOfSurjective (includeRight_residueField_surjective R B)
  have he : e (Ideal.Quotient.mk _ x) = (1 : ResidueField R) ⊗ₜ[R] x := rfl
  have h := hx.map e.symm
  rwa [← he, AlgEquiv.symm_apply_apply] at h

theorem isLocalRing_of_isLocalRing_residueField_tensor (R B : Type*) [CommRing R]
    [IsLocalRing R] [CommRing B] [Algebra R B] [Module.Finite R B]
    [IsLocalRing (ResidueField R ⊗[R] B)] : IsLocalRing B := by
  haveI : Nontrivial B := (includeRight_residueField_surjective R B).nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self ((1 : ResidueField R) ⊗ₜ[R] x) with h | h
  · exact Or.inl (isUnit_of_isUnit_one_tmul_residueField R h)
  · right
    apply isUnit_of_isUnit_one_tmul_residueField R
    rwa [TensorProduct.tmul_sub, ← Algebra.TensorProduct.one_def]

theorem existsUnique_idempotent_lift_quotient (R : Type*) {S : Type*} [CommRing R]
    [HenselianLocalRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    {c : S ⧸ (maximalIdeal R).map (algebraMap R S)} (hc : IsIdempotentElem c) :
    ∃! e : S, IsIdempotentElem e ∧ Ideal.Quotient.mk _ e = c := by
  refine existsUnique_idempotent_lift_of_henselian R (Ideal.Quotient.mk _)
    Ideal.Quotient.mk_surjective ?_ hc
  rw [Ideal.mk_ker]
  exact map_maximalIdeal_le_jacobson_of_finite R S

theorem bijective_baseChange_residueField_of_etale (R A B : Type*) [CommRing R]
    [HenselianLocalRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Algebra.Etale R A] [Module.Finite R B] :
    Function.Bijective fun f : A →ₐ[R] B ↦
      Algebra.TensorProduct.map (AlgHom.id (ResidueField R) (ResidueField R)) f := by
  have hG := bijective_algHom_comp_of_etale_of_henselian R (A := A)
    (Algebra.TensorProduct.includeRight : B →ₐ[R] ResidueField R ⊗[R] B)
    (includeRight_residueField_surjective R B) (ker_includeRight_residueField_le_jacobson R B)
  have key : ∀ f : A →ₐ[R] B,
      ((Algebra.TensorProduct.map (AlgHom.id (ResidueField R) (ResidueField R)) f).restrictScalars
        R).comp Algebra.TensorProduct.includeRight = Algebra.TensorProduct.includeRight.comp f := by
    intro f
    ext a
    simp
  refine ⟨fun f g hfg => ?_, fun h => ?_⟩
  · apply hG.1
    dsimp only at hfg ⊢
    rw [← key f, ← key g, hfg]
  · obtain ⟨f, hf⟩ := hG.2 ((h.restrictScalars R).comp Algebra.TensorProduct.includeRight)
    refine ⟨f, ?_⟩
    dsimp only at hf ⊢
    apply Algebra.TensorProduct.ext'
    intro a b
    have hb : Algebra.TensorProduct.map (AlgHom.id (ResidueField R) (ResidueField R)) f
        ((1 : ResidueField R) ⊗ₜ[R] b) = h ((1 : ResidueField R) ⊗ₜ[R] b) := by
      have := congrArg (fun φ : A →ₐ[R] ResidueField R ⊗[R] B => φ b) hf
      simpa using this
    have hab : a ⊗ₜ[R] b = a • ((1 : ResidueField R) ⊗ₜ[R] b) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hab, map_smul, map_smul, hb]

theorem etale_adjoinRoot_of_isUnit_derivative {R : Type*} [CommRing R] {f : R[X]} (hf : f.Monic)
    (h : IsUnit (AdjoinRoot.mk f f.derivative)) : Algebra.Etale R (AdjoinRoot f) := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_surjective (↑u⁻¹ : AdjoinRoot f)
  have h1 : AdjoinRoot.mk f (derivative f * p - 1) = 0 := by
    rw [map_sub, map_mul, hp, ← hu, Units.mul_inv, map_one, sub_self]
  obtain ⟨q, hq⟩ := AdjoinRoot.mk_eq_zero.mp h1
  let P : StandardEtalePair R :=
    ⟨f, hf, 1, p, -q, 0, by rw [pow_zero]; linear_combination hq⟩
  have hunit : IsUnit (AdjoinRoot.mk P.f P.g) := by
    simp [P]
  let e2 : AdjoinRoot f ≃ₐ[R] Localization.Away (AdjoinRoot.mk P.f P.g) :=
    (IsLocalization.atUnit (AdjoinRoot f) (Localization.Away (AdjoinRoot.mk P.f P.g)) _
      hunit).restrictScalars R
  exact Algebra.Etale.of_equiv (P.equivAwayAdjoinRoot.trans e2.symm)

theorem exists_etale_lift_of_isSeparable.{u} (R : Type u) (L : Type*) [CommRing R] [IsLocalRing R]
    [Field L] [Algebra (ResidueField R) L] [Module.Finite (ResidueField R) L]
    [Algebra.IsSeparable (ResidueField R) L] :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A), Module.Finite R A ∧ Algebra.Etale R A ∧
      IsLocalRing A ∧ Nonempty (ResidueField R ⊗[R] A ≃ₐ[ResidueField R] L) := by
  let pb := Field.powerBasisOfFiniteOfSeparable (ResidueField R) L
  have hsep : (minpoly (ResidueField R) pb.gen).Separable :=
    Algebra.IsSeparable.isSeparable _ pb.gen
  have hmon : (minpoly (ResidueField R) pb.gen).Monic := minpoly.monic pb.isIntegral_gen
  have hs : Function.Surjective (algebraMap R (ResidueField R)) := IsLocalRing.residue_surjective
  obtain ⟨f, hfmap, hfdeg, hf⟩ := Polynomial.lifts_and_degree_eq_and_monic
    ((Polynomial.mem_lifts _).mpr (Polynomial.map_surjective _ hs _)) hmon
  haveI hfin : Module.Finite R (AdjoinRoot f) := (AdjoinRoot.powerBasis' hf).finite
  letI : Algebra R L :=
    ((algebraMap (ResidueField R) L).comp (algebraMap R (ResidueField R))).toAlgebra
  haveI : IsScalarTower R (ResidueField R) L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hroot : Polynomial.aeval pb.gen f = 0 := by
    rw [← Polynomial.aeval_map_algebraMap (ResidueField R), hfmap, minpoly.aeval]
  let g : AdjoinRoot f →ₐ[R] L := AdjoinRoot.liftAlgHom f (Algebra.ofId R L) pb.gen hroot
  let ψ : ResidueField R ⊗[R] AdjoinRoot f →ₐ[ResidueField R] L :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) g fun _ _ => Commute.all _ _
  have hψroot : ψ ((1 : ResidueField R) ⊗ₜ[R] AdjoinRoot.root f) = pb.gen := by
    simp only [ψ, g, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    exact AdjoinRoot.liftAlgHom_root _ _ _ _
  have hsurjψ : Function.Surjective ψ := by
    rw [← AlgHom.range_eq_top, eq_top_iff, ← pb.adjoin_gen_eq_top, Algebra.adjoin_le_iff,
      Set.singleton_subset_iff]
    exact (AlgHom.mem_range ψ).mpr ⟨_, hψroot⟩
  let bT := Algebra.TensorProduct.basis (ResidueField R) (AdjoinRoot.powerBasis' hf).basis
  haveI : Module.Finite (ResidueField R) (ResidueField R ⊗[R] AdjoinRoot f) :=
    Module.Finite.of_basis bT
  have hdim : Module.finrank (ResidueField R) (ResidueField R ⊗[R] AdjoinRoot f) =
      Module.finrank (ResidueField R) L := by
    rw [Module.finrank_eq_card_basis bT, Fintype.card_fin, AdjoinRoot.powerBasis'_dim, pb.finrank,
      ← pb.natDegree_minpoly, Polynomial.natDegree_eq_of_degree_eq hfdeg]
  have hinjψ : Function.Injective ψ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim (f := ψ.toLinearMap)).mpr
      hsurjψ
  let e := AlgEquiv.ofBijective ψ ⟨hinjψ, hsurjψ⟩
  haveI : Nontrivial (ResidueField R ⊗[R] AdjoinRoot f) := hsurjψ.nontrivial
  haveI : IsLocalRing (ResidueField R ⊗[R] AdjoinRoot f) :=
    IsLocalRing.of_surjective' e.symm.toRingEquiv.toRingHom e.symm.surjective
  have hloc : IsLocalRing (AdjoinRoot f) := isLocalRing_of_isLocalRing_residueField_tensor R _
  have hder : IsUnit (AdjoinRoot.mk f (derivative f)) := by
    apply isUnit_of_isUnit_one_tmul_residueField R
    have h1 : ψ ((1 : ResidueField R) ⊗ₜ[R] AdjoinRoot.mk f (derivative f)) =
        Polynomial.aeval pb.gen (derivative (minpoly (ResidueField R) pb.gen)) := by
      rw [← hfmap, Polynomial.derivative_map, Polynomial.aeval_map_algebraMap]
      simp only [ψ, g, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      rfl
    have h2 : IsUnit (e ((1 : ResidueField R) ⊗ₜ[R] AdjoinRoot.mk f (derivative f))) := by
      rw [show e _ = ψ _ from rfl, h1, isUnit_iff_ne_zero]
      exact hsep.aeval_derivative_ne_zero (minpoly.aeval _ _)
    simpa using h2.map e.symm
  haveI := etale_adjoinRoot_of_isUnit_derivative hf hder
  exact ⟨AdjoinRoot f, inferInstance, inferInstance, hfin, inferInstance, hloc, ⟨e⟩⟩

theorem exists_etale_lift_of_etale.{u, v} (R : Type u) (E : Type v) [CommRing R] [IsLocalRing R]
    [CommRing E] [Algebra (ResidueField R) E] [Algebra.Etale (ResidueField R) E] :
    ∃ (A : Type (max u v)) (_ : CommRing A) (_ : Algebra R A), Module.Finite R A ∧
      Algebra.Etale R A ∧ Nonempty (ResidueField R ⊗[R] A ≃ₐ[ResidueField R] E) := by
  obtain ⟨I, hI, Ai, _, _, e, hAi⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod (ResidueField R) E).mp inferInstance
  have H : ∀ i, ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A), Module.Finite R A ∧
      Algebra.Etale R A ∧ IsLocalRing A ∧
        Nonempty (ResidueField R ⊗[R] A ≃ₐ[ResidueField R] Ai i) := fun i => by
    haveI := (hAi i).1
    haveI := (hAi i).2
    exact exists_etale_lift_of_isSeparable R (Ai i)
  choose A hA1 hA2 hfin het _ hiso using H
  have := Fintype.ofFinite I
  classical
  refine ⟨Π i, A i, inferInstance, inferInstance, inferInstance, inferInstance, ⟨?_⟩⟩
  exact (Algebra.TensorProduct.piRight R (ResidueField R) (ResidueField R) A).trans
    ((AlgEquiv.piCongrRight fun i => (hiso i).some).trans e.symm)

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumOpTransversal
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumOpTransversal
noncomputable section

open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

section
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]

private lemma quotient_mk_eq_mk_iff_sub_mem (A B : Submodule R X) (x y : B.toAddSubgroup) :
    ((x : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup) = y) ↔
      (y : X) - x ∈ A := by
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
  simp [neg_add_eq_sub]

private lemma heis_apply_eq_of_sub_mem_of_fixes {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}
    (h : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W) {A B : Submodule R X}
    (hB : _root_.GlobalTheory.FinWeil.SelfDual γ B) {v : M} (hv : _root_.GlobalTheory.FinWeil.Fixes W A v) {x y : X}
    (hx : x ∈ B) (hy : y ∈ B) (hxy : y - x ∈ A) : W y v = W x v := by
  have hyx : y - x ∈ B := B.sub_mem hy hx
  calc W y v = W (x + (y - x)) v := by rw [add_sub_cancel]
    _ = W x (W (y - x) v) := (h.comp_of_mem hB hx hyx v).symm
    _ = W x v := by rw [hv _ hxy]

private lemma quotient_out_sub_mem (A B : Submodule R X)
    (q : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup) (x : B.toAddSubgroup)
    (hq : (x : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup) = q) :
    ((Quotient.out q : B.toAddSubgroup) : X) - x ∈ A := by
  rw [← quotient_mk_eq_mk_iff_sub_mem, hq]
  exact (QuotientAddGroup.out_eq' q).symm

theorem _root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}
    (h : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W)
    (A B : Submodule R X) (hB : _root_.GlobalTheory.FinWeil.SelfDual γ B) (v : M)
    (hv : _root_.GlobalTheory.FinWeil.Fixes W A v) (ι : Type) [Fintype ι] (f : ι → X)
    (hf : ∀ i, f i ∈ B) (ht : ∀ b ∈ B, ∃! i, b - f i ∈ A) :
    _root_.GlobalTheory.FinWeil.sumOp W A B v = ∑ i, W (f i) v ∧
      _root_.GlobalTheory.FinWeil.idx A B = Fintype.card ι := by
  let φ : ι → B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup :=
    fun i => ((⟨f i, hf i⟩ : B.toAddSubgroup) : B.toAddSubgroup ⧸ _)
  have hφ : Function.Bijective φ := by
    constructor
    · intro i j hij
      have hji : f j - f i ∈ A := (quotient_mk_eq_mk_iff_sub_mem A B _ _).1 hij
      obtain ⟨k, -, hk⟩ := ht (f j) (hf j)
      rw [hk i hji, hk j (by simp)]
    · intro q
      induction q using QuotientAddGroup.induction_on with
      | H b =>
        obtain ⟨i, hi, -⟩ := ht b b.2
        exact ⟨i, (quotient_mk_eq_mk_iff_sub_mem A B _ _).2 hi⟩
  let e := Equiv.ofBijective φ hφ
  refine ⟨?_, ?_⟩
  · unfold _root_.GlobalTheory.FinWeil.sumOp
    rw [← finsum_comp_equiv e, finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact heis_apply_eq_of_sub_mem_of_fixes h hB hv (hf i) (Quotient.out (e i)).2
      (quotient_out_sub_mem A B (e i) ⟨f i, hf i⟩ rfl)
  · unfold _root_.GlobalTheory.FinWeil.idx
    rw [AddSubgroup.relIndex, AddSubgroup.index, ← Nat.card_congr e, Nat.card_eq_fintype_card]

theorem _root_.GlobalTheory.FinWeil.exists_transversal_of_idx_ne_zero (A B : Submodule R X)
    (hi : _root_.GlobalTheory.FinWeil.idx A B ≠ 0) :
    ∃ (n : ℕ) (f : Fin n → X), (∀ i, f i ∈ B) ∧ ∀ b ∈ B, ∃! i, b - f i ∈ A := by
  unfold _root_.GlobalTheory.FinWeil.idx at hi
  rw [AddSubgroup.relIndex, AddSubgroup.index] at hi
  haveI := Nat.finite_of_card_ne_zero hi
  let e := Finite.equivFin (B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup)
  refine ⟨_, fun i => ((Quotient.out (e.symm i) : B.toAddSubgroup) : X),
    fun i => (Quotient.out (e.symm i) : B.toAddSubgroup).2, ?_⟩
  intro b hb
  refine ⟨e (⟨b, hb⟩ : B.toAddSubgroup), ?_, fun j hj => ?_⟩
  · have := quotient_out_sub_mem A B (e.symm (e (⟨b, hb⟩ : B.toAddSubgroup))) ⟨b, hb⟩ (by simp)
    simpa using A.neg_mem this
  · have h1 : ((⟨b, hb⟩ : B.toAddSubgroup) :
        B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup) = e.symm j := by
      rw [← QuotientAddGroup.out_eq' (e.symm j), quotient_mk_eq_mk_iff_sub_mem]
      simpa using A.neg_mem hj
    rw [h1, Equiv.apply_symm_apply]

end

variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] in
private lemma fixes_sumOp_of_selfDual {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}
    (h : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W) {A B : Submodule R X}
    (hB : _root_.GlobalTheory.FinWeil.SelfDual γ B) {v : M} (hv : _root_.GlobalTheory.FinWeil.Fixes W A v) :
    _root_.GlobalTheory.FinWeil.Fixes W B (_root_.GlobalTheory.FinWeil.sumOp W A B v) := by
  intro b hb
  unfold _root_.GlobalTheory.FinWeil.sumOp
  set g : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup → M :=
    fun q => W ((Quotient.out q : B.toAddSubgroup) : X) v with hg
  have hinj : ∀ u : M, W b u = 0 → u = 0 := by
    intro u hu
    have h1 := h.neg_comp b u
    rw [hu, map_zero] at h1
    exact (smul_eq_zero.1 h1.symm).resolve_left (h.ne_zero _ _)
  have hmap : W b (∑ᶠ q, g q) = ∑ᶠ q, W b (g q) := by
    by_cases hs : (Function.support g).Finite
    · exact map_finsum (W b) hs
    · have hs' : ¬ (Function.support fun q => W b (g q)).Finite := by
        refine fun hfin => hs (hfin.subset fun q hq => ?_)
        exact fun h0 => hq (hinj _ h0)
      rw [finsum_of_infinite_support hs, map_zero, finsum_of_infinite_support hs']
  rw [hmap]
  let c : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup :=
    ((⟨b, hb⟩ : B.toAddSubgroup) : B.toAddSubgroup ⧸ _)
  have hterm : ∀ q, W b (g q) = g (c + q) := by
    intro q
    have hq : ((Quotient.out q : B.toAddSubgroup) : X) ∈ B := (Quotient.out q).2
    rw [hg, h.comp_of_mem hB hb hq v]
    refine (heis_apply_eq_of_sub_mem_of_fixes h hB hv (B.add_mem hb hq) (Quotient.out (c + q)).2
      (quotient_out_sub_mem A B (c + q) (⟨b, hb⟩ + Quotient.out q) ?_)).symm
    rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq']
  simp_rw [hterm]
  exact finsum_comp_equiv (Equiv.addLeft c)

theorem _root_.GlobalTheory.FinWeil.sumOp_transversal : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X]
    [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M},
    _root_.GlobalTheory.FinWeil.IsHeis σ w γ W → ∀ (A B : Submodule R X),
    _root_.GlobalTheory.FinWeil.SelfDual γ B → (∀ v, _root_.GlobalTheory.FinWeil.Fixes W A v → ∀ (ι : Type) [Fintype ι]
      (f : ι → X), (∀ i, f i ∈ B) → (∀ b ∈ B, ∃! i, b - f i ∈ A) →
      _root_.GlobalTheory.FinWeil.sumOp W A B v = ∑ i, W (f i) v ∧
        _root_.GlobalTheory.FinWeil.idx A B = Fintype.card ι) ∧
    (_root_.GlobalTheory.FinWeil.idx A B ≠ 0 → (∃ (n : ℕ) (f : Fin n → X), (∀ i, f i ∈ B) ∧
      ∀ b ∈ B, ∃! i, b - f i ∈ A) ∧
      (∀ v, _root_.GlobalTheory.FinWeil.Fixes W A v →
        _root_.GlobalTheory.FinWeil.Fixes W B (_root_.GlobalTheory.FinWeil.sumOp W A B v)) ∧
      ∀ (c : ℂ) v, _root_.GlobalTheory.FinWeil.sumOp W A B (c • v) = c • _root_.GlobalTheory.FinWeil.sumOp W A B v) ∧
    (B ≤ A → _root_.GlobalTheory.FinWeil.idx A B = 1 ∧
      ∀ v, _root_.GlobalTheory.FinWeil.Fixes W A v → _root_.GlobalTheory.FinWeil.sumOp W A B v = v) := by
  intro R X M _ _ _ _ _ σ w γ W h A B hB
  have hunit : ∀ v, _root_.GlobalTheory.FinWeil.Fixes W A v → B ≤ A →
      _root_.GlobalTheory.FinWeil.sumOp W A B v = ∑ _i : Unit, W 0 v ∧
        _root_.GlobalTheory.FinWeil.idx A B = Fintype.card Unit := fun v hv hBA =>
    _root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal h A B hB v hv Unit (fun _ => 0) (fun _ => B.zero_mem)
      (fun b hb => ⟨(), by simpa using hBA hb, fun _ _ => rfl⟩)
  refine ⟨fun v hv ι _ f hf ht => _root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal h A B hB v hv ι f hf ht,
    fun hi => ⟨_root_.GlobalTheory.FinWeil.exists_transversal_of_idx_ne_zero A B hi,
      fun v hv => fixes_sumOp_of_selfDual h hB hv, fun c v => ?_⟩, fun hBA => ?_⟩
  · unfold _root_.GlobalTheory.FinWeil.sumOp
    simp_rw [map_smul]
    exact (smul_finsum c _).symm
  · refine ⟨(hunit 0 (fun a _ => map_zero _) hBA).2.trans (by simp), fun v hv => ?_⟩
    rw [(hunit v hv hBA).1]
    simpa using hv 0 A.zero_mem

end GlobalTheory.FinWeil
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumOpTransversalStatement
open Classical GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sumOp_transversal_fixes_linear_and_of_le : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ (A B : Submodule R X), SelfDual γ B → (∀ v, Fixes W A v → ∀ (ι : Type) [Fintype ι] (f : ι → X), (∀ i, f i ∈ B) → (∀ b ∈ B, ∃! i, b - f i ∈ A) → sumOp W A B v = ∑ i, W (f i) v ∧ idx A B = Fintype.card ι) ∧ (idx A B ≠ 0 → (∃ (n : ℕ) (f : Fin n → X), (∀ i, f i ∈ B) ∧ ∀ b ∈ B, ∃! i, b - f i ∈ A) ∧ (∀ v, Fixes W A v → Fixes W B (sumOp W A B v)) ∧ ∀ (c : ℂ) v, sumOp W A B (c • v) = c • sumOp W A B v) ∧ (B ≤ A → idx A B = 1 ∧ ∀ v, Fixes W A v → sumOp W A B v = v) := by
  first | exact @GlobalTheory.FinWeil.sumOp_transversal | exact GlobalTheory.FinWeil.sumOp_transversal | (intros; apply GlobalTheory.FinWeil.sumOp_transversal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LogClassNumberLeLogAbsDiscrDiv
open NumberField

namespace GlobalTheory

theorem _root_.GlobalTheory.log_classNumber_le_log_abs_discr_div :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (f : ℕ),
      Module.finrank ℚ E = 2*f →
      Real.log (classNumber E) ≤ f*(Real.log |(discr E : ℝ)|/(2*f)) +
        2*f*Real.log (1 + f*(Real.log |(discr E : ℝ)|/(2*f))) := by
  intro E _ _ _ f hf
  have hdeg : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hf0 : (f : ℝ) ≠ 0 := by
    have : f ≠ 0 := by
      rintro rfl
      omega
    exact_mod_cast this
  have key : (f : ℝ) * (Real.log |(discr E : ℝ)| / (2 * f)) = Real.log √|(discr E : ℝ)| := by
    rw [Real.log_sqrt (abs_nonneg _)]
    field_simp
  rw [key]
  have hb := _root_.GlobalTheory.classNumber_le_of_finrank_eq_two_mul E hf
  have hpos : (0 : ℝ) < classNumber E := by exact_mod_cast classNumber_pos E
  have hs : 1 ≤ √|(discr E : ℝ)| := _root_.GlobalTheory.one_le_sqrt_abs_discr E
  have hL : 0 ≤ Real.log √|(discr E : ℝ)| := Real.log_nonneg hs
  calc Real.log (classNumber E)
      ≤ Real.log (√|(discr E : ℝ)| * (1 + Real.log √|(discr E : ℝ)|) ^ (2 * f)) :=
        Real.log_le_log hpos hb
    _ = Real.log √|(discr E : ℝ)| + ((2 * f : ℕ) : ℝ) * Real.log (1 + Real.log √|(discr E : ℝ)|) := by
        rw [Real.log_mul (by linarith) (pow_ne_zero _ (by linarith)), Real.log_pow]
    _ = Real.log √|(discr E : ℝ)| + 2 * f * Real.log (1 + Real.log √|(discr E : ℝ)|) := by
        push_cast
        ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntertwinerHeisenbergCocycleOfFixedVector
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LinearIndependentOfJointEigenvectors
namespace GlobalTheory.JointEigenvectorsIndependent

theorem linearIndependent_of_joint_eigenvectors {ι α M : Type} [AddCommGroup M] [Module ℂ M]
    (f : ι → M) (χ : ι → α → ℂ) (op : α → M →ₗ[ℂ] M) (hχ : Function.Injective χ)
    (hop : ∀ (a : α) (i : ι), (op a : M → M) (f i) = χ i a • f i)
    (hf : ∀ i : ι, f i ≠ (0 : M)) : LinearIndependent ℂ f := by
  classical
  rw [linearIndependent_iff']
  intro s
  induction s using Finset.induction_on with
  | empty => intro g _ i hi; simp at hi
  | insert j s hj ih =>
    intro g hg
    rw [Finset.sum_insert hj] at hg
    have hs : ∀ i ∈ s, g i = 0 := by
      intro i hi
      have hij : i ≠ j := fun h => hj (h ▸ hi)
      obtain ⟨a, ha⟩ : ∃ a, χ i a ≠ χ j a := Function.ne_iff.mp (fun h => hij (hχ h))
      have h1 : (g j * χ j a) • f j + ∑ k ∈ s, (g k * χ k a) • f k = 0 := by
        have h := congrArg (op a) hg
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_add (f := _), map_sum, map_zero, map_smul, hop, smul_smul] at h
        simpa only [map_smul, hop, smul_smul] using h
      have h2 : (g j * χ j a) • f j + ∑ k ∈ s, (g k * χ j a) • f k = 0 := by
        have h := congrArg (fun x => χ j a • x) hg
        simpa only [smul_add, Finset.smul_sum, smul_zero, smul_smul, mul_comm (χ j a)] using h
      have h3 : ∑ k ∈ s, (g k * (χ k a - χ j a)) • f k = 0 := by
        have h4 : ∑ k ∈ s, (g k * χ k a) • f k = ∑ k ∈ s, (g k * χ j a) • f k :=
          add_left_cancel (h1.trans h2.symm)
        simp only [mul_sub, sub_smul, Finset.sum_sub_distrib, h4, sub_self]
      have h5 := ih (fun k => g k * (χ k a - χ j a)) h3 i hi
      exact (mul_eq_zero.mp h5).resolve_right (sub_ne_zero.mpr ha)
    have hsum : ∑ k ∈ s, g k • f k = 0 :=
      Finset.sum_eq_zero fun k hk => by rw [hs k hk, zero_smul]
    rw [hsum, add_zero] at hg
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact (smul_eq_zero.mp hg).resolve_right (hf _)
    · exact hs i hi

end GlobalTheory.JointEigenvectorsIndependent
end

noncomputable section

open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

theorem linearIndependent_of_simultaneous_eigen {ι α M : Type} [AddCommGroup M] [Module ℂ M] (f : ι → M) (χ : ι → α → ℂ)
    (op : α → M →ₗ[ℂ] M) (hχ : Function.Injective χ) (hop : ∀ a i, op a (f i) = χ i a • f i) (hf : ∀ i, f i ≠ 0) :
    LinearIndependent ℂ f := by
  first
  | exact @_root_.GlobalTheory.JointEigenvectorsIndependent.linearIndependent_of_joint_eigenvectors
  | exact _root_.GlobalTheory.JointEigenvectorsIndependent.linearIndependent_of_joint_eigenvectors
  | (apply _root_.GlobalTheory.JointEigenvectorsIndependent.linearIndependent_of_joint_eigenvectors <;> assumption)
  | (intros; apply _root_.GlobalTheory.JointEigenvectorsIndependent.linearIndependent_of_joint_eigenvectors <;> assumption)
  | (intros; apply @_root_.GlobalTheory.JointEigenvectorsIndependent.linearIndependent_of_joint_eigenvectors <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.JointEigenvectorsIndependent.linearIndependent_of_joint_eigenvectors ..)

end GlobalTheory.FinWeil
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeOperatorsOnHalfPlaneFunctionsAgreeExplicit
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeOperatorsOnHalfPlaneFunctionsAgreeExplicit
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm

noncomputable section
namespace GlobalTheory.SlashUpperTriangularMatrices

theorem toGL_val (g : Matrix (Fin 2) (Fin 2) ℤ) (h : g.det ≠ 0) :
    ((toGL g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = (Int.castRingHom ℝ).mapMatrix g := by
  unfold toGL; rw [dite_eq_right h]; rfl

theorem slash_upper (k : ℤ) (a b d : ℤ) (ha : 0 < a) (hd : 0 < d) (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] toGL !![a, b; 0, d]) τ =
      f (ofComplex (((a : ℂ) * τ + b) / d)) * ((a : ℂ) * d) ^ (k - 1) * (d : ℂ) ^ (-k) := by
  have hdet : (!![a, b; 0, d]).det ≠ 0 := by
    rw [Matrix.det_fin_two_of]; simp [ha.ne', hd.ne']
  have hv := toGL_val _ hdet
  set G := toGL !![a, b; 0, d]
  have e00 : G 0 0 = a := by simp [G, hv]
  have e01 : G 0 1 = b := by simp [G, hv]
  have e10 : G 1 0 = 0 := by simp [G, hv]
  have e11 : G 1 1 = d := by simp [G, hv]
  have hG : G.det.val = (a : ℝ) * d := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, e00, e01, e10, e11]; ring
  have hpos : 0 < G.det.val := by rw [hG]; positivity
  have hsm : G • τ = ofComplex (((a : ℂ) * τ + b) / d) := by
    rw [← ofComplex_apply (G • τ), coe_smul_of_det_pos hpos]
    simp [num, denom, e00, e01, e10, e11]
  rw [ModularForm.slash_apply, hsm, σ, if_pos hpos, hG]
  have hden : denom G τ = d := by simp [denom, e10, e11]
  rw [hden, abs_of_pos (by positivity)]
  simp

theorem pow_pair (x : ℂ) (hx : x ≠ 0) (k : ℤ) : x ^ (k - 1) * x ^ (-k) = x⁻¹ := by
  rw [← zpow_add₀ hx]; ring_nf; simp

theorem toGL_SL (σ : SL(2, ℤ)) : toGL (mat σ) = (σ : GL (Fin 2) ℝ) := by
  have h : (mat σ).det ≠ 0 := by simp [mat]
  ext i j
  rw [toGL_val _ h]
  simp [mat]

theorem ul_eq (k : ℤ) (l : ℕ) (f : ℍ → ℂ) (hl : 0 < l) : UlF k l f = GlobalTheory.Hk.uOp l f := by
  funext τ
  simp only [UlF, hkF, Finset.sum_apply, ulFam]
  have hl' : (0 : ℤ) < l := by exact_mod_cast hl
  simp only [fun j : Fin l => slash_upper k 1 (j : ℤ) l one_pos hl' f τ]
  rw [GlobalTheory.Hk.uOp, Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun j => f (ofComplex (((((1 : ℤ)) : ℂ) * τ + ((j : ℤ) : ℂ)) / ((l : ℤ) : ℂ))) *
      (((1 : ℤ) : ℂ) * ((l : ℤ) : ℂ)) ^ (k - 1) * ((l : ℤ) : ℂ) ^ (-k)) l]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hx : ((l : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  push_cast
  rw [one_mul, one_mul, mul_assoc, pow_pair _ hx, mul_comm]

theorem dd_eq (k : ℤ) (σ : SL(2, ℤ)) (f : ℍ → ℂ) : DdF k σ f = GlobalTheory.Hk.dia k σ f := by
  simp [DdF, hkF, GlobalTheory.Hk.dia, toGL_SL, ModularForm.SL_slash]

theorem toGL_mul (g h : Matrix (Fin 2) (Fin 2) ℤ) (hg : g.det ≠ 0) (hh : h.det ≠ 0) :
    toGL (g * h) = toGL g * toGL h := by
  have hgh : (g * h).det ≠ 0 := by rw [Matrix.det_mul]; exact mul_ne_zero hg hh
  ext i j
  rw [Units.val_mul, toGL_val _ hgh, toGL_val _ hg, toGL_val _ hh, RingHom.map_mul]

theorem tq_eq (k : ℤ) (q : ℕ) (σ : SL(2, ℤ)) (f : ℍ → ℂ) (hq : 0 < q) :
    TqF k q σ f = GlobalTheory.Hk.heckeT k q σ f := by
  have hsplit : TqF k q σ f = UlF k q f + f ∣[k] toGL (mat σ * dg q 1) := by
    have e : ∀ i : Fin q, tqFam q σ i.castSucc = ulFam q i := fun i => by
      rw [tqFam, if_pos (by simp)]; rfl
    have e2 : tqFam q σ (Fin.last q) = mat σ * dg q 1 := by
      rw [tqFam, if_neg (by simp)]
    simp only [TqF, UlF, hkF]
    rw [Fin.sum_univ_castSucc, e2]
    simp only [e]
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  have hdg : (dg q 1).det ≠ 0 := by simp [dg, Matrix.det_fin_two_of, hq.ne']
  have hσ : (mat σ).det ≠ 0 := by simp [mat]
  rw [hsplit, ul_eq k q f hq, toGL_mul _ _ hσ hdg, SlashAction.slash_mul, toGL_SL, ← ModularForm.SL_slash,
    GlobalTheory.Hk.heckeT]
  funext τ
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  rw [dg, slash_upper k q 0 1 hq' one_pos, GlobalTheory.Hk.vOp]
  push_cast
  simp [mul_comm]

theorem dia_iff (N l : ℕ) (d : ℤ) (σ : SL(2, ℤ)) : IsDiam N l (d : ZMod N) σ ↔ GlobalTheory.Hk.IsDia N l d σ := by
  simp [IsDiam, GlobalTheory.Hk.IsDia, CongruenceSubgroup.Gamma0_mem, mat]

end GlobalTheory.SlashUpperTriangularMatrices

namespace GlobalTheory.SlashUpperTriangularMatrices

theorem bridge : (∀ (k : ℤ) (l : ℕ) (f : ℍ → ℂ), 0 < l → UlF k l f = GlobalTheory.Hk.uOp l f) ∧
  (∀ (k : ℤ) (σ : SL(2, ℤ)) (f : ℍ → ℂ), DdF k σ f = GlobalTheory.Hk.dia k σ f) ∧
  (∀ (k : ℤ) (q : ℕ) (σ : SL(2, ℤ)) (f : ℍ → ℂ), 0 < q → TqF k q σ f = GlobalTheory.Hk.heckeT k q σ f) ∧
  (∀ (N l : ℕ) (d : ℤ) (σ : SL(2, ℤ)), IsDiam N l (d : ZMod N) σ ↔ GlobalTheory.Hk.IsDia N l d σ) ∧
  ∀ N l : ℕ, Lev N l = GlobalTheory.Hk.lev N l :=
  ⟨fun k l f hl => ul_eq k l f hl, dd_eq, fun k q σ f hq => tq_eq k q σ f hq, dia_iff, fun _ _ => rfl⟩

end GlobalTheory.SlashUpperTriangularMatrices
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeOperatorsOnHalfPlaneFunctionsAgreeExplicitStatement
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeOperatorsOnHalfPlaneFunctions_agree_explicit : (∀ (k : ℤ) (l : ℕ) (f : ℍ → ℂ), 0 < l → UlF k l f = GlobalTheory.Hk.uOp l f) ∧
  (∀ (k : ℤ) (σ : SL(2, ℤ)) (f : ℍ → ℂ), DdF k σ f = GlobalTheory.Hk.dia k σ f) ∧
  (∀ (k : ℤ) (q : ℕ) (σ : SL(2, ℤ)) (f : ℍ → ℂ), 0 < q → TqF k q σ f = GlobalTheory.Hk.heckeT k q σ f) ∧
  (∀ (N l : ℕ) (d : ℤ) (σ : SL(2, ℤ)), IsDiam N l (d : ZMod N) σ ↔ GlobalTheory.Hk.IsDia N l d σ) ∧
  ∀ N l : ℕ, Lev N l = GlobalTheory.Hk.lev N l := by
  first | exact @GlobalTheory.SlashUpperTriangularMatrices.bridge | exact GlobalTheory.SlashUpperTriangularMatrices.bridge | (intros; apply GlobalTheory.SlashUpperTriangularMatrices.bridge <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUOperatorExplicitEqSumSlash
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUOperatorExplicitEqSumSlash
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem uOp_eq_sum_slash (q : ℕ) (k : ℤ) (f : ℍ → ℂ) (hq : 0 < q) : GlobalTheory.Hk.uOp q f = ∑ j ∈ Finset.range q, f ∣[k] (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : ℚ), (j : ℚ); 0, (q : ℚ)] (by simp [Matrix.det_fin_two_of]; exact_mod_cast hq.ne'))) := by
  funext z
  rw [Finset.sum_apply, uOp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  set g := Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : ℚ), (j : ℚ); 0, (q : ℚ)] (by simp [Matrix.det_fin_two_of]; exact_mod_cast hq.ne')) with hg
  have hval : g.1 = !![(1 : ℝ), (j : ℝ); 0, (q : ℝ)] := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [hg]
  have hdet : g.det.val = (q : ℝ) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hval]; simp
  have hpos : 0 < g.det.val := by rw [hdet]; exact_mod_cast hq
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [slash_apply, σ, ite_eq_left hpos, abs_of_pos hpos, hdet, ← ofComplex_apply (g • z),
    coe_smul_of_det_pos hpos]
  simp [num, denom, hval]
  rw [mul_assoc, ← zpow_neg (q : ℂ) k, ← zpow_add₀ hq0,
    show k - 1 + -k = -1 by omega, zpow_neg_one, mul_comm]

end GlobalTheory.Hk
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUOperatorExplicitEqSumSlashStatement
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeUOperatorExplicit_eq_sum_slash : ∀ (q : ℕ) (k : ℤ) (f : ℍ → ℂ) (hq : 0 < q), GlobalTheory.Hk.uOp q f = ∑ j ∈ Finset.range q, f ∣[k] (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : ℚ), (j : ℚ); 0, (q : ℚ)] (by simp [Matrix.det_fin_two_of]; exact_mod_cast hq.ne'))) := by
  first | exact @GlobalTheory.Hk.uOp_eq_sum_slash | exact GlobalTheory.Hk.uOp_eq_sum_slash | (intros; apply GlobalTheory.Hk.uOp_eq_sum_slash <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CosetRepresentativeTraceFixedProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CosetRepresentativeTraceFixedProperties
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem cosetTrace_fixed_props : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G] [MulSemiringAction G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ (N : Subgroup G) [Fintype (G ⧸ N)], ∀ z ∈ Fix L N, (∀ g : G, g • cosetTrace N z = cosetTrace N z) ∧ (v z ≤ 1 → v (cosetTrace N z) ≤ 1) ∧ ∀ e : L, (∀ g : G, g • e = e) → cosetTrace N (e * z) = e * cosetTrace N z := by
  intro L _ v G _ _ hv N _ z hz
  have hfix : ∀ n : G, n ∈ N → n • z = z := fun n hn => hz ⟨n, hn⟩
  refine ⟨?_, ?_, ?_⟩
  · intro g
    unfold cosetTrace
    rw [Finset.smul_sum]
    have key : ∀ q : G ⧸ N, g • q.out • z = (g • q).out • z := by
      intro q
      have h1 : (QuotientGroup.mk (g * q.out) : G ⧸ N) = g • q := by
        conv_rhs => rw [← QuotientGroup.out_eq' q]
        rfl
      have h2 : ((g • q).out)⁻¹ * (g * q.out) ∈ N := by
        rw [← QuotientGroup.eq, QuotientGroup.out_eq', h1]
      have h3 : g * q.out = (g • q).out * (((g • q).out)⁻¹ * (g * q.out)) := by group
      rw [smul_smul, h3, mul_smul, hfix _ h2]
    simp_rw [key]
    exact Equiv.sum_comp (MulAction.toPerm g) (fun q : G ⧸ N => q.out • z)
  · intro hz1
    unfold cosetTrace
    apply Valuation.map_sum_le
    intro q _
    rw [hv]; exact hz1
  · intro e he
    unfold cosetTrace
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [smul_mul', he]

end GlobalTheory.AlmostEt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CosetRepresentativeTraceFixedPropertiesStatement
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cosetRepresentativeTrace_fixed_properties : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G] [MulSemiringAction G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ (N : Subgroup G) [Fintype (G ⧸ N)], ∀ z ∈ Fix L N, (∀ g : G, g • cosetTrace N z = cosetTrace N z) ∧ (v z ≤ 1 → v (cosetTrace N z) ≤ 1) ∧ ∀ e : L, (∀ g : G, g • e = e) → cosetTrace N (e * z) = e * cosetTrace N z := by
  first | exact @GlobalTheory.AlmostEt.cosetTrace_fixed_props | exact GlobalTheory.AlmostEt.cosetTrace_fixed_props | (intros; apply GlobalTheory.AlmostEt.cosetTrace_fixed_props <;> assumption)
end
end

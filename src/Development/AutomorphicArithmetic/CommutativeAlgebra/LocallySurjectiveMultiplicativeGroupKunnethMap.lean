module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentPolynomialCohomologyVanishing
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsRootOfKummerClassEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCofilteredLimitAffineEtaleOfIsStalkStatement

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EtaleCohomologyLocallyAcyclic
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem UpperTheory.Cb.etale_cohomology_locally_acyclic :
    GlobalTheory.EtC.C5 :=
  GlobalTheory.T.etale_cohomology_locally_acyclic
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LaurentCharacterLambda
@[reducible] noncomputable def UpperTheory.Reformulated.B.LaurentCharacterLambda.LqR :
    ℕ → Type :=
    fun (q : ℕ) ↦ LaurentPolynomial (Localization.Away (↑q : ℤ))

theorem UpperTheory.Reformulated.B.LaurentCharacterLambda.aux3 :
    ∀ {S : Type} [inst : CommRing S] (q : ℕ), IsUnit (↑q : S) → IsUnit ((Int.castRingHom S : ℤ → S) (↑q : ℤ)) := by
  intro S _ q hq
  rwa [map_natCast]

noncomputable def UpperTheory.Reformulated.B.LaurentCharacterLambda.lam :
    {S : Type} → [inst : CommRing S] → (q : ℕ) → IsUnit (↑q : S) → Localization.Away (↑q : ℤ) →+* S :=
    fun {S : Type} [CommRing S] (q : ℕ) (hq : IsUnit (↑q : S)) ↦
      IsLocalization.Away.lift (↑q : ℤ) (UpperTheory.Reformulated.B.LaurentCharacterLambda.aux3 q hq)

theorem UpperTheory.Reformulated.B.LaurentCharacterLambda.aux5 :
    ∀ (S : Type) [inst : CommRing S], LaurentPolynomial.T (1 : ℤ) * LaurentPolynomial.T (-1 : ℤ) = (1 : LaurentPolynomial S) := by
  intro S _
  rw [← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero]

theorem UpperTheory.Reformulated.B.LaurentCharacterLambda.aux6 :
    ∀ (S : Type) [inst : CommRing S], LaurentPolynomial.T (-1 : ℤ) * LaurentPolynomial.T (1 : ℤ) = (1 : LaurentPolynomial S) := by
  intro S _
  rw [← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero]

noncomputable def UpperTheory.Reformulated.B.LaurentCharacterLambda.tU :
    (S : Type) → [inst : CommRing S] → (LaurentPolynomial S)ˣ :=
    fun (S : Type) [CommRing S] ↦
      { val := LaurentPolynomial.T (1 : ℤ), inv := LaurentPolynomial.T (-1 : ℤ), val_inv := UpperTheory.Reformulated.B.LaurentCharacterLambda.aux5 S,
        inv_val := UpperTheory.Reformulated.B.LaurentCharacterLambda.aux6 S : (LaurentPolynomial S)ˣ }

noncomputable def UpperTheory.Reformulated.B.LaurentCharacterLambda.iot :
    {S : Type} → [inst : CommRing S] → (q : ℕ) → IsUnit (↑q : S) → UpperTheory.Reformulated.B.LaurentCharacterLambda.LqR q →+* LaurentPolynomial S :=
    fun {S : Type} [CommRing S] (q : ℕ) (hq : IsUnit (↑q : S)) ↦
      LaurentPolynomial.eval₂ (LaurentPolynomial.C.comp (UpperTheory.Reformulated.B.LaurentCharacterLambda.lam q hq)) (UpperTheory.Reformulated.B.LaurentCharacterLambda.tU S)

theorem UpperTheory.Reformulated.B.LaurentCharacterLambda.aux9 :
    ∀ (q : ℕ), LaurentPolynomial.T (1 : ℤ) * LaurentPolynomial.T (-1 : ℤ) = (1 : UpperTheory.Reformulated.B.LaurentCharacterLambda.LqR q) := by
  intro q
  exact UpperTheory.Reformulated.B.LaurentCharacterLambda.aux5 _

theorem UpperTheory.Reformulated.B.LaurentCharacterLambda.laurent_T_neg_one_mul_T_one :
    ∀ (q : ℕ), LaurentPolynomial.T (-1 : ℤ) * LaurentPolynomial.T (1 : ℤ) = (1 : UpperTheory.Reformulated.B.LaurentCharacterLambda.LqR q) := by
  intro q
  exact UpperTheory.Reformulated.B.LaurentCharacterLambda.aux6 _

noncomputable def UpperTheory.Reformulated.B.LaurentCharacterLambda.tR :
    (q : ℕ) → (UpperTheory.Reformulated.B.LaurentCharacterLambda.LqR q)ˣ :=
    fun (q : ℕ) ↦
      { val := LaurentPolynomial.T (1 : ℤ), inv := LaurentPolynomial.T (-1 : ℤ), val_inv := UpperTheory.Reformulated.B.LaurentCharacterLambda.aux9 q,
        inv_val := UpperTheory.Reformulated.B.LaurentCharacterLambda.laurent_T_neg_one_mul_T_one q : (UpperTheory.Reformulated.B.LaurentCharacterLambda.LqR q)ˣ }

noncomputable def UpperTheory.Reformulated.B.LaurentCharacterLambda.chi :
    {S : Type} →
      [inst : CommRing S] →
        (q : ℕ) →
          {R : Type} → [inst_1 : CommRing R] → (UpperTheory.Reformulated.B.LaurentCharacterLambda.LqR q →+* R) → (S →+* R) → LaurentPolynomial S →+* R :=
    fun {S : Type} [CommRing S] (q : ℕ) {R : Type} [CommRing R] (φ : UpperTheory.Reformulated.B.LaurentCharacterLambda.LqR q →+* R) (ψ : S →+* R) ↦
      LaurentPolynomial.eval₂ ψ
        ((Units.map (↑φ : UpperTheory.Reformulated.B.LaurentCharacterLambda.LqR q →* R) : (UpperTheory.Reformulated.B.LaurentCharacterLambda.LqR q)ˣ → Rˣ) (UpperTheory.Reformulated.B.LaurentCharacterLambda.tR q))

private theorem UpperTheory.Reformulated.B.LaurentCharacterLambda.laurent_hom_ext {S R : Type} [CommRing S] [CommRing R]
    (f g : LaurentPolynomial S →+* R)
    (hC : ∀ a : S, f (LaurentPolynomial.C a) = g (LaurentPolynomial.C a))
    (hT : f (LaurentPolynomial.T 1) = g (LaurentPolynomial.T 1)) : f = g := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial S))
  apply Polynomial.ringHom_ext
  · intro a
    simpa [LaurentPolynomial.algebraMap_eq_toLaurent] using hC a
  · simpa [LaurentPolynomial.algebraMap_eq_toLaurent] using hT

theorem UpperTheory.Reformulated.B.LaurentCharacterLambda.chi_uniq :
    ∀ {S : Type} [inst : CommRing S] (q : ℕ) (hq : IsUnit (↑q : S)) {R : Type} [inst_1 : CommRing R]
      (φ : UpperTheory.Reformulated.B.LaurentCharacterLambda.LqR q →+* R) (ψ : S →+* R) (χ : LaurentPolynomial S →+* R),
      χ.comp (UpperTheory.Reformulated.B.LaurentCharacterLambda.iot q hq) = φ → χ.comp LaurentPolynomial.C = ψ → χ = UpperTheory.Reformulated.B.LaurentCharacterLambda.chi q φ ψ := by
  intro S _ q hq R _ φ ψ χ h1 h2
  apply UpperTheory.Reformulated.B.LaurentCharacterLambda.laurent_hom_ext
  · intro a
    rw [UpperTheory.Reformulated.B.LaurentCharacterLambda.chi, LaurentPolynomial.eval₂_C, ← h2, RingHom.comp_apply]
  · rw [UpperTheory.Reformulated.B.LaurentCharacterLambda.chi, LaurentPolynomial.eval₂_T, zpow_one, Units.coe_map, ← h1]
    change _ = χ (UpperTheory.Reformulated.B.LaurentCharacterLambda.iot q hq (LaurentPolynomial.T 1))
    rw [UpperTheory.Reformulated.B.LaurentCharacterLambda.iot, LaurentPolynomial.eval₂_T, zpow_one]
    rfl
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.BijectiveEtaleCohomologyMultiplicativeGroupProd
section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.BijectiveEtaleCohomologyLaurentPolynomialOfCoord
section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.CohomologySubsingletonPosOfStrictlyHenselian
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

private theorem exists_section_of_etale (O : Type) [CommRing O] [HenselianLocalRing O]
    [IsSepClosed (IsLocalRing.ResidueField O)] {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of O))
    [Etale f] [Surjective f] : ∃ s : Spec (CommRingCat.of O) ⟶ Y, s ≫ f = 𝟙 _ := by
  obtain ⟨y, hy⟩ := (Surjective.surj (f := f)) (⟨IsLocalRing.maximalIdeal O, inferInstance⟩ : PrimeSpectrum O)
  let U := Y.affineOpenCover
  obtain ⟨x, hx⟩ := U.covers y
  have hi : IsOpenImmersion (U.f (U.idx y)) := U.map_prop _
  let φ : CommRingCat.of O ⟶ U.X (U.idx y) := Spec.preimage (U.f (U.idx y) ≫ f)
  have hφ : Spec.map φ = U.f (U.idx y) ≫ f := Spec.map_preimage _
  have he : Etale (Spec.map φ) := by rw [hφ]; infer_instance
  have hE : φ.hom.Etale := HasRingHomProperty.Spec_iff.mp he
  letI : Algebra O (U.X (U.idx y)) := φ.hom.toAlgebra
  haveI : Algebra.Etale O (U.X (U.idx y)) := hE
  have h1 : (Spec.map φ).base x = (⟨IsLocalRing.maximalIdeal O, inferInstance⟩ : PrimeSpectrum O) := by
    rw [hφ]
    change f (U.f (U.idx y) x) = _
    rw [hx, hy]
  let p : PrimeSpectrum (U.X (U.idx y)) := x
  obtain ⟨s, hs⟩ := (GlobalTheory.T.exists_etale_section_iff_henselian_and_isSepClosed O).mpr ⟨inferInstance, inferInstance⟩ (U.X (U.idx y)) p.asIdeal
    (congrArg PrimeSpectrum.asIdeal h1)
  refine ⟨Spec.map (CommRingCat.ofHom s.toRingHom) ≫ U.f (U.idx y), ?_⟩
  rw [Category.assoc, ← hφ, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext a
  exact s.commutes a

theorem UpperTheory.cohomology_subsingleton_pos_of_strictly_henselian :
    ∀ (R : Type) [CommRing R] (O : Type) [CommRing O], SH O → ∀ (F : Shv R) (n : ℤ), 0 < n → Subsingleton (H R (sp O) F n) := by
  intro R _ O _ hO F n hn
  obtain ⟨_, _⟩ := hO
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨Y, f, hf, hsurj, hx⟩ := GlobalTheory.T.positiveDegreeClasses_die_on_etaleCover R _ F n hn x
  obtain ⟨s, hs⟩ := exists_section_of_etale O f
  calc x = pull R (sch.map (s ≫ f)) F n x := by
        rw [hs, sch.map_id, pull_id]
    _ = 0 := by
        rw [sch.map_comp, pull_comp, hx, map_zero]
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ConnectedSpaceSpecLocalAndLaurent
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

private theorem conn_of_idem (R : Type) [CommRing R] [Nontrivial R]
    (h : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1) : ConnectedSpace (PrimeSpectrum R) := by
  rw [connectedSpace_iff_clopen]
  refine ⟨inferInstance, fun s hs => ?_⟩
  obtain ⟨e, he, rfl⟩ := PrimeSpectrum.isClopen_iff.mp hs
  rcases h e he with rfl | rfl
  · left
    simp
  · right
    simp

private theorem idem_local (O : Type) [CommRing O] [IsLocalRing O] (e : O)
    (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with h | h
  · right
    have h1 : e * e = e * 1 := by rw [he.eq, mul_one]
    exact h.mul_left_cancel h1
  · left
    have h1 : (1 - e) * e = (1 - e) * 0 := by rw [mul_zero, sub_mul, one_mul, he.eq, sub_self]
    exact h.mul_left_cancel h1

private theorem idem_zero (O : Type) [CommRing O] [IsLocalRing O] (e : LaurentPolynomial O)
    (he : IsIdempotentElem e) (hm : ∀ n, e.coeff n ∈ IsLocalRing.maximalIdeal O) : e = 0 := by
  classical
  set I : Ideal O := Ideal.span ((e.coeff.support.image e.coeff : Finset O) : Set O) with hI
  have hfg : I.FG := ⟨_, rfl⟩
  have hmem : ∀ n, e.coeff n ∈ I := by
    intro n
    by_cases hn : n ∈ e.coeff.support
    · exact Ideal.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hn))
    · rw [Finsupp.notMem_support_iff.1 hn]
      exact zero_mem _
  have hsq : I ≤ I * I := by
    rw [hI, Ideal.span_le]
    intro x hx
    obtain ⟨n, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
    have h2 : e.coeff n = (e * e).coeff n := by rw [he.eq]
    rw [← hI, h2, AddMonoidAlgebra.coeff_mul]
    simp only [Finsupp.sum]
    refine Ideal.sum_mem _ fun i _ => Ideal.sum_mem _ fun j _ => ?_
    split_ifs
    · exact Ideal.mul_mem_mul (hmem i) (hmem j)
    · exact zero_mem _
  have hidem : IsIdempotentElem I := le_antisymm Ideal.mul_le_right hsq
  obtain ⟨f, hf, hIf⟩ := (Ideal.isIdempotentElem_iff_of_fg I hfg).mp hidem
  have hfI : f ∈ I := hIf ▸ Submodule.mem_span_singleton_self f
  have hIm : I ≤ IsLocalRing.maximalIdeal O := by
    rw [hI, Ideal.span_le]
    intro x hx
    obtain ⟨n, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
    exact hm n
  have hf0 : f = 0 := by
    rcases idem_local O f hf with h | h
    · exact h
    · exfalso
      have := hIm hfI
      rw [h] at this
      exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 this)
  apply AddMonoidAlgebra.ext
  ext n
  have hn := hmem n
  rw [hIf, hf0] at hn
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hn
  rw [← ha, smul_zero]
  rfl

private theorem idem_laurent (O : Type) [CommRing O] [IsLocalRing O] (e : LaurentPolynomial O)
    (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  set φ := AddMonoidAlgebra.mapRingHom ℤ (IsLocalRing.residue O) with hφ
  have key : ∀ x : LaurentPolynomial O, φ x = 0 → ∀ n, x.coeff n ∈ IsLocalRing.maximalIdeal O := by
    intro x hx n
    have := congrArg (fun y => AddMonoidAlgebra.coeff y n) hx
    simp only [hφ, AddMonoidAlgebra.coeff_mapRingHom] at this
    rw [← IsLocalRing.residue_eq_zero_iff]
    simpa using this
  rcases IsIdempotentElem.iff_eq_zero_or_one.1 (he.map φ) with h | h
  · left
    exact idem_zero O e he (key e h)
  · right
    have h1 : 1 - e = 0 := idem_zero O (1 - e) he.one_sub (key _ (by rw [map_sub, map_one, h, sub_self]))
    exact (sub_eq_zero.1 h1).symm

theorem UpperTheory.connectedSpace_spec_local_and_laurent :
    ∀ (O : Type) [CommRing O] [IsLocalRing O], ConnectedSpace (Spec (CommRingCat.of O)) ∧ ConnectedSpace (Spec (CommRingCat.of (LaurentPolynomial O))) := by
  intro O _ _
  exact ⟨conn_of_idem O (idem_local O), conn_of_idem _ (idem_laurent O)⟩
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.NonemptyPrimitiveRootOfStrictlyHenselian
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem UpperTheory.nonempty_primitive_root_of_strictly_henselian :
    ∀ (q : ℕ) [NeZero q] (O : Type) [CommRing O], SH O → IsUnit (q : O) → Nonempty (Prim q O) := by
  intro q _ O _ hO hq
  obtain ⟨hH, hsep⟩ := hO
  have key : ∀ (p : Polynomial O) (x : O), IsLocalRing.residue O (p.eval x) =
      (p.map (IsLocalRing.residue O)).eval (IsLocalRing.residue O x) := by
    intro p x
    rw [Polynomial.eval_map, Polynomial.eval₂_hom]
  have hqk : ((q : ℕ) : IsLocalRing.ResidueField O) ≠ 0 := by
    have := (IsLocalRing.residue_ne_zero_iff_isUnit (q : O)).2 hq
    simpa using this
  haveI : NeZero ((q : ℕ) : IsLocalRing.ResidueField O) := ⟨hqk⟩
  have hdeg : (Polynomial.cyclotomic q (IsLocalRing.ResidueField O)).degree ≠ 0 := by
    rw [Polynomial.degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
  obtain ⟨r, hr⟩ := IsSepClosed.exists_root _ hdeg
    (Polynomial.separable_cyclotomic q (IsLocalRing.ResidueField O))
  obtain ⟨a₀, rfl⟩ := IsLocalRing.residue_surjective r
  have h1 : (Polynomial.cyclotomic q O).eval a₀ ∈ IsLocalRing.maximalIdeal O := by
    rw [← IsLocalRing.residue_eq_zero_iff, key, Polynomial.map_cyclotomic]
    exact hr
  have h2 : IsUnit ((Polynomial.derivative (Polynomial.cyclotomic q O)).eval a₀) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, key, ← Polynomial.derivative_map,
      Polynomial.map_cyclotomic]
    have h0 := (Polynomial.separable_cyclotomic q (IsLocalRing.ResidueField O)).aeval_derivative_ne_zero
      (x := IsLocalRing.residue O a₀) (by simpa [Polynomial.coe_aeval_eq_eval] using hr)
    simpa [Polynomial.coe_aeval_eq_eval] using h0
  obtain ⟨a, ha, -⟩ := HenselianLocalRing.is_henselian (Polynomial.cyclotomic q O)
    (Polynomial.cyclotomic.monic q O) a₀ h1 h2
  refine ⟨⟨a, hq, ?_⟩⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact ha
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.DvdExponentOfPowEqLaurentMonomial
theorem UpperTheory.dvd_exponent_of_pow_eq_laurent_monomial :
    ∀ (q : ℕ) [NeZero q] (O : Type) [CommRing O] [IsLocalRing O] (c : ℕ) (v : (LaurentPolynomial O)ˣ), (v : LaurentPolynomial O) ^ q = LaurentPolynomial.T (c : ℤ) → q ∣ c := by
  intro q _ O _ _ c v hv
  classical
  let φ : LaurentPolynomial O →+* LaurentPolynomial (IsLocalRing.ResidueField O) :=
    AddMonoidAlgebra.mapRingHom ℤ (IsLocalRing.residue O)
  have hT : ∀ n : ℤ, φ (LaurentPolynomial.T n) = LaurentPolynomial.T n := by
    intro n
    show AddMonoidAlgebra.mapRingHom ℤ (IsLocalRing.residue O) (AddMonoidAlgebra.single n 1) =
      AddMonoidAlgebra.single n 1
    rw [AddMonoidAlgebra.mapRingHom_single, map_one]
  have hw : (φ v) ^ q = LaurentPolynomial.T (c : ℤ) := by
    rw [← map_pow, hv, hT]
  obtain ⟨n, p, hp⟩ := LaurentPolynomial.exists_T_pow (φ v)
  have hpq : p ^ q = Polynomial.X ^ (c + q * n) := by
    apply Polynomial.toLaurent_injective
    rw [map_pow, hp, mul_pow, hw, LaurentPolynomial.T_pow, ← LaurentPolynomial.T_add,
      Polynomial.toLaurent_X_pow]
    congr 1
  have hdeg := congrArg Polynomial.natDegree hpq
  rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_pow] at hdeg
  have h1 : q ∣ q * n + c := ⟨p.natDegree, by rw [add_comm]; exact hdeg.symm⟩
  exact (Nat.dvd_add_right (dvd_mul_right q n)).mp h1
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf

section
variable {q : ℕ} [NeZero q]

private theorem cast_zero' {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') :
    ((0 : Ht q E n i).cast hn hi : Ht q E n' i') = 0 := by
  subst hn hi; rfl

private theorem cast_eq_zero' {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E n i)
    (h : (x.cast hn hi : Ht q E n' i') = 0) : x = 0 := by
  subst hn hi; exact h

private theorem cup_cast' {E : Spc} {a a' b b' n i : ℤ} (ha : a = a') (hb : b = b') (y : Ht q E a b) (x : Ht q E n i) :
    cup q (y.cast ha hb : Ht q E a' b') x = (cup q y x).cast (by rw [ha]) (by rw [hb]) := by
  subst ha hb; rfl

private theorem inv_sch {X : Scheme.{0}} (ζ : Prim q Γ(X, ⊤)) : Inv q (sch.obj X) := by
  intro U hU
  obtain ⟨x⟩ := hU
  have x' : U ⟶ X := x
  simpa using ζ.2.1.map x'.appTop.hom

private theorem cupRootInj {X : Scheme.{0}} (ζ : Prim q Γ(X, ⊤)) (j : ℤ) {n i : ℤ} (x : Ht q (sch.obj X) n i)
    (h : cup q (rootClass j ζ) x = 0) : x = 0 := by
  have h1 : cup q (cup q (rootClass (-j) ζ) (rootClass j ζ)) x = 0 := by
    rw [GlobalTheory.T.tateTwistCupProduct_assoc, h, map_zero, cast_zero']
  rw [((GlobalTheory.T.tateTwistCup_unit_and_primitiveRoot_classes q).2 X ζ (-j) j).1] at h1
  rw [cup_cast'] at h1
  have h2 := cast_eq_zero' _ _ _ h1
  have key : ∀ (k : ℤ), k = 0 → cup q (rootClass k ζ) x = 0 → x = 0 := by
    intro k hk hx
    subst hk
    rw [((GlobalTheory.T.tateTwistCup_unit_and_primitiveRoot_classes q).2 X ζ 0 0).2, (GlobalTheory.T.tateTwistCup_unit_and_primitiveRoot_classes q).1 _ (inv_sch ζ)] at hx
    exact cast_eq_zero' _ _ _ hx
  exact key _ (by ring) h2

private theorem kum_pow {X : Scheme.{0}} (w : (Γ(X, ⊤))ˣ) (hq : IsUnit (q : Γ(X, ⊤))) (c : ℕ) :
    c • kum q w = kum q (w ^ c) := by
  induction c with
  | zero =>
    have h := ((GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q).2.2 (1 : (Γ(X, ⊤))ˣ) 1 hq).1
    rw [mul_one] at h
    have h0 : kum q (1 : (Γ(X, ⊤))ˣ) = 0 := by simpa using h
    simp [h0]
  | succ c ih =>
    rw [succ_nsmul, ih, pow_succ, ((GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q).2.2 (w ^ c) w hq).1]

private theorem tors {E : Spc} {n i : ℤ} (x : Ht q E n i) {c : ℕ} (h : q ∣ c) : c • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod q), (ZMod.natCast_eq_zero_iff c q).2 h, zero_smul]

private noncomputable def secHom (i : ℤ) (X : Scheme.{0}) : Sec (tw q i) X →+ Ht q (sch.obj X) 0 i :=
  AddMonoidHom.mk' (secClass (tw q i)) (GlobalTheory.T.degreeZeroSectionClass_properties (ZMod q) (tw q i) X).2.2.1

private theorem root_eq (i : ℤ) {X : Scheme.{0}} (ζ : Prim q Γ(X, ⊤)) : rootClass i ζ = secHom i X (twGen i ζ) :=
  (GlobalTheory.T.tateTwistUnitClass_rootClass_spec q).2.2.2 i X ζ

private theorem root_every {X : Scheme.{0}} [ConnectedSpace X] (ζ : Prim q Γ(X, ⊤)) (i : ℤ) (b : Ht q (sch.obj X) 0 i) :
    ∃ c : ℕ, b = c • rootClass i ζ := by
  obtain ⟨s, rfl⟩ := (GlobalTheory.T.degreeZeroSectionClass_properties (ZMod q) (tw q i) X).2.1.2 b
  obtain ⟨c, rfl⟩ := UpperTheory.twisted_section_eq_nsmul_generator_of_connected q i X ζ s
  refine ⟨c, ?_⟩
  rw [root_eq, ← map_nsmul]
  rfl

private theorem root_tors {X : Scheme.{0}} [Nonempty X] (ζ : Prim q Γ(X, ⊤)) (i : ℤ) (c : ℕ) (h : c • rootClass i ζ = 0) :
    q ∣ c := by
  rw [root_eq, ← map_nsmul] at h
  have hinj : Function.Injective (secHom (q := q) i X) := (GlobalTheory.T.degreeZeroSectionClass_properties (ZMod q) (tw q i) X).2.1.1
  have h0 : c • twGen i ζ = 0 := hinj (h.trans (map_zero _).symm)
  exact (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.1 X ζ c h0

private theorem pull_root {Y X : Scheme.{0}} (f : Y ⟶ X) (ζ : Prim q Γ(X, ⊤)) (i : ℤ) :
    pull _ (sch.map f) _ _ (rootClass i ζ) = rootClass i (ζ.map f.appTop.hom) := by
  rw [root_eq, root_eq]
  refine ((GlobalTheory.T.degreeZeroSectionClass_properties (ZMod q) (tw q i) X).2.2.2.1 f _).trans ?_
  rw [(GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.2.1 Y X f ζ]
  rfl

private theorem deg0 {X Y : Scheme.{0}} [ConnectedSpace X] [ConnectedSpace Y] (f : Y ⟶ X) (ζ : Prim q Γ(X, ⊤)) (i n : ℤ) (hn : n = 0) :
    Function.Bijective (pull _ (sch.map f) (tw q i) n) := by
  subst hn
  refine ⟨(injective_iff_map_eq_zero _).2 fun b hb => ?_, fun b' => ?_⟩
  · obtain ⟨c, rfl⟩ := root_every ζ i b
    rw [map_nsmul, pull_root] at hb
    exact tors _ (root_tors _ i c hb)
  · obtain ⟨c, rfl⟩ := root_every (ζ.map f.appTop.hom) i b'
    exact ⟨c • rootClass i ζ, by rw [map_nsmul, pull_root]⟩

end

theorem UpperTheory.bijective_etaleCohomology_laurentPolynomial_of_coordinate_unit :
    ∀ (q : ℕ) [NeZero q] (O : Type) [CommRing O], SH O → IsUnit (q : O) →
        ∀ u : (Γ(Spec (CommRingCat.of (LaurentPolynomial O)), ⊤))ˣ,
          (u : Γ(Spec (CommRingCat.of (LaurentPolynomial O)), ⊤)) =
            (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial O))).inv.hom (LaurentPolynomial.T 1) →
          ∀ m j : ℤ, Function.Bijective fun p : Ht q (sp O) (m + 1) (j + 1) × Ht q (sp O) m j =>
            pull _ (spMap (LaurentPolynomial.C : O →+* LaurentPolynomial O)) _ _ p.1 +
              cup q (pull _ (spMap (LaurentPolynomial.C : O →+* LaurentPolynomial O)) _ _ p.2) (kum q u) := by
  intro q _ O _ hSH hq u hu m j
  have hSH' := hSH
  obtain ⟨hh, hsep⟩ := hSH'
  haveI : HenselianLocalRing O := hh
  haveI : ConnectedSpace (Spec (CommRingCat.of O)) := (UpperTheory.connectedSpace_spec_local_and_laurent O).1
  haveI : ConnectedSpace (Spec (CommRingCat.of (LaurentPolynomial O))) := (UpperTheory.connectedSpace_spec_local_and_laurent O).2
  obtain ⟨ζ₀⟩ := UpperTheory.nonempty_primitive_root_of_strictly_henselian q O hSH hq
  let ζ : Prim q Γ(Spec (CommRingCat.of O), ⊤) := ζ₀.map (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom
  let f : Spec (CommRingCat.of (LaurentPolynomial O)) ⟶ Spec (CommRingCat.of O) :=
    Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : O →+* LaurentPolynomial O))
  let ζ' := ζ.map f.appTop.hom
  have hqL : IsUnit (q : Γ(Spec (CommRingCat.of (LaurentPolynomial O)), ⊤)) := ζ'.2.1
  have hC5 := UpperTheory.Cb.etale_cohomology_locally_acyclic q O hSH hq
  have hneg : ∀ (E : Spc) (n i : ℤ), n < 0 → Subsingleton (Ht q E n i) := fun E n i hn =>
    (GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero (ZMod q) (tw q i)).1 E n hn
  have hpos : ∀ (n i : ℤ), 0 < n → Subsingleton (Ht q (sp O) n i) := fun n i hn => UpperTheory.cohomology_subsingleton_pos_of_strictly_henselian (ZMod q) O hSH (tw q i) n hn

  have hinj : Function.Injective fun b : Ht q (sp O) 0 j => cup q (pull _ (sch.map f) _ _ b) (kum q u) := by
    have hadd : ∀ a b : Ht q (sp O) 0 j, cup q (pull _ (sch.map f) _ _ (a + b)) (kum q u) =
        cup q (pull _ (sch.map f) _ _ a) (kum q u) + cup q (pull _ (sch.map f) _ _ b) (kum q u) := by
      intro a b
      rw [map_add (f := _), map_add (f := _), AddMonoidHom.add_apply]
    refine (injective_iff_map_eq_zero (AddMonoidHom.mk' _ hadd)).2 fun b hb => ?_
    change cup q (pull _ (sch.map f) _ _ b) (kum q u) = 0 at hb
    obtain ⟨c, rfl⟩ := root_every ζ j b
    rw [map_nsmul, pull_root, map_nsmul, AddMonoidHom.nsmul_apply, ← map_nsmul, kum_pow u hqL] at hb
    obtain ⟨v, hv⟩ := UpperTheory.exists_root_of_kummer_class_eq_zero q _ (u ^ c) hqL (cupRootInj ζ' j _ hb)
    refine tors _ (UpperTheory.dvd_exponent_of_pow_eq_laurent_monomial q O c (Units.map (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial O))).hom.hom.toMonoidHom v) ?_)
    have h1 := congrArg (fun w : (Γ(Spec (CommRingCat.of (LaurentPolynomial O)), ⊤))ˣ =>
      (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial O))).hom.hom (w : Γ(Spec (CommRingCat.of (LaurentPolynomial O)), ⊤))) hv
    simp only [Units.val_pow_eq_pow_val, map_pow, hu] at h1
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial O))).hom.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial O))).inv.hom (LaurentPolynomial.T 1)) = LaurentPolynomial.T 1 := by
      simp
    rw [h2, LaurentPolynomial.T_pow] at h1
    simpa using h1
  have hsurj : Function.Surjective fun b : Ht q (sp O) 0 j => cup q (pull _ (sch.map f) _ _ b) (kum q u) := by
    obtain ⟨e⟩ : Nonempty (Ht q (sch.obj (Spec (CommRingCat.of (LaurentPolynomial O)))) (0 + 1) (j + 1) ≃+ ZMod q) := (hC5 1 (j + 1)).2
    haveI : Finite (Ht q (sch.obj (Spec (CommRingCat.of (LaurentPolynomial O)))) (0 + 1) (j + 1)) := Finite.of_equiv _ e.symm.toEquiv
    have key : ∀ a b : ℕ, b < q → a ≤ b → a • rootClass j ζ = b • rootClass j ζ → a = b := by
      intro a b hb hle h
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
      rw [add_nsmul, left_eq_add] at h
      have := Nat.eq_zero_of_dvd_of_lt (root_tors ζ j d h) (by omega)
      omega
    have hfin : Function.Injective fun c : Fin q => (c : ℕ) • rootClass j ζ := by
      intro a b hab
      rcases le_total (a : ℕ) (b : ℕ) with h | h
      · exact Fin.ext (key _ _ b.2 h hab)
      · exact Fin.ext (key _ _ a.2 h hab.symm).symm
    have hcomp := Function.Injective.bijective_of_nat_card_le (hinj.comp hfin) (by
      rw [Nat.card_congr e.toEquiv, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin])
    exact Function.Surjective.of_comp hcomp.2
  rcases lt_trichotomy m 0 with hm | hm | hm
  · rcases eq_or_lt_of_le (show m + 1 ≤ 0 by omega) with h0 | h0
    · have hm' : m = -1 := by omega
      subst hm'
      haveI := hneg (sp O) (-1) j (by norm_num)
      have hb := deg0 f ζ (j + 1) _ h0
      refine ⟨fun p p' h => ?_, fun y => ?_⟩
      · have h2 : p.2 = p'.2 := Subsingleton.elim _ _
        have h3 : pull _ (sch.map f) _ _ p.1 = pull _ (sch.map f) _ _ p'.1 := by
          have h' : pull _ (sch.map f) _ _ p.1 + _ = pull _ (sch.map f) _ _ p'.1 + _ := h
          rw [h2] at h'
          exact add_right_cancel h'
        exact Prod.ext (hb.1 h3) h2
      · obtain ⟨b, rfl⟩ := hb.2 y
        refine ⟨(b, 0), ?_⟩
        simp
        rfl
    · haveI := hneg (sp O) _ (j + 1) h0
      haveI := hneg (sp O) m j hm
      haveI := hneg (sp (LaurentPolynomial O)) _ (j + 1) h0
      exact ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
  · subst hm
    haveI := hpos (0 + 1) (j + 1) (by norm_num)
    refine ⟨fun p p' h => ?_, fun y => ?_⟩
    · have h1 : p.1 = p'.1 := Subsingleton.elim _ _
      have h' : pull _ (sch.map f) _ _ p.1 + _ = pull _ (sch.map f) _ _ p'.1 + _ := h
      rw [h1] at h'
      exact Prod.ext h1 (hinj (add_left_cancel h'))
    · obtain ⟨b, rfl⟩ := hsurj y
      refine ⟨(0, b), ?_⟩
      simp
      rfl
  · haveI := hpos (m + 1) (j + 1) (by omega)
    haveI := hpos m j hm
    haveI := (hC5 (m + 1) (j + 1)).1 (by omega)
    exact ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf

namespace UpperTheory.KG

variable {S : Type} [CommRing S]

private noncomputable def tU (S : Type) [CommRing S] : (LaurentPolynomial S)ˣ :=
  ⟨LaurentPolynomial.T 1, LaurentPolynomial.T (-1), by rw [← LaurentPolynomial.T_add]; simp,
    by rw [← LaurentPolynomial.T_add]; simp⟩

private theorem tU_zpow (n : ℤ) : (((tU S) ^ n : (LaurentPolynomial S)ˣ) : LaurentPolynomial S) = LaurentPolynomial.T n := by
  obtain ⟨k, rfl | rfl⟩ := n.eq_nat_or_neg
  · rw [zpow_natCast, Units.val_pow_eq_pow_val]
    change (LaurentPolynomial.T 1 : LaurentPolynomial S) ^ k = _
    rw [LaurentPolynomial.T_pow]; simp
  · rw [zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val]
    change (LaurentPolynomial.T (-1) : LaurentPolynomial S) ^ k = _
    rw [LaurentPolynomial.T_pow]; simp

private theorem lp_hom_ext {R : Type} [CommRing R] {f g : LaurentPolynomial S →+* R}
    (h1 : f.comp LaurentPolynomial.C = g.comp LaurentPolynomial.C)
    (h2 : f (LaurentPolynomial.T 1) = g (LaurentPolynomial.T 1)) : f = g := by
  have hu : Units.map f.toMonoidHom (tU S) = Units.map g.toMonoidHom (tU S) := Units.ext h2
  have hT : ∀ n : ℤ, f (LaurentPolynomial.T n) = g (LaurentPolynomial.T n) := by
    intro n
    rw [← tU_zpow n]
    have h : Units.map f.toMonoidHom (tU S ^ n) = Units.map g.toMonoidHom (tU S ^ n) := by
      rw [map_zpow, map_zpow, hu]
    exact congrArg (fun v : Rˣ => (v : R)) h
  refine RingHom.ext fun p => ?_
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq]
  | C_mul_T n a => rw [map_mul, map_mul, hT n]; exact congrArg (· * _) (RingHom.congr_fun h1 a)

private noncomputable def lam (q : ℕ) (hq : IsUnit (q : S)) : Localization.Away (q : ℤ) →+* S :=
  IsLocalization.Away.lift (q : ℤ) (g := Int.castRingHom S) (by simpa using hq)

private noncomputable def iot (q : ℕ) (hq : IsUnit (q : S)) : LqR q →+* LaurentPolynomial S :=
  LaurentPolynomial.eval₂ (LaurentPolynomial.C.comp (lam q hq)) (tU S)

private theorem inclusion_T (q : ℕ) (hq : IsUnit (q : S)) : iot q hq (LaurentPolynomial.T 1) = LaurentPolynomial.T 1 := by
  rw [iot, LaurentPolynomial.eval₂_T, tU_zpow]

private noncomputable def chi (q : ℕ) {R : Type} [CommRing R] (φ : LqR q →+* R) (ψ : S →+* R) : LaurentPolynomial S →+* R :=
  LaurentPolynomial.eval₂ ψ (Units.map φ.toMonoidHom (tR q))

private theorem character_T (q : ℕ) {R : Type} [CommRing R] (φ : LqR q →+* R) (ψ : S →+* R) :
    chi q φ ψ (LaurentPolynomial.T 1) = φ (LaurentPolynomial.T 1) := by
  rw [chi, LaurentPolynomial.eval₂_T, zpow_one]; rfl

private theorem chi_C (q : ℕ) {R : Type} [CommRing R] (φ : LqR q →+* R) (ψ : S →+* R) :
    (chi q φ ψ).comp LaurentPolynomial.C = ψ :=
  RingHom.ext fun a => LaurentPolynomial.eval₂_C _ _ _

private theorem chi_iot (q : ℕ) (hq : IsUnit (q : S)) {R : Type} [CommRing R] (φ : LqR q →+* R) (ψ : S →+* R) :
    (chi q φ ψ).comp (iot q hq) = φ := by
  refine lp_hom_ext ?_ ?_
  · refine IsLocalization.ringHom_ext (Submonoid.powers (q : ℤ)) (RingHom.ext_int _ _)
  · rw [RingHom.comp_apply, inclusion_T, character_T]

private theorem chi_uniq (q : ℕ) (hq : IsUnit (q : S)) {R : Type} [CommRing R] (φ : LqR q →+* R) (ψ : S →+* R)
    (χ : LaurentPolynomial S →+* R) (h1 : χ.comp (iot q hq) = φ) (h2 : χ.comp LaurentPolynomial.C = ψ) :
    χ = chi q φ ψ :=
  _root_.UpperTheory.Reformulated.B.LaurentCharacterLambda.chi_uniq q hq φ ψ χ h1 h2

private noncomputable def sec {X : Scheme.{0}} {R : CommRingCat.{0}} (f : X ⟶ Spec R) : R ⟶ Γ(X, ⊤) :=
  (Scheme.ΓSpecIso R).inv ≫ f.appTop

private theorem sec_inj {X : Scheme.{0}} {R : CommRingCat.{0}} {f g : X ⟶ Spec R} (h : sec f = sec g) : f = g :=
  ext_of_isAffine ((cancel_epi (Scheme.ΓSpecIso R).inv).1 h)

private theorem sec_comp {X : Scheme.{0}} {R R' : CommRingCat.{0}} (f : X ⟶ Spec R') (ψ : R ⟶ R') :
    sec (f ≫ Spec.map ψ) = ψ ≫ sec f := by
  simp only [sec, Scheme.Hom.comp_appTop]
  rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]

private theorem sec_to {X : Scheme.{0}} {R : CommRingCat.{0}} (φ : R ⟶ Γ(X, ⊤)) : sec (X.toSpecΓ ≫ Spec.map φ) = φ := by
  rw [sec_comp, sec, Scheme.toSpecΓ_appTop, Iso.inv_hom_id, Category.comp_id]

private noncomputable def isProd (q : ℕ) (hq : IsUnit (q : S)) :
    IsLimit (BinaryFan.mk (Spec.map (CommRingCat.ofHom (iot q hq)) : Spec (CommRingCat.of (LaurentPolynomial S)) ⟶ Gq q)
      (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : S →+* LaurentPolynomial S)) :
        Spec (CommRingCat.of (LaurentPolynomial S)) ⟶ Spec (CommRingCat.of S))) :=
  BinaryFan.isLimitMk
    (fun s => s.pt.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (chi q (sec s.fst).hom (sec s.snd).hom)))
    (fun s => sec_inj (by
      rw [sec_comp, sec_to, ← CommRingCat.ofHom_comp, chi_iot]; rfl))
    (fun s => sec_inj (by
      rw [sec_comp, sec_to, ← CommRingCat.ofHom_comp, chi_C]; rfl))
    (fun s m h1 h2 => sec_inj (by
      rw [sec_to]
      have e1 : (sec m).hom.comp (iot q hq) = (sec s.fst).hom := by
        rw [← h1, sec_comp]; rfl
      have e2 : (sec m).hom.comp LaurentPolynomial.C = (sec s.snd).hom := by
        rw [← h2, sec_comp]; rfl
      rw [← chi_uniq q hq _ _ _ e1 e2]; rfl))

private theorem isUnit_q (q : ℕ) : IsUnit ((q : ℕ) : Γ(Gq q, ⊤)) := by
  have h0 : IsUnit ((q : ℕ) : Localization.Away (q : ℤ)) := by
    have := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (q : ℤ)) (q : ℤ)
    simpa using this
  have h1 : IsUnit ((q : ℕ) : LqR q) := by
    simpa using h0.map (LaurentPolynomial.C : Localization.Away (q : ℤ) →+* LqR q)
  simpa using h1.map (Scheme.ΓSpecIso (CommRingCat.of (LqR q))).inv.hom

private theorem coord (q : ℕ) (hq : IsUnit (q : S)) :
    ((Units.map (Spec.map (CommRingCat.ofHom (iot q hq))).appTop.hom.toMonoidHom (tq q) :
        (Γ(Spec (CommRingCat.of (LaurentPolynomial S)), ⊤))ˣ) : Γ(Spec (CommRingCat.of (LaurentPolynomial S)), ⊤)) =
      (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial S))).inv.hom (LaurentPolynomial.T 1) := by
  have n := congrArg (fun k => k.hom (LaurentPolynomial.T 1 : LqR q))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (iot q hq)))
  have n' : (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial S))).inv.hom (iot q hq (LaurentPolynomial.T 1)) =
      (Spec.map (CommRingCat.ofHom (iot q hq))).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (LqR q))).inv.hom (LaurentPolynomial.T 1)) := n
  rw [inclusion_T] at n'
  exact n'.symm

private theorem pull_cup {q : ℕ} {E E' : Spc} (s : E ⟶ E') {n m i j : ℤ} (x : Ht q E' n i) (y : Ht q E' m j) :
    pull _ s _ _ (cup q x y) = cup q (pull _ s _ _ x) (pull _ s _ _ y) :=
  GlobalTheory.T.cup_hypercohomologyPullback (ZMod q) (twPair q i j) s rfl x y

end UpperTheory.KG

theorem UpperTheory.bijective_etaleCohomology_multiplicativeGroup_prod :
    ∀ (q : ℕ) [NeZero q] (O : Type) [CommRing O], SH O → IsUnit (q : O) → ∀ m j : ℤ,
        Function.Bijective fun p : Ht q (sp O) (m + 1) (j + 1) × Ht q (sp O) m j =>
          pull _ (sch.map (prod.snd : Gq q ⨯ Spec (CommRingCat.of O) ⟶ Spec (CommRingCat.of O))) _ _ p.1 +
            cup q (pull _ (sch.map (prod.snd : Gq q ⨯ Spec (CommRingCat.of O) ⟶ Spec (CommRingCat.of O))) _ _ p.2)
              (pull _ (sch.map (prod.fst : Gq q ⨯ Spec (CommRingCat.of O) ⟶ Gq q)) _ _ (kappa q)) := by
  intro q _ O _ hO hq m j
  let i0 := IsLimit.conePointUniqueUpToIso (UpperTheory.KG.isProd q hq) (prodIsProd (Gq q) (Spec (CommRingCat.of O)))
  let i : Spec (CommRingCat.of (LaurentPolynomial O)) ≅ Gq q ⨯ Spec (CommRingCat.of O) := i0
  have h1 : i.hom ≫ (prod.fst : Gq q ⨯ Spec (CommRingCat.of O) ⟶ Gq q) =
      Spec.map (CommRingCat.ofHom (UpperTheory.KG.iot q hq)) :=
    IsLimit.conePointUniqueUpToIso_hom_comp (UpperTheory.KG.isProd q hq) (prodIsProd _ _) ⟨WalkingPair.left⟩
  have h2 : i.hom ≫ (prod.snd : Gq q ⨯ Spec (CommRingCat.of O) ⟶ Spec (CommRingCat.of O)) =
      Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : O →+* LaurentPolynomial O)) :=
    IsLimit.conePointUniqueUpToIso_hom_comp (UpperTheory.KG.isProd q hq) (prodIsProd _ _) ⟨WalkingPair.right⟩
  have hbij : Function.Bijective (pull _ (sch.map i.hom) (tw q (j + 1)) (m + 1)) := by
    refine Function.bijective_iff_has_inverse.2 ⟨pull _ (sch.map i.inv) _ _, fun x => ?_, fun x => ?_⟩
    · rw [← GlobalTheory.EtC.pull_comp, ← Functor.map_comp, i.inv_hom_id, CategoryTheory.Functor.map_id, GlobalTheory.EtC.pull_id]
    · rw [← GlobalTheory.EtC.pull_comp, ← Functor.map_comp, i.hom_inv_id, CategoryTheory.Functor.map_id, GlobalTheory.EtC.pull_id]
  have hk := UpperTheory.bijective_etaleCohomology_laurentPolynomial_of_coordinate_unit q O hO hq _ (UpperTheory.KG.coord q hq) m j
  refine (Function.Bijective.of_comp_iff' hbij _).1 ?_
  refine (congrArg Function.Bijective (funext fun p => ?_)).mpr hk
  have hκ : pull _ (sch.map i.hom) _ _ (pull _ (sch.map (prod.fst : Gq q ⨯ Spec (CommRingCat.of O) ⟶ Gq q)) _ _ (kappa q)) =
      kum q (Units.map (Spec.map (CommRingCat.ofHom (UpperTheory.KG.iot q hq))).appTop.hom.toMonoidHom (tq q)) := by
    rw [← GlobalTheory.EtC.pull_comp, ← Functor.map_comp, h1]
    exact (GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q).2.1 _ _ (UpperTheory.KG.isUnit_q q)
  simp only [Function.comp_apply, map_add (f := _), UpperTheory.KG.pull_cup, hκ]
  rw [← GlobalTheory.EtC.pull_comp, ← GlobalTheory.EtC.pull_comp, ← Functor.map_comp, h2]
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf

namespace UpperTheory.KunRed

private theorem pull_cup' {q : ℕ} {E E' : Spc} (f : E ⟶ E') {n m i j : ℤ} (a : Ht q E' n i) (b : Ht q E' m j) :
    pull _ f _ _ (cup q a b) = cup q (pull _ f _ _ a) (pull _ f _ _ b) :=
  GlobalTheory.T.cup_hypercohomologyPullback _ (twPair q i j) f rfl a b

private noncomputable def Phi (q : ℕ) (m j : ℤ) (V : Scheme.{0})
    (p : Ht q (sch.obj V) (m + 1) (j + 1) × Ht q (sch.obj V) m j) : Ht q (sch.obj (Gq q ⨯ V)) (m + 1) (j + 1) :=
  pull _ (sch.map (prod.snd : Gq q ⨯ V ⟶ V)) _ _ p.1 +
    cup q (pull _ (sch.map (prod.snd : Gq q ⨯ V ⟶ V)) _ _ p.2) (pull _ (sch.map (prod.fst : Gq q ⨯ V ⟶ Gq q)) _ _ (kappa q))

private theorem Phi_nat (q : ℕ) (m j : ℤ) {V' V : Scheme.{0}} (g : V' ⟶ V)
    (p : Ht q (sch.obj V) (m + 1) (j + 1) × Ht q (sch.obj V) m j) :
    pull _ (sch.map (prod.map (𝟙 (Gq q)) g)) _ _ (Phi q m j V p) =
      Phi q m j V' (pull _ (sch.map g) _ _ p.1, pull _ (sch.map g) _ _ p.2) := by
  have h1 : ∀ {n i : ℤ} (a : Ht q (sch.obj V) n i),
      pull _ (sch.map (prod.map (𝟙 (Gq q)) g)) _ _ (pull _ (sch.map (prod.snd : Gq q ⨯ V ⟶ V)) _ _ a) =
        pull _ (sch.map (prod.snd : Gq q ⨯ V' ⟶ V')) _ _ (pull _ (sch.map g) _ _ a) := by
    intro n i a
    rw [← pull_comp, ← pull_comp, ← sch.map_comp, ← sch.map_comp, prod.map_snd]
  have h2 : pull _ (sch.map (prod.map (𝟙 (Gq q)) g)) _ _ (pull _ (sch.map (prod.fst : Gq q ⨯ V ⟶ Gq q)) _ _ (kappa q)) =
      pull _ (sch.map (prod.fst : Gq q ⨯ V' ⟶ Gq q)) _ _ (kappa q) := by
    rw [← pull_comp, ← sch.map_comp, prod.map_fst, Category.comp_id]
  simp only [Phi]
  rw [map_add (f := _), pull_cup', h1, h1, h2]

private theorem pull_prod (q : ℕ) {n i : ℤ} {V'' V' V : Scheme.{0}} (h : V'' ⟶ V') (g : V' ⟶ V)
    (y : Ht q (sch.obj (Gq q ⨯ V)) n i) :
    pull _ (sch.map (prod.map (𝟙 (Gq q)) h)) _ _ (pull _ (sch.map (prod.map (𝟙 (Gq q)) g)) _ _ y) =
      pull _ (sch.map (prod.map (𝟙 (Gq q)) (h ≫ g))) _ _ y := by
  rw [← pull_comp, ← sch.map_comp, prod.map_map, Category.comp_id]

private theorem tw_finitary (q : ℕ) (i : ℤ) : Finitary (tw q i) :=
  GlobalTheory.T.etaleSheafOfRingFunctor_isFinitary (ZMod q) (twF q i) (GlobalTheory.T.tateTwistRingFunctor_preservesFilteredColimits q i)

private theorem affine_prod (W X : Scheme.{0}) [IsAffine W] [IsAffine X] : IsAffine (W ⨯ X) := by
  haveI : IsAffine (⊤_ Scheme.{0}) := IsAffine.of_isIso (terminalIsoIsTerminal specZIsTerminal).hom
  haveI : IsAffine (pullback (terminal.from W) (terminal.from X)) :=
    isAffine_of_isAffineHom (pullback.snd (terminal.from W) (terminal.from X))
  exact IsAffine.of_isIso (prodIsoPullback W X).hom

private theorem exists_nbhd (q : ℕ) [NeZero q] (T : Scheme.{0}) (hq : IsUnit (q : Γ(T, ⊤))) (u : T) :
    ∃ (O : Type) (_ : CommRing O) (s : Spec (CommRingCat.of O) ⟶ T) (I : Type) (_ : SmallCategory I) (_ : IsCofiltered I)
      (D : I ⥤ Scheme.{0}) (t : ∀ i, D.obj i ⟶ T) (e : ∀ i, Spec (CommRingCat.of O) ⟶ D.obj i),
      SH O ∧ IsUnit (q : O) ∧ (∃ v, s v = u) ∧ (∀ i, IsAffine (D.obj i) ∧ Etale (t i)) ∧ (∀ i, e i ≫ t i = s) ∧
      (∀ {i k : I} (f : k ⟶ i), D.map f ≫ t i = t k) ∧ (∀ {i k : I} (f : k ⟶ i), e k ≫ D.map f = e i) ∧
      (∀ n i' : ℤ, (∀ x : Ht q (sch.obj (Spec (CommRingCat.of O))) n i', ∃ (k : I) (y : Ht q (sch.obj (D.obj k)) n i'),
          pull _ (sch.map (e k)) _ _ y = x) ∧
        ∀ (k : I) (y : Ht q (sch.obj (D.obj k)) n i'), pull _ (sch.map (e k)) _ _ y = 0 →
          ∃ (k' : I) (f : k' ⟶ k), pull _ (sch.map (D.map f)) _ _ y = 0) ∧
      (∀ n i' : ℤ, ∀ (k : I) (y : Ht q (sch.obj (Gq q ⨯ D.obj k)) n i'),
        pull _ (sch.map (prod.map (𝟙 (Gq q)) (e k))) _ _ y = 0 →
          ∃ (k' : I) (f : k' ⟶ k), pull _ (sch.map (prod.map (𝟙 (Gq q)) (D.map f))) _ _ y = 0) := by
  obtain ⟨O, _, s, g, hs, v, hv⟩ := GlobalTheory.T.exists_strictlyHenselianEtaleStalk_over_point T (Over.mk (𝟙 T)) (by dsimp; infer_instance) u
  obtain ⟨I, _, _, G, π, ⟨hl⟩, hG⟩ := GlobalTheory.T.exists_cofiltered_limit_affine_etale_of_isStalk' T O s hs
  haveI : IsConnected I := IsCofiltered.isConnected I
  have hgs : g.left = s := by simpa using Over.w g
  have hc : IsLimit ((Over.forget T).mapCone (Cone.mk _ π)) := isLimitOfPreserves (Over.forget T) hl
  haveI := prod_preservesConnectedLimits (J := I) (Gq q)
  have hc2 := isLimitOfPreserves (prod.functor.obj (Gq q)) hc
  have hπ : ∀ {i k : I} (f : k ⟶ i), π.app k ≫ G.map f = π.app i := fun f => by
    simpa using (π.naturality f).symm
  refine ⟨O, inferInstance, s, I, inferInstance, inferInstance, G ⋙ Over.forget T, fun i => (G.obj i).hom,
    fun i => (π.app i).left, hs.1, ?_, ⟨v, ?_⟩, fun i => hG i, fun i => Over.w (π.app i), fun f => Over.w (G.map f),
    fun f => by
      have := congrArg (fun a => a.left) (hπ f)
      simpa using this, ?_, ?_⟩
  · have := (hq.map s.appTop.hom).map (Scheme.ΓSpecIso (CommRingCat.of O)).hom.hom
    simpa using this
  · rw [← hgs]; exact hv
  · intro n i'
    exact GlobalTheory.T.cohomologyContinuous_cofiltered_affine_limit (ZMod q) (tw q i') (tw_finitary q i') I (G ⋙ Over.forget T) _ hc (fun i => (hG i).1) n
  · intro n i' k y hy
    have hA : ∀ i, IsAffine (((G ⋙ Over.forget T) ⋙ prod.functor.obj (Gq q)).obj i) := fun i => by
      haveI := (hG i).1
      exact affine_prod (Gq q) (G.obj i).left
    exact (GlobalTheory.T.cohomologyContinuous_cofiltered_affine_limit (ZMod q) (tw q i') (tw_finitary q i') I ((G ⋙ Over.forget T) ⋙ prod.functor.obj (Gq q)) _ hc2
      hA n).2 k y hy

private theorem surj_part (q : ℕ) [NeZero q] (T : Scheme.{0}) (hq : IsUnit (q : Γ(T, ⊤))) (m j : ℤ)
    (y : Ht q (sch.obj (Gq q ⨯ T)) (m + 1) (j + 1)) :
    Loc T fun V g => ∃ p, Phi q m j V p = pull _ (sch.map (prod.map (𝟙 (Gq q)) g)) _ _ y := by
  refine (GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover T _ ?_).2 ?_
  · rintro V W g k ⟨p, hp⟩
    refine ⟨(pull _ (sch.map k) _ _ p.1, pull _ (sch.map k) _ _ p.2), ?_⟩
    rw [← Phi_nat, hp, pull_prod]
  intro u
  obtain ⟨O, _, s, I, _, _, D, t, e, hO, hqO, ⟨v, hv⟩, hD, het, hDt, hDe, c1, c2⟩ := exists_nbhd q T hq u
  obtain ⟨p, hp⟩ := (UpperTheory.bijective_etaleCohomology_multiplicativeGroup_prod q O hO hqO m j).2 (pull _ (sch.map (prod.map (𝟙 (Gq q)) s)) _ _ y)
  change Phi q m j _ p = _ at hp
  obtain ⟨i1, a, ha⟩ := (c1 (m + 1) (j + 1)).1 p.1
  obtain ⟨i2, b, hb⟩ := (c1 m j).1 p.2
  let k := IsCofiltered.min i1 i2
  let f1 : k ⟶ i1 := IsCofiltered.minToLeft i1 i2
  let f2 : k ⟶ i2 := IsCofiltered.minToRight i1 i2
  let a1 := pull _ (sch.map (D.map f1)) _ _ a
  let b1 := pull _ (sch.map (D.map f2)) _ _ b
  have ea : pull _ (sch.map (e k)) _ _ a1 = p.1 := by
    rw [← ha, ← pull_comp, ← sch.map_comp, hDe]
  have eb : pull _ (sch.map (e k)) _ _ b1 = p.2 := by
    rw [← hb, ← pull_comp, ← sch.map_comp, hDe]
  have hd : pull _ (sch.map (prod.map (𝟙 (Gq q)) (e k))) _ _
      (Phi q m j (D.obj k) (a1, b1) - pull _ (sch.map (prod.map (𝟙 (Gq q)) (t k))) _ _ y) = 0 := by
    rw [map_sub, Phi_nat, pull_prod, het, sub_eq_zero]
    simp only [ea, eb]
    exact hp
  obtain ⟨k', f', hf'⟩ := c2 _ _ k _ hd
  refine ⟨D.obj k', t k', (hD k').1, (hD k').2, ⟨e k' v, ?_⟩,
    (pull _ (sch.map (D.map f')) _ _ a1, pull _ (sch.map (D.map f')) _ _ b1), ?_⟩
  · rw [← Scheme.Hom.comp_apply, het, hv]
  · rw [map_sub, sub_eq_zero, Phi_nat, pull_prod, hDt] at hf'
    exact hf'

private theorem inj_part (q : ℕ) [NeZero q] (T : Scheme.{0}) (hq : IsUnit (q : Γ(T, ⊤))) (m j : ℤ)
    (p : Ht q (sch.obj T) (m + 1) (j + 1) × Ht q (sch.obj T) m j) (hp : Phi q m j T p = 0) :
    Loc T fun V g => pull _ (sch.map g) _ _ p.1 = 0 ∧ pull _ (sch.map g) _ _ p.2 = 0 := by
  refine (GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover T _ ?_).2 ?_
  · rintro V W g k ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [sch.map_comp, pull_comp, h1, map_zero]
    · rw [sch.map_comp, pull_comp, h2, map_zero]
  intro u
  obtain ⟨O, _, s, I, _, _, D, t, e, hO, hqO, ⟨v, hv⟩, hD, het, hDt, hDe, c1, c2⟩ := exists_nbhd q T hq u
  have h0 : Phi q m j _ (pull _ (sch.map s) _ _ p.1, pull _ (sch.map s) _ _ p.2) = 0 := by
    rw [← Phi_nat, hp, map_zero]
  have hz : Phi q m j (Spec (CommRingCat.of O)) 0 = 0 := by
    simp [Phi]
  have hinj : (pull _ (sch.map s) _ _ p.1, pull _ (sch.map s) _ _ p.2) =
      (0 : Ht q (sp O) (m + 1) (j + 1) × Ht q (sp O) m j) :=
    (UpperTheory.bijective_etaleCohomology_multiplicativeGroup_prod q O hO hqO m j).1 (h0.trans hz.symm)
  have s1 : pull _ (sch.map s) _ _ p.1 = 0 := congrArg Prod.fst hinj
  have s2 : pull _ (sch.map s) _ _ p.2 = 0 := congrArg Prod.snd hinj
  obtain ⟨i0⟩ : Nonempty I := IsCofiltered.nonempty
  have d1 : pull _ (sch.map (e i0)) _ _ (pull _ (sch.map (t i0)) _ _ p.1) = 0 := by
    rw [← pull_comp, ← sch.map_comp, het, s1]
  have d2 : pull _ (sch.map (e i0)) _ _ (pull _ (sch.map (t i0)) _ _ p.2) = 0 := by
    rw [← pull_comp, ← sch.map_comp, het, s2]
  obtain ⟨k1, f1, h1⟩ := (c1 _ _).2 i0 _ d1
  obtain ⟨k2, f2, h2⟩ := (c1 _ _).2 i0 _ d2
  let k := IsCofiltered.min k1 k2
  let g1 : k ⟶ k1 := IsCofiltered.minToLeft k1 k2
  let g2 : k ⟶ k2 := IsCofiltered.minToRight k1 k2
  refine ⟨D.obj k, t k, (hD k).1, (hD k).2, ⟨e k v, ?_⟩, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, het, hv]
  · have e1 : t k = D.map g1 ≫ D.map f1 ≫ t i0 := by rw [hDt, hDt]
    rw [e1, sch.map_comp, sch.map_comp, pull_comp, pull_comp, h1, map_zero]
  · have e2 : t k = D.map g2 ≫ D.map f2 ≫ t i0 := by rw [hDt, hDt]
    rw [e2, sch.map_comp, sch.map_comp, pull_comp, pull_comp, h2, map_zero]

end UpperTheory.KunRed

theorem UpperTheory.locally_surjective_multiplicativeGroupKunnethMap :
    ∀ (q : ℕ) [NeZero q] (T : Scheme.{0}), IsUnit (q : Γ(T, ⊤)) → ∀ m j : ℤ,
        (∀ y : Ht q (sch.obj (Gq q ⨯ T)) (m + 1) (j + 1), Loc T fun V g =>
          ∃ p : Ht q (sch.obj V) (m + 1) (j + 1) × Ht q (sch.obj V) m j,
            pull _ (sch.map (prod.snd : Gq q ⨯ V ⟶ V)) _ _ p.1 +
              cup q (pull _ (sch.map (prod.snd : Gq q ⨯ V ⟶ V)) _ _ p.2) (pull _ (sch.map (prod.fst : Gq q ⨯ V ⟶ Gq q)) _ _ (kappa q)) =
            pull _ (sch.map (prod.map (𝟙 (Gq q)) g)) _ _ y) ∧
        (∀ p : Ht q (sch.obj T) (m + 1) (j + 1) × Ht q (sch.obj T) m j,
          pull _ (sch.map (prod.snd : Gq q ⨯ T ⟶ T)) _ _ p.1 +
              cup q (pull _ (sch.map (prod.snd : Gq q ⨯ T ⟶ T)) _ _ p.2) (pull _ (sch.map (prod.fst : Gq q ⨯ T ⟶ Gq q)) _ _ (kappa q)) = 0 →
          Loc T fun V g => pull _ (sch.map g) _ _ p.1 = 0 ∧ pull _ (sch.map g) _ _ p.2 = 0) :=
  fun q _ T hq m j => ⟨fun y => UpperTheory.KunRed.surj_part q T hq m j y, fun p hp => UpperTheory.KunRed.inj_part q T hq m j p hp⟩

module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleCosetSumFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedOfSmoothOverFieldStatement

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PPtChart
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.ptChart_of :
    PtChart := by
  intro Y V hV κ _
  refine ⟨?_, ?_, ?_⟩
  · intro f g hfg
    unfold ptOf at hfg
    have h := Spec.map_injective ((cancel_mono hV.fromSpec).mp hfg)
    exact congrArg CommRingCat.Hom.hom h
  · intro φ f m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [Function.iterate_succ_apply', ih, pow_succ']
      unfold twist ptOf
      rw [← Spec.map_comp_assoc]
      rfl
  · intro Z r W hW h B _ ρ z
    unfold ptOf
    rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec r hV hW h, ← Spec.map_comp_assoc,
      ← Spec.map_comp_assoc]
    rfl
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PSnBasic
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

private theorem form_map' {A A' ι : Type} [CommRing A] [CommRing A'] [Fintype ι] (ρ : A →+* A') (c : ι → A) :
    (form c).map (MvPolynomial.map ρ) = form (fun k => ρ (c k)) := by
  unfold form
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  congr 2
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, MvPolynomial.map_C, MvPolynomial.map_X]

private theorem form_eval' {A ι : Type} [CommRing A] [Fintype ι] (x y : ι → A) :
    Polynomial.evalRingHom (∑ k, MvPolynomial.C (x k) * MvPolynomial.X k) (form y) =
      ∑ k, MvPolynomial.C (x k - y k) * MvPolynomial.X k := by
  unfold form
  show Polynomial.eval _ _ = _
  rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => by rw [map_sub, sub_mul]

private theorem form_natDegree' {A ι : Type} [CommRing A] [Fintype ι] [Nontrivial A] (v : Multiset (ι → A)) :
    ((v.map form).prod).natDegree = v.card := by
  rw [Polynomial.natDegree_multiset_prod_of_monic]
  · simp only [Multiset.map_map, Function.comp_def, form, Polynomial.natDegree_X_sub_C]
    simp
  · intro f hf
    obtain ⟨c, -, rfl⟩ := Multiset.mem_map.1 hf
    exact Polynomial.monic_X_sub_C _

theorem UpperTheory.Gal.crystallineComparison.snBasic_of :
    SameNormBasic := by
  intro A ι _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A' _ ρ u u' h
    unfold SameNorm at h ⊢
    have e := congrArg (Polynomial.map (MvPolynomial.map ρ)) h
    simp only [Polynomial.map_multiset_prod, Multiset.map_map, Function.comp_def, form_map'] at e
    simpa [Multiset.map_map, Function.comp_def] using e
  · intro x u u' h
    simp only [SameNorm, Multiset.map_cons, Multiset.prod_cons] at h ⊢
    exact (show (form x).Monic from Polynomial.monic_X_sub_C _).isRegular.left h
  · intro _ u u' h
    unfold SameNorm at h
    have e := congrArg Polynomial.natDegree h
    rwa [form_natDegree', form_natDegree'] at e
  · intro x u u' h hx
    unfold SameNorm at h
    have e := congrArg (Polynomial.evalRingHom (∑ k, MvPolynomial.C (x k) * MvPolynomial.X k)) h
    rw [map_multiset_prod, map_multiset_prod, Multiset.map_map, Multiset.map_map] at e
    simp only [Function.comp_def, form_eval'] at e
    rw [← e]
    apply Multiset.prod_eq_zero
    exact Multiset.mem_map.2 ⟨x, hx, by simp⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PSecChart
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.secChart_of :
    SecChart := by
  intro l Y T U hU
  haveI := T.fin
  letI := T.alg U
  have hZ : IsAffineOpen (T.p ⁻¹ᵁ U) := hU.preimage T.p
  have hsq : Spec.map (T.p.app U) ≫ hU.fromSpec = hZ.fromSpec ≫ T.p := by
    rw [Scheme.Hom.app_eq_appLE]
    exact IsAffineOpen.SpecMap_appLE_fromSpec T.p hU hZ le_rfl
  refine ⟨hZ, fun B _ _ => ?_⟩
  have hrange : ∀ z : T.Sec (ptOf hU B (algebraMap Γ(Y, U) B)),
      Set.range z.1 ⊆ Set.range hZ.fromSpec := by
    rintro z _ ⟨x, rfl⟩
    rw [hZ.range_fromSpec]
    have hx : (z.1 ≫ T.p) x ∈ Set.range hU.fromSpec := by
      rw [z.2]
      unfold ptOf
      rw [Scheme.Hom.comp_apply]
      exact ⟨_, rfl⟩
    rw [hU.range_fromSpec] at hx
    simpa using hx
  have hlift : ∀ z : T.Sec (ptOf hU B (algebraMap Γ(Y, U) B)),
      Spec.map (T.p.app U ≫ Spec.preimage (IsOpenImmersion.lift hZ.fromSpec z.1 (hrange z)))
        = Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, U) B)) := by
    intro z
    rw [← cancel_mono hU.fromSpec, Spec.map_comp, Category.assoc, hsq, Spec.map_preimage,
      IsOpenImmersion.lift_fac_assoc]
    exact z.2
  refine ⟨{ toFun := fun g => ⟨Spec.map (CommRingCat.ofHom g.toRingHom) ≫ hZ.fromSpec, ?_⟩,
            invFun := fun z =>
              { toRingHom := (Spec.preimage (IsOpenImmersion.lift hZ.fromSpec z.1 (hrange z))).hom
                commutes' := fun r => by
                  have h := congrArg (fun φ => φ.hom r) (Spec.map_injective (hlift z))
                  exact h }
            left_inv := fun g => ?_
            right_inv := fun z => ?_ }, fun z => rfl⟩
  · show _ = Spec.map _ ≫ hU.fromSpec
    rw [Category.assoc, ← hsq, ← Spec.map_comp_assoc]
    congr 2
    ext r
    exact g.commutes r
  · apply AlgHom.coe_ringHom_injective
    show (Spec.preimage _).hom = (CommRingCat.ofHom g.toRingHom).hom
    congr 1
    apply Spec.map_injective
    rw [Spec.map_preimage]
    exact (IsOpenImmersion.lift_uniq _ _ _ _ rfl).symm
  · apply Subtype.ext
    show Spec.map (Spec.preimage _) ≫ _ = _
    rw [Spec.map_preimage, IsOpenImmersion.lift_fac]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PMatchVal
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.matchVal_of :
    IdemCover → ValLocal → MatchPart → MatchingVal := by
  intro hC hL hP B _ ϖ hϖ hv ι _ I I' _ _ _ _ N hI hI' u u' hS
  classical
  let J : (I ≃ I') → Ideal B := fun σ =>
    { carrier := {b | ∀ i k, ϖ ∣ b * (u i k - u' (σ i) k)}
      add_mem' := by
        intro a b ha hb i k
        rw [add_mul]
        exact dvd_add (ha i k) (hb i k)
      zero_mem' := by
        intro i k
        simp
      smul_mem' := by
        intro c b hb i k
        rw [smul_eq_mul, mul_assoc]
        exact Dvd.dvd.mul_left (hb i k) c }
  have hJ : ∀ σ b, b ∈ J σ ↔ ∀ i k, ϖ ∣ b * (u i k - u' (σ i) k) := fun _ _ => Iff.rfl
  obtain ⟨e, he, hmem⟩ := hC B (I ≃ I') J (by
    intro 𝔪 h𝔪
    let D : Finset B := (Finset.univ : Finset (I × I' × ι)).image fun p => u p.1 p.2.2 - u' p.2.1 p.2.2
    have hD : ∀ i i' k, u i k - u' i' k ∈ D := fun i i' k =>
      Finset.mem_image.2 ⟨(i, i', k), Finset.mem_univ _, rfl⟩
    obtain ⟨e, hid, hnot, h1, h2⟩ := hL B ϖ hv 𝔪 h𝔪.isPrime D ((N + 1) ^ N)
    obtain ⟨σ, hσ⟩ := hP B ϖ hϖ ι I I' N hI hI' u u' hS e hid
      (fun i i' k m hm => h1 _ (hD i i' k) m hm)
      (fun i i' k k' h => h2 _ (hD i i' k) _ (hD i i' k') h)
    exact ⟨σ, e, (hJ σ e).2 hσ, hid, hnot⟩)
  exact ⟨e, he, fun σ i k => (hJ σ (e σ)).1 (hmem σ) i k⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PSplitsField
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

private theorem exists_forall_algHom_pi_eq_apply_of_finite {K P : Type} [Field K] [Finite P] (ψ : (P → K) →ₐ[K] K) :
    ∃ p, ∀ x, ψ x = x p := by
  classical
  have hex : ∃ p, ψ (Pi.single p 1) ≠ 0 := by
    by_contra h
    push_neg at h
    have := Fintype.ofFinite P
    have h1 : (1 : P → K) = ∑ p, Pi.single p 1 := by
      simpa using (Finset.univ_sum_single (1 : P → K)).symm
    have h2 : ψ 1 = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [h1, map_sum]
      simp [h]
    simp at h2
  obtain ⟨p, hp⟩ := hex
  refine ⟨p, fun x => ?_⟩
  have hid : ψ (Pi.single p 1) = 1 := by
    have h2 : ψ (Pi.single p 1) * ψ (Pi.single p 1) = ψ (Pi.single p 1) := by
      rw [← map_mul]
      congr 1
      ext i
      by_cases h : i = p <;> simp [Pi.single_apply, h]
    exact (mul_left_inj' hp).1 (h2.trans (one_mul _).symm)
  have hx : x * Pi.single p 1 = algebraMap K (P → K) (x p) * Pi.single p 1 := by
    ext i
    by_cases h : i = p <;> simp [Pi.single_apply, h]
  have h3 := congrArg ψ hx
  rw [map_mul, map_mul, AlgHom.commutes, hid] at h3
  simpa using h3

theorem UpperTheory.Gal.crystallineComparison.splitsField_of :
    SplitsField := by
  intro R S K _ _ _ _ _ _ hE
  classical
  have hfin : Module.Finite K (K ⊗[R] S) := Algebra.FormallyUnramified.finite_of_free K (K ⊗[R] S)
  haveI : IsArtinianRing (K ⊗[R] S) := isArtinian_of_tower K inferInstance
  haveI : Finite (PrimeSpectrum (K ⊗[R] S)) := inferInstance
  let e := Algebra.FormallyEtale.equivPiOfIsSepClosed K (K ⊗[R] S)
  let F := splitMap (R := R) (S := S) (B := K) (I := S →ₐ[R] K) (fun z => z)
  let L : (S →ₐ[R] K) → ((K ⊗[R] S) →ₐ[K] K) := fun ψ => (Pi.evalAlgHom K (fun _ => K) ψ).comp F
  have hL : ∀ ψ x, L ψ x = F x ψ := fun _ _ => rfl
  have hLs : ∀ ψ (s : S), L ψ (1 ⊗ₜ s) = ψ s := by
    intro ψ s
    simp [L, F, splitMap]
  choose q hq using fun ψ => exists_forall_algHom_pi_eq_apply_of_finite ((L ψ).comp e.symm.toAlgHom)
  have hLe : ∀ ψ x, L ψ x = e x (q ψ) := by
    intro ψ x
    simpa using hq ψ (e x)
  have qinj : Function.Injective q := by
    intro ψ1 ψ2 h
    ext s
    rw [← hLs, ← hLs, hLe, hLe, h]
  have hsec : ∀ p, ∃ ψ, q ψ = p := by
    intro p
    let g : (K ⊗[R] S) →ₐ[K] K := (Pi.evalAlgHom K (fun _ => K) p).comp e.toAlgHom
    let ψ : S →ₐ[R] K := (g.restrictScalars R).comp Algebra.TensorProduct.includeRight
    have hg : L ψ = g := by
      apply Algebra.TensorProduct.ext
      · exact Subsingleton.elim _ _
      · ext s
        simp [hLs, ψ]
    refine ⟨ψ, ?_⟩
    have h1 := hLe ψ (e.symm (Pi.single p 1))
    rw [hg] at h1
    simp only [g, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgHom.coe_coe,
      AlgEquiv.apply_symm_apply, Pi.evalAlgHom_apply] at h1
    by_contra hne
    simp [Pi.single_apply, hne] at h1
  refine ⟨Finite.of_injective q qinj, ?_⟩
  show Function.Bijective F
  constructor
  · intro x y h
    apply e.injective
    funext p
    obtain ⟨ψ, rfl⟩ := hsec p
    rw [← hLe, ← hLe, hL, hL, h]
  · intro v
    refine ⟨e.symm (Function.extend q v 0), ?_⟩
    funext ψ
    rw [← hL, hLe, e.apply_symm_apply, qinj.extend_apply]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PSmoothRed
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.smoothRed_of :
    SmoothReduced :=
  GlobalTheory.T.isReduced_of_smooth_over_field'
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PDetSplit
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.detSplit_of :
    DetSplit := by
  intro A _ m I _ _ P Q hPQ d
  have h1 : 1 - Q * P + Q * Matrix.diagonal d * P = 1 + Q * ((Matrix.diagonal d - 1) * P) := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, ← Matrix.mul_assoc]
    abel
  rw [h1, Matrix.det_one_add_mul_comm, Matrix.mul_assoc, hPQ, Matrix.mul_one, add_sub_cancel,
    Matrix.det_diagonal]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PEtUnit
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.etUnit_of :
    EtOfUnit := by
  intro l R S B _ _ _ _ _ h hl
  have hl' : IsUnit (algebraMap R B (l : R)) := by simpa using hl
  letI : Algebra (Localization.Away (l : R)) B :=
    (IsLocalization.Away.lift (S := Localization.Away (l : R)) (l : R) hl').toAlgebra
  haveI : IsScalarTower R (Localization.Away (l : R)) B :=
    IsScalarTower.of_algebraMap_eq fun r =>
      (IsLocalization.Away.lift_eq (S := Localization.Away (l : R)) (l : R) hl' r).symm
  exact Algebra.Etale.of_equiv
    (Algebra.TensorProduct.cancelBaseChange R (Localization.Away (l : R)) B B S)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PEtAway
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.etAway_of :
    SecChart → EtChart → EtAwayChart := by
  intro hsec het l Y T U hU
  obtain ⟨hZ, hpts⟩ := hsec l Y T U hU
  have hfin := @IsFinite.finite_app _ _ _ T.fin U hU
  letI : Algebra Γ(Y, U) Γ(T.Z, T.p ⁻¹ᵁ U) := (T.p.app U).hom.toAlgebra
  refine EtAway.mk hfin (het l Y T U hU) ?_
  intro K _ _ _ hl
  obtain ⟨e, -⟩ := hpts K
  rw [Nat.card_congr e]
  exact T.deg K hl _
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PLiftP
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.liftingProperty :
    LiftP := by
  intro R T ι _ _ f N' h
  have hl : N' ∈ Polynomial.lifts (MvPolynomial.map (σ := ι) f) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro a
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro c hc
    obtain ⟨m, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hc
    exact h a m
  rw [Polynomial.lifts_iff_set_range] at hl
  obtain ⟨N, hN⟩ := hl
  exact ⟨N, hN⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PPermMap
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.permMap_of :
    PermOfMap := by
  classical
  intro I I' P _ _ f g h
  have hc : ∀ p : P, Fintype.card {i // f i = p} = Fintype.card {j // g j = p} := by
    intro p
    have hp := congrArg (Multiset.count p) h
    simp only [Multiset.count_map] at hp
    rw [Fintype.card_subtype, Fintype.card_subtype]
    simpa [Finset.card_def, Finset.filter_val, eq_comm] using hp
  let e : ∀ p, {i // f i = p} ≃ {j // g j = p} := fun p => Fintype.equivOfCardEq (hc p)
  refine ⟨(Equiv.sigmaFiberEquiv f).symm.trans ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv g)), ?_⟩
  intro i
  show f i = g ((e (f i)) ⟨i, rfl⟩).1
  exact ((e (f i)) ⟨i, rfl⟩).2.symm
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PCongrRad
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.congrRad_of :
    CongrRad := by
  intro R _ 𝔞 h𝔞 ι N N' H B' _ g hg
  have key : ∀ (a : ℕ) (m : ι →₀ ℕ),
      AddMonoidAlgebra.coeff (N.coeff a) m - AddMonoidAlgebra.coeff (N'.coeff a) m ∈ 𝔞 := by
    intro a m
    rw [← h𝔞.radical, ← Ideal.sInf_minimalPrimes, Ideal.mem_sInf]
    intro 𝔭 h𝔭
    obtain ⟨κ, _, f, hker, hf⟩ := H 𝔭 h𝔭
    rw [← hker, RingHom.mem_ker, map_sub, sub_eq_zero]
    have := congrArg (fun p => AddMonoidAlgebra.coeff (p.coeff a) m) hf
    simpa [mapP, Polynomial.coeff_map, MvPolynomial.coeff_map] using this
  refine Polynomial.ext fun a => MvPolynomial.ext _ _ fun m => ?_
  simp only [mapP, Polynomial.coeff_map, MvPolynomial.coeff_map]
  rw [← sub_eq_zero, ← map_sub]
  exact hg _ (key a m)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PCoeffInt
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.coeffInt_of :
    CoeffInt := by
  intro R T _ _ _ ι I _ _ c hc a m
  let c' : I → ι → integralClosure R T := fun i k => ⟨c i k, hc i k⟩
  let f : MvPolynomial ι (integralClosure R T) →+* MvPolynomial ι T :=
    MvPolynomial.map (algebraMap (integralClosure R T) T)
  have hform : ∀ i, form (c i) = (form (c' i)).map f := by
    intro i
    simp [form, f, Polynomial.map_sub, MvPolynomial.map_C, c']
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Polynomial.map_sum]
    simp [Polynomial.map_mul, Polynomial.map_C, MvPolynomial.map_C, MvPolynomial.map_X]
  have hP : (∏ i, form (c i)) = (∏ i, form (c' i)).map f := by
    rw [Polynomial.map_prod]
    exact Finset.prod_congr rfl fun i _ => hform i
  rw [hP, Polynomial.coeff_map]
  simp only [f, MvPolynomial.coeff_map]
  exact (((∏ i, form (c' i)).coeff a).coeff m).2
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PPtsProd
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.ptsProd_of :
    PtsProd := by
  intro B B' _ _ ρ ι J _ _ I _ a v
  have hf : ∀ c : ι → B, Polynomial.map (MvPolynomial.map ρ) (form c) = form (fun k => ρ (c k)) := by
    intro c
    set_option synthInstance.maxHeartbeats 100000 in
      simp [form, Polynomial.map_sub, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C]
  have key : ∀ (m : J → Multiset (ι → B')) (s : Finset J),
      (Multiset.map form (∑ j ∈ s, a j • m j)).prod = ∏ j ∈ s, (Multiset.map form (m j)).prod ^ a j := by
    intro m s
    classical
    refine Finset.induction_on s (by simp) ?_
    intro j s hj ih
    rw [Finset.sum_insert hj, Finset.prod_insert hj, Multiset.map_add (f := _), Multiset.prod_add, ih,
      Multiset.map_nsmul, Multiset.prod_nsmul]
  simp only [pts, mapP]
  rw [key, Polynomial.map_prod]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [Polynomial.map_pow, Polynomial.map_prod, Multiset.map_map]
  congr 1
  rw [Finset.prod_eq_multiset_prod]
  simp [Function.comp_def, hf]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PValPts
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.valPts_of :
    ValPts := by
  intro R S V _ _ _ _ _ _ _ _
  have hinj : Function.Injective (IsScalarTower.toAlgHom R V (FractionRing V)) :=
    IsFractionRing.injective V (FractionRing V)
  constructor
  · intro z z' h
    ext s
    apply hinj
    simpa only [AlgHom.comp_apply] using AlgHom.congr_fun h s
  · intro φ
    have hmem : ∀ s, φ s ∈ (IsScalarTower.toAlgHom R V (FractionRing V)).range := by
      intro s
      have h1 : IsIntegral R (φ s) := (Algebra.IsIntegral.isIntegral s).map φ
      have h2 : IsIntegral V (φ s) := h1.tower_top
      obtain ⟨v, hv⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
      exact (AlgHom.mem_range _).2 ⟨v, hv⟩
    let e := AlgEquiv.ofInjective (IsScalarTower.toAlgHom R V (FractionRing V)) hinj
    refine ⟨e.symm.toAlgHom.comp (φ.codRestrict _ hmem), ?_⟩
    ext s
    have h := e.apply_symm_apply ⟨φ s, hmem s⟩
    exact congrArg Subtype.val h
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PSplitsEquiv
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.splitsEquiv_of :
    SplitsOfEquiv := by
  intro R S B _ _ _ _ _ I e
  let z : I → (S →ₐ[R] B) := fun i =>
    (((Pi.evalAlgHom B (fun _ => B) i).comp e.toAlgHom).restrictScalars R).comp
      Algebra.TensorProduct.includeRight
  refine ⟨z, ?_⟩
  have h : ∀ x, splitMap z x = e x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [hx, hy]
    | tmul b s =>
      funext i
      have hb : b ⊗ₜ[R] s = b • ((1 : B) ⊗ₜ[R] s) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [splitMap_tmul, hb, map_smul, Pi.smul_apply, smul_eq_mul]
      rfl
  have hf : (splitMap z : B ⊗[R] S → (I → B)) = e := funext h
  unfold Splits
  rw [hf]
  exact e.bijective
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PCharts
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.charts_of :
    ChartsExist := by
  intro l Y hY J _ T y
  haveI : ∀ j, IsFinite (T j).p := fun j => (T j).fin
  let S : Set Y := {y} ∪ ⋃ j, (T j).r '' ((T j).p ⁻¹' {y})
  have hS : S.Finite := (Set.finite_singleton y).union
    (Set.finite_iUnion fun j => ((T j).p.finite_preimage_singleton y).image _)
  obtain ⟨V, hV, hSV⟩ := hY hS.toFinset
  have hSV' : ∀ x ∈ S, x ∈ V := fun x hx => hSV x (hS.mem_toFinset.mpr hx)
  have hclosed : IsClosed (⋃ j, (T j).p '' ((T j).r ⁻¹ᵁ V : Set _)ᶜ) :=
    isClosed_iUnion_of_finite fun j => (T j).p.isClosedMap _ ((T j).r ⁻¹ᵁ V).isOpen.isClosed_compl
  let O : Y.Opens := ⟨(⋃ j, (T j).p '' ((T j).r ⁻¹ᵁ V : Set _)ᶜ)ᶜ, hclosed.isOpen_compl⟩
  have hyO : y ∈ O := by
    show y ∈ (⋃ j, (T j).p '' ((T j).r ⁻¹ᵁ V : Set _)ᶜ)ᶜ
    rintro hy
    obtain ⟨j, z, hz, hzy⟩ := Set.mem_iUnion.mp hy
    apply hz
    show (T j).r z ∈ V
    exact hSV' _ (Or.inr (Set.mem_iUnion.mpr ⟨j, z, hzy, rfl⟩))
  obtain ⟨U, hU, hyU, hUO⟩ := exists_isAffineOpen_mem_and_subset hyO
  refine ⟨U, V, hU, hV, hyU, fun j z hz => ?_⟩
  by_contra h
  have hz' : (T j).p z ∈ (O : Set Y) := hUO hz
  exact hz' (Set.mem_iUnion.mpr ⟨j, z, h, rfl⟩)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PRankDeg
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.rankDeg_of :
    SplitsField → RankOfDeg := by
  intro hSF A S _ _ _ _ _ d hd
  funext p
  letI : Algebra A (AlgebraicClosure p.asIdeal.ResidueField) :=
    ((algebraMap p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField)).comp
      (algebraMap A p.asIdeal.ResidueField)).toAlgebra
  let q : PrimeSpectrum (AlgebraicClosure p.asIdeal.ResidueField) := ⟨⊥, Ideal.isPrime_bot⟩
  have hq : PrimeSpectrum.comap (algebraMap A (AlgebraicClosure p.asIdeal.ResidueField)) q = p := by
    ext x
    change algebraMap A (AlgebraicClosure p.asIdeal.ResidueField) x ∈ (⊥ : Ideal _) ↔ x ∈ p.asIdeal
    rw [Ideal.mem_bot]
    change algebraMap p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField)
      (algebraMap A p.asIdeal.ResidueField x) = 0 ↔ x ∈ p.asIdeal
    rw [map_eq_zero_iff _ (algebraMap p.asIdeal.ResidueField _).injective,
      Ideal.algebraMap_residueField_eq_zero]
  rw [← hq, ← Module.rankAtStalk_baseChange q, Module.rankAtStalk_eq_finrank_of_free]
  obtain ⟨hfin, hsp⟩ := hSF A S (AlgebraicClosure p.asIdeal.ResidueField) inferInstance
  haveI := Fintype.ofFinite (S →ₐ[A] AlgebraicClosure p.asIdeal.ResidueField)
  have e := AlgEquiv.ofBijective (splitMap fun z => z) hsp
  have h1 := e.toLinearEquiv.finrank_eq
  rw [Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card,
    hd (AlgebraicClosure p.asIdeal.ResidueField)] at h1
  simp [h1]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PBaseChart
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.baseChart_of :
    BaseOfSmooth → BaseOfChart := by
  intro h
  unfold BaseOfChart
  intro l O _ _ _ ϖ hϖ hl hlu Y g hg U hU
  let φ : O →+* Γ(Y, U) :=
    (g.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom
  have hφ : ∀ a : O, φ a = (Y.presheaf.map (homOfLE le_top).op).hom
      ((g.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom a)) := fun a => rfl
  have hsm : φ.Smooth := by
    refine RingHom.Smooth.comp (RingHom.Smooth.of_bijective ?_) ?_
    · exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of O)).inv)
    · exact HasRingHomProperty.appLE @Smooth g hg ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ (by simp)
  letI : Algebra O Γ(Y, U) := φ.toAlgebra
  haveI : Algebra.Smooth O Γ(Y, U) := hsm
  have hb := h l O Γ(Y, U) ϖ hϖ hl hlu
  have hϖφ : (algebraMap O Γ(Y, U)) ϖ = (Y.presheaf.map (homOfLE le_top).op).hom (fn g ϖ) := hφ ϖ
  rw [hϖφ] at hb
  refine ⟨hb, 1, ?_⟩
  have hmem : (l : O) ∈ Ideal.span {ϖ} := by
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ]
    exact (IsLocalRing.mem_maximalIdeal _).mpr hlu
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  rw [pow_one, ← hϖφ, Ideal.mem_span_singleton']
  refine ⟨algebraMap O Γ(Y, U) c, ?_⟩
  rw [← map_mul, hc, map_natCast]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PBaseSmooth
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.baseSmooth_of :
    SmoothClosed → SmoothReduced → BaseOfSmooth := by
  intro hC hR l O R _ _ _ _ _ _ ϖ hϖ hl _
  have hflat : Module.Flat O R := Algebra.Smooth.flat O R
  have hlO : (l : O) ∈ nonZeroDivisors O := mem_nonZeroDivisors_of_ne_zero hl
  refine ⟨?_, hC l O R hl, ?_⟩
  · have hreg : IsSMulRegular R (l : O) := Module.Flat.isSMulRegular_of_nonZeroDivisors hlO
    have key : ∀ x : R, (l : R) * x = 0 → x = 0 := by
      intro x hx
      apply hreg
      simp only [Algebra.smul_def, map_natCast, mul_zero]
      exact hx
    rw [mem_nonZeroDivisors_iff]
    exact ⟨key, fun x hx => key x (by rw [mul_comm]; exact hx)⟩
  · rw [Ideal.isRadical_iff_quotient_reduced]
    have hspan : Ideal.span {(algebraMap O R) ϖ} = (IsLocalRing.maximalIdeal O).map (algebraMap O R) := by
      rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span, Set.image_singleton]
    rw [hspan]
    haveI : Algebra.Smooth (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] R) :=
      Algebra.Smooth.baseChange O R (IsLocalRing.ResidueField O)
    have hred : IsReduced (IsLocalRing.ResidueField O ⊗[O] R) :=
      hR (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] R)
    haveI : IsReduced ((O ⧸ IsLocalRing.maximalIdeal O) ⊗[O] R) := hred
    let e := ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot R (IsLocalRing.maximalIdeal O)).restrictScalars O).trans
      (Algebra.TensorProduct.comm O R (O ⧸ IsLocalRing.maximalIdeal O))
    exact isReduced_of_injective e.toRingHom e.injective
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PGaussLin
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.gaussLin_of :
    GaussLin := by
  intro A ι _ c s hs hc
  by_contra hc0
  have hmem : ∀ a : A, a ∈ (Submodule.span A {c}).annihilator ↔ a * c = 0 := by
    intro a
    rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul]
  have hIt : (Submodule.span A {c}).annihilator ≠ ⊤ := by
    intro h
    have h1 : (1:A) ∈ (Submodule.span A {c}).annihilator := by
      rw [h]; exact Submodule.mem_top
    rw [hmem, one_mul] at h1
    exact hc0 h1
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal _ hIt
  haveI := hM
  letI := Ideal.Quotient.field M
  have hprod : MvPolynomial.map (Ideal.Quotient.mk M) s.prod = 0 := by
    ext m
    change (MvPolynomial.map (Ideal.Quotient.mk M) s.prod).coeff m = 0
    rw [MvPolynomial.coeff_map, Ideal.Quotient.eq_zero_iff_mem]
    apply hIM
    rw [hmem, mul_comm, ← MvPolynomial.coeff_C_mul, hc]
    rfl
  rw [map_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hprod
  obtain ⟨p, hp, hp0⟩ := hprod
  obtain ⟨m, hm⟩ := hs p hp
  have h2 := congrArg (AddMonoidAlgebra.coeff · m) hp0
  rw [MvPolynomial.coeff_map, hm, map_one, MvPolynomial.coeff_zero] at h2
  exact one_ne_zero h2
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PGenMul
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.genMul_of :
    GenericMulOfProd := by
  intro K _ n α hα t hcard hmem hprod
  classical
  by_cases hn : Nonempty (Fin n)
  · let g := Function.invFun α
    have hg : ∀ x ∈ t, α (g x) = x := fun x hx => by
      obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 (hmem x hx)
      exact Function.invFun_eq ⟨i, rfl⟩
    let u := t.map g
    have hu : u.map α = t := by
      rw [Multiset.map_map]
      conv_rhs => rw [← Multiset.map_id t]
      exact Multiset.map_congr rfl hg
    have key := hα (fun i => u.count i) ?_ ?_
    · have hu1 : u = Finset.univ.val := Multiset.ext.2 fun i => by
        rw [key i, Multiset.count_eq_one_of_mem Finset.univ.nodup (Finset.mem_univ i)]
      rw [← hu, hu1]
    · rw [Multiset.sum_count_eq_card (fun a _ => Finset.mem_univ a)]
      simp [u, hcard]
    · calc ∏ i, α i ^ u.count i = (u.map α).prod := by
            rw [Finset.prod_multiset_map_count]
            exact (Finset.prod_subset (Finset.subset_univ _) (fun i _ hi => by
              rw [Multiset.count_eq_zero.2 (by simpa using hi), pow_zero])).symm
        _ = t.prod := by rw [hu]
        _ = ∏ i, α i := by rw [hprod, Finset.prod_eq_multiset_prod]
  · have h0 : (Finset.univ : Finset (Fin n)).val = 0 := by
      rw [Finset.univ_eq_empty_iff.2 (not_nonempty_iff.1 hn)]
      rfl
    rw [h0, Multiset.map_zero] at hcard ⊢
    exact Multiset.card_eq_zero.1 hcard
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PSplitsBC
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.splitsBC_of :
    SplitsBC := by
  intro R R' S B _ _ _ _ _ _ _ _ _ I z hz
  let z' : I → (R' ⊗[R] S →ₐ[R'] B) := fun i =>
    Algebra.TensorProduct.lift (Algebra.ofId R' B) (z i) (fun _ _ => Commute.all _ _)
  have hz' : ∀ i (r : R') (s : S), z' i (r ⊗ₜ s) = algebraMap R' B r * z i s := by
    intro i r s
    simp [z', Algebra.ofId_apply]
  refine ⟨z', ?_, ?_⟩
  · have key : ∀ x, splitMap z' x =
        splitMap z (Algebra.TensorProduct.cancelBaseChange R R' B B S x) := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simp only [map_add (f := _), ha, hb]
      | tmul b y =>
        induction y using TensorProduct.induction_on with
        | zero => simp
        | add a c ha hc => simp only [tmul_add, map_add (f := _), ha, hc]
        | tmul r s =>
          funext i
          rw [splitMap_tmul, hz', Algebra.TensorProduct.cancelBaseChange_tmul, splitMap_tmul]
          simp [Algebra.smul_def, mul_assoc, mul_left_comm, mul_comm]
    have hfun : (⇑(splitMap z') : B ⊗[R'] (R' ⊗[R] S) → (I → B)) =
        (splitMap z) ∘ (Algebra.TensorProduct.cancelBaseChange R R' B B S) := funext key
    unfold Splits
    rw [hfun]
    exact hz.comp (AlgEquiv.bijective _)
  · intro i s
    rw [hz']
    simp
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PGenChart
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.genChart_of :
    GenChart := by
  intro Y π U hU V _ _ f hmin
  set πU := Y.presheaf.map (homOfLE le_top).op π with hπU
  let P : PrimeSpectrum Γ(Y, U) := ⟨Ideal.comap f (IsLocalRing.maximalIdeal V), inferInstance⟩
  have hx : ptOf hU V f (IsLocalRing.closedPoint V) = hU.fromSpec P := rfl
  have hinU : ∀ q : PrimeSpectrum Γ(Y, U), hU.fromSpec q ∈ U := by
    intro q
    have : hU.fromSpec q ∈ Set.range hU.fromSpec := ⟨q, rfl⟩
    rw [hU.range_fromSpec] at this
    exact this
  have hmem : ∀ q : PrimeSpectrum Γ(Y, U), hU.fromSpec q ∈ Y.basicOpen π ↔ πU ∉ q.asIdeal := by
    intro q
    have h1 : q ∈ PrimeSpectrum.basicOpen πU ↔ hU.fromSpec q ∈ Y.basicOpen πU := by
      rw [← hU.fromSpec_preimage_basicOpen]
      rfl
    rw [← PrimeSpectrum.mem_basicOpen, h1, hπU, Scheme.basicOpen_res]
    exact ⟨fun h => ⟨hinU q, h⟩, fun h => h.2⟩
  rw [hx]
  refine ⟨?_, ?_⟩
  · rw [hmem, not_not]
    exact hmin.1.2 (Ideal.subset_span (Set.mem_singleton _))
  · intro x' hx' hsp
    have hx'U : x' ∈ U := hsp.mem_open U.isOpen (hinU P)
    obtain ⟨q, rfl⟩ : x' ∈ Set.range hU.fromSpec := by
      rw [hU.range_fromSpec]
      exact hx'U
    have hqp : q ⤳ P := hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff.mp hsp
    have hqp' : q.asIdeal ≤ P.asIdeal := (PrimeSpectrum.le_iff_specializes (R := Γ(Y, U)) q P).mpr hqp
    have hπq : πU ∈ q.asIdeal := by
      by_contra h
      exact hx' ((hmem q).mpr h)
    have hPq : P.asIdeal ≤ q.asIdeal :=
      hmin.2 ⟨q.2, Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hπq)⟩ hqp'
    congr 1
    exact PrimeSpectrum.ext (le_antisymm hqp' hPq)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PInjSplit
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

private def baseChangePts {R A S K : Type} [CommRing R] [CommRing A] [CommRing S] [CommRing K]
    [Algebra R A] [Algebra R S] [Algebra A K] [Algebra R K] [IsScalarTower R A K] :
    (A ⊗[R] S →ₐ[A] K) ≃ (S →ₐ[R] K) where
  toFun f := (f.restrictScalars R).comp Algebra.TensorProduct.includeRight
  invFun g := Algebra.TensorProduct.lift (Algebra.ofId A K) g fun _ _ => Commute.all _ _
  left_inv f := by
    apply Algebra.TensorProduct.ext
    · ext
    · ext s
      simp [Algebra.ofId_apply]
  right_inv g := by
    ext s
    simp [Algebra.ofId_apply]

theorem UpperTheory.Gal.crystallineComparison.injSplit_of :
    RankOfDeg → SplitsOfEquiv → InjSplit := by
  intro hRank hSplitEq l d R S _ _ _ hE
  haveI := hE.fin
  haveI := hE.et
  have hdeg : ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (Localization.Away (l : R)) K],
      Nat.card (Localization.Away (l : R) ⊗[R] S →ₐ[Localization.Away (l : R)] K) = d := by
    intro K _ _ _
    letI : Algebra R K := ((algebraMap (Localization.Away (l : R)) K).comp
      (algebraMap R (Localization.Away (l : R)))).toAlgebra
    haveI : IsScalarTower R (Localization.Away (l : R)) K := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hl : (l : K) ≠ 0 := by
      have hu : IsUnit (algebraMap R (Localization.Away (l : R)) (l : R)) :=
        IsLocalization.Away.algebraMap_isUnit (l : R)
      have hu' := hu.map (algebraMap (Localization.Away (l : R)) K)
      simpa using hu'.ne_zero
    rw [Nat.card_congr baseChangePts]
    exact hE.deg K hl
  have hn := hRank (Localization.Away (l : R)) (Localization.Away (l : R) ⊗[R] S) d hdeg
  obtain ⟨T, _, _, _, _, _, hT⟩ := Algebra.IsFiniteSplit.exists_tensorProduct_of_etale hn
  obtain ⟨n, ⟨e⟩⟩ := hT.nonempty_algEquiv_fun
  obtain ⟨z, hz⟩ := hSplitEq (Localization.Away (l : R)) (Localization.Away (l : R) ⊗[R] S) T (Fin n) e
  exact ⟨T, inferInstance, inferInstance, n, z,
    FaithfulSMul.algebraMap_injective (Localization.Away (l : R)) T, hz⟩
end

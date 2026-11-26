module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemPolarizationIdealOfMemConj

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvdPowOfZeros
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.HSChoice.HyperplaneFactor

theorem eval_lin {K : Type} [Field K] {N : ℕ} (x : Fin 1 × Fin N → K) (y : Fin N → K) :
    eval x (lin y) = ∑ j, x (0, j) * y j := by
  simp [lin]

theorem coeff_lin {K : Type} [Field K] {N : ℕ} (y : Fin N → K) (j : Fin N) :
    AddMonoidAlgebra.coeff (lin y) (Finsupp.single ((0 : Fin 1), j) 1) = y j := by
  classical
  rw [lin, coeff_sum]
  simp only [mul_comm (X _) (C _), coeff_C_mul, coeff_X', Finsupp.single_left_inj (one_ne_zero' ℕ)]
  simp

theorem isHomogeneous_lin {K : Type} [Field K] {N : ℕ} (y : Fin N → K) : (lin y).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun _ _ => (isHomogeneous_X K _).mul (isHomogeneous_C _ _)

theorem irreducible_lin {K : Type} [Field K] {N : ℕ} {y : Fin N → K} (hy : y ≠ 0) : Irreducible (lin y) := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hy
  have h0 : lin y ≠ 0 := fun h => hj (by
    have := coeff_lin y j
    simp only [h, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at this
    exact this.symm)
  refine irreducible_of_totalDegree_eq_one ((isHomogeneous_lin y).totalDegree h0) fun x hx => ?_
  have hd := hx (Finsupp.single (0, j) 1)
  rw [coeff_lin] at hd
  exact isUnit_of_dvd_unit hd (IsUnit.mk0 _ hj)

theorem exists_dvd_pow_of_zeros {K : Type} [Field K] [IsAlgClosed K] {N : ℕ} {a b : MvPolynomial (Fin 1 × Fin N) K}
    (h : ∀ x, eval x a = 0 → eval x b = 0) : ∃ n : ℕ, a ∣ b ^ n := by
  have hb : b ∈ (Ideal.span {a}).radical := by
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := K)]
    intro x hx
    have h1 := hx a (Ideal.subset_span rfl)
    have e : ∀ p : MvPolynomial (Fin 1 × Fin N) K, aeval x p = eval x p := fun p =>
      DFunLike.congr_fun (coe_aeval_eq_eval x) p
    rw [e] at h1
    change aeval x b = 0
    rw [e]
    exact h x h1
  obtain ⟨n, hn⟩ := hb
  exact ⟨n, Ideal.mem_span_singleton.1 hn⟩

theorem eq_C_mul_prod_lin : ∀ (K : Type) [Field K] [IsAlgClosed K] (N δ m : ℕ) (g : MvPolynomial (Fin 1 × Fin N) K)
    (y : Fin m → Fin N → K), g.IsHomogeneous δ → NoSquare g → (∀ q, y q ≠ 0) →
    (∀ q q' (c : K), y q' = c • y q → q = q') →
    (∀ ξ : Fin N → K, eval (fun p => ξ p.2) g = 0 ↔ ∃ q, ∑ j, ξ j * y q j = 0) →
    m = δ ∧ ∃ c : K, c ≠ 0 ∧ g = C c * ∏ q, lin (y q) := by
  intro K _ _ N δ m g y hg hns hy hinj hz
  classical
  have hz' : ∀ x : Fin 1 × Fin N → K, eval x g = 0 ↔ ∃ q, eval x (lin (y q)) = 0 := by
    intro x
    have e : (fun p : Fin 1 × Fin N => x (0, p.2)) = x := by
      funext ⟨i, j⟩
      rw [Subsingleton.elim i 0]
    have h1 := hz fun j => x (0, j)
    simp only [e] at h1
    simpa only [eval_lin] using h1
  have irr : ∀ q, Irreducible (lin (y q)) := fun q => irreducible_lin (hy q)
  have dvdg : ∀ q, lin (y q) ∣ g := fun q => by
    obtain ⟨n, hn⟩ := exists_dvd_pow_of_zeros (a := lin (y q)) (b := g) fun x hx => (hz' x).2 ⟨q, hx⟩
    exact (irr q).prime.dvd_of_dvd_pow hn
  have nondvd : ∀ q q', q ≠ q' → ¬ lin (y q) ∣ lin (y q') := by
    intro q q' hne hd
    obtain ⟨a, ha⟩ := (irr q).associated_of_dvd (irr q') hd
    obtain ⟨t, -, ht⟩ := isUnit_iff_eq_C_of_isReduced.1 a.isUnit
    rw [ht, mul_comm] at ha
    refine hne (hinj q q' t (funext fun j => ?_))
    have h1 := congrArg (AddMonoidAlgebra.coeff · (Finsupp.single ((0 : Fin 1), j) 1)) ha
    rw [coeff_C_mul, coeff_lin, coeff_lin] at h1
    simpa using h1.symm
  have Pdvd : (∏ q, lin (y q)) ∣ g := Finset.prod_dvd_of_isRelPrime
    (fun q _ q' _ hne => (irr q).isRelPrime_iff_not_dvd.2 (nondvd q q' hne)) fun q _ => dvdg q
  obtain ⟨h, hh⟩ := Pdvd
  have h0 : h ≠ 0 := fun e => hns.1 (by rw [hh, e, mul_zero])
  have hu : IsUnit h := by
    by_contra hu
    obtain ⟨p, pirr, pd⟩ := WfDvdMonoid.exists_irreducible_factor hu h0
    obtain ⟨n, hn⟩ := exists_dvd_pow_of_zeros (a := g) (b := ∏ q, lin (y q)) fun x hx => by
      obtain ⟨q, hq⟩ := (hz' x).1 hx
      rw [map_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ q) hq
    have pg : p ∣ g := hh ▸ pd.mul_left _
    obtain ⟨q, -, hq⟩ := (Prime.exists_mem_finset_dvd pirr.prime (pirr.prime.dvd_of_dvd_pow (pg.trans hn)))
    have hl : lin (y q) ∣ p := ((pirr.associated_of_dvd (irr q) hq).symm).dvd
    refine hns.2 (y q) (hy q) ?_
    rw [hh, pow_two]
    exact mul_dvd_mul (Finset.dvd_prod_of_mem _ (Finset.mem_univ q)) (hl.trans pd)
  obtain ⟨c, hc, hcC⟩ := isUnit_iff_eq_C_of_isReduced.1 hu
  have hgC : g = C c * ∏ q, lin (y q) := by rw [hh, hcC, mul_comm]
  have hP : (∏ q, lin (y q)).IsHomogeneous m := by
    simpa using IsHomogeneous.prod Finset.univ (fun q => lin (y q)) (fun _ => 1) fun q _ => isHomogeneous_lin (y q)
  have hgm : g.IsHomogeneous m := by
    rw [hgC]
    simpa using (isHomogeneous_C (Fin 1 × Fin N) c).mul hP
  exact ⟨(hgm.totalDegree hns.1).symm.trans (hg.totalDegree hns.1), c, hc.ne_zero, hgC⟩

end GlobalTheory.HSChoice.HyperplaneFactor
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleOfFinrankLeCardAlgHomAlgebraicClosure
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleOfFinrankLeCardAlgHomAlgebraicClosure
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open scoped TensorProduct

namespace GlobalTheory

theorem etale_of_finrank_le_card_algHom_algebraicClosure : ∀ (E R : Type) [Field E] [CommRing R] [Algebra E R] [Module.Finite E R], Finite (R →ₐ[E] AlgebraicClosure E) ∧ Nat.card (R →ₐ[E] AlgebraicClosure E) ≤ Module.finrank E R ∧ (Module.finrank E R ≤ Nat.card (R →ₐ[E] AlgebraicClosure E) → Algebra.Etale E R) := by
  intro E R _ _ _ _
  refine ⟨inferInstance, card_algHom_le_finrank E R (AlgebraicClosure E), fun hle => ?_⟩
  classical
  set Ω := AlgebraicClosure E
  set S := Ω ⊗[E] R
  set ι := S →ₐ[Ω] Ω
  have : Fintype ι := Fintype.ofFinite ι
  have hcard : Nat.card ι = Nat.card (R →ₐ[E] Ω) :=
    (Nat.card_congr (AlgHom.liftEquiv E Ω R Ω)).symm
  have hrank : Module.finrank Ω S = Module.finrank E R := Module.finrank_baseChange
  let φ : S →ₐ[Ω] (ι → Ω) := AlgHom.pi fun f => f
  have hsurj : Function.Surjective φ.toLinearMap := by
    rw [← LinearMap.dualMap_injective_iff, injective_iff_map_eq_zero]
    intro g hg
    have hs : ∀ i : ι, (fun j => if i = j then (1 : Ω) else 0) = Pi.single i 1 := fun i => by
      ext j; simp [Pi.single_apply, eq_comm]
    have hli := Fintype.linearIndependent_iff.mp (linearIndependent_algHom_toLinearMap Ω S Ω)
      (fun f => g (Pi.single f 1))
    have hc : ∀ f, g (Pi.single f 1) = 0 := by
      apply hli
      refine LinearMap.ext fun s => ?_
      have := LinearMap.congr_fun hg s
      simp only [LinearMap.dualMap_apply, LinearMap.zero_apply] at this
      rw [LinearMap.zero_apply, ← this, LinearMap.pi_apply_eq_sum_univ g]
      simp only [hs, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [φ, mul_comm]
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.pi_apply_eq_sum_univ g]
    simp [hs, hc]
  have hinj : Function.Injective φ.toLinearMap := by
    have hle' : Module.finrank Ω S ≤ Module.finrank Ω (ι → Ω) := by
      rw [Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card, hcard, hrank]
      exact hle
    have hge : Module.finrank Ω (ι → Ω) ≤ Module.finrank Ω S := by
      have h := LinearMap.finrank_range_le φ.toLinearMap
      rwa [LinearMap.range_eq_top.mpr hsurj, finrank_top] at h
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (le_antisymm hle' hge)).mpr hsurj
  have : IsReduced S := isReduced_of_injective φ.toRingHom hinj
  have : IsArtinianRing S := .of_finite Ω S
  have hE : Algebra.Etale Ω S := by
    have (I : MaximalSpectrum S) : Algebra.FormallyEtale Ω (S ⧸ I.asIdeal) := by
      let := Ideal.Quotient.field I.asIdeal
      exact Algebra.FormallyEtale.of_isSeparable Ω (S ⧸ I.asIdeal)
    exact ⟨.of_equiv ((IsArtinianRing.equivPi S).restrictScalars Ω).symm,
      Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat Ω

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleOfFinrankLeCardAlgHomAlgebraicClosureStatement
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_of_finrank_le_card_algHom : ∀ (E R : Type) [Field E] [CommRing R] [Algebra E R] [Module.Finite E R], Finite (R →ₐ[E] AlgebraicClosure E) ∧ Nat.card (R →ₐ[E] AlgebraicClosure E) ≤ Module.finrank E R ∧ (Module.finrank E R ≤ Nat.card (R →ₐ[E] AlgebraicClosure E) → Algebra.Etale E R) := by
  first | exact @GlobalTheory.etale_of_finrank_le_card_algHom_algebraicClosure | exact GlobalTheory.etale_of_finrank_le_card_algHom_algebraicClosure | (intros; apply GlobalTheory.etale_of_finrank_le_card_algHom_algebraicClosure <;> assumption)
end
end

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.HSChoice.EtaleSection

theorem exists_eq_isoSpec_comp {k : Type} [CommRing k] {X : Scheme.{0}} [IsAffine X] (g : X ⟶ Spec (.of k)) :
    letI := algebraΓOfHom g
    ∃ a : CommRingCat.of k ⟶ Γ(X, ⊤), a.hom = algebraMap k Γ(X, ⊤) ∧ g = X.isoSpec.hom ≫ Spec.map a := by
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ g.appTop, rfl, ?_⟩
  rw [Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom, ← Scheme.toSpecΓ_naturality, Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

theorem natCard_subPts {k : Type} [Field k] (S : LinSys k) (I : S.Y.IdealSheafData) (hI : S.IsFiniteSub I)
    (Ω : Type) [Field Ω] [Algebra k Ω] :
    letI := algebraΓOfHom (I.subschemeι ≫ S.str)
    Nat.card (S.subPts I Ω) = Nat.card (Γ(I.subscheme, ⊤) →ₐ[k] Ω) := by
  letI := algebraΓOfHom (I.subschemeι ≫ S.str)
  haveI : IsFinite (I.subschemeι ≫ S.str) := hI
  haveI : IsAffine I.subscheme := isAffine_of_isAffineHom (I.subschemeι ≫ S.str)
  obtain ⟨a, ha, he⟩ := exists_eq_isoSpec_comp (I.subschemeι ≫ S.str)
  have e1 : Nat.card (S.subPts I Ω) =
      Nat.card {z : Sp Ω ⟶ I.subscheme // z ≫ I.subschemeι ≫ S.str = spMap (algebraMap k Ω)} := by
    refine (Nat.card_congr (Equiv.ofBijective (fun z => (⟨⟨z.1 ≫ I.subschemeι, by rw [Category.assoc]; exact z.2⟩,
      z.1, rfl⟩ : S.subPts I Ω)) ⟨?_, ?_⟩)).symm
    · intro z z' h
      apply Subtype.ext
      have h0 : z.1 ≫ I.subschemeι = z'.1 ≫ I.subschemeι := congrArg (fun x : S.subPts I Ω => x.1.1) h
      exact (cancel_mono I.subschemeι).1 h0
    · rintro ⟨x, z, hz⟩
      refine ⟨⟨z, ?_⟩, ?_⟩
      · rw [← Category.assoc, hz]
        exact x.2
      · apply Subtype.ext
        apply Subtype.ext
        exact hz
  have hmk : ∀ φ : Γ(I.subscheme, ⊤) →ₐ[k] Ω,
      (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ I.subscheme.isoSpec.inv) ≫ I.subschemeι ≫ S.str =
        spMap (algebraMap k Ω) := by
    intro φ
    rw [he, Category.assoc, Iso.inv_hom_id_assoc, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext r
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    rw [ha]
    exact φ.commutes r
  have e2 : Nat.card {z : Sp Ω ⟶ I.subscheme // z ≫ I.subschemeι ≫ S.str = spMap (algebraMap k Ω)} =
      Nat.card (Γ(I.subscheme, ⊤) →ₐ[k] Ω) := by
    refine (Nat.card_congr (Equiv.ofBijective (fun φ : Γ(I.subscheme, ⊤) →ₐ[k] Ω =>
      (⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ I.subscheme.isoSpec.inv, hmk φ⟩ :
        {z : Sp Ω ⟶ I.subscheme // z ≫ I.subschemeι ≫ S.str = spMap (algebraMap k Ω)})) ⟨?_, ?_⟩)).symm
    · intro φ ψ h
      simp only [Subtype.mk.injEq, cancel_mono] at h
      have h2 := Spec.map_injective h
      ext r
      exact congrArg (fun f => f.hom r) h2
    · rintro ⟨z, hz⟩
      have hψ : Spec.map (Spec.preimage (z ≫ I.subscheme.isoSpec.hom)) = z ≫ I.subscheme.isoSpec.hom :=
        Spec.map_preimage _
      have hc : a ≫ Spec.preimage (z ≫ I.subscheme.isoSpec.hom) = CommRingCat.ofHom (algebraMap k Ω) := by
        apply Spec.map_injective
        rw [Spec.map_comp, hψ, Category.assoc, ← he]
        exact hz
      refine ⟨AlgHom.mk (Spec.preimage (z ≫ I.subscheme.isoSpec.hom)).hom (fun r => ?_), ?_⟩
      · have h3 := congrArg (fun f => f.hom r) hc
        simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, ha] at h3
        exact h3
      · apply Subtype.ext
        rw [Iso.comp_inv_eq]
        exact hψ
  rw [e1, e2]

theorem etale_of_algebraEtale {k : Type} [Field k] (S : LinSys k) (I : S.Y.IdealSheafData) (hI : S.IsFiniteSub I) :
    letI := algebraΓOfHom (I.subschemeι ≫ S.str)
    Algebra.Etale k Γ(I.subscheme, ⊤) → Etale (I.subschemeι ≫ S.str) := by
  letI := algebraΓOfHom (I.subschemeι ≫ S.str)
  intro h
  haveI : IsFinite (I.subschemeι ≫ S.str) := hI
  haveI : IsAffine I.subscheme := isAffine_of_isAffineHom (I.subschemeι ≫ S.str)
  obtain ⟨a, ha, he⟩ := exists_eq_isoSpec_comp (I.subschemeι ≫ S.str)
  have h2 : Etale (Spec.map a) := by
    refine HasRingHomProperty.Spec_iff.mpr ?_
    rw [ha]
    exact (RingHom.etale_algebraMap (R := k) (S := Γ(I.subscheme, ⊤))).mpr h
  rw [he]
  infer_instance

theorem finite_finrank {F : Type} [Field F] [NumberField F] (T : Tuple F) (hT : T.IsGeometric) (E : Type) [Field E]
    [Algebra F E] (s : Fin T.D → Fin T.N → E)
    (hfin : ((T.linSection E s).support : Set (T.toLinSys.baseChange E).Y).Finite) :
    (T.toLinSys.baseChange E).IsFiniteSub (T.linSection E s) ∧
    (letI := algebraΓOfHom ((T.linSection E s).subschemeι ≫ (T.toLinSys.baseChange E).str)
    Module.Finite E Γ((T.linSection E s).subscheme, ⊤) ∧
      (Module.finrank E Γ((T.linSection E s).subscheme, ⊤) : ℤ) = T.del) := by
  have hv : (T.toLinSys.baseChange E).IsVariety := hT.alg.variety.baseChange E
  have H := GlobalTheory.ProperCut.topSelf_eq_length_of_smooth (T.toLinSys.baseChange E).str hv.smooth hv.proj
    (T.toLinSys.baseChange E).isLB (fun i => (T.toLinSys.baseChange E).comb (s i)) hfin
  have hdel : (T.toLinSys.baseChange E).del = T.del :=
    GlobalTheory.FieldChangeInter.del_baseChange F E T.toLinSys hT.alg.variety.proj
  refine ⟨H.1, ?_⟩
  refine ⟨H.2.2.2.2.1, ?_⟩
  rw [← hdel]
  exact H.2.2.2.2.2.symm

private lemma isHomogeneous_join_C_X {K : Type} [CommRing K] {D N : ℕ} (s : Fin D → Fin N → K) (v : Fin (D + 1) × Fin N) :
    (join (fun i j => (C (s i j) : MvPolynomial (Fin 1 × Fin N) K)) (fun j => X ((0 : Fin 1), j)) v).IsHomogeneous
      (if v.1 = Fin.last D then 1 else 0) := by
  obtain ⟨i, j⟩ := v
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
  · simpa [join, Fin.castSucc_ne_last] using isHomogeneous_C (Fin 1 × Fin N) (s i j)
  · simpa [join] using isHomogeneous_X K ((0 : Fin 1), j)

theorem isHomogeneous_spec {F K : Type} [Field F] [Field K] [Algebra F K] {D N δ : ℕ} (s : Fin D → Fin N → K)
    (f : MvPolynomial (Fin (D + 1) × Fin N) F) (hf : IsMultiHomogeneous (fun _ => δ) f) :
    (spec s f).IsHomogeneous δ := by
  classical
  unfold spec
  set_option synthInstance.maxHeartbeats 100000 in
    rw [f.as_sum, map_sum]
  apply IsHomogeneous.sum
  intro m hm
  have hprod : (m.prod fun v e =>
      (join (fun i j => (C (s i j) : MvPolynomial (Fin 1 × Fin N) K)) (fun j => X ((0 : Fin 1), j)) v) ^ e).IsHomogeneous
      (∑ v ∈ m.support, (if v.1 = Fin.last D then 1 else 0) * m v) :=
    IsHomogeneous.prod _ _ _ fun v _ => (isHomogeneous_join_C_X s v).pow (m v)
  have hdeg : ∑ v ∈ m.support, (if v.1 = Fin.last D then 1 else 0) * m v = δ := by
    rw [Finset.sum_subset (Finset.subset_univ _) (fun v _ hv => by simp [Finsupp.notMem_support_iff.1 hv])]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single (Fin.last D)]
    · simpa using hf m hm (Fin.last D)
    · intro i _ hi
      simp [hi]
    · simp
  have h2 := (isHomogeneous_C (Fin 1 × Fin N) (algebraMap F K (AddMonoidAlgebra.coeff f m))).mul hprod
  rw [zero_add, hdeg] at h2
  rw [aeval_monomial, MvPolynomial.algebraMap_apply]
  exact h2

private lemma eval_join_C_X_eq_join {K : Type} [CommRing K] {D N : ℕ} (s : Fin D → Fin N → K) (ξ : Fin N → K)
    (v : Fin (D + 1) × Fin N) :
    eval (fun p : Fin 1 × Fin N => ξ p.2)
      (join (fun i j => (C (s i j) : MvPolynomial (Fin 1 × Fin N) K)) (fun j => X ((0 : Fin 1), j)) v) = join s ξ v := by
  obtain ⟨i, j⟩ := v
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
  · simp [join]
  · simp [join]

theorem eval_spec {F K : Type} [CommRing F] [CommRing K] [Algebra F K] {D N : ℕ} (s : Fin D → Fin N → K)
    (f : MvPolynomial (Fin (D + 1) × Fin N) F) (ξ : Fin N → K) :
    eval (fun p => ξ p.2) (spec s f) = aeval (join s ξ) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [spec, MvPolynomial.algebraMap_apply]
  | add p q hp hq =>
    simp only [spec, map_add (f := _)] at hp hq ⊢
    rw [hp, hq]
  | mul_X p v hp =>
    simp only [spec, map_mul, aeval_X] at hp ⊢
    rw [hp, eval_join_C_X_eq_join]

end GlobalTheory.HSChoice.EtaleSection

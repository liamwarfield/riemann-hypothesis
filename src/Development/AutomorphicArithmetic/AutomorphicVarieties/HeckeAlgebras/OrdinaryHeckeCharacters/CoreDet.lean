module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CoreSep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.HiAlgUnit
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CdNormLt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.GlueRep
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Imports
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.DescendLam
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.AmitsurSub
open Polynomial UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.amitsurSub :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (m : ℕ) (g : Fin m → G) (β : Fin m →₀ ℕ),
    AddMonoidAlgebra.coeff (D.D (MvPolynomial (Fin m) A) (GDet.gen fun j => MonoidAlgebra.single (g j) 1)) β ∈
      Subring.closure {a | ∃ i ≤ n, ∃ s : G, a = D.lam i (MonoidAlgebra.single s 1)} := by
  intro n A G _ _ D m g β
  have h := UpperTheory.V.CA.d_coef_mem D.toDet (MonoidHom.mrange (MonoidAlgebra.of A G))
    (Subring.closure {a | ∃ i ≤ n, ∃ s : G, a = D.lam i (MonoidAlgebra.single s 1)})
    (by
      rintro x ⟨s, rfl⟩ i - h2
      rw [(UpperTheory.V.CA.d_toDet D _).2.1]
      exact Subring.subset_closure ⟨i, h2, s, rfl⟩)
    (fun j => MonoidAlgebra.single (g j) 1) (fun j => ⟨g j, rfl⟩) β
  have e : D.toDet.poly (fun j => MonoidAlgebra.single (g j) (1 : A)) =
      D.D (MvPolynomial (Fin m) A) (GDet.gen fun j => MonoidAlgebra.single (g j) 1) := by
    change D.D _ (ofT A G _ (Det.gen _)) = _
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Det.gen, GDet.gen, map_sum, ofT_tmul, MvPolynomial.algebraMap_eq]
  rwa [e] at h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Descend
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.ExtendPoly
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.LiftIndep
open Polynomial UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.liftIndep :
    ∀ {A G : Type} [CommRing A] [Group G] (d : ∀ σ : Type, MonoidAlgebra (MvPolynomial σ A) G →* MvPolynomial σ A),
    (∀ (σ τ : Type) (f : MvPolynomial σ A →ₐ[A] MvPolynomial τ A) (x : MonoidAlgebra (MvPolynomial σ A) G),
      d τ (MonoidAlgebra.mapRingHom G (f : MvPolynomial σ A →+* MvPolynomial τ A) x) = f (d σ x)) →
    ∀ (B : Type) [CommRing B] [Algebra A B] (σ τ : Type) (p : MvPolynomial σ A →ₐ[A] B) (q : MvPolynomial τ A →ₐ[A] B)
      (x : MonoidAlgebra (MvPolynomial σ A) G) (z : MonoidAlgebra (MvPolynomial τ A) G),
      MonoidAlgebra.mapRingHom G (p : MvPolynomial σ A →+* B) x = MonoidAlgebra.mapRingHom G (q : MvPolynomial τ A →+* B) z →
      p (d σ x) = q (d τ z) := by
  intro A G _ _ d hd B _ _ σ τ p q x z hxz
  classical
  let S : Finset G := x.coeff.support ∪ z.coeff.support
  let w : MonoidAlgebra (MvPolynomial G A) G := ∑ g ∈ S, MonoidAlgebra.single g (MvPolynomial.X g)
  let φ : MvPolynomial G A →ₐ[A] MvPolynomial σ A := MvPolynomial.aeval fun g => x.coeff g
  let ψ : MvPolynomial G A →ₐ[A] MvPolynomial τ A := MvPolynomial.aeval fun g => z.coeff g
  have hx : MonoidAlgebra.mapRingHom G (φ : MvPolynomial G A →+* MvPolynomial σ A) w = x := by
    ext g
    by_cases hg : g ∈ S
    set_option synthInstance.maxHeartbeats 100000 in
      · simp [w, φ, map_sum, MonoidAlgebra.coeff_single, Finsupp.single_apply, hg]
    · have h0 : x.coeff g = 0 := by
        by_contra h
        exact hg (Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr h))
      set_option synthInstance.maxHeartbeats 100000 in
        simp [w, φ, map_sum, MonoidAlgebra.coeff_single, Finsupp.single_apply, hg, h0]
  have hz : MonoidAlgebra.mapRingHom G (ψ : MvPolynomial G A →+* MvPolynomial τ A) w = z := by
    ext g
    by_cases hg : g ∈ S
    set_option synthInstance.maxHeartbeats 100000 in
      · simp [w, ψ, map_sum, MonoidAlgebra.coeff_single, Finsupp.single_apply, hg]
    · have h0 : z.coeff g = 0 := by
        by_contra h
        exact hg (Finset.mem_union_right _ (Finsupp.mem_support_iff.mpr h))
      set_option synthInstance.maxHeartbeats 100000 in
        simp [w, ψ, map_sum, MonoidAlgebra.coeff_single, Finsupp.single_apply, hg, h0]
  have key : p.comp φ = q.comp ψ := by
    refine MvPolynomial.algHom_ext fun g => ?_
    have h := congrArg (fun y : MonoidAlgebra B G => y.coeff g) hxz
    simpa [φ, ψ] using h
  calc p (d σ x) = p (φ (d G w)) := by rw [← hd, hx]
    _ = (p.comp φ) (d G w) := rfl
    _ = (q.comp ψ) (d G w) := by rw [key]
    _ = q (d τ z) := by
      change q (ψ (d G w)) = q (d τ z)
      rw [← hd, hz]
end

open Polynomial UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.extendPoly :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (d : ∀ σ : Type, MonoidAlgebra (MvPolynomial σ A) G →* MvPolynomial σ A),
    (∀ (σ τ : Type) (f : MvPolynomial σ A →ₐ[A] MvPolynomial τ A) (x : MonoidAlgebra (MvPolynomial σ A) G),
      d τ (MonoidAlgebra.mapRingHom G (f : MvPolynomial σ A →+* MvPolynomial τ A) x) = f (d σ x)) →
    (∀ (σ : Type) (b : MvPolynomial σ A) (x : MonoidAlgebra (MvPolynomial σ A) G), d σ (b • x) = b ^ n * d σ x) →
    ∃ D : GDet n A G, ∀ (σ : Type) (x : MonoidAlgebra (MvPolynomial σ A) G), D.D (MvPolynomial σ A) x = d σ x := by
  intro n A G _ _ d hnat hhom
  have hsurj : ∀ (B : Type) [CommRing B] [Algebra A B],
      Function.Surjective (MonoidAlgebra.mapRingHom G
        ((MvPolynomial.aeval id : MvPolynomial B A →ₐ[A] B) : MvPolynomial B A →+* B)) := by
    intro B _ _
    rw [MonoidAlgebra.coe_mapRingHom]
    refine MonoidAlgebra.map_surjective _ ?_
    intro b
    exact ⟨MvPolynomial.X b, by simp⟩
  have spec : ∀ (B : Type) [CommRing B] [Algebra A B] (y : MonoidAlgebra B G),
      MonoidAlgebra.mapRingHom G
        ((MvPolynomial.aeval id : MvPolynomial B A →ₐ[A] B) : MvPolynomial B A →+* B)
        (hsurj B y).choose = y :=
    fun B _ _ y => (hsurj B y).choose_spec
  have ind : ∀ (B : Type) [CommRing B] [Algebra A B] (x x' : MonoidAlgebra (MvPolynomial B A) G),
      MonoidAlgebra.mapRingHom G
          ((MvPolynomial.aeval id : MvPolynomial B A →ₐ[A] B) : MvPolynomial B A →+* B) x =
        MonoidAlgebra.mapRingHom G
          ((MvPolynomial.aeval id : MvPolynomial B A →ₐ[A] B) : MvPolynomial B A →+* B) x' →
      MvPolynomial.aeval id (d B x) = MvPolynomial.aeval id (d B x') :=
    fun B _ _ x x' h => UpperTheory.V.AlgebraTools.Det.liftIndep d hnat B B B _ _ x x' h
  refine ⟨⟨fun B _ _ =>
    { toFun := fun y => MvPolynomial.aeval id (d B (hsurj B y).choose)
      map_one' := ?_
      map_mul' := ?_ }, ?_, ?_⟩, ?_⟩
  · show MvPolynomial.aeval id (d B (hsurj B 1).choose) = 1
    rw [ind B _ 1 (by rw [spec, map_one]), map_one, map_one]
  · intro y y'
    show MvPolynomial.aeval id (d B (hsurj B (y * y')).choose) =
      MvPolynomial.aeval id (d B (hsurj B y).choose) * MvPolynomial.aeval id (d B (hsurj B y').choose)
    rw [ind B _ ((hsurj B y).choose * (hsurj B y').choose) (by rw [spec, map_mul, spec, spec]),
      map_mul, map_mul]
  · intro B B' _ _ _ _ f y
    have h := UpperTheory.V.AlgebraTools.Det.liftIndep d hnat B' B' B (MvPolynomial.aeval id)
      (f.comp (MvPolynomial.aeval id)) (hsurj B' (MonoidAlgebra.mapRingHom G (f : B →+* B') y)).choose
      (hsurj B y).choose (by
        rw [spec]
        conv_lhs => rw [← spec B y]
        rw [← RingHom.comp_apply, ← MonoidAlgebra.mapRingHom_comp]
        rfl)
    exact h
  · intro B _ _ b y
    show MvPolynomial.aeval id (d B (hsurj B (b • y)).choose) =
      b ^ n * MvPolynomial.aeval id (d B (hsurj B y).choose)
    rw [ind B _ (MvPolynomial.X b • (hsurj B y).choose) (by
        rw [spec]
        conv_lhs => rw [← spec B y]
        ext m
        rw [MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_mapRingHom,
          MonoidAlgebra.coeff_mapRingHom,
          MonoidAlgebra.coeff_smul_apply (MvPolynomial.X b : MvPolynomial B A) (hsurj B y).choose m]
        simp [smul_eq_mul]), hhom, map_mul, map_pow, MvPolynomial.aeval_X, id]
  · intro σ x
    show MvPolynomial.aeval id (d (MvPolynomial σ A) (hsurj (MvPolynomial σ A) x).choose) = d σ x
    have h := UpperTheory.V.AlgebraTools.Det.liftIndep d hnat (MvPolynomial σ A) (MvPolynomial σ A) σ
      (MvPolynomial.aeval id) (AlgHom.id A _) _ x (by rw [spec])
    simpa using h
end

open Polynomial UpperTheory.V.W

private theorem exists_isCompact_preimage_eq_of_isLimit_of_isAffineHom {n : ℕ} {A G : Type} [CommRing A] [Group G] {A' : Type} [CommRing A']
    (ι : A →+* A') (D' : GDet n A' G)
    (hc : ∀ (m : ℕ) (g : Fin m → G) (β : Fin m →₀ ℕ),
      AddMonoidAlgebra.coeff (D'.D (MvPolynomial (Fin m) A') (GDet.gen fun j => MonoidAlgebra.single (g j) 1)) β ∈ ι.range)
    (σ : Type) (x : MonoidAlgebra (MvPolynomial σ A) G) :
    D'.D (MvPolynomial σ A') (MonoidAlgebra.mapRingHom G (MvPolynomial.map ι) x) ∈ Set.range (MvPolynomial.map ι) := by
  obtain ⟨m, g, b, rfl⟩ := UpperTheory.V.AlgebraTools.Det.genSpan (A := A) (G := G) (MvPolynomial σ A) x
  have hP : D'.D (MvPolynomial (Fin m) A') (GDet.gen fun j => MonoidAlgebra.single (g j) 1) ∈ Set.range (MvPolynomial.map ι) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro c hc'
    obtain ⟨β, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hc'
    exact hc m g β
  obtain ⟨Q, hQ⟩ := hP
  have key := UpperTheory.V.AlgebraTools.Det.genEval D' (MvPolynomial σ A') m (fun j => MonoidAlgebra.single (g j) 1) (fun j => MvPolynomial.map ι (b j))
  refine ⟨MvPolynomial.aeval b Q, ?_⟩
  have hx : MonoidAlgebra.mapRingHom G (MvPolynomial.map ι) (∑ j, b j • MonoidAlgebra.mapRingHom G (algebraMap A (MvPolynomial σ A)) (MonoidAlgebra.single (g j) 1)) = ∑ j, (MvPolynomial.map ι (b j)) • MonoidAlgebra.mapRingHom G (algebraMap A' (MvPolynomial σ A')) (MonoidAlgebra.single (g j) 1) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, MonoidAlgebra.mapRingHom_single]
  rw [hx, key, ← hQ, MvPolynomial.map_aeval]
  simp [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
  rw [MvPolynomial.bind₁, MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
  rfl

private theorem mapRingHom_gdet_gen_single_eq_gen_single {A G : Type} [CommRing A] [Group G] {A' : Type} [CommRing A'] (ι : A →+* A')
    (m : ℕ) (g : Fin m → G) :
    MonoidAlgebra.mapRingHom G (MvPolynomial.map ι) (GDet.gen (A := A) fun j => MonoidAlgebra.single (g j) 1) =
      GDet.gen (A := A') fun j => MonoidAlgebra.single (g j) 1 := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [GDet.gen, map_sum, MonoidAlgebra.mapRingHom_single]

theorem UpperTheory.V.AlgebraTools.Det.descend :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] {A' : Type} [CommRing A'] (ι : A →+* A') (D' : GDet n A' G), Function.Injective ι →
    (∀ (m : ℕ) (g : Fin m → G) (β : Fin m →₀ ℕ),
      AddMonoidAlgebra.coeff (D'.D (MvPolynomial (Fin m) A') (GDet.gen fun j => MonoidAlgebra.single (g j) 1)) β ∈ ι.range) →
    ∃! D : GDet n A G, D.map ι = D' := by
  intro n A G _ _ A' _ ι D' hι hc
  have hr := fun σ x => exists_isCompact_preimage_eq_of_isLimit_of_isAffineHom ι D' hc σ x
  have hinj : ∀ σ : Type, Function.Injective (MvPolynomial.map (σ := σ) ι) :=
    fun σ => MvPolynomial.map_injective ι hι
  let d : (σ : Type) → MonoidAlgebra (MvPolynomial σ A) G →* MvPolynomial σ A := fun σ =>
    { toFun := fun x => Classical.choose (hr σ x)
      map_one' := hinj σ (by rw [Classical.choose_spec (hr σ 1), map_one, map_one, map_one])
      map_mul' := fun x y => hinj σ (by
        rw [Classical.choose_spec (hr σ (x * y)), map_mul, map_mul, map_mul,
          Classical.choose_spec (hr σ x), Classical.choose_spec (hr σ y)]) }
  have hd : ∀ σ x, MvPolynomial.map ι (d σ x) =
      D'.D (MvPolynomial σ A') (MonoidAlgebra.mapRingHom G (MvPolynomial.map ι) x) :=
    fun σ x => Classical.choose_spec (hr σ x)
  have hnat : ∀ (σ τ : Type) (f : MvPolynomial σ A →ₐ[A] MvPolynomial τ A) (x : MonoidAlgebra (MvPolynomial σ A) G),
      d τ (MonoidAlgebra.mapRingHom G (f : MvPolynomial σ A →+* MvPolynomial τ A) x) = f (d σ x) := by
    intro σ τ f x
    apply hinj τ
    let f' : MvPolynomial σ A' →ₐ[A'] MvPolynomial τ A' :=
      MvPolynomial.aeval fun i => MvPolynomial.map ι (f (MvPolynomial.X i))
    have hf : (MvPolynomial.map ι).comp (f : MvPolynomial σ A →+* MvPolynomial τ A) =
        (f' : MvPolynomial σ A' →+* MvPolynomial τ A').comp (MvPolynomial.map ι) := by
      apply MvPolynomial.ringHom_ext
      · intro a
        have ha := f.commutes a
        simp only [MvPolynomial.algebraMap_eq] at ha
        simp [f', ha]
      · intro i
        simp [f']
    have e1 : MonoidAlgebra.mapRingHom G (MvPolynomial.map ι) (MonoidAlgebra.mapRingHom G (f : MvPolynomial σ A →+* MvPolynomial τ A) x) =
        MonoidAlgebra.mapRingHom G (f' : MvPolynomial σ A' →+* MvPolynomial τ A') (MonoidAlgebra.mapRingHom G (MvPolynomial.map ι) x) := by
      rw [← RingHom.comp_apply, ← MonoidAlgebra.mapRingHom_comp, hf, MonoidAlgebra.mapRingHom_comp, RingHom.comp_apply]
    rw [hd, e1, D'.nat (MvPolynomial σ A') (MvPolynomial τ A') f', ← hd]
    exact (RingHom.congr_fun hf _).symm
  have hhom : ∀ (σ : Type) (b : MvPolynomial σ A) (x : MonoidAlgebra (MvPolynomial σ A) G),
      d σ (b • x) = b ^ n * d σ x := by
    intro σ b x
    apply hinj σ
    have hs : MonoidAlgebra.mapRingHom G (MvPolynomial.map ι) (b • x) =
        MvPolynomial.map ι b • MonoidAlgebra.mapRingHom G (MvPolynomial.map ι) x := by
      ext g
      simp [MonoidAlgebra.mapRingHom_apply]
    rw [hd, map_mul, map_pow, hd, hs, D'.homog]
  obtain ⟨D, hD⟩ := UpperTheory.V.AlgebraTools.Det.extendPoly d hnat hhom
  have hex : D.map ι = D' := by
    apply UpperTheory.V.AlgebraTools.Det.extGen
    intro m g
    rw [← mapRingHom_gdet_gen_single_eq_gen_single ι m g, (UpperTheory.V.AlgebraTools.Det.mapApi D ι).2.2.2.1 (Fin m), hD, hd]
  refine ⟨D, hex, fun D2 h2 => ?_⟩
  exact (UpperTheory.V.AlgebraTools.Det.injTest (X := Unit) (fun _ => A') (fun _ => ι)
    (fun a ha => hι (by rw [ha (), map_zero])) ).1 D2 D (fun _ => by rw [h2, hex])
end

open Polynomial UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.descendLam :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] {A' : Type} [CommRing A'] (ι : A →+* A') (D' : GDet n A' G), Function.Injective ι →
    (∀ i ≤ n, ∀ g : G, D'.lam i (MonoidAlgebra.single g 1) ∈ ι.range) → ∃! D : GDet n A G, D.map ι = D' := by
  intro n A G _ _ A' _ ι D' hι h
  refine UpperTheory.V.AlgebraTools.Det.descend ι D' hι fun m g β => ?_
  refine (Subring.closure_le (t := ι.range)).2 ?_ (UpperTheory.V.AlgebraTools.Det.amitsurSub D' m g β)
  rintro a ⟨i, hi, s, rfl⟩
  exact h i hi s
end

open Polynomial UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.glue :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] [TopologicalSpace A] [CompactSpace A] [TopologicalSpace G] {A' : Type} [CommRing A'] [TopologicalSpace A'] [T2Space A']
    (ι : A →+* A') (D' : GDet n A' G) (S : Set G), Continuous ι → Function.Injective ι → Dense S →
    (∀ i ≤ n, Continuous fun g : G => D'.lam i (MonoidAlgebra.single g 1)) →
    (∀ g ∈ S, ∀ i ≤ n, D'.lam i (MonoidAlgebra.single g 1) ∈ ι.range) →
    ∃ D : GDet n A G, D.map ι = D' ∧ ∀ i ≤ n, Continuous fun g : G => D.lam i (MonoidAlgebra.single g 1) := by
  intro n A G _ _ _ _ _ A' _ _ _ ι D' S hι hinj hS hcont hmem
  have hemb := hι.isClosedEmbedding hinj
  have hall : ∀ i ≤ n, ∀ g : G, D'.lam i (MonoidAlgebra.single g 1) ∈ ι.range := by
    intro i hi g
    have hcl : IsClosed {g : G | D'.lam i (MonoidAlgebra.single g 1) ∈ ι.range} := by
      have hr : IsClosed (Set.range ι) := hemb.isClosed_range
      rw [← RingHom.coe_range] at hr
      exact hr.preimage (hcont i hi)
    have hsub : S ⊆ {g : G | D'.lam i (MonoidAlgebra.single g 1) ∈ ι.range} :=
      fun g hg => hmem g hg i hi
    have h1 := closure_minimal hsub hcl
    rw [hS.closure_eq] at h1
    exact h1 (Set.mem_univ g)
  obtain ⟨D, hD, -⟩ := UpperTheory.V.AlgebraTools.Det.descendLam ι D' hinj hall
  refine ⟨D, hD, fun i hi => ?_⟩
  rw [hemb.isEmbedding.continuous_iff]
  have heq : (⇑ι ∘ fun g : G => D.lam i (MonoidAlgebra.single g 1)) =
      fun g => D'.lam i (MonoidAlgebra.single g 1) := by
    funext g
    simp only [Function.comp]
    have hchi : ∀ y, (D.map ι).chi (MonoidAlgebra.mapRingHom G ι y) = (D.chi y).map ι := by
      intro y
      have e : MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C (MonoidAlgebra.mapRingHom G ι y) =
          MonoidAlgebra.mapRingHom G (Polynomial.mapRingHom ι) (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C y) := by
        rw [map_sub, MonoidAlgebra.mapRingHom_single, Polynomial.coe_mapRingHom, Polynomial.map_X,
          ← RingHom.comp_apply, ← RingHom.comp_apply, ← MonoidAlgebra.mapRingHom_comp,
          ← MonoidAlgebra.mapRingHom_comp, Polynomial.mapRingHom_comp_C]
      show (D.map ι).D A'[X] _ = _
      rw [e]
      have hφ : ∀ a, Polynomial.mapRingHom ι (algebraMap A A[X] a) = algebraMap A' A'[X] (ι a) := by
        intro a
        simp
      let : Algebra A A'[X] := ((algebraMap A' A'[X]).comp ι).toAlgebra
      exact D.nat A[X] A'[X] { Polynomial.mapRingHom ι with commutes' := hφ } _
    have hlam : ∀ i y, (D.map ι).lam i (MonoidAlgebra.mapRingHom G ι y) = ι (D.lam i y) := by
      intro i y
      simp only [GDet.lam, hchi, Polynomial.coeff_map, map_mul, map_pow, map_neg, map_one]
    have hs : (D.map ι).lam i (MonoidAlgebra.single g 1) = ι (D.lam i (MonoidAlgebra.single g 1)) := by
      simpa using hlam i (MonoidAlgebra.single g 1)
    rw [← hs, hD]
  rw [heq]
  exact hcont i hi
end

open Polynomial UpperTheory.V.W

private def UpperTheory.V.AlgebraTools.Det.piRep {n : ℕ} {G X : Type} [Group G] (K : X → Type) [∀ x, CommRing (K x)]
    (ρ : ∀ x, G →* Matrix (Fin n) (Fin n) (K x)) : G →* Matrix (Fin n) (Fin n) (∀ x, K x) where
  toFun g := Matrix.of fun i j x => ρ x g i j
  map_one' := by
    ext i j x
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  map_mul' g h := by
    ext i j x
    simp [Matrix.mul_apply, Finset.sum_apply]

theorem UpperTheory.V.AlgebraTools.Det.glueRep :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] [TopologicalSpace A] [CompactSpace A] [TopologicalSpace G] {X : Type} (K : X → Type) [∀ x, CommRing (K x)]
    [∀ x, TopologicalSpace (K x)] [∀ x, IsTopologicalRing (K x)] [∀ x, T2Space (K x)] (f : ∀ x, A →+* K x)
    (ρ : ∀ x, G →* Matrix (Fin n) (Fin n) (K x)) (S : Set G), (∀ x, Continuous (f x)) → (∀ a, (∀ x, f x a = 0) → a = 0) → Dense S →
    (∀ x, Continuous (ρ x)) → (∀ g ∈ S, ∃ p : A[X], ∀ x, p.map (f x) = (ρ x g).charpoly) →
    ∃ D : GDet n A G, (∀ x, D.map (f x) = GDet.ofRep (ρ x)) ∧ ∀ i ≤ n, Continuous fun g : G => D.lam i (MonoidAlgebra.single g 1) := by
  intro n A G _ _ _ _ _ X K _ _ _ _ f ρ S hf hinj hS hρ hp
  let ι : A →+* (∀ x, K x) := Pi.ringHom f
  have hιc : Continuous ι := continuous_pi fun x => hf x
  have hιi : Function.Injective ι := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    exact hinj a fun x => congrFun ha x
  let R := UpperTheory.V.AlgebraTools.Det.piRep K ρ
  have hR : Continuous R := by
    apply continuous_matrix
    intro i j
    apply continuous_pi
    intro x
    exact ((hρ x).matrix_elem i j)
  obtain ⟨D, hD, hDc⟩ := UpperTheory.V.AlgebraTools.Det.glue ι (GDet.ofRep R) S hιc hιi hS
    (fun i _ => UpperTheory.V.AlgebraTools.Det.repCont R hR i)
    (by
      intro g hg i _
      obtain ⟨p, hp⟩ := hp g hg
      have hchar : (R g).charpoly = p.map ι := by
        ext k x
        have h1 := congrArg (fun q : (K x)[X] => q.coeff k)
          (Matrix.charpoly_map (R g) (Pi.evalRingHom K x))
        have h2 : (R g).map (Pi.evalRingHom K x) = ρ x g := by
          ext i j
          rfl
        rw [h2, ← hp x, Polynomial.coeff_map, Polynomial.coeff_map] at h1
        rw [Polynomial.coeff_map]
        exact h1.symm
      refine ⟨(-1) ^ i * p.coeff (n - i), ?_⟩
      show ι ((-1) ^ i * p.coeff (n - i)) = (-1) ^ i * ((GDet.ofRep R).chi (MonoidAlgebra.single g 1)).coeff (n - i)
      rw [(UpperTheory.V.AlgebraTools.Det.repApi R).2.1 g, hchar, Polynomial.coeff_map, map_mul, map_pow, map_neg, map_one])
  refine ⟨D, ?_, hDc⟩
  intro x
  have hfx : f x = (Pi.evalRingHom K x).comp ι := by
    ext a
    rfl
  rw [hfx, ← (UpperTheory.V.AlgebraTools.Det.mapApi D ι).2.2.2.2.2.2.1 (Pi.evalRingHom K x), hD, (UpperTheory.V.AlgebraTools.Det.repApi R).2.2.2.2.2.1 (Pi.evalRingHom K x)]
  congr 1
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.IsContIff
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.AdicContIff
open Polynomial UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.adicContIff :
    ∀ {Γ R : Type} [TopologicalSpace Γ] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (I : Ideal R), IsAdic I →
    ∀ f : Γ → R, UpperTheory.V.Alg.AdicCont I f ↔ Continuous f := by
  intro Γ R _ _ _ _ I hI f
  rw [isAdic_iff] at hI
  obtain ⟨hopen, hsmall⟩ := hI
  unfold UpperTheory.V.Alg.AdicCont
  constructor
  · intro hf
    rw [continuous_iff_continuousAt]
    intro g
    rw [ContinuousAt, tendsto_sub_nhds_zero_iff.symm]
    intro s hs
    obtain ⟨N, hN⟩ := hsmall s hs
    have hloc := (IsLocallyConstant.iff_eventually_eq _).mp (hf N) g
    rw [Filter.mem_map]
    filter_upwards [hloc] with y hy
    exact hN (Ideal.Quotient.eq.mp hy)
  · intro hf N
    rw [IsLocallyConstant.iff_eventually_eq]
    intro g
    have hO : IsOpen {r : R | r - f g ∈ I ^ N} :=
      (hopen N).preimage (continuous_id.sub continuous_const)
    have hmem : f g ∈ {r : R | r - f g ∈ I ^ N} := by
      simp
    filter_upwards [hf.continuousAt (hO.mem_nhds hmem)] with y hy
    exact Ideal.Quotient.eq.mpr hy
end

open Polynomial UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.isContIff :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace G] (I : Ideal A), IsAdic I → ∀ D : GDet n A G,
    D.IsCont I ↔ ∀ i ≤ n, Continuous fun g : G => D.lam i (MonoidAlgebra.single g 1) := by
  intro n A G _ _ _ _ _ I hI D
  unfold GDet.IsCont
  simp only [UpperTheory.V.AlgebraTools.Det.adicContIff I hI]
  constructor
  · intro h i _
    exact h i
  · intro h i
    by_cases hi : i ≤ n
    · exact h i hi
    · have heq : (fun g : G => D.lam i (MonoidAlgebra.single g 1)) =
          fun g => (-1) ^ (i + n) * D.lam n (MonoidAlgebra.single g 1) := by
        funext g
        unfold GDet.lam
        rw [Nat.sub_eq_zero_of_le (not_le.mp hi).le, Nat.sub_self, ← mul_assoc, ← pow_add, add_assoc,
          ← two_mul, pow_add, pow_mul, neg_one_sq, one_pow, mul_one]
      rw [heq]
      exact continuous_const.mul (h n le_rfl)
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance high] UpperTheory.V.W.coefLocal

private theorem cd_compact {R : Type} [CommRing R] [WithIdeal R] [IsAdicComplete (WithIdeal.i : Ideal R) R]
    (hf : ∀ N : ℕ, Finite (R ⧸ (WithIdeal.i : Ideal R) ^ N)) : CompactSpace R := by
  have hI : IsAdic (WithIdeal.i : Ideal R) := rfl
  have hc : CompleteSpace R := (hI.isAdicComplete_iff.1 inferInstance).1
  refine ⟨isCompact_iff_totallyBounded_isComplete.2 ⟨?_, complete_univ⟩⟩
  rw [totallyBounded_iff_subset_finite_iUnion_nhds_zero]
  intro U hU
  obtain ⟨N, hN⟩ := (isAdic_iff.1 hI).2 U hU
  choose s hs using fun q : R ⧸ (WithIdeal.i : Ideal R) ^ N => Ideal.Quotient.mk_surjective q
  refine ⟨Set.range s, Set.finite_range s, fun x _ => ?_⟩
  refine Set.mem_biUnion (Set.mem_range_self (Ideal.Quotient.mk _ x)) ⟨x - s (Ideal.Quotient.mk _ x), hN ?_, by simp⟩
  exact Ideal.Quotient.eq.1 (hs _).symm

private theorem cd_intIff {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl' : minpoly ℚ_[l] x ∈ lifts (algebraMap ℤ_[l] ℚ_[l]) :=
      (lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
    exact ⟨q, hqm, by rw [← aeval_def, ← aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

private theorem cd_norm_lt {l : ℕ} [Fact l.Prime] (c : Coef l) {R : Type} [CommRing R] [IsLocalRing R] [Algebra c.O R]
    (y : R →ₐ[c.O] PadicAlgCl l) (a : R) (ha : a ∈ maximalIdeal R) : ‖y a‖ < 1 :=
  _root_.UpperTheory.Reformulated.B.Gs5b.cd_norm_lt c y a ha

private theorem cd_pow {l : ℕ} [Fact l.Prime] (c : Coef l) {R : Type} [CommRing R] [Algebra c.O R] [Alg.IsCO c.O R]
    (y : R →ₐ[c.O] PadicAlgCl l) : ∃ b : ℝ, 0 ≤ b ∧ b < 1 ∧ ∀ N : ℕ, ∀ a ∈ maximalIdeal R ^ N, ‖y a‖ ≤ b ^ N := by
  have h1 : ∀ a, ‖y a‖ ≤ 1 := fun a => by
    obtain ⟨o, ho⟩ := Alg.IsCO.res_surj (O := c.O) a
    have e : y a = y (a - algebraMap c.O R o) + algebraMap c.O _ o := by simp
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (cd_norm_lt c y _ ho).le ((cd_intIff _).1 ?_))
    exact (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) o).map (IsScalarTower.toAlgHom ℤ_[l] c.O (PadicAlgCl l))
  let J : ℝ → Ideal R := fun b =>
    { carrier := {a | ‖y a‖ ≤ max b 0}
      add_mem' := fun {p q} hp hq => by
        change ‖y (p + q)‖ ≤ _
        rw [map_add (f := _)]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hp hq)
      zero_mem' := by simp
      smul_mem' := fun r p hp => by
        change ‖y (r * p)‖ ≤ _
        rw [map_mul, norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (h1 r)).trans hp }
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian (maximalIdeal R)
  have hb : ∃ b : ℝ, 0 ≤ b ∧ b < 1 ∧ ∀ a ∈ s, ‖y a‖ ≤ b := by
    refine ⟨(s.sup fun a => ‖y a‖₊ : NNReal), NNReal.coe_nonneg _, ?_, fun a ha => ?_⟩
    · rw [← NNReal.coe_one, NNReal.coe_lt_coe, Finset.sup_lt_iff (by simp)]
      exact fun a ha => cd_norm_lt c y a (hs ▸ Submodule.subset_span ha)
    · exact NNReal.coe_le_coe.2 (Finset.le_sup (f := fun a => ‖y a‖₊) ha)
  obtain ⟨b, b0, b1, hb⟩ := hb
  have hm : ∀ a ∈ maximalIdeal R, ‖y a‖ ≤ b := fun a ha => by
    have : maximalIdeal R ≤ J b := by
      rw [← hs, Submodule.span_le]
      exact fun a ha => (hb a ha).trans (le_max_left _ _)
    exact (this ha).trans (max_le le_rfl b0)
  refine ⟨b, b0, b1, fun N => ?_⟩
  induction N with
  | zero => simpa using h1
  | succ N ih =>
    have : maximalIdeal R ^ (N + 1) ≤ J (b ^ (N + 1)) := by
      rw [pow_succ (maximalIdeal R), Ideal.mul_le]
      intro p hp q hq
      change ‖y (p * q)‖ ≤ max (b ^ (N + 1)) 0
      refine le_trans ?_ (le_max_left _ _)
      rw [map_mul, norm_mul, pow_succ]
      exact mul_le_mul (ih p hp) (hm q hq) (norm_nonneg _) (pow_nonneg b0 _)
    exact fun a ha => (this ha).trans (max_le le_rfl (pow_nonneg b0 _))

private theorem cd_cont {l : ℕ} [Fact l.Prime] (c : Coef l) {R : Type} [CommRing R] [Algebra c.O R] [Alg.IsCO c.O R]
    [TopologicalSpace R] [IsTopologicalRing R] (hI : IsAdic (maximalIdeal R))
    (y : R →ₐ[c.O] PadicAlgCl l) : Continuous y := by
  obtain ⟨b, b0, b1, hb⟩ := cd_pow c y
  refine continuous_of_continuousAt_zero y (Metric.tendsto_nhds.2 fun ε hε => ?_)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε b1
  filter_upwards [((isAdic_iff.1 hI).1 N).mem_nhds (zero_mem _)] with a ha
  rw [map_zero, dist_zero_right]
  exact (hb N a ha).trans_lt hN

private theorem cd_xi {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {R : Type} [CommRing R] (I : Ideal R) (φ : Uo k →* Rˣ) (u : Rˣ)
    (hφ : ∀ N : ℕ, ∃ c : ℕ, ∀ y : Uo k, valuation k (((y : kˣ) : k) - 1) ≤ uniformizer k ^ ((c + 1 : ℕ) : ℤ) →
      (φ y : R) - 1 ∈ I ^ N) :
    ∃ ξ : kˣ →* Rˣ, Alg.AdicCont I (fun x => (ξ x : R)) ∧ (∀ y : Uo k, ξ y = φ y) ∧ ξ (unif k) = u := by
  let ξ : kˣ →* Rˣ := MonoidHom.mk' (fun x => φ ⟨x / unif k ^ ord k x, GlAx.val_div_ord x⟩ * u ^ ord k x) fun x y => by
    rw [mul_mul_mul_comm, ← map_mul, ← _root_.zpow_add, ← ord_mul]
    congr 2
    refine Subtype.ext ?_
    change x * y / _ = x / _ * (y / _)
    rw [ord_mul, _root_.zpow_add, mul_div_mul_comm]
  have h1 : ∀ y : Uo k, ξ y = φ y := fun y => by
    change φ ⟨_, _⟩ * u ^ ord k y = φ y
    have : ord k y = 0 := ord_eq_zero y.2
    simp only [this, zpow_zero, div_one, mul_one]
  refine ⟨ξ, fun N => ?_, h1, ?_⟩
  · obtain ⟨c, hc⟩ := hφ N
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hp : uniformizer k ^ ((c + 1 : ℕ) : ℤ) ≠ 0 := (zpow_pos GlAx.unif_pos _).ne'
    have hlt : uniformizer k ^ ((c + 1 : ℕ) : ℤ) < 1 := zpow_lt_one₀ GlAx.unif_pos uniformizer_lt_one (by omega)
    have hn : {z : k | valuation k z < uniformizer k ^ ((c + 1 : ℕ) : ℤ)} ∈ nhds (0 : k) :=
      (IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨Units.mk0 _ hp, subset_rfl⟩
    have hc' : Continuous fun y : kˣ => ((x⁻¹ * y : kˣ) : k) - 1 :=
      (Units.continuous_val.comp (continuous_const.mul continuous_id)).sub continuous_const
    filter_upwards [hc'.continuousAt.preimage_mem_nhds (x := x) (by simpa using hn)] with y hy
    have hy' : valuation k (((x⁻¹ * y : kˣ) : k) - 1) < uniformizer k ^ ((c + 1 : ℕ) : ℤ) := hy
    have hu : x⁻¹ * y ∈ Uo k := by
      have := (valuation k).map_one_add_of_lt (hy'.trans hlt)
      rwa [add_sub_cancel] at this
    have e : ξ y = ξ x * φ ⟨_, hu⟩ := by rw [← h1, ← map_mul]; simp
    rw [Ideal.Quotient.eq, e, Units.val_mul, ← mul_sub_one]
    exact Ideal.mul_mem_left _ _ (hc ⟨_, hu⟩ hy'.le)
  · change φ ⟨_, _⟩ * u ^ ord k (unif k) = u
    have : ord k (unif k) = 1 := ord_eq_one GlAx.unif_spec
    simp only [this, zpow_one, div_self']
    rw [show φ ⟨1, _⟩ = 1 from map_one φ, one_mul]

private theorem cd_alg {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {l : ℕ} [Fact l.Prime] (π : ℤ_[l] →+* R)
    (I : Ideal R) (hI : (l : R) ∈ I) (f : Γ → ℤ_[l]) (hf : Continuous f) :
    Alg.AdicCont I fun g => π (f g) := by
  intro n
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hpos : (0 : ℝ) < (l : ℝ) ^ (-(n : ℤ)) := zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _
  filter_upwards [hf.continuousAt.eventually (Metric.closedBall_mem_nhds (f x) hpos)] with y hy
  rw [dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton'] at hy
  obtain ⟨a, ha⟩ := hy
  rw [Ideal.Quotient.eq, ← map_sub, ← ha, map_mul, map_pow, map_natCast]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hI n)

private theorem cd_tel {M : Type} [CommGroup M] {n : ℕ} (U : Fin n → M) :
    ∃ u : Fin n → M, ∀ j, ∏ i with i ≤ j, u i = U j := by
  let V : ℕ → M := fun j => if h : 0 < j ∧ j - 1 < n then U ⟨j - 1, h.2⟩ else 1
  refine ⟨fun i => V (i + 1) / V i, fun j => ?_⟩
  have e : ∏ i with i ≤ j, V (i + 1) / V i = ∏ i ∈ Finset.range (j + 1), V (i + 1) / V i := by
    refine Finset.prod_bij (fun i _ => (i : ℕ)) ?_ ?_ ?_ ?_
    · intro i hi
      have : (i : ℕ) ≤ j := (Finset.mem_filter.1 hi).2
      simp; omega
    · exact fun a _ b _ h => Fin.ext h
    · intro b hb
      have := Finset.mem_range.1 hb
      have := j.2
      exact ⟨⟨b, by omega⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [Fin.le_def]; simp; omega⟩, rfl⟩
    · exact fun _ _ => rfl
  rw [e, Finset.prod_range_div]
  simp [V]

private theorem cd_fin {l : ℕ} [Fact l.Prime] (c : Coef l) : Finite (ResidueField c.O) := by
  have h : (maximalIdeal c.O).comap (algebraMap ℤ_[l] c.O) = maximalIdeal ℤ_[l] :=
    eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := ℤ_[l]) (maximalIdeal c.O))
  have : IsLocalHom (algebraMap ℤ_[l] c.O) := ((IsLocalRing.local_hom_tfae _).out 5 1).1 h
  exact ResidueField.finite_of_finite (R := ℤ_[l]) inferInstance

private theorem cd_eT {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    (i : Fin n) (c : ℕ) (y : Uo k) (hy : valuation k (((y : kˣ) : k) - 1) ≤ uniformizer k ^ ((c + 1 : ℕ) : ℤ)) :
    (eT k n i y : GL (Fin n) k) ∈ (glIwa k n).Tc c := by
  have key : ∀ y : Uo k, valuation k (((y : kˣ) : k) - 1) ≤ uniformizer k ^ ((c + 1 : ℕ) : ℤ) →
      GlAx.Bd ((c + 1 : ℕ) : ℤ) (eT k n i y : GL (Fin n) k) := fun y hy a b => by
    change valuation k (((diagT k (Fin n) (Pi.mulSingle i (y : kˣ))).val - 1) a b) ≤ _
    rw [val_diagT, ← Matrix.diagonal_one, Matrix.diagonal_sub, Matrix.diagonal_apply]
    split_ifs with h
    · by_cases h' : a = i
      · subst h'
        simpa using hy
      · simp [Pi.mulSingle_eq_of_ne h']
    · simp
  refine ⟨(eT k n i y).2, GlAx.mem_Kc.2 ⟨key y hy, ?_⟩⟩
  rw [← Subgroup.coe_inv, ← map_inv]
  refine key _ ?_
  have h1 : valuation k ((y : kˣ) : k) = 1 := y.2
  have e : (((y⁻¹ : Uo k) : kˣ) : k) - 1 = -(((y : kˣ) : k) - 1) * ((y : kˣ) : k)⁻¹ := by
    rw [Subgroup.coe_inv, Units.val_inv_eq_inv_val]
    field_simp
    ring
  rw [e, map_mul, map_inv₀, h1, Valuation.map_neg]
  simpa using hy

private theorem cd_psi (hN : GlobalTheory.Mem.LiteralAutomorphy.LitN) {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    {l : ℕ} [Fact l.Prime] {n : ℕ} {c : Coef l} (H : HSet L Ω l n c) (hH : H.Ax)
    {A : Type} [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ) (hθ : H.X.I.ContChar θ)
    {T : Type} [CommRing T] [Algebra c.O T] [Alg.IsCO c.O T] (f : A →ₐ[c.O] T) (v : H.V) (i : Fin n) (u : Tˣ) :
    ∃ ψ : Dec (F := L) (H.pl v) →* Tˣ, Alg.AdicCont (maximalIdeal T) (fun g => (ψ g : T)) ∧
      (∀ (s : Weil (H.ovr v)) (g : Dec (F := L) (H.pl v)) (y : Uo ((H.Sl v).adicCompletion L)),
        (g : G L Ω) = (s : G L Ω) → H.art v s = y →
        (ψ g * H.epsV T v g ^ (i : ℕ) : Tˣ) * f (θ (eV n H.Sl v i y)) = 1) ∧
      ∀ (s : Weil (H.ovr v)) (g : Dec (F := L) (H.pl v)), (g : G L Ω) = (s : G L Ω) → H.art v s = Hi.unif _ →
        ψ g * H.epsV T v g ^ (i : ℕ) = u := by
  classical
  let e : Uo ((H.Sl v).adicCompletion L) →* H.X.I.T := MonoidHom.mk' (eV n H.Sl v i) fun x y => Subtype.ext (by
    change (eV n H.Sl v i (x * y)).1 = (eV n H.Sl v i x).1 * (eV n H.Sl v i y).1
    unfold eV
    simp only [map_mul, Subgroup.coe_mul, Pi.mulSingle_mul])
  let φ : Uo ((H.Sl v).adicCompletion L) →* Tˣ := ((Units.map (f : A →* T)).comp (θ.comp e))⁻¹
  have hle : ∀ N, maximalIdeal A ^ N ≤ (maximalIdeal T ^ N).comap (f : A →+* T) := fun N => by
    refine le_trans (Ideal.pow_right_mono (fun y hy => ?_) N) (Ideal.le_comap_pow _ N)
    show f y ∈ maximalIdeal T
    rw [← Alg.res_eq_zero_iff c.O, Alg.res_map, Alg.res_eq_zero_iff]
    exact hy
  obtain ⟨ξ, hξ, hξu, hξp⟩ := cd_xi (maximalIdeal T) φ u fun N => by
    obtain ⟨b, hb⟩ := hθ N
    refine ⟨b, fun y hy => ?_⟩
    have h1 : ((e y : H.X.I.T) : GV n H.Sl) ∈ H.X.I.Tc b := fun v' _ => by
      change (eV n H.Sl v i y).1 v' ∈ _
      unfold eV
      by_cases h : v' = v
      · subst h
        simp only [Pi.mulSingle_eq_same]
        exact cd_eT i b y hy
      · simp only [Pi.mulSingle_eq_of_ne h]
        exact Subgroup.one_mem _
    have h2 := hle N (hb (e y)⁻¹ (inv_mem h1))
    rw [Ideal.mem_comap, map_sub, map_one, map_inv] at h2
    exact h2
  have := cd_fin c
  have hcnl := IsCNL.ofCO c.O T
  obtain ⟨ψ, ⟨hψ, hψa⟩, -⟩ := Loc.charExt hN.aut.art (H.ovr v) (H.art v) (hH.art_spec v) T ξ hξ
  have hl : ((l : ℕ) : T) ∈ maximalIdeal T := by
    have h : (maximalIdeal c.O).comap (algebraMap ℤ_[l] c.O) = maximalIdeal ℤ_[l] :=
      eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := ℤ_[l]) (maximalIdeal c.O))
    have h1 : (l : ℤ_[l]) ∈ maximalIdeal ℤ_[l] := by
      rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _
    rw [← h, Ideal.mem_comap] at h1
    have h2 := map_nonunit (algebraMap c.O T) _ h1
    rwa [map_natCast, map_natCast] at h2
  have hc := cd_alg ((algebraMap c.O T).comp (algebraMap ℤ_[l] c.O)) _ hl
    (fun g : Dec (F := L) (H.pl v) => ((cycZ L Ω l g ^ (i : ℕ))⁻¹ : ℤ_[l]ˣ))
    (Units.continuous_coe_inv.comp (((continuous_cycZ L Ω l).comp continuous_subtype_val).pow _))
  have hv : ∀ g, (ψ * (H.epsV T v ^ (i : ℕ))⁻¹) g * H.epsV T v g ^ (i : ℕ) = ψ g := fun g => by simp
  refine ⟨ψ * (H.epsV T v ^ (i : ℕ))⁻¹, fun N => ?_, fun s g y hg hy => ?_, fun s g hg hy => ?_⟩
  · convert (hψ N).mul (hc N) using 1
    funext g
    rw [Pi.mul_apply, ← map_mul]
    congr 1
    simp [HSet.epsV]
  · rw [hv, hψa s g hg trivial, hy, hξu]
    exact Units.inv_mul (Units.map (f : A →* T) (θ (e y)))
  · rw [hv, hψa s g hg trivial, hy, hξp]

private theorem cd_glue {l : ℕ} [Fact l.Prime] (c : Coef l) {n : ℕ} {T Γ : Type} [CommRing T] [Algebra c.O T] [Alg.IsCO c.O T]
    [Group Γ] [TopologicalSpace Γ] (Q : (T →ₐ[c.O] Qbar l) → Prop) (hsep : ∀ t, (∀ x, Q x → x t = 0) → t = 0)
    {J : Type} (s : J → Γ) (p : J → T[X]) (hs : DenseRange s)
    (hr : ∀ x, Q x → ∃ r : Γ →* GL (Fin n) (Qbar l), Continuous r ∧
      ∀ j, (p j).map x.toRingHom = (r (s j) : Matrix (Fin n) (Fin n) (Qbar l)).charpoly) :
    ∃ D : W.GDet n T Γ, D.IsCont (maximalIdeal T) ∧ ∀ j, D.chi (MonoidAlgebra.single (s j) 1) = p j := by
  choose r hrc hrf using hr
  have := cd_fin c
  have hcnl := IsCNL.ofCO c.O T
  letI : WithIdeal T := ⟨maximalIdeal _⟩
  have hI : IsAdic (maximalIdeal T) := rfl
  haveI : CompactSpace T := @cd_compact _ _ _ hcnl.complete fun N => by
    haveI : Finite (T ⧸ maximalIdeal T) := hcnl.finite
    exact Ideal.finite_quotient_pow (I := maximalIdeal T) (IsNoetherian.noetherian _) N
  have hinj : ∀ t : T, (∀ x : {x // Q x}, x.1.toRingHom t = 0) → t = 0 :=
    fun t ht => hsep t fun x hx => ht ⟨x, hx⟩
  obtain ⟨D, hD, hDc⟩ := AlgebraTools.Det.glueRep (fun _ : {x // Q x} => Qbar l) (fun x => x.1.toRingHom)
    (fun x => W.mat (r x.1 x.2)) _ (fun x => cd_cont c hI x.1) hinj hs
    (fun x => Units.continuous_val.comp (hrc x.1 x.2)) (by
      rintro _ ⟨j, rfl⟩
      exact ⟨_, fun x => hrf x.1 x.2 j⟩)
  refine ⟨D, (AlgebraTools.Det.isContIff _ hI D).2 hDc, fun j => Polynomial.ext fun k => ?_⟩
  rw [← sub_eq_zero]
  refine hinj _ fun x => ?_
  have h1 := (AlgebraTools.Det.mapApi D x.1.toRingHom).1 (MonoidAlgebra.single (s j) 1)
  rw [hD x, MonoidAlgebra.mapRingHom_single, map_one, (AlgebraTools.Det.repApi (W.mat (r x.1 x.2))).2.1] at h1
  have h2 := congrArg (fun p => p.coeff k) (h1.symm.trans (hrf x.1 x.2 j).symm)
  simp only [Polynomial.coeff_map] at h2
  rw [map_sub, sub_eq_zero]
  exact h2

private theorem cd_pol {T : Type} [CommRing T] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (x : T →+* Qbar l) (n q : ℕ)
    (a : ℕ → T) (b : ℕ → ℂ) (h : ∀ j ≤ n, ι (x (a j)) = b j) (p : (Qbar l)[X]) (hp : p.map ι.toRingHom = Hi.heckePol n q b) :
    (Hi.heckePol n q a).map x = p := by
  apply Polynomial.map_injective ι.toRingHom ι.injective
  rw [hp]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Hi.heckePol, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow, map_C, map_X]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp [← h j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))]

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in
theorem UpperTheory.V.Hi.coreDet :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ) (P : Wt L l n → (H.Gq →* GL (Fin n) (Qbar l)) → Prop), H.Aut ι P →
    ∀ lam0 ∈ H.admitted, H.DenseWt θ lam0 → ∀ (a : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))] [Alg.IsCO c.O (H.TK θ a K)], ∃ (D : W.GDet n (H.TK θ a K) H.Gq) (ψ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* (H.TK θ a K)ˣ), H.IsUniv θ a K (maximalIdeal _) D ψ := by
  intro hN L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ hθ ι P hP lam hlam hd a K _ _
  have hne : H.MK θ a K ≠ ⊥ := fun h => by
    have : Subsingleton (H.MK θ a K) := Submodule.subsingleton_iff_eq_bot.2 h
    exact zero_ne_one (α := H.TK θ a K) (Subtype.ext (Subsingleton.elim _ _))
  obtain ⟨_, -, -, -, hU, -⟩ := hiAlg L Ω l n c H hH A θ hθ a K hne
  choose u hu using fun v => cd_tel fun j => (hU v j).unit
  choose ψ hψ1 hψ2 hψ3 using fun v i =>
    cd_psi hN H hH θ hθ.cont (IsScalarTower.toAlgHom c.O A (H.TK θ a K)) v i (u v i)
  obtain ⟨D, hD, hDf⟩ := cd_glue (n := n) c (fun x => H.Good θ (x.toRingHom.comp (algebraMap A _)) lam)
    (coreSep hN L Ω l n c H hH A θ hθ ι P hP a K lam hlam hd)
    (J := {j : H.Wp × ValuationSubring Ω × G L Ω // IsPlaceOver j.2.1 j.1.1 ∧ IsFrob j.2.1 (normV j.1.1) j.2.2})
    (fun j => H.prj j.1.2.2⁻¹) (fun j => heckePol n (normV j.1.1.1) (H.genW θ a K j.1.1))
    (hH.dense.mono (by
      rintro _ ⟨w, hw, B, σ, hB, hσ, rfl⟩
      exact ⟨⟨(⟨w, hw⟩, B, σ), hB, hσ⟩, rfl⟩)) fun x hx => by
    obtain ⟨d, ξ, c0, sp, hsp⟩ := spec L Ω l n c H hH A θ hθ ι (x.comp (IsScalarTower.toAlgHom c.O A _)) lam hx.2.1
    obtain ⟨-, act, -, -, -, h4, -⟩ := partAct0 hN L Ω l n c H hH A θ hθ ι P hP _ lam d ξ c0 sp hsp hlam a K _ rfl
    obtain ⟨Y, F, e, -, -, hF, hFY, hop⟩ := h4 x rfl
    refine ⟨Y.r, Y.cont, fun ⟨⟨w, B, σ⟩, hB, hσ⟩ => cd_pol ι _ n _ _ (Y.a w) (fun j hj => ?_) _ (Y.frob w B σ hB hσ)⟩
    change ι (x (H.genW θ a K w j)) = _
    rcases j with _ | j
    · rw [HSet.genW, dite_eq_right (by omega), map_one, map_one, Y.a_zero]
    · rw [HSet.genW, dite_eq_left ⟨j.succ_pos, hj⟩]
      exact smul_left_injective ℂ hF ((hop (.inl (w, ⟨j, hj⟩))).symm.trans (Y.sph w (j + 1) F hFY.1))
  refine ⟨D, ψ, hD, hψ1, fun w B σ hB hσ => hDf ⟨(w, B, σ), hB, hσ⟩, hψ2, fun v j s g hg hs => ?_⟩
  rw [Finset.prod_congr rfl fun i _ => hψ3 v i s g hg hs, hu]
  rfl

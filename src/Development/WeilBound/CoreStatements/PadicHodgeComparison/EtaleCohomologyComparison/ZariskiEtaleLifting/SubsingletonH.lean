module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.PropsA
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstCohomologyVectorBundleRank
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemSpanIffOfBijective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemMapBasis
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StepDesc
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentLocalizationUniversal
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FTors
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIntegralMultipleBoundedPlaces
public import Lean.LibrarySuggestions.Basic
public import Lean.Elab.Command

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IncPtInjective
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.ElOnto

variable {l : ℕ} [Fact l.Prime]

theorem elMap_full {P P' : PAlg l ⥤ Type} (u : P ⟶ P') (hu : ∀ A, Function.Injective (u.app A)) : (elMap u).Full := by
  refine ⟨fun {X Y} f => ⟨⟨f.1, ?_⟩, rfl⟩⟩
  apply hu
  exact (NatTrans.naturality_apply u ((testι l).map f.1) X.2).trans f.2

theorem elMap_faithful {P P' : PAlg l ⥤ Type} (u : P ⟶ P') : (elMap u).Faithful := by
  refine ⟨fun {X Y} f g h => Functor.Elements.Hom.ext ?_⟩
  have h' := congrArg (fun f => f.hom) h
  exact h'

variable {O : Type} [CommRing O]

theorem inc_pt_injective {F : Fn O} (κ : O →+* OC l) (V : F.Sub) (A : PAlg l) :
    Function.Injective ((V.inc.pt κ).app A) := by
  intro a b h
  have h' := congrArg Subtype.val h
  apply Subtype.ext
  apply Subtype.ext
  exact h'

theorem onto_subEl : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {d : ℕ} (𝒜 : F.Atlas d) (S : Set 𝒜.A) (k : Bool) (n : ℕ), n ≠ 0 → Onto (subEl κ (Fn.Sub.inter 𝒜.V S)) fun T => ∀ α ∈ S, (𝒜.V α).In ((gT F κ k n).obj T).y.1.2 := by
  intro l _ O _ F κ d 𝒜 S k n hn
  refine ⟨elMap_full _ (inc_pt_injective κ _), elMap_faithful _, ?_, ?_⟩
  · intro T α hα
    exact (𝒜.V α).in_map _ (T.2.1.2 α hα)
  · intro T hT
    obtain ⟨hs, hj⟩ := (GlobalTheory.T.period_ring_base_change_from_universal T.1.obj n).2.2.2.2.2.2 k hn
    refine ⟨⟨⟨⟨T.2.1, fun α hα => 𝒜.jac α _ _ (CommRingCat.ofHom (uJ k T.1.obj n)) T.2.1 hs hj (hT α hα)⟩, T.2.2⟩⟩, ⟨Iso.refl _⟩⟩

end GlobalTheory.CompanionTheory.ElOnto
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AcrTeichProd
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.TestZar

theorem idem_unit {R : Type} [CommRing R] {u : R} (hu : IsIdempotentElem u) (h : IsUnit u) : u = 1 :=
  h.mul_left_cancel (by rw [mul_one]; exact hu)

theorem factor_one {R R' ι : Type} [CommRing R] [CommRing R'] (g : R →+* R') (b : ι → R) (hb : ∀ i, IsIdempotentElem (b i))
    (S : Finset ι) (h : g (∏ i ∈ S, b i) = 1) {i : ι} (hi : i ∈ S) : g (b i) = 1 :=
  idem_unit ((hb i).map g) (isUnit_of_dvd_unit (map_dvd g (Finset.dvd_prod_of_mem b hi)) (h ▸ isUnit_one))

theorem span_of_nil {R P ι : Type} [CommRing R] [CommRing P] (I : Ideal R) (hI : ∀ x ∈ I, IsNilpotent x) (g : ι → R)
    (π : P →+* R ⧸ I) (e : ι → P) (he : Ideal.span (Set.range e) = ⊤)
    (h : ∀ i, π (e i) = Ideal.Quotient.mk I (g i)) : Ideal.span (Set.range g) = ⊤ := by
  have h1 : Ideal.map (Ideal.Quotient.mk I) (Ideal.span (Set.range g)) = ⊤ := by
    have e1 : (Ideal.Quotient.mk I) ∘ g = π ∘ e := funext fun i => (h i).symm
    rw [Ideal.map_span, ← Set.range_comp, e1, Set.range_comp, ← Ideal.map_span, he, Ideal.map_top]
  have h2 : (1 : R ⧸ I) ∈ Ideal.map (Ideal.Quotient.mk I) (Ideal.span (Set.range g)) := by
    rw [h1]; trivial
  obtain ⟨a, ha, ha1⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 h2
  have hj : a - 1 ∈ I := Ideal.Quotient.eq.1 (by rw [ha1, map_one])
  have hu : IsUnit a := by
    have := (hI _ hj).isUnit_add_one
    simpa using this
  exact Ideal.eq_top_of_isUnit_mem _ ha hu

section Gen

open GlobalTheory.CompanionTheory.ThickZar

variable {O : Type} [CommRing O] {F : Fn O} {b : Base} {ht : b.t = 1} {κ : O →+* b.R ⧸ b.I}
  {R₀ : Type} [CommRing R₀] (c : R₀ →+* b.R) (r : ℕ)
  {C : Type*} [Category C] (G : C ⥤ Thick (F.cr b ht κ))

def locModG {m : ℕ} (T' : C) (Lc : Finset (Fin m) → C) (lam : ∀ S, T' ⟶ Lc S)
    (f : Fin m → (G.obj T').B) (hf : Ideal.span (Set.range f) = ⊤)
    (h1 : ∀ S, ∀ k ∈ S, (G.map (lam S)).φ (f k) = 1)
    (hs : ∀ S, ∀ y ∈ (G.obj (Lc S)).pdPow r, ∃ x ∈ (G.obj T').pdPow r, (G.map (lam S)).φ x = y)
    (hk : ∀ S x, (G.map (lam S)).φ x = 0 → (∏ k ∈ S, f k) * x = 0) :
    LocMod (G ⋙ (pdS (F.cr b ht κ) c r).fn) T' Lc lam where
  Λ := (G.obj T').B
  f := f
  span := hf
  ρ₀ := mulR c r (G.obj T')
  ρ S := (mulR c r (G.obj (Lc S))).comp (G.map (lam S)).φ
  lam_ρ S a x := Subtype.ext (map_mul (G.map (lam S)).φ a (show (G.obj T').B from x.1))
  tr_ρ S S' t ht' a x := by
    have e : (G.map t).φ.comp (G.map (lam S)).φ = (G.map (lam S')).φ := by
      have := congrArg Thick.Hom.φ (congrArg G.map ht')
      rw [G.map_comp] at this
      exact this
    refine Subtype.ext ?_
    change (G.map t).φ ((G.map (lam S)).φ a * (show (G.obj (Lc S)).B from x.1)) =
      (G.map (lam S')).φ a * (G.map t).φ (show (G.obj (Lc S)).B from x.1)
    rw [map_mul, ← RingHom.comp_apply (G.map t).φ, e]
  unit S k hk' := by
    change Function.Bijective (mulR c r (G.obj (Lc S)) ((G.map (lam S)).φ (f k)))
    rw [h1 S k hk', map_one]
    exact Function.bijective_id
  surj S y := by
    obtain ⟨x, hx, e⟩ := hs S y.1 y.2
    refine ⟨0, ⟨x, hx⟩, ?_⟩
    rw [pow_zero, map_one]
    exact Subtype.ext e.symm
  ker S x hx := by
    have h0 : (G.map (lam S)).φ (show (G.obj T').B from x.1) = 0 := congrArg Subtype.val hx
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one]
    exact hk S _ h0

end Gen

variable {l : ℕ} [Fact l.Prime]

theorem step_onto {A B : PAlg l} (lam : A ⟶ B) (k : Bool) (n r : ℕ) (hs : Function.Surjective (mapAcr lam n))
    {y : B.Acr n} (hy : y ∈ fil (DD k B n) r) : ∃ x ∈ fil (DD k A n) r, mapAcr lam n x = y := by
  have hA := (GlobalTheory.T.period_ring_base_change_from_universal A n).2.2.2.2.1 k r
  have hB := (GlobalTheory.T.period_ring_base_change_from_universal B n).2.2.2.2.1 k r
  have e : (mapAcr lam n).comp (mapAcr A.fromBase n) = mapAcr B.fromBase n :=
    RingHom.ext fun x => mapAcr_fromBase lam n x
  rw [hB, ← e, ← Ideal.map_map, ← hA] at hy
  exact (Ideal.mem_map_iff_of_surjective _ hs).1 hy

theorem span_acr (A : PAlg l) (n : ℕ) {m : ℕ} (e : Fin m → A.A) (he : Ideal.span (Set.range e) = ⊤) :
    Ideal.span (Set.range fun i => A.toAcr n (WittVector.teichmuller l (e i))) = ⊤ := by
  obtain ⟨⟨π, hπ, -⟩, -, -, -, -, hnil, -⟩ := GlobalTheory.T.period_ring_base_change_from_universal A n
  exact span_of_nil (A.PFil n) (fun x hx => (hnil x hx).1) _ π e he fun i => hπ _

theorem acr_teich_one {A B : PAlg l} (f : A ⟶ B) (n : ℕ) {a : A.A} (h : Hom.f f a = 1) :
    mapAcr f n (A.toAcr n (WittVector.teichmuller l a)) = 1 := by
  rw [mapAcr_toAcr, mapW, WittVector.map_teichmuller, h, map_one, map_one]

theorem acr_teich_prod (A : PAlg l) (n : ℕ) {ι : Type} (S : Finset ι) (a : ι → A.A) :
    A.toAcr n (WittVector.teichmuller l (∏ i ∈ S, a i)) = ∏ i ∈ S, A.toAcr n (WittVector.teichmuller l (a i)) := by
  rw [map_prod, map_prod]

section Fac

variable {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l)

def facObj (T' : El (F.pt κ)) (A' : PAlg l) (lam : T'.1.obj ⟶ A') (h : A'.IsTest) : El (F.pt κ) :=
  (testι l ⋙ F.pt κ).elementsMk ⟨A', h⟩ ((F.pt κ).map lam T'.val)

def facHom (T' : El (F.pt κ)) (A' : PAlg l) (lam : T'.1.obj ⟶ A') (h : A'.IsTest) : T' ⟶ facObj F κ T' A' lam h :=
  ⟨ObjectProperty.homMk lam, rfl⟩

theorem fac_univ (T' : El (F.pt κ)) (A' : PAlg l) (lam : T'.1.obj ⟶ A') (h : A'.IsTest) (T'' : El (F.pt κ)) (ψ : T' ⟶ T'')
    (hu : ∃! χ : A' ⟶ T''.1.obj, lam ≫ χ = ψ.1.hom) :
    ∃! χ : facObj F κ T' A' lam h ⟶ T'', facHom F κ T' A' lam h ≫ χ = ψ := by
  obtain ⟨χ, hχ, huniq⟩ := hu
  refine ⟨⟨ObjectProperty.homMk χ, ?_⟩, Functor.Elements.hom_ext (ObjectProperty.hom_ext _ hχ), fun χ' h' =>
    Functor.Elements.hom_ext (ObjectProperty.hom_ext _ (huniq χ'.1.hom (congrArg (fun z => z.1.hom) h')))⟩
  change (F.pt κ).map χ ((F.pt κ).map lam T'.2) = T''.2
  rw [← Functor.map_comp_apply, hχ]
  exact ψ.2

theorem fac_loc (k : Bool) (n r : ℕ) (T' : El (F.pt κ)) {m : ℕ} (b : Fin m → T'.1.obj.A)
    (hspan : Ideal.span (Set.range b) = ⊤) (A' : Finset (Fin m) → PAlg l) (lam : ∀ S, T'.1.obj ⟶ A' S)
    (ht : ∀ S, (A' S).IsTest) (h1 : ∀ S, ∀ i ∈ S, Hom.f (lam S) (b i) = 1)
    (hs : ∀ S, Function.Surjective (mapAcr (lam S) n))
    (hk : ∀ S x, mapAcr (lam S) n x = 0 → T'.1.obj.toAcr n (WittVector.teichmuller l (∏ i ∈ S, b i)) * x = 0) :
    Nonempty (LocMod (gT F κ k n ⋙ (pdS (Lc F κ k n) ((base l).cris n) r).fn) T'
      (fun S => facObj F κ T' (A' S) (lam S) (ht S)) fun S => facHom F κ T' (A' S) (lam S) (ht S)) := by
  have hf : Ideal.span (Set.range fun i => T'.1.obj.toAcr n (WittVector.teichmuller l (b i))) = ⊤ := span_acr _ n b hspan
  have hk' : ∀ S x, mapAcr (lam S) n x = 0 →
      (∏ i ∈ S, T'.1.obj.toAcr n (WittVector.teichmuller l (b i))) * x = 0 := fun S x hx => by
    have h := hk S x hx
    rw [acr_teich_prod] at h
    exact h
  exact ⟨locModG (F := F) (b := bs l k n) (ht := rfl) (κ := κb κ k n) ((base l).cris n) r (gT F κ k n) T'
    (fun S => facObj F κ T' (A' S) (lam S) (ht S)) (fun S => facHom F κ T' (A' S) (lam S) (ht S))
    (fun i => T'.1.obj.toAcr n (WittVector.teichmuller l (b i))) hf
    (fun S i hi => acr_teich_one (lam S) n (h1 S i hi))
    (fun S y hy => step_onto (lam S) k n r (hs S) hy) hk'⟩

theorem factors (k : Bool) (n r : ℕ) (T' : El (F.pt κ)) {m : ℕ}
    (b : Fin m → T'.1.obj.A) (hb : ∀ i, IsIdempotentElem (b i)) (hspan : Ideal.span (Set.range b) = ⊤) :
    ∃ (Lc' : Finset (Fin m) → El (F.pt κ)) (lamE : ∀ S, T' ⟶ Lc' S),
      (∀ S, ∀ i ∈ S, Hom.f (lamE S).1.hom (b i) = 1) ∧
      (∀ S (T'' : El (F.pt κ)) (ψ : T' ⟶ T''), (∀ i ∈ S, Hom.f ψ.1.hom (b i) = 1) → ∃! χ : Lc' S ⟶ T'', lamE S ≫ χ = ψ) ∧
      Nonempty (LocMod (gT F κ k n ⋙ (pdS (Lc F κ k n) ((base l).cris n) r).fn) T' Lc' lamE) := by
  have ha : ∀ S : Finset (Fin m), IsIdempotentElem (∏ i ∈ S, b i) := fun S =>
    Finset.prod_induction _ IsIdempotentElem (fun _ _ h h' => h.mul h') IsIdempotentElem.one fun i _ => hb i
  choose A' lam htest hlam huniv hacr using fun S => GlobalTheory.T.idempotent_localization_universal T'.1.obj (∏ i ∈ S, b i) (ha S)
  have h1 : ∀ S, ∀ i ∈ S, Hom.f (lam S) (b i) = 1 := fun S i hi => factor_one (Hom.f (lam S)) b hb S (hlam S) hi
  have ht : ∀ S, (A' S).IsTest := fun S => htest S T'.1.property
  refine ⟨fun S => facObj F κ T' (A' S) (lam S) (ht S), fun S => facHom F κ T' (A' S) (lam S) (ht S), h1,
    fun S T'' ψ h => fac_univ F κ T' (A' S) (lam S) (ht S) T'' ψ (huniv S T''.1.obj ψ.1.hom ?_),
    fac_loc F κ k n r T' b hspan A' lam ht h1 (fun S => (hacr S n).1) fun S => (hacr S n).2⟩
  rw [map_prod]
  exact Finset.prod_eq_one fun i hi => h i hi

end Fac

theorem chart_of_one {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {d : ℕ} (𝒜 : F.Atlas d) (k : Bool) (n : ℕ)
    {T T₁ : El (F.pt κ)} (ψ : T ⟶ T₁) (s : T.1.obj.U) (a : T.1.obj.A) (ha : T.1.obj.sharp a ∈ Ideal.span {s})
    (hcov : ∀ (B' : CommRingCat) (φ : CommRingCat.of T.1.obj.U ⟶ B'), IsUnit (φ.hom s) →
      ∃ α, (𝒜.V α).In (F.Pt.map φ T.2.1))
    (h : Hom.f ψ.1.hom a = 1) : ∃ α, (𝒜.V α).In ((gT F κ k n).obj T₁).y.1.2 := by
  have hu : IsUnit ((CommRingCat.ofHom (mapU ψ.1.hom)).hom s) := by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 ha
    have h2 := congrArg (mapU ψ.1.hom) hc
    rw [map_mul, mapU_sharp, h, map_one] at h2
    exact IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact h2)
  obtain ⟨α, hα⟩ := hcov _ _ hu
  have hpt : F.Pt.map (CommRingCat.ofHom (mapU ψ.1.hom)) T.2.1 = T₁.2.1 := congrArg Subtype.val ψ.2
  rw [hpt] at hα
  exact ⟨α, (𝒜.V α).in_map (CommRingCat.ofHom (uJ k T₁.1.obj n)) hα⟩

theorem zarCov_test : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {d : ℕ} (𝒜 : F.Atlas d)
    (k : Bool) (n r : ℕ), ZarCov (gT F κ k n ⋙ (pdS (Lc F κ k n) ((base l).cris n) r).fn)
      fun T => ∃ α, (𝒜.V α).In ((gT F κ k n).obj T).y.1.2 := by
  intro l _ O _ F κ d 𝒜 k n r
  refine ⟨fun T T' φ h => (GlobalTheory.CompanionTheory.ThickZar.zarCov_pdS F (bs l k n) rfl (κb κ k n) ((base l).cris n) 𝒜
    (Fact.out : l.Prime).ne_zero r).1 ((gT F κ k n).map φ) h, fun T => ?_⟩
  obtain ⟨m, s, hs, hcov⟩ := 𝒜.cov (CommRingCat.of T.1.obj.U) T.2.1
  obtain ⟨e, hidem, hspan, hes⟩ := GlobalTheory.T.idempotent_refinement_of_unimodular T.1.obj T.1.property s hs
  refine ⟨m, fun i _ ψ => Hom.f ψ.1.hom (e i) = 1, fun i T₁ T₂ ψ χ h => ?_,
    fun i T₁ ψ h => chart_of_one F κ 𝒜 k n ψ (s i) (e i) (hes i) (hcov i) h, fun T' φ => ?_⟩
  · have h' : Hom.f ψ.1.hom (e i) = 1 := h
    have e1 : Hom.f (ψ ≫ χ).1.hom (e i) = Hom.f χ.1.hom (Hom.f ψ.1.hom (e i)) := rfl
    exact e1.trans (by rw [h', map_one])
  have hspan' : Ideal.span (Set.range fun i => Hom.f φ.1.hom (e i)) = ⊤ := by
    have h := congrArg (Ideal.map (Hom.f φ.1.hom)) hspan
    rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at h
    exact h
  obtain ⟨Lc', lamE, h1, h2, h3⟩ := factors F κ k n r T' (fun i => Hom.f φ.1.hom (e i))
    (fun i => (hidem i).map (Hom.f φ.1.hom)) hspan'
  exact ⟨Lc', lamE, fun S i hi => h1 S i hi, fun S T'' ψ h => h2 S T'' ψ fun i hi => h i hi, h3⟩

end GlobalTheory.CompanionTheory.TestZar
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GammaComp
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.ThetaEx

section Gen
variable {O : Type} [CommRing O] {F : Fn O} {d : ℕ} (s : F.Small d) {b : Base} (ht : b.t = 1)
  {κ : O →+* b.R ⧸ b.I}
  (𝓛 : Lift s.a (fun k => (s.T k : s.R)) b.R b.I κ) (δ : DividedPowers (b.I.map 𝓛.i))
  (hδ : IsDPMorphism b.γ δ 𝓛.i) (hp : b.p ≠ 0) (hn : IsNilpotent (b.p : b.R))

theorem arrow_ex (T : Thick (F.cr b ht κ)) (g' : s.R →+* T.B ⧸ T.J)
    (hg' : F.Pt.map (CommRingCat.ofHom g') s.y₀ = T.y.1.2) (u : Fin d → T.B)
    (hu : ∀ k, Ideal.Quotient.mk T.J (u k) = g' (s.T k)) :
    ∃ c : liftObj s ht 𝓛 δ hδ hp hn ⟶ T, ∀ k, c.φ (𝓛.t k) = u k := by
  obtain ⟨g, -, hg, hU⟩ := GlobalTheory.CompanionTheory.ThickHom.main s ht 𝓛 δ hδ hp hn T
  obtain ⟨g₀, -, h₀⟩ := s.univ (CommRingCat.of (T.B ⧸ T.J)) T.y.1.2 (T.y.1.1.comp κ) T.y.2
  have e : g' = g := (h₀ g' hg').trans (h₀ g hg).symm
  subst e
  exact (hU u hu).exists

theorem arrow_uniq (T : Thick (F.cr b ht κ)) (c c' : liftObj s ht 𝓛 δ hδ hp hn ⟶ T)
    (h : ∀ k, c.φ (𝓛.t k) = c'.φ (𝓛.t k)) : c = c' := by
  obtain ⟨g, hc, -, hU⟩ := GlobalTheory.CompanionTheory.ThickHom.main s ht 𝓛 δ hδ hp hn T
  exact (hU (fun k => c'.φ (𝓛.t k)) (fun k => hc c' _ _ (𝓛.hT k).symm)).unique h fun _ => rfl

end Gen

theorem gamma_comp {C C₀ : Type*} [Category C] [Category C₀] {j : C₀ ⥤ C} {U : UF C} {d : ℕ} {D T : C}
    (A : Act j U d D) (a : Gam d) (θ : D ⟶ T) :
    (A.γ a).asHom ≫ θ = A.act (fun k => U.q T ^ (Multiplicative.toAdd a k)) θ := by
  change A.act _ (𝟙 D) ≫ θ = _
  rw [A.act_comp, Category.id_comp]
  congr 1
  funext k
  rw [map_pow, U.map_q]

theorem i_qU {l : ℕ} [Fact l.Prime] (ε : Eps l) (A : PAlg l) (n : ℕ) :
    mapAcr A.fromBase n (ε.qU n : (base l).Acr n) = A.toAcr n (WittVector.teichmuller l (A.s (ε.e 0))) := by
  rw [ε.qU_val, mapAcr_cris, ε.cris_qk]

theorem teich_step {l : ℕ} [Fact l.Prime] (A : PAlg l) (f : A ⟶ A) (n m : ℕ) (e c : A.A)
    (h : Hom.f f c = e ^ m * c) :
    A.toAcr n (WittVector.teichmuller l e) ^ m * A.toAcr n (WittVector.teichmuller l c) =
      mapAcr f n (A.toAcr n (WittVector.teichmuller l c)) := by
  rw [mapAcr_toAcr, mapW, WittVector.map_teichmuller, h, map_mul, map_pow, map_mul, map_pow]

theorem main : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F : Fn O} {κ : O →+* OC l} {d : ℕ} {s : F.Small d} (𝒯 : Tower κ s) (k : Bool) (n : ℕ) (𝓛 : Lift s.a (fun k => (s.T k : s.R)) (bs l k n).R (bs l k n).I (κb κ k n)) (δ : DividedPowers ((bs l k n).I.map 𝓛.i)) (hδ : IsDPMorphism (bs l k n).γ δ 𝓛.i) (hp : (bs l k n).p ≠ 0) (hn : IsNilpotent ((bs l k n).p : (bs l k n).R)) (ε : Eps l) (A : Act (𝟭 _) (thU (Lc F κ k n) (ε.qU n) (ε.qU_mem k n)) d (liftObj s (b := bs l k n) rfl 𝓛 δ hδ hp hn)) (A' : Act (jE (F.pt κ)) (epsU ε (F.pt κ)) d 𝒯.obj), (∀ (T : Thick (Lc F κ k n)) (a : Fin d → (thU (Lc F κ k n) (ε.qU n) (ε.qU_mem k n)).U T) (c : liftObj s (b := bs l k n) rfl 𝓛 δ hδ hp hn ⟶ T) (j : Fin d), (A.act a c).φ (𝓛.t j) = ((a j).1 : T.B) * c.φ (𝓛.t j)) → (∀ (T : (F.pt κ).Elements) (a : Fin d → (epsU ε (F.pt κ)).U T) (φ : 𝒯.obj ⟶ T) (j : Fin d), PAlg.Hom.f (A'.act a φ).hom (𝒯.c j 0).val = ((a j).1 : T.1.A) * PAlg.Hom.f φ.hom (𝒯.c j 0).val) → ∃ θ : liftObj s (b := bs l k n) rfl 𝓛 δ hδ hp hn ⟶ (gE F κ k n).obj 𝒯.obj, (∀ j, θ.φ (𝓛.t j) = 𝒯.A.toAcr n (WittVector.teichmuller l (𝒯.c j 0 : 𝒯.A.A))) ∧ ∀ a, (A.γ a).asHom ≫ θ = θ ≫ (gE F κ k n).map (A'.γ a).asHom := by
  intro l _ O _ F κ d s 𝒯 k n 𝓛 δ hδ hp hn ε A A' hA hA'
  have hy : F.Pt.map (CommRingCat.ofHom ((uJ k 𝒯.A n).comp 𝒯.g)) s.y₀ = ((gE F κ k n).obj 𝒯.obj).y.1.2 := by
    rw [CommRingCat.ofHom_comp, F.Pt.map_comp]
    rfl
  have hu : ∀ j, Ideal.Quotient.mk (JJ k 𝒯.A n) (𝒯.A.toAcr n (WittVector.teichmuller l (𝒯.c j 0 : 𝒯.A.A))) =
      (uJ k 𝒯.A n).comp 𝒯.g (s.T j) := fun j => by
    rw [RingHom.comp_apply, ← 𝒯.c_sharp j]
    exact (uJ_th k 𝒯.A n _).symm
  obtain ⟨θ, hθ⟩ := arrow_ex s rfl 𝓛 δ hδ hp hn ((gE F κ k n).obj 𝒯.obj) ((uJ k 𝒯.A n).comp 𝒯.g) hy
    (fun j => 𝒯.A.toAcr n (WittVector.teichmuller l (𝒯.c j 0 : 𝒯.A.A))) hu
  refine ⟨θ, hθ, fun a => arrow_uniq s rfl 𝓛 δ hδ hp hn _ _ _ fun j => ?_⟩
  have h1 : ((A.γ a).asHom ≫ θ).φ (𝓛.t j) =
      𝒯.A.toAcr n (WittVector.teichmuller l (𝒯.A.s (ε.e 0))) ^ (Multiplicative.toAdd a j) *
        𝒯.A.toAcr n (WittVector.teichmuller l (𝒯.c j 0 : 𝒯.A.A)) := by
    rw [gamma_comp A a θ, hA _ _ θ j, hθ j, ← i_qU]
    rfl
  have h2 : PAlg.Hom.f (A'.γ a).asHom.hom (𝒯.c j 0).val =
      (𝒯.A.s (ε.e 0)) ^ (Multiplicative.toAdd a j) * (𝒯.c j 0).val := hA' 𝒯.obj _ (𝟙 𝒯.obj) j
  have h3 : (θ ≫ (gE F κ k n).map (A'.γ a).asHom).φ (𝓛.t j) =
      mapAcr (A'.γ a).asHom.hom n (𝒯.A.toAcr n (WittVector.teichmuller l (𝒯.c j 0 : 𝒯.A.A))) :=
    congrArg (mapAcr (A'.γ a).asHom.hom n) (hθ j)
  rw [h1, h3]
  exact teich_step 𝒯.A _ n _ _ _ h2

end GlobalTheory.CompanionTheory.ThetaEx
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLine
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

namespace GlobalTheory.CompanionTheory.LineUniv

theorem exists_line : ∀ {C : Type u} [Category.{v} C] (U : UF C) (P : ∀ ⦃T T' : C⦄, (T ⟶ T') → (T' ⟶ T') → Prop), (∀ T : C, ∃ (T₁ : C) (i : T ⟶ T₁) (η : U.U T₁), (∀ (T' : C) (φ : T ⟶ T') (a : U.U T'), ∃! ψ : T₁ ⟶ T', i ≫ ψ = φ ∧ U.map ψ η = a) ∧ ∀ g : T₁ ⟶ T₁, i ≫ g = i → U.map g η = U.q _ * η → P i g) → ∃ L : Line (𝟭 C) U, ∀ T, P (L.i.app T) (L.γ.app T) := by
  intro C _ U P h
  choose T₁ i η hu hP using h
  have hm : ∀ (T T' : C) (φ : T ⟶ T'), ∃ ψ : T₁ T ⟶ T₁ T', i T ≫ ψ = φ ≫ i T' ∧ U.map ψ (η T) = η T' :=
    fun T T' φ => (hu T _ (φ ≫ i T') (η T')).exists
  choose m hm1 hm2 using hm
  have hg : ∀ T, ∃ g : T₁ T ⟶ T₁ T, i T ≫ g = i T ∧ U.map g (η T) = U.q _ * η T :=
    fun T => (hu T _ (i T) _).exists
  choose g hg1 hg2 using hg
  have uniq : ∀ (T T' : C) (φ : T ⟶ T') (a : U.U T') (ψ ψ' : T₁ T ⟶ T'), i T ≫ ψ = φ → U.map ψ (η T) = a →
      i T ≫ ψ' = φ → U.map ψ' (η T) = a → ψ = ψ' :=
    fun T T' φ a ψ ψ' h1 h2 h3 h4 => (hu T T' φ a).unique ⟨h1, h2⟩ ⟨h3, h4⟩
  let Ξ : C ⥤ C :=
    { obj := T₁
      map := fun {T T'} φ => m T T' φ
      map_id := fun T => uniq T _ (i T) (η T) _ _ (by rw [hm1, Category.id_comp]) (hm2 _ _ _)
        (Category.comp_id _) (U.map_id _ _)
      map_comp := fun {T T' T''} φ ψ => uniq T _ (φ ≫ ψ ≫ i T'') (η T'') _ _
        (by rw [hm1, Category.assoc]) (hm2 _ _ _)
        (by rw [← Category.assoc, hm1, Category.assoc, hm1])
        (by rw [U.map_comp, hm2, hm2]) }
  let iN : 𝟭 C ⟶ Ξ :=
    { app := i
      naturality := fun {T T'} φ => (hm1 T T' φ).symm }
  let γN : Ξ ⟶ Ξ :=
    { app := g
      naturality := fun {T T'} φ => uniq T _ (φ ≫ i T') (U.q _ * η T') _ _
        (by
          change i T ≫ m T T' φ ≫ g T' = _
          rw [← Category.assoc, hm1, Category.assoc, hg1])
        (by
          change U.map (m T T' φ ≫ g T') (η T) = _
          rw [U.map_comp, hm2, hg2])
        (by
          change i T ≫ g T ≫ m T T' φ = _
          rw [← Category.assoc, hg1, hm1])
        (by
          change U.map (g T ≫ m T T' φ) (η T) = _
          rw [U.map_comp, hg2, map_mul, hm2, U.map_q]) }
  refine ⟨{ Ξ := Ξ, i := iN, η := η, map_η := fun {T T'} φ => hm2 T T' φ, γ := γN, iγ := ?_, γη := hg2, univ := ?_ }, ?_⟩
  · ext T
    exact hg1 T
  · intro T t φ a
    exact hu T t φ a
  · intro T
    exact hP T (g T) (hg1 T) (hg2 T)

end GlobalTheory.CompanionTheory.LineUniv
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.PropsE
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

theorem CrystallineSemistableComparison.B.P.eps_facts : ∀ {l : ℕ} [Fact l.Prime] (ε : Eps l), D.InWm l ((WittVector.teichmuller l (ε.e 1 : Ob l)) - 1) ∧ (∀ k, ε.qk (k + 1) ^ l = ε.qk k) ∧ (∀ (A : PAlg l) (n : ℕ), A.cris n (∑ i ∈ Finset.range l, ε.qk 1 ^ i) ∈ A.Fil n 1) ∧ ε.μ = (ε.qk 1 - 1) * ∑ i ∈ Finset.range l, ε.qk 1 ^ i ∧ ∀ m, IsPrimitiveRoot (theta0 l (WittVector.teichmuller l (ε.e m : Ob l))) (l ^ m) :=
  @GlobalTheory.CompanionTheory.EpsFacts.eps_facts

theorem CrystallineSemistableComparison.B.P.cont_line : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (ε : Eps l) (k : Bool) (n : ℕ) (ρ : ℕ → ℕ) (hρ : Slow ρ), ∃ L : Line (jE (F.pt κ)) (epsU ε (F.pt κ)), ∀ T, ((flt F κ ε k n ρ hρ).comap (gE F κ k n)).FAcyc (L.i.app T) (L.γ.app T) :=
  @GlobalTheory.CompanionTheory.ContLine.exists_line

theorem CrystallineSemistableComparison.B.P.tower_ex : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F : Fn O} (κ : O →+* OC l) {d : ℕ} (s : F.Small d), Nonempty (Tower κ s) :=
  @GlobalTheory.CompanionTheory.TowerEx.tower_ex

theorem CrystallineSemistableComparison.B.P.tower_act : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F : Fn O} {κ : O →+* OC l} {d : ℕ} {s : F.Small d} (𝒯 : Tower κ s) (ε : Eps l), ∃ A : Act (jE (F.pt κ)) (epsU ε (F.pt κ)) d 𝒯.obj, ∀ (T : (F.pt κ).Elements) (a : Fin d → (epsU ε (F.pt κ)).U T) (φ : 𝒯.obj ⟶ T) (k : Fin d), PAlg.Hom.f (A.act a φ).1 (𝒯.c k 0).val = ((a k).1 : T.1.A) * PAlg.Hom.f φ.1 (𝒯.c k 0).val :=
  @GlobalTheory.CompanionTheory.TowerAct.tower_act

theorem CrystallineSemistableComparison.B.P.theta_ex : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F : Fn O} {κ : O →+* OC l} {d : ℕ} {s : F.Small d} (𝒯 : Tower κ s) (k : Bool) (n : ℕ) (𝓛 : Lift s.a (fun k => (s.T k : s.R)) (bs l k n).R (bs l k n).I (κb κ k n)) (δ : DividedPowers ((bs l k n).I.map 𝓛.i)) (hδ : IsDPMorphism (bs l k n).γ δ 𝓛.i) (hp : (bs l k n).p ≠ 0) (hn : IsNilpotent ((bs l k n).p : (bs l k n).R)) (ε : Eps l) (A : Act (𝟭 _) (thU (Lc F κ k n) (ε.qU n) (ε.qU_mem k n)) d (liftObj s (b := bs l k n) rfl 𝓛 δ hδ hp hn)) (A' : Act (jE (F.pt κ)) (epsU ε (F.pt κ)) d 𝒯.obj), (∀ (T : Thick (Lc F κ k n)) (a : Fin d → (thU (Lc F κ k n) (ε.qU n) (ε.qU_mem k n)).U T) (c : liftObj s (b := bs l k n) rfl 𝓛 δ hδ hp hn ⟶ T) (j : Fin d), (A.act a c).φ (𝓛.t j) = ((a j).1 : T.B) * c.φ (𝓛.t j)) → (∀ (T : (F.pt κ).Elements) (a : Fin d → (epsU ε (F.pt κ)).U T) (φ : 𝒯.obj ⟶ T) (j : Fin d), PAlg.Hom.f (A'.act a φ).1 (𝒯.c j 0).val = ((a j).1 : T.1.A) * PAlg.Hom.f φ.1 (𝒯.c j 0).val) → ∃ θ : liftObj s (b := bs l k n) rfl 𝓛 δ hδ hp hn ⟶ (gE F κ k n).obj 𝒯.obj, (∀ j, θ.φ (𝓛.t j) = 𝒯.A.toAcr n (WittVector.teichmuller l (𝒯.c j 0 : 𝒯.A.A))) ∧ ∀ a, (A.γ a).asHom ≫ θ = θ ≫ (gE F κ k n).map (A'.γ a).asHom :=
  @GlobalTheory.CompanionTheory.ThetaEx.main

theorem CrystallineSemistableComparison.B.P.local_ni : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F : Fn O} {κ : O →+* OC l} {d : ℕ} {s : F.Small d} (𝒯 : Tower κ s) (k : Bool) (n : ℕ) (𝓛 : Lift s.a (fun k => (s.T k : s.R)) (bs l k n).R (bs l k n).I (κb κ k n)) (δ : DividedPowers ((bs l k n).I.map 𝓛.i)) (hδ : IsDPMorphism (bs l k n).γ δ 𝓛.i) (hp : (bs l k n).p ≠ 0) (hn : IsNilpotent ((bs l k n).p : (bs l k n).R)) (ε : Eps l) (ρ : ℕ → ℕ) (hρ : Slow ρ) (γ : Gam d →* End (liftObj s (b := bs l k n) rfl 𝓛 δ hδ hp hn)) (γ' : Gam d →* End 𝒯.obj) (θ : SingleObj.functor γ ⟶ SingleObj.functor γ' ⋙ gE F κ k n), n ≠ 0 → (∀ j, (θ.app (SingleObj.star _)).φ (𝓛.t j) = 𝒯.A.toAcr n (WittVector.teichmuller l (𝒯.c j 0 : 𝒯.A.A))) → (∀ a j, Thick.Hom.φ (γ a).asHom (𝓛.t j) = 𝓛.i (ε.qU n) ^ (Multiplicative.toAdd a j) * 𝓛.t j) → (∀ a j, PAlg.Hom.f (A := 𝒯.A) (B := 𝒯.A) (γ' a).asHom.1 (𝒯.c j 0).val = 𝒯.A.s (ε.e 0) ^ (Multiplicative.toAdd a j) * (𝒯.c j 0).val) → Nonempty (NI (Polynomial.X : Polynomial ℤ) (Functor.whiskerRight θ (flt F κ ε k n ρ hρ).rees)) :=
  @GlobalTheory.CompanionTheory.TowerNI.main

theorem CrystallineSemistableComparison.B.P.desc : ∀ {l : ℕ} [Fact l.Prime], D.Out l → ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (ε : Eps l) (k : Bool) (n : ℕ) (ρ : ℕ → ℕ) (hρ : Slow ρ), (k = false ∨ ρ = 0) → Desc (Polynomial.X : Polynomial ℤ) (gE F κ k n ⋙ (flt F κ ε k n ρ hρ).rees) (jE (F.pt κ)) :=
  @GlobalTheory.CompanionTheory.DescTest.main

theorem CrystallineSemistableComparison.B.P.el_zar : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {d : ℕ} (𝒜 : F.Atlas d) (k : Bool) (n r : ℕ), ZarCov (gT F κ k n ⋙ (pdS (Lc F κ k n) ((base l).cris n) r).fn) fun T => ∃ α, (𝒜.V α).In ((gT F κ k n).obj T).y.1.2 :=
  @GlobalTheory.CompanionTheory.TestZar.zarCov_test

theorem CrystallineSemistableComparison.B.P.el_onto : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {d : ℕ} (𝒜 : F.Atlas d) (S : Set 𝒜.A) (k : Bool) (n : ℕ), n ≠ 0 → Onto (subEl κ (Fn.Sub.inter 𝒜.V S)) fun T => ∀ α ∈ S, (𝒜.V α).In ((gT F κ k n).obj T).y.1.2 :=
  @GlobalTheory.CompanionTheory.ElOnto.onto_subEl
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FGlue
section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FNiCoh
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

namespace CrystallineSemistableComparison.B

section NiCoh

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C]

theorem ni_nat {F F' : C ⥤ ModuleCat.{w} R} (β : F ⟶ F') {T T' : C} (φ : T ⟶ T') (x : F.obj T) :
    (β.app T').hom ((F.map φ).hom x) = (F'.map φ).hom ((β.app T).hom x) := by
  rw [← ModuleCat.comp_apply, β.naturality, ModuleCat.comp_apply]

theorem ni_pull_cls {F F' : C ⥤ ModuleCat.{w} R} (β : F ⟶ F') (n : ℕ) (a : Cn F n) (ha : d F n a = 0) :
    ∃ hb, (Mor.ofNatTrans β).pull n ((cx F).cls a ha) = (cx F').cls (fun s => (β.app _).hom (a s)) hb := by
  have hb : d F' n (fun s => (β.app _).hom (a s)) = 0 :=
    ((Mor.ofNatTrans β).d_pullC n a).trans (by rw [ha, map_zero])
  exact ⟨hb, CrystallineSemistableComparison.P.mapH_cls (Mor.ofNatTrans β).hom n a ha hb⟩

theorem ni_pull_add {F F' : C ⥤ ModuleCat.{w} R} (β β' : F ⟶ F') (n : ℕ) (x : H F n) :
    (Mor.ofNatTrans (β + β')).pull n x = (Mor.ofNatTrans β).pull n x + (Mor.ofNatTrans β').pull n x := by
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx F) n).1 x
  obtain ⟨h1, e1⟩ := ni_pull_cls (β + β') n a ha
  obtain ⟨h2, e2⟩ := ni_pull_cls β n a ha
  obtain ⟨h3, e3⟩ := ni_pull_cls β' n a ha
  rw [e1, e2, e3, ← (CrystallineSemistableComparison.P.cls_surj (cx F') n).2.2.2.1 _ _ h2 h3 (by rw [map_add (f := _), h2, h3, add_zero])]
  congr 1

theorem ni_pull_zero {F F' : C ⥤ ModuleCat.{w} R} (n : ℕ) (x : H F n) :
    (Mor.ofNatTrans (0 : F ⟶ F')).pull n x = 0 := by
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx F) n).1 x
  obtain ⟨h1, e1⟩ := ni_pull_cls (0 : F ⟶ F') n a ha
  rw [e1, (CrystallineSemistableComparison.P.cls_surj (cx F') n).2.1]
  have : (fun s => ((0 : F ⟶ F').app _).hom (a s)) = (0 : Cn F' n) := by
    funext s
    simp only [NatTrans.app_zero, ModuleCat.hom_zero, LinearMap.zero_apply, Pi.zero_apply]
  rw [this]
  exact Submodule.zero_mem _

theorem ni_pull_sum {ι : Type} {F F' : C ⥤ ModuleCat.{w} R} (β : ι → (F ⟶ F')) (S : Finset ι) (n : ℕ) (x : H F n) :
    (Mor.ofNatTrans (∑ k ∈ S, β k)).pull n x = ∑ k ∈ S, (Mor.ofNatTrans (β k)).pull n x := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, ni_pull_zero]
  | insert k S hk ih => rw [Finset.sum_insert hk, Finset.sum_insert hk, ni_pull_add, ih]

theorem ni_pull_comp {F F' F'' : C ⥤ ModuleCat.{w} R} (β : F ⟶ F') (β' : F' ⟶ F'') (n : ℕ) (x : H F n) :
    (Mor.ofNatTrans (β ≫ β')).pull n x = (Mor.ofNatTrans β').pull n ((Mor.ofNatTrans β).pull n x) := by
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx F) n).1 x
  obtain ⟨h1, e1⟩ := ni_pull_cls (β ≫ β') n a ha
  obtain ⟨h2, e2⟩ := ni_pull_cls β n a ha
  obtain ⟨h3, e3⟩ := ni_pull_cls β' n _ h2
  rw [e1, e2, e3]
  rfl

theorem ni_pull_id {F : C ⥤ ModuleCat.{w} R} (n : ℕ) (x : H F n) :
    (Mor.ofNatTrans (𝟙 F)).pull n x = x := by
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx F) n).1 x
  obtain ⟨h1, e1⟩ := ni_pull_cls (𝟙 F) n a ha
  rw [e1]
  rfl

def fixF {F : C ⥤ ModuleCat.{w} R} (e : F ⟶ F) : SubF F where
  S T := LinearMap.ker ((e.app T).hom - LinearMap.id)
  map_mem := fun {_ _} φ {_} hx => by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hx ⊢
    rw [ni_nat, hx]

theorem mem_fixF {F : C ⥤ ModuleCat.{w} R} (e : F ⟶ F) (T : C) (x : F.obj T) :
    x ∈ (fixF e).S T ↔ (e.app T).hom x = x := by
  change x ∈ LinearMap.ker ((e.app T).hom - LinearMap.id) ↔ _
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

def fixP {F : C ⥤ ModuleCat.{w} R} (e : F ⟶ F) (he : e ≫ e = e) : F ⟶ (fixF e).fn where
  app T := ModuleCat.ofHom (LinearMap.codRestrict _ (e.app T).hom fun x => by
    rw [mem_fixF, ← ModuleCat.comp_apply, ← NatTrans.comp_app, he])
  naturality T T' φ := ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext (ni_nat e φ x))

def fixI {F : C ⥤ ModuleCat.{w} R} (S : SubF F) : S.fn ⟶ F where
  app T := ModuleCat.ofHom (S.S T).subtype
  naturality _ _ _ := ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

theorem fixP_fixI {F : C ⥤ ModuleCat.{w} R} (e : F ⟶ F) (he : e ≫ e = e) : fixP e he ≫ fixI (fixF e) = e :=
  NatTrans.ext (funext fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl))

def gNat {d : ℕ} (G : SingleObj (Gam d) ⥤ ModuleCat.{w} R) (g : Gam d) : G ⟶ G where
  app _ := G.map (X := SingleObj.star _) (Y := SingleObj.star _) g
  naturality X Y a := by
    rw [← G.map_comp, ← G.map_comp]
    congr 1
    exact mul_comm (g : Gam d) (a : Gam d)

theorem gNat_pull {d : ℕ} (G : SingleObj (Gam d) ⥤ ModuleCat.{w} R) (g : Gam d) (n : ℕ) (x : H G n) :
    (Mor.ofNatTrans (gNat G g)).pull n x = x := by
  have := CrystallineSemistableComparison.P.prism (Mor.ofNatTrans (gNat G g)) (Mor.id G)
    { app := fun _ => (g : SingleObj.star (Gam d) ⟶ SingleObj.star (Gam d)), naturality := fun _ _ a => mul_comm (g : Gam d) (a : Gam d) }
    (fun T x => rfl) n x
  rw [this]
  exact ((CrystallineSemistableComparison.P.pull_comp (Mor.id G) (Mor.id G) n x).2)

theorem killed_of {d : ℕ} (G : SingleObj (Gam d) ⥤ ModuleCat.{w} R) (g : Gam d) (s : R)
    (hu : ∀ T, UpTo s ((gNat G g - 𝟙 G).app T).hom) (n : ℕ) (z : H G n) : s ^ 2 • z = 0 := by
  obtain ⟨x, hx⟩ := (CrystallineSemistableComparison.P.coef_upTo _ s hu n).2 z
  rw [← hx]
  have e1 := ni_pull_add (gNat G g - 𝟙 G) (𝟙 G) n x
  rw [sub_add_cancel, gNat_pull, ni_pull_id] at e1
  calc _ = ((Mor.ofNatTrans (gNat G g - 𝟙 G)).pull n x + x) - x := (add_sub_cancel_right _ _).symm
    _ = x - x := by rw [← e1]
    _ = 0 := sub_self x

theorem ni_killed {d : ℕ} (s : R) {M N : SingleObj (Gam d) ⥤ ModuleCat.{w} R} (α : M ⟶ N) (h : NI s α) (k : Fin d)
    (n : ℕ) (z : H (fixF (h.π k)).fn n) : s ^ 2 • z = 0 := by
  refine killed_of _ (gen k) s (fun T => ?_) n z
  change UpTo s ((gNat (fixF (h.π k)).fn (gen k) - 𝟙 _).app (SingleObj.star _)).hom
  have hδ : ∀ y : (fixF (h.π k)).fn.obj (SingleObj.star _), ((gNat (fixF (h.π k)).fn (gen k) - 𝟙 _).app (SingleObj.star _)).hom y =
      ((fixF (h.π k)).fn.map (X := SingleObj.star _) (Y := SingleObj.star _) (gen k)).hom y - y := fun y => rfl
  refine ⟨fun y hy => ?_, fun y => ?_⟩
  · rw [hδ, sub_eq_zero] at hy
    have h1 : ((h.π k).app _).hom y.1 = y.1 := (mem_fixF (h.π k) _ y.1).1 y.2
    exact Subtype.ext (h.inj k y.1 h1 (congrArg Subtype.val hy))
  · have h1 : ((h.π k).app _).hom y.1 = y.1 := (mem_fixF (h.π k) _ y.1).1 y.2
    obtain ⟨x, hx, hx2⟩ := h.surj k y.1 h1
    exact ⟨⟨x, (mem_fixF (h.π k) _ x).2 hx⟩, by rw [hδ]; exact Subtype.ext hx2⟩

end NiCoh

end CrystallineSemistableComparison.B

theorem CrystallineSemistableComparison.B.P.ni_coh : ∀ {R : Type} [CommRing R] {d : ℕ} (s : R) {M N : SingleObj (Gam d) ⥤ ModuleCat.{w} R} (α : M ⟶ N), NI s α → ∀ n, IsoLe (s ^ 2) n (Mor.ofNatTrans α) := by
  intro R _ d s M N α h n j _
  refine ⟨fun x hx => ?_, fun y => ?_⟩
  · have e := ni_pull_comp α h.ρ j x
    rw [h.αρ, ni_pull_id, hx, map_zero] at e
    rw [e, smul_zero]
  · refine ⟨(Mor.ofNatTrans h.ρ).pull j (s ^ 2 • y), ?_⟩
    rw [← ni_pull_comp]
    have e := ni_pull_add (h.ρ ≫ α) (∑ k, h.π k) j (s ^ 2 • y)
    rw [h.sum, ni_pull_id, ni_pull_sum] at e
    have hk : ∀ k, (Mor.ofNatTrans (h.π k)).pull j (s ^ 2 • y) = 0 := by
      intro k
      rw [← fixP_fixI (h.π k) (h.idem k), ni_pull_comp, map_smul, ni_killed s α h k, map_zero]
    rw [Finset.sum_eq_zero (fun k _ => hk k), add_zero] at e
    exact e.symm
end

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

namespace CrystallineSemistableComparison.B

lemma gl_res_one {R : Type} [CommRing R] {K : Cx.{w} R} {M : Type w'} [AddCommGroup M] [Module R M]
    (ε : M →ₗ[R] K.X 0) (s : R) (h : K.ResUpTo 1 ε) : K.ResUpTo s ε := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  refine ⟨h0, fun x hx => by rw [← one_smul R x, h1 x hx, smul_zero], fun y hy => ?_, fun m y hy => ?_⟩
  · obtain ⟨x, hx⟩ := h2 y hy
    exact ⟨s • x, by rw [map_smul, hx, one_smul]⟩
  · obtain ⟨x, hx⟩ := h3 m y hy
    exact ⟨s • x, by rw [map_smul, hx, one_smul]⟩

lemma gl_desc_id {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R) (s : R) :
    Desc s F (𝟭 C) := by
  intro T
  have hI : Limits.IsInitial (StructuredArrow.mk (𝟙 T) : StructuredArrow T (𝟭 C)) :=
    StructuredArrow.mkIdInitial (T := 𝟭 C) (Y := T)
  have h := CrystallineSemistableComparison.P.initial (StructuredArrow.proj T (𝟭 C) ⋙ 𝟭 C ⋙ F) _ hI
  have e : (aug (StructuredArrow.proj T (𝟭 C) ⋙ 𝟭 C ⋙ F) fun x =>
      ((StructuredArrow.proj T (𝟭 C) ⋙ 𝟭 C ⋙ F).map (hI.to x)).hom) = unAug F (𝟭 C) T := by
    unfold unAug
    congr 1
    funext x
    have hx : (hI.to x).right = x.hom := by simpa using StructuredArrow.w (hI.to x)
    change (F.map (hI.to x).right).hom = _
    rw [hx]
  rw [← e]
  exact gl_res_one _ s h

end CrystallineSemistableComparison.B

theorem CrystallineSemistableComparison.B.P.glue : ∀ d n : ℕ, ∃ N : ℕ, ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {E : Type u'} [Category.{v'} E] {E₀ : Type u''} [Category.{v''} E₀] (F : C ⥤ ModuleCat.{w} R) (G : E ⥤ C) (j : E₀ ⥤ E) [j.Full] [j.Faithful] (U : UF C) (D : C) (A : Act (𝟭 C) U d D) (L : Line (𝟭 C) U) (U' : UF E) (D' : E) (A' : Act j U' d D') (L' : Line j U') (θ : D ⟶ G.obj D') (h : ∀ a, (A.γ a).asHom ≫ θ = θ ≫ G.map (A'.γ a).asHom) (s : R), (∀ T, Acyc1 s (F.map (L.i.app T)).hom (F.map (L.γ.app T)).hom) → Desc s (G ⋙ F) j → (∀ T, Acyc1 s ((G ⋙ F).map (L'.i.app T)).hom ((G ⋙ F).map (L'.γ.app T)).hom) → NI s (Functor.whiskerRight (⟨fun _ => θ, fun _ _ a => h a⟩ : A.ι ⟶ A'.ι ⋙ G) F) → RI (s ^ N) n F (j ⋙ G) := by
  intro d n
  obtain ⟨N₁, h₁⟩ := CrystallineSemistableComparison.B.P.tors.{w, v, u, v, u} d n
  obtain ⟨N₂, h₂⟩ := CrystallineSemistableComparison.B.P.tors.{w, v', u', v'', u''} d n
  refine ⟨N₂ + (N₁ + 2) + (2 * n + 3), ?_⟩
  intro R _ C _ E _ E₀ _ F G j _ _ U D A L U' D' A' L' θ h s hL hD hL' hN
  let θn : A.ι ⟶ A'.ι ⋙ G := ⟨fun _ => θ, fun _ _ a => h a⟩
  have t1 : RI (s ^ N₁) n F A.ι := h₁ F (𝟭 C) U D A L s (gl_desc_id F s) hL
  have t2 : RI (s ^ N₂) n (G ⋙ F) A'.ι := h₂ (G ⋙ F) j U' D' A' L' s hD hL'
  have t3 : RI (s ^ N₁ * s ^ 2) n F (A'.ι ⋙ G) := by
    intro i hi
    have hp : (Mor.restrict F (A'.ι ⋙ G)).pull i =
        ((Mor.ofNatTrans (Functor.whiskerRight θn F)).pull i).comp ((Mor.restrict F A.ι).pull i) := by
      rw [← rc_pull_comp]
      exact (LinearMap.ext fun x => CrystallineSemistableComparison.P.prism ((Mor.restrict F A.ι).comp (Mor.ofNatTrans (Functor.whiskerRight θn F)))
        (Mor.restrict F (A'.ι ⋙ G)) θn (fun T x => rfl) i x).symm
    rw [hp]
    exact (CrystallineSemistableComparison.P.upTo_alg _ _ _ _).1 (t1 i hi) (P.ni_coh s (Functor.whiskerRight θn F) hN n i hi)
  have t4 : RI (s ^ N₂ * (s ^ N₁ * s ^ 2)) n F G := (P.ri_calc F G A'.ι _ _ n).2.2.1 t2 t3
  have t5 : RI (s ^ (2 * n + 3)) n (G ⋙ F) j := P.fib (Mor.restrict (G ⋙ F) j) s hD n
  have t6 := (P.ri_calc F G j _ _ n).1 t4 t5
  have he : s ^ (N₂ + (N₁ + 2) + (2 * n + 3)) = s ^ N₂ * (s ^ N₁ * s ^ 2) * s ^ (2 * n + 3) := by ring
  rw [he]
  exact t6
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FGlob
section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FChart
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

namespace CrystallineSemistableComparison.B

abbrev ChI (A : Type) : Type := {S : Set A // S.Nonempty}

def chPi {C : Type u} [Category.{v} C] {A : Type} (Q : A → C → Prop)
    (hQ : ∀ α ⦃T T' : C⦄, (T ⟶ T') → Q α T → Q α T') (hA : ∀ T, ∃ α, Q α T) : C ⥤ ChI A where
  obj T := ⟨{α | Q α T}, hA T⟩
  map f := homOfLE (show _ ≤ _ from fun α h => hQ α f h)

def chPhi {C : Type u} [Category.{v} C] {C₁ : Type u'} [Category.{v'} C₁] {A : Type} (P : C ⥤ ChI A)
    (S : ChI A) (ι : C₁ ⥤ C) (hm : ∀ T, S.1 ⊆ (P.obj (ι.obj T)).1) : C₁ ⥤ StructuredArrow S P :=
  Functor.toStructuredArrow ι S P (fun T => homOfLE (show S ≤ _ from hm T)) (fun _ => Subsingleton.elim _ _)

lemma chPhi_equiv {C : Type u} [Category.{v} C] {C₁ : Type u'} [Category.{v'} C₁] {A : Type} (P : C ⥤ ChI A)
    (S : ChI A) (ι : C₁ ⥤ C) (hO : Onto ι (fun T => S.1 ⊆ (P.obj T).1)) :
    (chPhi P S ι hO.mem).IsEquivalence := by
  have := hO.full
  have := hO.faithful
  have : (chPhi P S ι hO.mem).Full :=
    ⟨fun {X Y} f => ⟨ι.preimage f.right, StructuredArrow.hom_ext _ _ (ι.map_preimage f.right)⟩⟩
  have : (chPhi P S ι hO.mem).Faithful :=
    ⟨fun {X Y} f g h => ι.map_injective (congrArg (fun k => CommaMorphism.right k) h)⟩
  have : (chPhi P S ι hO.mem).EssSurj := ⟨fun X => by
    obtain ⟨T₁, ⟨e⟩⟩ := hO.ess X.right (leOfHom X.hom)
    exact ⟨T₁, ⟨StructuredArrow.isoMk e (Subsingleton.elim _ _)⟩⟩⟩
  exact {}

end CrystallineSemistableComparison.B

theorem CrystallineSemistableComparison.B.P.chart : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] (F : C ⥤ ModuleCat.{w} R) (G : C' ⥤ C) {A : Type} (Q : A → C → Prop) (s : R) (n : ℕ), (∀ α ⦃T T' : C⦄, (T ⟶ T') → Q α T → Q α T') → (∀ T, ∃ α, Q α T) → (∀ S : Set A, S.Nonempty → ∃ (C₁ : Type u) (_ : Category.{v} C₁) (C₁' : Type u') (_ : Category.{v'} C₁') (ι : C₁ ⥤ C) (ι' : C₁' ⥤ C') (G₁ : C₁' ⥤ C₁), Onto ι (fun T => ∀ α ∈ S, Q α T) ∧ Onto ι' (fun T => ∀ α ∈ S, Q α (G.obj T)) ∧ Nonempty (G₁ ⋙ ι ≅ ι' ⋙ G) ∧ RI s (n + 1) (ι ⋙ F) G₁) → RI (s ^ (2 * n + 3)) n F G := by
  intro R _ C _ C' _ F G A Q s n hQ hA hS
  let π := chPi Q hQ hA
  have key : ∀ S : ChI A, RI s (n + 1) (StructuredArrow.proj S π ⋙ F) (StructuredArrow.pre S G π) := by
    intro S
    obtain ⟨C₁, _, C₁', _, ι, ι', G₁, hO, hO', ⟨e⟩, hR⟩ := hS S.1 S.2
    have hO2 : Onto ι (fun T => S.1 ⊆ (π.obj T).1) := hO
    have hO2' : Onto ι' (fun T => S.1 ⊆ ((G ⋙ π).obj T).1) := hO'
    let Φ := chPhi π S ι hO2.mem
    let Φ' := chPhi (G ⋙ π) S ι' hO2'.mem
    let X := StructuredArrow.proj S π ⋙ F
    have h1 : RI 1 (n + 1) X Φ := (P.ri_calc X Φ (𝟭 _) 1 1 (n + 1)).2.2.2.2.2.1 (chPhi_equiv π S ι hO2)
    have h2 : RI s (n + 1) (Φ ⋙ X) G₁ := hR
    have h3 : RI (1 * s) (n + 1) X (G₁ ⋙ Φ) := (P.ri_calc X Φ G₁ 1 s (n + 1)).1 h1 h2
    have iso : G₁ ⋙ Φ ≅ Φ' ⋙ StructuredArrow.pre S G π :=
      NatIso.ofComponents (fun T => StructuredArrow.isoMk (e.app T) (Subsingleton.elim _ _))
        (fun f => StructuredArrow.hom_ext _ _ (e.hom.naturality f))
    have h4 : RI (1 * s) (n + 1) X (Φ' ⋙ StructuredArrow.pre S G π) :=
      (P.ri_calc X (G₁ ⋙ Φ) (𝟭 _) (1 * s) 1 (n + 1)).2.2.2.2.1 _ iso h3
    have h5 : RI 1 (n + 1) (StructuredArrow.pre S G π ⋙ X) Φ' :=
      (P.ri_calc (StructuredArrow.pre S G π ⋙ X) Φ' (𝟭 _) 1 1 (n + 1)).2.2.2.2.2.1 (chPhi_equiv (G ⋙ π) S ι' hO2')
    have h6 := (P.ri_calc X (StructuredArrow.pre S G π) Φ' 1 (1 * s) (n + 1)).2.2.1 h5 h4
    rwa [one_mul, one_mul] at h6
  intro j hj
  have h := CrystallineSemistableComparison.P.rel π (Mor.restrict F G) s j (fun S q hq => key S q (by omega))
  have he : s ^ (2 * n + 3) = s ^ (2 * j + 3) * s ^ (2 * (n - j)) := by
    rw [← pow_add]; congr 1; omega
  rw [he]
  exact (CrystallineSemistableComparison.P.upTo_alg _ LinearMap.id _ _).2.2.2.1 h
end

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

namespace CrystallineSemistableComparison.B

lemma gl_onto {D : Type u} [Category.{v} D] {D₁ : Type u'} [Category.{v'} D₁] (Z : ObjectProperty D)
    (κ : D₁ ⥤ D) (hκ : ∀ T, Z (κ.obj T)) (W : D → Prop) (h : Onto κ W) :
    Onto (Z.lift κ hκ) (fun T => W T.obj) := by
  have : κ.Full := h.full
  have : κ.Faithful := h.faithful
  have : (Z.lift κ hκ ⋙ Z.ι).Full := h.full
  have : (Z.lift κ hκ ⋙ Z.ι).Faithful := h.faithful
  refine ⟨Functor.Full.of_comp_faithful _ Z.ι, Functor.Faithful.of_comp _ Z.ι, fun T => h.mem T, ?_⟩
  intro T hT
  obtain ⟨T₁, ⟨f⟩⟩ := h.ess T.obj hT
  exact ⟨T₁, ⟨Z.ι.preimageIso f⟩⟩

end CrystallineSemistableComparison.B

theorem CrystallineSemistableComparison.B.P.glob : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] (F : C ⥤ ModuleCat.{w} R) (G : C' ⥤ C) {A : Type} (Q : A → C → Prop) (s : R) (n : ℕ), (∀ α ⦃T T' : C⦄, (T ⟶ T') → Q α T → Q α T') → RI 1 n F (ObjectProperty.ι fun T => ∃ α, Q α T) → RI 1 n (G ⋙ F) (ObjectProperty.ι fun T => ∃ α, Q α (G.obj T)) → (∀ S : Set A, S.Nonempty → ∃ (C₁ : Type u) (_ : Category.{v} C₁) (C₁' : Type u') (_ : Category.{v'} C₁') (ι : C₁ ⥤ C) (ι' : C₁' ⥤ C') (G₁ : C₁' ⥤ C₁), Onto ι (fun T => ∀ α ∈ S, Q α T) ∧ Onto ι' (fun T => ∀ α ∈ S, Q α (G.obj T)) ∧ Nonempty (G₁ ⋙ ι ≅ ι' ⋙ G) ∧ RI s (n + 1) (ι ⋙ F) G₁) → RI (s ^ (2 * n + 3)) n F G := by
  intro R _ C _ C' _ F G A Q s n hQ hP hP' hS
  let Pr : ObjectProperty C := fun T => ∃ α, Q α T
  let Pr' : ObjectProperty C' := fun T => ∃ α, Q α (G.obj T)
  let Gq : Pr'.FullSubcategory ⥤ Pr.FullSubcategory := Pr.lift (Pr'.ι ⋙ G) (fun T => T.property)
  let Fq : Pr.FullSubcategory ⥤ ModuleCat.{w} R := Pr.ι ⋙ F
  have hc : RI (s ^ (2 * n + 3)) n Fq Gq := by
    refine P.chart Fq Gq (fun α T => Q α T.obj) s n (fun α T T' f h => hQ α f.hom h) (fun T => T.property) ?_
    intro S hSn
    obtain ⟨C₁, _, C₁', _, ι, ι', G₁, hO, hO', ⟨e⟩, hR⟩ := hS S hSn
    obtain ⟨α₀, hα₀⟩ := hSn
    let ιq : C₁ ⥤ Pr.FullSubcategory := Pr.lift ι (fun T => ⟨α₀, hO.mem T α₀ hα₀⟩)
    let ιq' : C₁' ⥤ Pr'.FullSubcategory := Pr'.lift ι' (fun T => ⟨α₀, hO'.mem T α₀ hα₀⟩)
    refine ⟨C₁, inferInstance, C₁', inferInstance, ιq, ιq', G₁, ?_, ?_, ?_, hR⟩
    · exact gl_onto Pr ι _ (fun T => ∀ α ∈ S, Q α T) hO
    · exact gl_onto Pr' ι' _ (fun T => ∀ α ∈ S, Q α (G.obj T)) hO'
    · exact ⟨Functor.fullyFaithfulCancelRight Pr.ι e⟩
  have h1 : RI (1 * s ^ (2 * n + 3)) n F (Gq ⋙ Pr.ι) := (P.ri_calc F Pr.ι Gq 1 _ n).1 hP hc
  have h2 : RI (1 * (1 * s ^ (2 * n + 3))) n F G := (P.ri_calc F G Pr'.ι 1 _ n).2.2.1 hP' h1
  rwa [one_mul, one_mul] at h2
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FReesUp
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

theorem CrystallineSemistableComparison.B.P.rees_up : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {F : C ⥤ ModuleCat.{w} R} (Φ : Flt F) (G : C' ⥤ C) (n : ℕ), ((∀ r, RI 1 n (Φ.S r).fn G) → RI 1 n Φ.rees G) ∧ (∀ μ' ξ : R, Φ.μ = μ' * ξ → (∀ r T x, x ∈ (Φ.S r).S T → ξ • x ∈ (Φ.S (r + 1)).S T) → (∀ r, Desc μ' (Φ.S r).fn G) → Desc (X : ℤ[X]) Φ.rees G) ∧ ∀ {T T' : C} (i : T ⟶ T') (g : T' ⟶ T'), Φ.FAcyc i g → Acyc1 (X : ℤ[X]) (Φ.rees.map i).hom (Φ.rees.map g).hom :=
  @GlobalTheory.CompanionTheory.ReesUp.main
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FLineUniv
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

theorem CrystallineSemistableComparison.B.P.line_univ : ∀ {C : Type u} [Category.{v} C] (U : UF C) (P : ∀ ⦃T T' : C⦄, (T ⟶ T') → (T' ⟶ T') → Prop), (∀ T : C, ∃ (T₁ : C) (i : T ⟶ T₁) (η : U.U T₁), (∀ (T' : C) (φ : T ⟶ T') (a : U.U T'), ∃! ψ : T₁ ⟶ T', i ≫ ψ = φ ∧ U.map ψ η = a) ∧ ∀ g : T₁ ⟶ T₁, i ≫ g = i → U.map g η = U.q _ * η → P i g) → ∃ L : Line (𝟭 C) U, ∀ T, P (L.i.app T) (L.γ.app T) :=
  @GlobalTheory.CompanionTheory.LineUniv.exists_line
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FReesDown
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

theorem CrystallineSemistableComparison.B.P.rees_down : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {F : C ⥤ ModuleCat.{w} R} (Φ : Flt F) (G : C' ⥤ C) (n N : ℕ), (∀ T, (Φ.S 0).S T = ⊤) → RI ((X : ℤ[X]) ^ N) n Φ.rees G → ∀ j ≤ n, InjUpTo (Φ.μ ^ N) ((Mor.restrict F G).pull j) ∧ ∀ y, ∃ x ∈ (Φ.S N).img j, (Mor.restrict F G).pull j x = Φ.μ ^ N • y :=
  @GlobalTheory.CompanionTheory.ReesDown.main
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris

namespace CrystallineSemistableComparison.B

open PAlg CH

theorem exists_dp {Λ D : Type} [CommRing Λ] [CommRing D] (i : Λ →+* D) (h : i.Flat) (I : Ideal Λ) (γ : DividedPowers I) :
    ∃ δ : DividedPowers (I.map i), IsDPMorphism γ δ i := by
  let _ := i.toAlgebra
  have : Module.Flat Λ D := h
  exact GlobalTheory.CompanionTheory.JLiftDP.dpFlat Λ D I γ

variable {l : ℕ} [Fact l.Prime]

theorem local_of (hD : D.Out l) : Local l := by
  intro d j
  obtain ⟨N, hN⟩ := P.glue.{0, 0, 1, 0, 1, 0, 1} d j
  refine ⟨N, fun {O} _ F κ ε k n ρ hρ hn hk s => ?_⟩
  obtain ⟨𝓛⟩ := P.elift s.a (fun k => (s.T k : s.R)) (bs l k n).I (κb κ k n) s.et
  obtain ⟨δ, hδ⟩ := exists_dp 𝓛.i (P.lift_flat 𝓛.i 𝓛.t 𝓛.et).1 (bs l k n).I (bs l k n).γ
  have hp : (bs l k n).p ≠ 0 := (Fact.out : l.Prime).ne_zero
  have hnil : IsNilpotent ((bs l k n).p : (bs l k n).R) := ⟨n, (base l).pow_l_acr n⟩
  obtain ⟨𝒯⟩ := P.tower_ex κ s
  obtain ⟨A, hA⟩ := P.thick_act s (b := bs l k n) rfl 𝓛 δ hδ hp hnil (ε.qU n) (ε.qU_mem k n)
  obtain ⟨A', hA'⟩ := P.tower_act 𝒯 ε
  obtain ⟨θ, hθ, hθγ⟩ := P.theta_ex 𝒯 k n 𝓛 δ hδ hp hnil ε A A' hA hA'
  have hε := P.eps_facts ε
  have hq : (ε.qU n : (bs l k n).R) = (base l).cris n (ε.qk 1) ^ (bs l k n).p :=
    (ε.qU_val n).trans ((congrArg ((base l).cris n) (hε.2.1 0).symm).trans (map_pow _ _ _))
  have hμ : (base l).cris n ε.μ = (ε.qU n : (bs l k n).R) - 1 := by
    change (base l).cris n (ε.qk 0 - 1) = (ε.qU n : (bs l k n).R) - 1
    calc
      _ = (base l).cris n (ε.qk 0) - (base l).cris n 1 := ((base l).cris n).map_sub _ _
      _ = _ := congrArg₂ (· - ·) (ε.qU_val n).symm ((base l).cris n).map_one
  have hξ : (∑ i ∈ Finset.range (bs l k n).p, (base l).cris n (ε.qk 1) ^ i) ∈ (bs l k n).I := by
    have := fil_le k (base l) n (hε.2.2.1 (base l) n)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa only [map_sum, map_pow] using this
  obtain ⟨L, hL⟩ := P.line_univ (thU (Lc F κ k n) (ε.qU n) (ε.qU_mem k n)) (fun _ _ i g => (flt F κ ε k n ρ hρ).FAcyc i g)
    (P.thick_line F (bs l k n) rfl (κb κ k n) ((base l).cris n) ρ hρ ε.μ (ε.μ_mem k (base l) n) (ε.qU n) (ε.qU_mem k n)
      ((base l).cris n (ε.qk 1)) Fact.out hq hμ hξ)
  obtain ⟨L', hL'⟩ := P.cont_line F κ ε k n ρ hρ
  obtain ⟨ni⟩ := P.local_ni 𝒯 k n 𝓛 δ hδ hp hnil ε ρ hρ A.γ A'.γ ⟨fun _ => θ, fun _ _ a => hθγ a⟩ hn hθ
    (fun a j => (hA _ _ (𝟙 _) j).trans (congrArg (· * 𝓛.t j) (Units.val_pow_eq_pow_val _ _)))
    (fun a j => (hA' _ _ (𝟙 _) j).trans (congrArg (· * (𝒯.c j 0).val) (Units.val_pow_eq_pow_val _ _)))
  exact hN (flt F κ ε k n ρ hρ).rees (gE F κ k n) (jE _) _ _ A L _ _ A' L' θ hθγ _
    (fun T => (P.rees_up (flt F κ ε k n ρ hρ) (𝟭 _) 0).2.2 _ _ (hL T)) (P.desc hD F κ ε k n ρ hρ hk)
    (fun T => (P.rees_up ((flt F κ ε k n ρ hρ).comap (gE F κ k n)) (𝟭 _) 0).2.2 _ _ (hL' T)) ni

theorem ri_pow {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C'] {F : C ⥤ ModuleCat.{0} R} {G : C' ⥤ C}
    {s : R} {a b n : ℕ} (h : a ≤ b) (H : RI (s ^ a) n F G) : RI (s ^ b) n F G := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add]
  exact (P.ri_calc F G (𝟭 _) _ _ n).2.2.2.1 H

theorem global_of (h : Local l) (d j : ℕ) : ∃ N : ℕ, ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (ε : Eps l)
    (k : Bool) (n : ℕ) (ρ : ℕ → ℕ) (hρ : Slow ρ), n ≠ 0 → (k = false ∨ ρ = 0) → F.Atlas d →
    RI ((Polynomial.X : Polynomial ℤ) ^ N) j (flt F κ ε k n ρ hρ).rees (gT F κ k n) := by
  choose N hN using fun d' => h d' (j + 1)
  refine ⟨((Finset.range (d + 1)).sup N) * (2 * j + 3), fun {O} _ F κ ε k n ρ hρ hn hk 𝒜 => ?_⟩
  rw [pow_mul]
  have hp : (bs l k n).p ≠ 0 := (Fact.out : l.Prime).ne_zero
  have z₁ := fun r => P.thick_zar F (bs l k n) rfl (κb κ k n) ((base l).cris n) 𝒜 hp r
  have z₂ := fun r => P.el_zar F κ 𝒜 k n r
  have onto : ∀ {C : Type 1} [Category.{0} C] (Q : C → Prop), Onto (ObjectProperty.ι Q) Q := fun Q =>
    ⟨inferInstance, inferInstance, fun T => T.property, fun T hT => ⟨⟨T, hT⟩, ⟨Iso.refl _⟩⟩⟩
  refine P.glob _ (gT F κ k n) (fun α T => (𝒜.V α).In T.y.1.2) _ j ?_ ?_ ?_ fun S hS => ?_
  · intro α T T' φ hT
    have e : F.Pt.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle)) T.y.1.2 = T'.y.1.2 :=
      congrArg (fun z => z.1.2) φ.pt
    exact e ▸ (𝒜.V α).in_map _ hT
  · exact (P.rees_up (flt F κ ε k n ρ hρ) _ j).1 fun r => P.zar _ _ _ (onto _) (z₁ (ρ r)) j
  · exact (P.rees_up ((flt F κ ε k n ρ hρ).comap (gT F κ k n)) _ j).1 fun r => P.zar _ _ _ (onto _) (z₂ (ρ r)) j
  · obtain ⟨d', hd', ⟨s⟩⟩ := 𝒜.small S hS
    refine ⟨_, _, _, _, subThick (Fn.Sub.inter 𝒜.V S) (bs l k n) rfl (κb κ k n), subEl κ (Fn.Sub.inter 𝒜.V S),
      gT (Fn.Sub.inter 𝒜.V S).fn κ k n, P.thick_onto _ _ _ _, P.el_onto F κ 𝒜 S k n hn, ⟨eqToIso (subEl_gT κ _ k n)⟩, ?_⟩
    rw [subThick_rees]
    exact ri_pow (Finset.le_sup (f := N) (Finset.mem_range.2 (Nat.lt_succ_of_le hd'))) (hN d' _ κ ε k n ρ hρ hn hk s)

theorem pull_factor {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C'] {F : C ⥤ ModuleCat.{0} R}
    {F' : C' ⥤ ModuleCat.{0} R} (m : Mor F F' (RingHom.id R)) (h : ∀ T, Function.Bijective (m.τ T)) (j : ℕ) :
    ∃ e : H (m.G ⋙ F) j →ₗ[R] H F' j, Function.Bijective e ∧ ∀ x, m.pull j x = e ((Mor.restrict F m.G).pull j x) := by
  let m' : Mor (m.G ⋙ F) F' (RingHom.id R) := ⟨𝟭 _, m.τ, m.nat⟩
  have : m'.G.IsLeftAdjoint := inferInstanceAs (𝟭 C').IsLeftAdjoint
  exact ⟨m'.pull j, CrystallineSemistableComparison.P.adj_mor m' h j, fun x => (CrystallineSemistableComparison.P.pull_comp (Mor.restrict F m.G) m' j x).1⟩

theorem transfer {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C'] {F : C ⥤ ModuleCat.{0} R}
    {F' : C' ⥤ ModuleCat.{0} R} (m : Mor F F' (RingHom.id R)) (h : ∀ T, Function.Bijective (m.τ T)) (j : ℕ) (s : R)
    (S : Submodule R (H F j)) (H₁ : InjUpTo s ((Mor.restrict F m.G).pull j))
    (H₂ : ∀ y, ∃ x ∈ S, (Mor.restrict F m.G).pull j x = s • y) :
    UpTo s (m.pull j) ∧ ∀ y, ∃ x ∈ S, m.pull j x = s • y := by
  obtain ⟨e, he, hm⟩ := pull_factor m h j
  have h2 : ∀ y, ∃ x ∈ S, m.pull j x = s • y := fun y => by
    obtain ⟨y', rfl⟩ := he.2 y
    obtain ⟨x, hx, e'⟩ := H₂ y'
    exact ⟨x, hx, by rw [hm, e', map_smul]⟩
  refine ⟨⟨fun x hx => H₁ x (he.1 ?_), fun y => (h2 y).imp fun _ hx => hx.2⟩, h2⟩
  rw [← hm, hx, map_zero]

theorem subsingleton_H {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R)
    (h : ∀ T, Subsingleton (F.obj T)) (j : ℕ) : Subsingleton (H F j) := by
  have : Subsingleton (Cn F j) := ⟨fun _ _ => funext fun _ => (h _).elim _ _⟩
  exact Submodule.Quotient.mk_surjective _ |>.subsingleton

theorem acr_zero (A : PAlg l) : Subsingleton (A.Acr 0) := subsingleton_of_zero_eq_one (by simpa using (A.pow_l_acr 0).symm)

theorem upTo_zero {R M N : Type _} [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] (h₁ : Subsingleton M)
    (h₂ : Subsingleton N) (f : M →ₗ[R] N) (s : R) (S : Submodule R M) : UpTo s f ∧ ∀ y, ∃ x ∈ S, f x = s • y :=
  ⟨⟨fun _ _ => h₁.elim _ _, fun _ => ⟨0, h₂.elim _ _⟩⟩, fun _ => ⟨0, zero_mem _, h₂.elim _ _⟩⟩

theorem om_zero {b : Base} (L : b.Fun) {Λ : Type} [CommRing Λ] (c : Λ →+* b.R) (h : Subsingleton b.R) (j : ℕ) :
    Subsingleton (H (OM L c) j) :=
  subsingleton_H _ (fun T => (show Subsingleton T.B from T.i.codomain_trivial)) j

theorem pdFlt_zero {b : Base} (L : b.Fun) {Λ : Type} [CommRing Λ] (c : Λ →+* b.R) (ρ : ℕ → ℕ) (hρ : Slow ρ) (μ : Λ)
    (hμ : c μ ∈ b.I) (T : Thick L) : ((pdFlt L c ρ hρ μ hμ).S 0).S T = ⊤ := eq_top_iff.2 fun x _ => by
  change (show T.B from x) ∈ T.pdPow (ρ 0)
  rw [hρ.1, T.pdPow_zero]; trivial

theorem level_zero {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) (j : ℕ) (s : Acris l)
    (S : Submodule (Acris l) (Hc F κ k 0 j)) : UpTo s (β F κ k 0 j) ∧ ∀ y, ∃ x ∈ S, β F κ k 0 j x = s • y :=
  upTo_zero (om_zero (Lc F κ k 0) ((base l).cris 0) (acr_zero (base l)) j)
    (subsingleton_H (modF (AcrEl (F.pt κ) 0)) (fun T => acr_zero T.1.obj) j) (β F κ k 0 j) s S

theorem level_pos {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (ε : Eps l) (k : Bool) (n j N : ℕ) (ρ : ℕ → ℕ) (hρ : Slow ρ)
    (h : RI ((Polynomial.X : Polynomial ℤ) ^ N) j (flt F κ ε k n ρ hρ).rees (gT F κ k n)) :
    UpTo (ε.μ ^ N) (β F κ k n j) ∧ ∀ y, ∃ x ∈ HcFil F κ k n (ρ N) j, β F κ k n j x = ε.μ ^ N • y :=
  have H := P.rees_down (flt F κ ε k n ρ hρ) (gT F κ k n) j N (pdFlt_zero _ _ ρ hρ _ _) h j le_rfl
  transfer (βMor F κ k n) (fun _ => Function.bijective_id) j (ε.μ ^ N) (HcFil F κ k n (ρ N) j) H.1 H.2

theorem slow_zero : Slow 0 := ⟨rfl, fun _ => Nat.zero_le _⟩

theorem slow_id : Slow id := ⟨rfl, fun _ => le_rfl⟩

theorem level_all {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (ε : Eps l) (k : Bool) (n j N : ℕ) (ρ : ℕ → ℕ) (hρ : Slow ρ)
    (h : n ≠ 0 → RI ((Polynomial.X : Polynomial ℤ) ^ N) j (flt F κ ε k n ρ hρ).rees (gT F κ k n)) :
    UpTo (ε.μ ^ N) (β F κ k n j) ∧ ∀ y, ∃ x ∈ HcFil F κ k n (ρ N) j, β F κ k n j x = ε.μ ^ N • y :=
  match n, h with
  | 0, _ => level_zero F κ k j _ _
  | n + 1, h => level_pos F κ ε k (n + 1) j N ρ hρ (h n.succ_ne_zero)

theorem main_of (hD : D.Out l) : Main l := fun d j =>
  (global_of (local_of hD) d j).imp fun N hN {_} _ F κ ε 𝒜 n =>
    ⟨fun k => (level_all F κ ε k n j N 0 slow_zero fun hn => hN F κ ε k n 0 slow_zero hn (Or.inr rfl) 𝒜).1,
      (level_all F κ ε false n j N id slow_id fun hn => hN F κ ε false n id slow_id hn (Or.inl rfl) 𝒜).2⟩

end CrystallineSemistableComparison.B

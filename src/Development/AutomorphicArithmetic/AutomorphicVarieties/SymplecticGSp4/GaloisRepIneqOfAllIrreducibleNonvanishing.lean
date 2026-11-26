module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.QuotientSaturatedSquareTorsionFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ExistsLiftOfDerivationOnIdeal

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.TorusConjugateCornerEntryEq
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem linked_iff_torus_conjugate {H K : Type} [Group H] [Field K] {r r' : H →* M4 K} {t : Kˣ × Kˣ}
    (h : ∀ g, r g = tconj t (r' g)) (i j : Fin 4) : Ge r i j ↔ Ge r' i j := by
  unfold Ge
  refine exists_congr fun g => ?_
  rw [h g]
  simp [tconj]

private theorem torus_conjugate_corner_entry_eq {H K : Type} [Group H] [Field K] {r r' : H →* M4 K} {t : Kˣ × Kˣ}
    (h : ∀ g, r g = tconj t (r' g)) (g : H) : r g 0 0 = r' g 0 0 := by
  rw [h g]
  simp [tconj, wv, wt]

private theorem diagonal_type_corner_cases {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (D : Raw Ω c) (hD : D.Good) (M : Model D) [GradedAlgebra M.gr] (hS : SoV Ω l) (hF : D.Fin0)
    (ξ : M.SS →ₐ[c.O] PadicAlgCl l) (hd : DiagType (M.rep ξ)) :
    (M.rep ξ D.s0 0 0 = ((D.th D.s0 : c.O) : PadicAlgCl l) ∧ NegZero M.gr (ξ.comp M.toSS)) ∨
    (M.rep ξ D.s0 0 0 = ((D.al D.s0 : c.O) : PadicAlgCl l) ∧ PosZero M.gr (ξ.comp M.toSS)) := by
  obtain ⟨t, r, hr, h⟩ := ptScale D hD M hF ξ
  obtain ⟨s1, s2, -⟩ := signs D hD M hF ξ
  have hd' : DiagType r := fun i j hij a b => hd i j hij ((linked_iff_torus_conjugate h i j).1 a) ((linked_iff_torus_conjugate h j i).1 b)
  have hs : (D.s0 : G ℚ Ω) ∈ D.Ip l := hD.decompSigma_mem.1.1
  rcases diagCases D hD hS r hr hd' with ⟨a, b⟩ | ⟨a, b⟩
  · exact Or.inl ⟨(torus_conjugate_corner_entry_eq h _).symm.trans (a _ hs), s1 fun i j hij e => b i j hij ((linked_iff_torus_conjugate h i j).2 e)⟩
  · exact Or.inr ⟨(torus_conjugate_corner_entry_eq h _).symm.trans (a _ hs), s2 fun i j hij e => b i j hij ((linked_iff_torus_conjugate h i j).2 e)⟩

theorem UpperTheory.V.GradeZeroInterpolatingElement.m3 :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, ∀ [GradedAlgebra M.gr], Loc.LocalPublishedTheorems → SoV Ω l → D.Fin0 → M3 M.gr (PadicAlgCl l) M.x0 M.eqns.ideal := by
  intro Ω _ _ _ l _ c D hD M _ hL hS hF x₁ h1 hn hp _
  obtain ⟨ξ₁, rfl⟩ := ptLift D hD M x₁ h1
  obtain ⟨t, r, hr, h⟩ := ptScale D hD M hF ξ₁
  obtain ⟨-, -, s3, -, s5⟩ := signs D hD M hF ξ₁
  have n02 : ¬ Ge r 0 2 := fun e => s3 hp ((linked_iff_torus_conjugate h 0 2).1 e)
  have hd : DiagType (M.rep ξ₁) := by
    rcases tri D hD hL r hr with a | a | a
    · obtain ⟨p1, -, -, -, -, p6, -⟩ := ptIn D hD _ r hr
      exact absurd ((geAlg _ r _ p1 p6).2.2.2.2.1.1 a 0 2) n02
    · exact fun i j hij u v => a i j hij ((linked_iff_torus_conjugate h i j).2 u) ((linked_iff_torus_conjugate h j i).2 v)
    · exact absurd a.1 n02
  have hne : ((D.th D.s0 : c.O) : PadicAlgCl l) ≠ ((D.al D.s0 : c.O) : PadicAlgCl l) := fun e => by
    have hinj := (facts D hD).2.2.2.2.2.2.1
    have : (0 : Fin 4) = 2 := hinj (Subtype.ext e)
    exact absurd this (by decide)
  have key : ∀ x : M.A →ₐ[c.O] PadicAlgCl l, OnS M.eqns.ideal x → Same0 M.gr x (ξ₁.comp M.toSS) →
      (M.rep ξ₁ D.s0 0 0 = ((D.th D.s0 : c.O) : PadicAlgCl l) ∧ NegZero M.gr x) ∨
      (M.rep ξ₁ D.s0 0 0 = ((D.al D.s0 : c.O) : PadicAlgCl l) ∧ PosZero M.gr x) := by
    intro x hx h0
    obtain ⟨ξ, rfl⟩ := ptLift D hD M x hx
    obtain ⟨q1, q2⟩ := s5 ξ fun b hb => (h0 b hb).symm
    rw [q1]
    exact diagonal_type_corner_cases D hD M hS hF ξ (q2 hd)
  rcases diagonal_type_corner_cases D hD M hS hF ξ₁ hd with ⟨a, -⟩ | ⟨a, -⟩
  · refine Or.inr ?_
    rintro ⟨x, hx, -, hnn, h0⟩
    rcases key x hx h0 with ⟨-, b⟩ | ⟨b, -⟩
    · exact hnn b
    · exact hne (a.symm.trans b)
  · refine Or.inl ?_
    rintro ⟨x, hx, -, hnn, h0⟩
    rcases key x hx h0 with ⟨b, -⟩ | ⟨-, b⟩
    · exact hne (b.symm.trans a)
    · exact hnn b
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MPrime
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.GradeZeroInterpolatingElement

private theorem der_zero {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]
    {Γ ι : Type} [Group Γ] [TopologicalSpace Γ] [Fintype ι] [DecidableEq ι] {rbar : Γ →* Matrix ι ι (ResidueField O)}
    {R S : Type} [CommRing R] [Algebra O R] [CommRing S] [Algebra O S] [IsCO O S] (π : R →ₐ[O] S)
    (hπ : Function.Surjective π) (r : Lift O rbar S) (hr : r.Generates) (x : R →ₐ[O] O) (hx : ∀ f, π f = 0 → x f = 0)
    (I : Ideal O) (d : R →ₗ[O] O) (hd : d ∈ PtDer x O) (h0 : ∀ f, π f = 0 → d f ∈ I)
    (h1 : ∀ g i j, ∃ f, π f = r.hom g i j ∧ d f ∈ I) (f : R) : d f ∈ I := by
  haveI : IsCO O (TrivSqZeroExt O (O ⧸ I)) := co_sqz O O _ fun _ => rfl
  have hd' : I.mkQ ∘ₗ d ∈ PtDer x (O ⧸ I) := fun f g => by
    have := hd f g
    simp only [LinearMap.comp_apply, this, map_add (f := _), map_smul]
  obtain ⟨y, hy⟩ := (der_hom O R O (O ⧸ I) x _).1 ⟨_, hd', rfl⟩
  obtain ⟨y', hy'⟩ := (der_hom O R O (O ⧸ I) x _).1 ⟨_, (PtDer x (O ⧸ I)).zero_mem, rfl⟩
  have key : ∀ f, d f ∈ I ↔ y f = y' f := fun f => by
    rw [TrivSqZeroExt.ext_iff, (hy f).1, (hy f).2, (hy' f).1, (hy' f).2]
    simp only [true_and, LinearMap.comp_apply, LinearMap.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  have k' : ∀ f, π f = 0 → y' f = 0 := fun f hf => TrivSqZeroExt.ext (by rw [(hy' f).1, hx f hf]; rfl) (by rw [(hy' f).2]; rfl)
  have k : ∀ f, π f = 0 → y f = 0 := fun f hf => ((key f).1 (h0 f hf)).trans (k' f hf)
  let e := (Ideal.quotientKerAlgEquivOfSurjective hπ).symm
  have he : ∀ f, e (π f) = Ideal.Quotient.mk _ f := fun f => by
    simp only [e]; rw [AlgEquiv.symm_apply_eq]; rfl
  let u : S →ₐ[O] TrivSqZeroExt O (O ⧸ I) := (Ideal.Quotient.liftₐ (RingHom.ker π) y k).comp e.toAlgHom
  let u' : S →ₐ[O] TrivSqZeroExt O (O ⧸ I) := (Ideal.Quotient.liftₐ (RingHom.ker π) y' k').comp e.toAlgHom
  have hu : ∀ f, u (π f) = y f := fun f => by
    show Ideal.Quotient.liftₐ (RingHom.ker π) y k (e (π f)) = _
    rw [he]; rfl
  have hu' : ∀ f, u' (π f) = y' f := fun f => by
    show Ideal.Quotient.liftₐ (RingHom.ker π) y' k' (e (π f)) = _
    rw [he]; rfl
  have huu : u = u' := hr _ u u' (Lift.ext (MonoidHom.ext fun g => Matrix.ext fun i j => by
    obtain ⟨f, hf, hf'⟩ := h1 g i j
    rw [Lift.map_hom, Lift.map_hom, ← hf, hu, hu', (key f).1 hf']))
  rw [key, ← hu, ← hu', huu]

private theorem wt_eq_neg (i j : Fin 4) : wt i j = -wPs → (i = 2 ∧ j = 0) ∨ (i = 3 ∧ j = 1) := by revert i j; decide

private theorem origin_part {O X R : Type} [CommRing O] [AddCommGroup X] [CommRing R] [Algebra O R] (W : WPres O X R)
    (h : W.HasOrigin) {j : X} (hj : j ≠ 0) {f : R} (hf : f ∈ W.part j) : W.origin h f = 0 := by
  obtain ⟨p, hp, rfl⟩ := hf
  have := hp 0 (by rw [map_zero]; exact hj.symm)
  rw [AlgHom.toLinearMap_apply, WPres.origin_π]
  simpa using this

private theorem len_le (hM : LemmaM') {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]
    {Γ : Type} [Group Γ] [TopologicalSpace Γ] {rbar : Γ →* M4 (ResidueField O)}
    {R S : Type} [CommRing R] [Algebra O R] [CommRing S] [Algebra O S] [IsCO O S] (π : R →ₐ[O] S)
    (hπ : Function.Surjective π) (r : Lift O rbar S) (hr : r.Generates) (x : R →ₐ[O] O) (hx : ∀ f, π f = 0 → x f = 0)
    (P : ℤ × ℤ → Submodule O R) (hom : ∀ g i j, ∃ f ∈ P (wt i j), π f = r.hom g i j)
    (A : Subalgebra O R) (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] (hA : ∀ n (f : A), f ∈ 𝒜 n ↔ f.1 ∈ P (0, n))
    (hA' : ∀ n f, f ∈ P (0, n) → f ∈ A) (hx1 : ∀ f ∈ P (0, -1), x f = 0)
    {ι : Type} (F : ι → A) (hF : ∀ i, F i ∈ 𝒜 (-1)) (hF0 : ∀ i, π (F i) = 0)
    (a : O) (ha : a ≠ 0) (N : Type) [AddCommGroup N] [Module O N] (Z : N →+ (Γ → O ⧸ Ideal.span {a}))
    (hZ : Function.Injective Z) (s t : Γ → Oˣ)
    (der : ∀ μ, ∃ δ ∈ PtDer x O, HasWt P (-wPs) δ ∧ (∀ f, π f = 0 → δ f ∈ Ideal.span {a}) ∧
      ∀ g f, (π f = r.hom g 2 0 → Ideal.Quotient.mk _ (δ f) = Ideal.Quotient.mk _ (s g : O) * Z μ g) ∧
        (π f = r.hom g 3 1 → Ideal.Quotient.mk _ (δ f) = Ideal.Quotient.mk _ (t g : O) * Z μ g)) :
    Module.length O N ≤ cotLen (x.comp A.val) 𝒜 (-1) F := by
  choose δ h1 h2 h3 h4 using der
  have hadd : ∀ μ ν f, Ideal.Quotient.mk (Ideal.span {a}) (δ (μ + ν) f) =
      Ideal.Quotient.mk _ (δ μ f) + Ideal.Quotient.mk _ (δ ν f) := fun μ ν f => by
    rw [← map_add (f := _), Ideal.Quotient.eq]
    refine der_zero π hπ r hr x hx (Ideal.span {a}) (δ (μ + ν) - (δ μ + δ ν))
      (sub_mem (h1 _) (add_mem (h1 _) (h1 _)))
      (fun f hf => sub_mem (h3 _ f hf) (add_mem (h3 _ f hf) (h3 _ f hf))) (fun g i j => ?_) f
    obtain ⟨f, hf, hf'⟩ := hom g i j
    refine ⟨f, hf', ?_⟩
    show δ (μ + ν) f - (δ μ f + δ ν f) ∈ _
    by_cases hw : wt i j = -wPs
    · rw [← Ideal.Quotient.eq, map_add (f := _)]
      rcases wt_eq_neg i j hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [(h4 _ g f).1 hf', (h4 _ g f).1 hf', (h4 _ g f).1 hf', map_add (f := _), Pi.add_apply, mul_add]
      · rw [(h4 _ g f).2 hf', (h4 _ g f).2 hf', (h4 _ g f).2 hf', map_add (f := _), Pi.add_apply, mul_add]
    · rw [h2 _ _ hw f hf, h2 _ _ hw f hf, h2 _ _ hw f hf]; simp
  let Dm : N →+ (A →ₗ[O] O ⧸ Ideal.span {a}) :=
    AddMonoidHom.mk' (fun μ => (Ideal.span {a}).mkQ ∘ₗ δ μ ∘ₗ A.val.toLinearMap) fun μ ν =>
      LinearMap.ext fun f => hadd μ ν f
  have hDm : ∀ μ (f : A), Dm μ f = Ideal.Quotient.mk _ (δ μ f) := fun _ _ => rfl
  refine hM O A ℤ 𝒜 (x.comp A.val) (-1) (fun f hf => hx1 _ ((hA _ f).1 hf)) ι F hF a ha N Dm ?_ (fun μ i => ?_)
    fun μ => ⟨δ μ ∘ₗ A.val.toLinearMap, fun f g => h1 μ f g, fun n hn f hf => ?_, fun f => rfl⟩
  · refine (injective_iff_map_eq_zero Dm).2 fun μ hμ => hZ ?_
    rw [map_zero]
    funext g
    obtain ⟨f, hf, hf'⟩ := hom g 2 0
    have e1 := hDm μ ⟨f, hA' (-1) f (by rwa [show wt 2 0 = (0, -1) by decide] at hf)⟩
    rw [hμ, LinearMap.zero_apply, (h4 μ g f).1 hf'] at e1
    exact ((s g).isUnit.map (Ideal.Quotient.mk (Ideal.span {a}))).mul_right_eq_zero.1 e1.symm
  · rw [hDm, Ideal.Quotient.eq_zero_iff_mem]
    exact h3 μ _ (hF0 i)
  · exact h2 μ (0, n) (fun h => hn (congrArg Prod.snd h)) _ ((hA n f).1 hf)

end UpperTheory.V.GradeZeroInterpolatingElement

theorem UpperTheory.V.GradeZeroInterpolatingElement.mPrime :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, ∀ [GradedAlgebra M.gr], LemmaM' → SoFin Ω l → D.sha ≤ cotLen M.x0 M.gr (-1) M.eqns.F := by
  intro Ω _ _ _ l _ c D hD M _ hM hS
  obtain ⟨-, a, ha, Z, hZ, hc⟩ := shaCoc D hD hS
  haveI : Finite (ResidueField c.O) := by
    obtain ⟨-, -, h, -⟩ := dvrFacts l c.O
    haveI : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ PadicInt.residueField.symm.toEquiv
    exact IsLocalRing.ResidueField.finite_of_finite ‹_›
  have hx : ∀ f, M.π f = 0 → M.W.origin M.org f = 0 := fun f hf => by
    obtain ⟨e, -, he⟩ := M.hom 1 0 0
    have h1 := M.at0 1 0 0 (f + e) (by rw [map_add (f := _), hf, he, zero_add])
    rw [map_add (f := _), M.at0 1 0 0 e he] at h1
    exact add_eq_right.1 h1
  set_option synthInstance.maxHeartbeats 200000 in
   exact len_le hM M.π M.surj M.ru M.gen (M.W.origin M.org) hx M.W.part M.hom M.A M.gr (fun _ _ => Iff.rfl)
    (fun n f hf => M.aPart_le hf) (fun f hf => origin_part M.W M.org (by decide) hf) M.eqns.F M.eqns.hF
    (fun i => by
      show M.F i ∈ RingHom.ker M.π
      rw [M.ker]
      exact Ideal.subset_span (Or.inl (Or.inl ⟨i, rfl⟩)))
    a ha _ Z hZ D.th D.Psi fun μ => M.der a (Z μ) ha (hc μ)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.FgMapMk
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem fg_map_mk {O A S : Type} [CommRing O] [IsNoetherianRing O] [CommRing A] [Algebra O A] [CommRing S]
    [Algebra O S] (f : A →ₐ[O] S) (I : Ideal A) (hI : ∀ a, f a = 0 ↔ a ∈ I) (P : Submodule O A) (T : Submodule O S)
    (hT : T.FG) (hP : ∀ a ∈ P, f a ∈ T) : (P.map (Ideal.Quotient.mkₐ O I).toLinearMap).FG := by
  have hIf : ∀ a ∈ I, f a = 0 := fun a ha => (hI a).mpr ha
  let g : A ⧸ I →ₐ[O] S := Ideal.Quotient.liftₐ I f hIf
  have hg : Function.Injective g := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact (hI a).mp hy
  haveI : IsNoetherian O T := isNoetherian_of_fg_of_noetherian T hT
  have hle : (P.map (Ideal.Quotient.mkₐ O I).toLinearMap).map g.toLinearMap ≤ T := by
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact hP a ha
  exact Submodule.fg_of_fg_map_injective g.toLinearMap hg (isNoetherian_submodule.mp inferInstance _ hle)

theorem UpperTheory.V.GradeZeroInterpolatingElement.m2 :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, ∀ [GradedAlgebra M.gr], D.Fin0 → M2 M.gr M.eqns.ideal := by
  intro Ω _ _ _ l _ c D hD M _ hF
  obtain ⟨h1, -, h3⟩ := kerA D hD M
  have hs := spanMono D hD M hF 0
  have hfin := hF M.S M.ru M.pt
  have hT : (Subalgebra.toSubmodule (Algebra.adjoin c.O (mono M.ru.hom 0))).FG :=
    Module.Finite.iff_fg.1 hfin
  refine fg_map_mk (M.SS.val.comp M.toSS) _ (fun a => ?_) _ _ hT (fun a ha => ?_)
  · rw [← h1 a]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  · have h4 : (M.toSS a).1 ∈ M.sPart 0 := h3 0 a ha
    rw [hs] at h4
    exact Algebra.span_le_adjoin _ _ h4
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.AGraded
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem wcomp_self_eq_of_mem_wtPart {O σ X : Type} [CommRing O] [AddCommGroup X] {wt : σ → X} {j : X}
    {f : MvPowerSeries σ O} (hf : f ∈ wtPart O wt j) : wcomp O wt j f = f := by
  have hf' : ∀ n, Finsupp.weight wt n ≠ j → MvPowerSeries.coeff n f = 0 := hf
  ext n
  rw [coeff_wcomp]
  by_cases h1 : Finsupp.weight wt n = j
  · rw [if_pos h1]
  · rw [if_neg h1]
    exact (hf' n h1).symm

private theorem wcomp_eq_zero_of_mem_wtPart_of_ne {O σ X : Type} [CommRing O] [AddCommGroup X] {wt : σ → X} {j : X}
    {f : MvPowerSeries σ O} (hf : f ∈ wtPart O wt j) {j' : X} (hj : j' ≠ j) : wcomp O wt j' f = 0 := by
  have hf' : ∀ n, Finsupp.weight wt n ≠ j → MvPowerSeries.coeff n f = 0 := hf
  ext n
  rw [coeff_wcomp, map_zero]
  by_cases h1 : Finsupp.weight wt n = j'
  · rw [if_pos h1]
    exact hf' n (by rw [h1]; exact hj)
  · rw [if_neg h1]

private theorem aGraded_internal {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]
    {c : Coef l} {D : Raw Ω c} (M : Model D) : DirectSum.IsInternal M.gr := by
  set_option synthInstance.maxHeartbeats 200000 in
    have key : ∀ (n : ℤ) (x : M.R), x ∈ M.aPart n → x ∈ (⨆ (m : ℤ) (_ : m ≠ n), M.aPart m) → x = 0 := by
      intro n x hx hx'
      have hle : (⨆ (m : ℤ) (_ : m ≠ n), M.aPart m) ≤
          Submodule.map M.W.π.toLinearMap
            (LinearMap.ker (M.W.π.toLinearMap ∘ₗ wcomp c.O M.W.wt ((0 : ℤ), n))) := by
        refine iSup₂_le fun m hm => ?_
        rintro y ⟨h, hh, rfl⟩
        refine ⟨h, ?_, rfl⟩
        change M.W.π (wcomp c.O M.W.wt ((0 : ℤ), n) h) = 0
        rw [wcomp_eq_zero_of_mem_wtPart_of_ne hh, map_zero]
        intro h'
        exact hm (Prod.ext_iff.mp h').2.symm
      obtain ⟨g, hg, hgx⟩ := hle hx'
      obtain ⟨f, hf, rfl⟩ := hx
      have hker : f - g ∈ RingHom.ker M.W.π := by
        rw [RingHom.mem_ker, map_sub]
        exact sub_eq_zero.mpr hgx.symm
      have h2 := M.W.homog _ hker ((0 : ℤ), n)
      rw [RingHom.mem_ker, map_sub, map_sub] at h2
      have hg' : M.W.π (wcomp c.O M.W.wt ((0 : ℤ), n) g) = 0 := hg
      have h3 : M.W.π (wcomp c.O M.W.wt ((0 : ℤ), n) f) = M.W.π f := by
        rw [wcomp_self_eq_of_mem_wtPart hf]
      change M.W.π f = 0
      calc M.W.π f = M.W.π (wcomp c.O M.W.wt ((0 : ℤ), n) f) := h3.symm
        _ = M.W.π (wcomp c.O M.W.wt ((0 : ℤ), n) g) := sub_eq_zero.mp h2
        _ = 0 := hg'
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    constructor
    · rw [iSupIndep_def]
      intro n
      rw [Submodule.disjoint_def]
      intro x hx hx'
      have h1 : (x : M.R) ∈ M.aPart n := hx
      have h2 : (x : M.R) ∈ (⨆ (m : ℤ) (_ : m ≠ n), M.aPart m) := by
        have := Submodule.mem_map_of_mem (f := M.A.val.toLinearMap) hx'
        simp only [Submodule.map_iSup] at this
        exact (iSup₂_mono fun m _ => Submodule.map_comap_le _ _) this
      exact Subtype.ext (key n _ h1 h2)
    · refine eq_top_iff.mpr fun x _ => ?_
      obtain ⟨y, hy⟩ := x
      have main : ∀ (z : M.R) (hz : z ∈ ⨆ n, M.aPart n), (⟨z, hz⟩ : M.A) ∈ ⨆ n, M.gr n := by
        intro z hz
        refine Submodule.iSup_induction' M.aPart
          (motive := fun z hz => (⟨z, hz⟩ : M.A) ∈ ⨆ n, M.gr n) ?_ ?_ ?_ hz
        · intro n w hw
          exact Submodule.mem_iSup_of_mem n hw
        · exact zero_mem _
        · intro a b ha hb iha ihb
          exact add_mem iha ihb
      exact main y hy

theorem UpperTheory.V.GradeZeroInterpolatingElement.aGraded :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, Nonempty (GradedAlgebra M.gr) := by
  intro Ω _ _ _ l _ c D _ M
  exact ⟨{ (inferInstance : SetLike.GradedMonoid M.gr), (aGraded_internal M).chooseDecomposition with }⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Nval
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

theorem UpperTheory.V.GradeZeroInterpolatingElement.nval :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l), IsNVal c.O (PadicAlgCl l) fun x => -Real.log ‖x‖ * ((eO l c.O).toNat : ℝ) / Real.log l := by
  intro l _ c
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hL : 0 < Real.log l := Real.log_pos hl
  have he : (0 : ℝ) ≤ ((eO l c.O).toNat : ℝ) := Nat.cast_nonneg _
  have anti : ∀ a b : PadicAlgCl l, a ≠ 0 → ‖a‖ ≤ ‖b‖ →
      -Real.log ‖b‖ * ((eO l c.O).toNat : ℝ) / Real.log l ≤
        -Real.log ‖a‖ * ((eO l c.O).toNat : ℝ) / Real.log l := by
    intro a b ha hab
    have hlog : Real.log ‖a‖ ≤ Real.log ‖b‖ := Real.log_le_log (norm_pos_iff.mpr ha) hab
    apply div_le_div_of_nonneg_right _ hL.le
    exact mul_le_mul_of_nonneg_right (by linarith) he
  refine ⟨?_, ?_, ?_⟩
  · intro x y hx hy
    rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hx) (norm_ne_zero_iff.mpr hy)]
    ring
  · intro x y hx hy hxy
    have h := IsUltrametricDist.norm_add_le_max x y
    rcases le_total ‖x‖ ‖y‖ with h1 | h1
    · rw [max_eq_right h1] at h
      exact (min_le_right _ _).trans (anti _ _ hxy h)
    · rw [max_eq_left h1] at h
      exact (min_le_left _ _).trans (anti _ _ hxy h)
  · intro a ha
    have h := normO l c.O a ha
    have h2 := congrArg Real.log h
    rw [Real.log_pow, Real.log_pow, Real.log_inv] at h2
    show -Real.log ‖(a : PadicAlgCl l)‖ * ((eO l c.O).toNat : ℝ) / Real.log l = _
    field_simp
    linarith
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.WeightAlgebraGeneratedDegreeTwo
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem aW_comb {σ : Type} [Fintype σ] (lam : σ → ℤ) (hl : ∀ s, lam s = -1 ∨ lam s = 0 ∨ lam s = 1)
    (P : (σ →₀ ℕ) → Prop) (h0 : P 0) (hadd : ∀ a b, P a → P b → P (a + b))
    (h1 : ∀ s, lam s = 0 → P (Finsupp.single s 1))
    (h2 : ∀ s t, lam s = 1 → lam t = -1 → P (Finsupp.single s 1 + Finsupp.single t 1)) :
    ∀ m, Finsupp.weight lam m = 0 → P m := by
  classical
  intro m
  induction m using WellFoundedLT.induction with
  | ind m ih =>
  intro hm
  have step : ∀ g : σ →₀ ℕ, g ≠ 0 → g ≤ m → Finsupp.weight lam g = 0 → P g → P m := fun g hg hle hw hP => by
    have e : m - g + g = m := tsub_add_cancel_of_le hle
    have hlt : m - g < m := by
      conv_rhs => rw [← e]
      exact lt_add_of_pos_right _ (pos_iff_ne_zero.2 hg)
    have hw' : Finsupp.weight lam (m - g) = 0 := by
      have := congrArg (Finsupp.weight lam) e
      rwa [map_add, hw, add_zero, hm] at this
    rw [← e]
    exact hadd _ _ (ih _ hlt hw') hP
  by_cases hz : ∃ s, m s ≠ 0 ∧ lam s = 0
  · obtain ⟨s, hs, hs0⟩ := hz
    refine step (Finsupp.single s 1) (by simp) ?_ (by simp [Finsupp.weight_single, hs0]) (h1 s hs0)
    rw [Finsupp.single_le_iff]
    omega
  by_cases hp : (∃ s, m s ≠ 0 ∧ lam s = 1) ∧ ∃ t, m t ≠ 0 ∧ lam t = -1
  · obtain ⟨⟨s, hs, hs1⟩, t, ht, ht1⟩ := hp
    have hst : s ≠ t := by
      rintro rfl
      omega
    refine step _ (by simp) ?_ (by simp [Finsupp.weight_single, hs1, ht1]) (h2 s t hs1 ht1)
    intro u
    simp only [Finsupp.add_apply, Finsupp.single_apply]
    split_ifs with a b b
    · exact absurd (a.trans b.symm) hst
    · subst a; omega
    · subst b; omega
    · omega
  have hsum : ∑ s, (m s : ℤ) * lam s = 0 := by
    rw [← hm, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  have : m = 0 := by
    ext u
    push Not at hz
    rcases not_and_or.1 hp with hp | hp
    · push Not at hp
      have hn : ∀ s ∈ Finset.univ, (m s : ℤ) * lam s ≤ 0 := fun s _ => by
        by_cases h : m s = 0
        · simp [h]
        · have := hl s; have := hp s h
          exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by omega)
      have h3 := (Finset.sum_eq_zero_iff_of_nonpos hn).1 hsum u (Finset.mem_univ _)
      by_contra h
      rcases mul_eq_zero.1 h3 with h4 | h4
      · exact h (by exact_mod_cast h4)
      · exact hz u h h4
    · push Not at hp
      have hn : ∀ s ∈ Finset.univ, 0 ≤ (m s : ℤ) * lam s := fun s _ => by
        by_cases h : m s = 0
        · simp [h]
        · have := hl s; have := hp s h
          exact mul_nonneg (by positivity) (by omega)
      have h3 := (Finset.sum_eq_zero_iff_of_nonneg hn).1 hsum u (Finset.mem_univ _)
      by_contra h
      rcases mul_eq_zero.1 h3 with h4 | h4
      · exact h (by exact_mod_cast h4)
      · exact hz u h h4
  rw [this]
  exact h0

private theorem aW_wts : ∀ w ∈ wts, (w.1 = -1 ∨ w.1 = 0 ∨ w.1 = 1) ∧ (-1 ≤ w.2 ∧ w.2 ≤ 1) := by decide

private theorem aW_gen {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (W : WPres O (ℤ × ℤ) R)
    (hw : ∀ s, W.wt s ∈ wts) (B : Subalgebra O R) (h0 : ∀ x ∈ W.part 0, x ∈ B)
    (h1 : ∀ s, (W.wt s).1 = 0 → W.z s ∈ B)
    (h2 : ∀ s t, (W.wt s).1 = 1 → (W.wt t).1 = -1 → W.z s * W.z t ∈ B) (n : ℤ) :
    ∀ x ∈ W.part (0, n), x ∈ B := by
  have hmon : ∀ m, Finsupp.weight (fun s => (W.wt s).1) m = 0 → W.π (MvPowerSeries.monomial m 1) ∈ B := by
    refine aW_comb _ (fun s => (aW_wts _ (hw s)).1) _ (by simp) (fun a b ha hb => ?_) h1 (fun s t hs ht => ?_)
    · have := mul_mem ha hb
      rwa [← map_mul, MvPowerSeries.monomial_mul_monomial, one_mul] at this
    · have := h2 s t hs ht
      rwa [WPres.z, WPres.z, ← map_mul, MvPowerSeries.X_def, MvPowerSeries.X_def,
        MvPowerSeries.monomial_mul_monomial, one_mul] at this
  have hfst : ∀ m : W.σ →₀ ℕ, Finsupp.weight (fun s => (W.wt s).1) m = (Finsupp.weight W.wt m).1 := fun m => by
    induction m using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, Prod.fst_add]
    | single s k => simp [Finsupp.weight_single]
  obtain ⟨μ, hμ, hdec⟩ := part_span O R (ℤ × ℤ) W {m | Finsupp.weight W.wt m = (0, n)} (0, n) (fun _ h => h)
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨b, hb, rfl⟩ := hdec f hf
  show W.π _ ∈ _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine sum_mem fun m hm => ?_
  rw [map_mul]
  refine mul_mem (h0 _ ⟨b m, hb m, rfl⟩) (hmon m ?_)
  have : Finsupp.weight W.wt m = (0, n) := hμ hm
  rw [hfst, this]

private theorem weight_algebra_generated_degree_two {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (W : WPres O (ℤ × ℤ) R)
    (hw : ∀ s, W.wt s ∈ wts) (a : ℤ → Submodule O R) [SetLike.GradedMonoid a] (ha : ∀ n, a n = W.part (0, n)) :
    ∃ s : Finset (gradedSub a), (∀ x ∈ s, x.1 ∈ a (-2) ∨ x.1 ∈ a (-1) ∨ x.1 ∈ a 1 ∨ x.1 ∈ a 2) ∧
      Algebra.adjoin O ({x : gradedSub a | x.1 ∈ a 0} ∪ s) = ⊤ := by
  classical
  let U : Set R := Set.range W.z ∪ Set.range fun p : W.σ × W.σ => W.z p.1 * W.z p.2
  have hU : U.Finite := (Set.finite_range _).union (Set.finite_range _)
  let T : Set (gradedSub a) := {x | (x.1 ∈ a (-2) ∨ x.1 ∈ a (-1) ∨ x.1 ∈ a 1 ∨ x.1 ∈ a 2) ∧ x.1 ∈ U}
  have hT : T.Finite := (hU.preimage Subtype.val_injective.injOn).subset fun x hx => hx.2
  refine ⟨hT.toFinset, fun x hx => (hT.mem_toFinset.1 hx).1, ?_⟩
  rw [hT.coe_toFinset]
  set S := Algebra.adjoin O ({x : gradedSub a | x.1 ∈ a 0} ∪ T) with hS
  have key : ∀ n : ℤ, -2 ≤ n → n ≤ 2 → ∀ y ∈ W.part (0, n), y ∈ U → y ∈ S.map (gradedSub a).val := by
    intro n hn hn' y hy hyU
    rw [← ha] at hy
    refine ⟨⟨y, le_iSup a n hy⟩, Algebra.subset_adjoin ?_, rfl⟩
    have h4 : n = 0 ∨ n = -2 ∨ n = -1 ∨ n = 1 ∨ n = 2 := by omega
    rcases h4 with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl hy
    · exact Or.inr ⟨Or.inl hy, hyU⟩
    · exact Or.inr ⟨Or.inr (Or.inl hy), hyU⟩
    · exact Or.inr ⟨Or.inr (Or.inr (Or.inl hy)), hyU⟩
    · exact Or.inr ⟨Or.inr (Or.inr (Or.inr hy)), hyU⟩
  have main := aW_gen W hw (S.map (gradedSub a).val)
    (fun y hy => by
      have hy' : y ∈ a 0 := by rw [ha]; exact hy
      exact ⟨⟨y, le_iSup a 0 hy'⟩, Algebra.subset_adjoin (Or.inl hy'), rfl⟩)
    (fun s hs => by
      have hb := (aW_wts _ (hw s)).2
      refine key (W.wt s).2 (by omega) (by omega) _ ?_ (Or.inl ⟨s, rfl⟩)
      rw [← hs]
      exact W.z_mem s)
    (fun s t hs ht => by
      have hb := (aW_wts _ (hw s)).2
      have hb' := (aW_wts _ (hw t)).2
      refine key ((W.wt s).2 + (W.wt t).2) (by omega) (by omega) _ ?_ (Or.inr ⟨(s, t), rfl⟩)
      have h5 : W.z s * W.z t ∈ W.part (W.wt s + W.wt t) :=
        SetLike.GradedMul.mul_mem (W.z_mem s) (W.z_mem t)
      have h6 : W.wt s + W.wt t = (0, (W.wt s).2 + (W.wt t).2) :=
        Prod.ext (by rw [Prod.fst_add, hs, ht]; rfl) rfl
      rwa [h6] at h5)
  rw [eq_top_iff]
  rintro ⟨x, hx⟩ -
  have hxS : x ∈ S.map (gradedSub a).val :=
    Submodule.iSup_induction a (motive := fun x => x ∈ S.map (gradedSub a).val) hx (fun n y hy => main n y (ha n ▸ hy))
      (zero_mem _) (fun a b ha hb => add_mem ha hb)
  obtain ⟨y, hy, hxy⟩ := hxS
  obtain rfl : y = ⟨x, hx⟩ := Subtype.ext hxy
  exact hy

theorem UpperTheory.V.GradeZeroInterpolatingElement.aW :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, ∀ [GradedAlgebra M.gr], IsWRing M.gr M.x0 := by
  intro Ω _ _ _ l _ c D _ M _
  classical
  have hz : ∀ s, M.W.z s ∈ maximalIdeal M.R := fun s => by
    rw [← res_eq_zero_iff c.O, ← res_map (M.W.origin M.org), WPres.z, M.W.origin_π, MvPowerSeries.constantCoeff_X,
      map_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    refine ⟨?_, ?_, ?_⟩
  · haveI := wPres_gr_zero_isCO_of_mem_maximalIdeal c.O (ℤ × ℤ) M.R M.W hz
    let p : M.W.gr 0 →ₐ[c.O] M.gr 0 :=
      { toFun := fun F => ⟨⟨F.1.1, M.aPart_le (n := 0) F.2⟩, F.2⟩
        map_one' := rfl
        map_mul' := fun F G => rfl
        map_zero' := rfl
        map_add' := fun F G => rfl
        commutes' := fun c => rfl }
    haveI : Nontrivial (M.gr 0) := ⟨⟨0, 1, fun h =>
      zero_ne_one (α := M.R) (congrArg (fun x : M.gr 0 => ((x : M.A) : M.R)) h)⟩⟩
    refine co_quot c.O (M.W.gr 0) (M.gr 0) p ?_
    rintro ⟨⟨x, hxA⟩, hx⟩
    exact ⟨⟨⟨x, M.W.part_le_A (j := 0) hx⟩, hx⟩, rfl⟩
  · exact weight_algebra_generated_degree_two M.W M.wt_mem M.aPart (fun _ => rfl)
  · rintro j hj f ⟨g, hg, hgf⟩
    have hgf' : M.W.π g = (f : M.R) := hgf
    show M.W.origin M.org (f : M.R) = 0
    rw [← hgf', M.W.origin_π, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hg 0 (by rw [map_zero]; exact fun h => hj (congrArg Prod.snd h).symm)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.AVal
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

theorem UpperTheory.V.GradeZeroInterpolatingElement.aElt :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, ∀ g, ∃ a ∈ M.gr 0, M.x0 a = 0 ∧ ∀ ξ : M.SS →ₐ[c.O] PadicAlgCl l, ξ (M.toSS a) = D.aVal g (M.rep ξ) := by
  intro Ω _ _ _ l _ c D _ M g
  choose f hf hπ using fun i : Fin 4 => M.hom g i i
  have hf0 : ∀ i, f i ∈ M.aPart 0 := by
    intro i
    have h := hf i
    rw [(wt_eq_zero i i).mpr rfl] at h
    exact h
  let fA : Fin 4 → M.A := fun i => ⟨f i, M.aPart_le (hf0 i)⟩
  have hx0 : ∀ i, M.x0 (fA i) = D.r0 g i i := fun i => M.at0 g i i (f i) (hπ i)
  have hss : ∀ i, M.toSS (fA i) = M.ent g i i := fun i => Subtype.ext (hπ i)
  refine ⟨∑ i, fA i - algebraMap c.O M.A (Matrix.trace (D.r0 g)), ?_, ?_, ?_⟩
  · apply Submodule.sub_mem
    · exact Submodule.sum_mem _ fun i _ => hf0 i
    · rw [Algebra.algebraMap_eq_smul_one]
      apply Submodule.smul_mem
      show (1 : M.R) ∈ M.aPart 0
      exact SetLike.GradedOne.one_mem
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum, AlgHom.commutes]
    simp only [hx0, Algebra.algebraMap_self, RingHom.id_apply, Matrix.trace, Matrix.diag]
    exact sub_self _
  · intro ξ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sub, map_sum, map_sum, AlgHom.commutes, AlgHom.commutes]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hss, Raw.aVal, Matrix.trace, Matrix.diag, map_sum]
    rfl
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

section Gen

variable {O A K : Type} [CommRing O] [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜]
  [Field K] [Algebra O K]

private theorem algHom_ext_graded {ξ ξ' : A →ₐ[O] K} (h : ∀ j, ∀ f ∈ 𝒜 j, ξ f = ξ' f) : ξ = ξ' := by
  ext f
  induction f using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | homogeneous f => exact h _ _ f.2
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]

private theorem same_orbit_trans {ξ ξ' ξ'' : A →ₐ[O] K} (h : SameOrbit 𝒜 ξ ξ') (h' : SameOrbit 𝒜 ξ' ξ'') :
    SameOrbit 𝒜 ξ ξ'' := by
  obtain ⟨s, rfl⟩ := h
  obtain ⟨t, rfl⟩ := h'
  refine ⟨t * s, algHom_ext_graded 𝒜 fun j f hf => ?_⟩
  simp only [act_of_mem 𝒜 _ _ hf, zpowersHom_apply, toAdd_ofAdd, mul_zpow, Units.val_mul, mul_assoc]

private theorem exists_minimal_orbit_cover (I : Ideal A) (h : ∃ T : Finset (A →ₐ[O] K), Covers 𝒜 I T) :
    ∃ T : Finset (A →ₐ[O] K), Covers 𝒜 I T ∧ ∀ ξ ∈ T, ∀ ξ' ∈ T, SameOrbit 𝒜 ξ ξ' → ξ = ξ' := by
  classical
  have h' : ∃ n, ∃ T : Finset (A →ₐ[O] K), Covers 𝒜 I T ∧ T.card = n := by
    obtain ⟨T, hT⟩ := h
    exact ⟨_, T, hT, rfl⟩
  obtain ⟨T, hT, hc⟩ := Nat.find_spec h'
  refine ⟨T, hT, fun ξ hξ ξ' hξ' ho => ?_⟩
  by_contra hne
  refine Nat.find_min h' (m := (T.erase ξ').card) (hc ▸ Finset.card_erase_lt_of_mem hξ') ⟨T.erase ξ', ⟨?_, ?_⟩, rfl⟩
  · exact fun x hx => hT.1 x (Finset.mem_of_mem_erase hx)
  · intro x hx h2
    obtain ⟨y, hy, hyx⟩ := hT.2 x hx h2
    by_cases e : y = ξ'
    · subst e
      exact ⟨ξ, Finset.mem_erase.2 ⟨hne, hξ⟩, same_orbit_trans 𝒜 ho hyx⟩
    · exact ⟨y, Finset.mem_erase.2 ⟨e, hy⟩, hyx⟩

end Gen

private theorem torus_conj_mul {R : Type} [CommRing R] (s t : Rˣ × Rˣ) (X : M4 R) :
    tconj s (tconj t X) = tconj (s * t) X := by
  ext i j
  simp only [tconj, wv, Matrix.of_apply, Prod.fst_mul, Prod.snd_mul, mul_zpow, Units.val_mul]
  ring

private theorem torus_conj_one {R : Type} [CommRing R] (X : M4 R) : tconj 1 X = X := by
  ext i j
  simp [tconj, wv]

private theorem irreducible_torus_conjugate {R H : Type} [CommRing R] [Group H] (t : Rˣ × Rˣ) (r r' : H →* M4 R)
    (h : ∀ g, r' g = tconj t (r g)) (hr : Irr r) : Irr r' := by
  obtain ⟨u, hu⟩ := (grp R).2.2.2.2.2.2.2.2.2.2.2.2 t
  have key : ∀ X ∈ Submodule.span R (Set.range r), (u : M4 R) * X * (u⁻¹ : (M4 R)ˣ) ∈ Submodule.span R (Set.range r') := by
    intro X hX
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact Submodule.subset_span ⟨g, by rw [h, hu]⟩
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add, add_mul]; exact add_mem hx hy
    | smul a x _ hx => rw [mul_smul_comm, smul_mul_assoc]; exact Submodule.smul_mem _ a hx
  refine eq_top_iff.2 fun X _ => ?_
  have := key (((u⁻¹ : (M4 R)ˣ) : M4 R) * X * u) (by rw [show Submodule.span R (Set.range r) = ⊤ from hr]; trivial)
  simpa only [mul_assoc, Units.mul_inv_cancel_left, Units.mul_inv, mul_one] using this

private theorem real_ratio_bound (s n e L S : ℝ) (he : 0 < e) (hL : 0 < L) (h1 : s ≤ n) (h2 : n ≤ 2 * (S * e / L)) :
    s / e * L ≤ 2 * S := by
  have h3 : s * L ≤ 2 * S * e := by
    have := mul_le_mul_of_nonneg_right (h1.trans h2) hL.le
    have e1 : 2 * (S * e / L) * L = 2 * S * e := by field_simp
    rwa [e1] at this
  rw [div_mul_eq_mul_div, div_le_iff₀ he]
  exact h3

section Pts

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}

private theorem same_orbit_of_conjugate_reps (hD : D.Good) (M : Model D) [GradedAlgebra M.gr] (h0 : D.Fin0)
    (ξ ξ' : M.SS →ₐ[c.O] PadicAlgCl l) (t t' : (PadicAlgCl l)ˣ × (PadicAlgCl l)ˣ) (r r' : G ℚ Ω →* M4 (PadicAlgCl l))
    (he : D.EPt r) (he' : D.EPt r') (hi : Irr r) (ht : ∀ g, r g = tconj t (M.rep ξ g))
    (ht' : ∀ g, r' g = tconj t' (M.rep ξ' g)) (hc : IsConj4 r r') :
    SameOrbit M.gr (ξ.comp M.toSS) (ξ'.comp M.toSS) := by
  obtain ⟨s, hs⟩ := conjTorus D hD _ _ he he' hi hc
  obtain ⟨η, hη, hw⟩ := ptAct D hD M _ ξ (t'⁻¹ * (s * t))
  have e : η = ξ' := by
    refine ptExt D hD M h0 _ _ _ (MonoidHom.ext fun g => ?_)
    rw [hη, ← torus_conj_mul, ← torus_conj_mul, ← ht, ← hs, ht', torus_conj_mul, inv_mul_cancel, torus_conj_one]
  subst e
  refine ⟨(t'⁻¹ * (s * t)).2, algHom_ext_graded M.gr fun j f hf => ?_⟩
  rw [act_of_mem M.gr _ _ hf, AlgHom.comp_apply, AlgHom.comp_apply, hw (0, j) _ ((kerA D hD M).2.2 j f hf)]
  simp only [wv, zpow_zero, one_mul, zpowersHom_apply, toAdd_ofAdd]

private theorem exists_rep_family_from_points (hD : D.Good) (M : Model D) [GradedAlgebra M.gr] (hL : Loc.LocalPublishedTheorems) (hV : SoV Ω l)
    (h0 : D.Fin0) (hNE : D.NoEnd) (g : G ℚ Ω) (a : M.A)
    (ha : ∀ ξ : M.SS →ₐ[c.O] PadicAlgCl l, ξ (M.toSS a) = D.aVal g (M.rep ξ)) :
    ∃ ρ : (M.A →ₐ[c.O] PadicAlgCl l) → (G ℚ Ω →* M4 (PadicAlgCl l)),
      (∀ x, OnS M.eqns.ideal x ∧ TwoSigned M.gr x → (D.EPt (ρ x) ∧ Irr (ρ x)) ∧ D.aVal g (ρ x) = x a) ∧
      ∀ x x', OnS M.eqns.ideal x ∧ TwoSigned M.gr x → OnS M.eqns.ideal x' ∧ TwoSigned M.gr x' →
        IsConj4 (ρ x) (ρ x') → SameOrbit M.gr x x' := by
  have hpt : ∀ x : M.A →ₐ[c.O] PadicAlgCl l, ∃ r : G ℚ Ω →* M4 (PadicAlgCl l), OnS M.eqns.ideal x ∧ TwoSigned M.gr x →
      ((D.EPt r ∧ Irr r) ∧ D.aVal g r = x a) ∧ ∃ (ξ : M.SS →ₐ[c.O] PadicAlgCl l)
        (t : (PadicAlgCl l)ˣ × (PadicAlgCl l)ˣ), ξ.comp M.toSS = x ∧ ∀ g, r g = tconj t (M.rep ξ g) := by
    intro x
    by_cases hx : OnS M.eqns.ideal x
    · set_option synthInstance.maxHeartbeats 200000 in
      obtain ⟨ξ, hξ⟩ := ptLift D hD M x hx
      obtain ⟨t, r, hr, hrt⟩ := ptScale D hD M h0 ξ
      refine ⟨r, fun h2 => ⟨⟨⟨hr, irreducible_torus_conjugate t _ _ hrt (twoIrr D hD M hL hV h0 hNE ξ (by rw [hξ]; exact h2.2))⟩, ?_⟩,
        ξ, t, hξ, hrt⟩⟩
      rw [← hξ, AlgHom.comp_apply, ha, Raw.aVal, Raw.aVal, hrt, (grp _).2.2.2.2.2.2.2.2.2.2.2.1]
    · exact ⟨1, fun h => absurd h.1 hx⟩
  choose ρ hρ using hpt
  refine ⟨ρ, fun x hx => (hρ x hx).1, fun x x' hx hx' hc => ?_⟩
  obtain ⟨⟨⟨he, hi⟩, -⟩, ξ, t, hξ, ht⟩ := hρ x hx
  obtain ⟨⟨⟨he', -⟩, -⟩, ξ', t', hξ', ht'⟩ := hρ x' hx'
  have := same_orbit_of_conjugate_reps hD M h0 ξ ξ' t t' _ _ he he' hi ht ht' hc
  rwa [hξ, hξ'] at this

private theorem covers_and_cotangent_length_bounds (hD : D.Good) (M : Model D) [GradedAlgebra M.gr] (hM : LemmaM) (hL : Loc.LocalPublishedTheorems) (hV : SoV Ω l)
    (h0 : D.Fin0) (hNE : D.NoEnd) (hR : D.AllIrr D.RigidAt) (a : M.A) (h5 : M5 M.gr (PadicAlgCl l) M.x0 M.eqns.ideal a) :
    (∃ T : Finset (M.A →ₐ[c.O] PadicAlgCl l), Covers M.gr M.eqns.ideal T) ∧ cotLen M.x0 M.gr (-1) M.eqns.F ≠ ⊤ ∧
    ∀ T : Finset (M.A →ₐ[c.O] PadicAlgCl l), Covers M.gr M.eqns.ideal T → ((cotLen M.x0 M.gr (-1) M.eqns.F).toNat : ℝ) ≤
      2 * ∑ ξ ∈ T, -Real.log ‖ξ a‖ * ((eO l c.O).toNat : ℝ) / Real.log l := by
  obtain ⟨h1, h2, h3⟩ := m1b D hD M hV
  exact hM c.O (PadicAlgCl l) _ (nval c) M.A M.gr M.x0 (aW D hD M) _ _ _ _ _ M.eqns a
    ⟨M.one_le, aSmooth D hD M, h1, h2, h3⟩ (m2 D hD M h0) (m3 D hD M hL hV h0) (m4 D hD M hL hV h0 hNE hR) h5

end Pts

theorem UpperTheory.V.GradeZeroInterpolatingElement.galoisRep_ineq_of_allIrreducible_nonvanishing :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, LemmaM → LemmaM' → Loc.LocalPublishedTheorems → SoV Ω l → SoFin Ω l → D.Fin0 → D.NoEnd → D.AllIrr D.RigidAt → ∀ g, D.AllIrr (fun r => D.aVal g r ≠ 0) → D.Ineq g := by
  intro Ω _ _ _ l hl c D hD M hM hM' hL hV hF h0 hNE hR g hA
  classical
  obtain ⟨inst⟩ := aGraded D hD M
  set_option synthInstance.maxHeartbeats 200000 in
  obtain ⟨a, ha0, hax, ha⟩ := aElt D hD M g
  obtain ⟨ρ, hρ, horb⟩ := exists_rep_family_from_points hD M hL hV h0 hNE g a ha
  obtain ⟨hT, hfin, hle⟩ := covers_and_cotangent_length_bounds hD M hM hL hV h0 hNE hR a
    ⟨ha0, hax, fun x hx h2 => by
      obtain ⟨⟨he, hi⟩, hv⟩ := hρ x ⟨hx, h2⟩
      rw [← hv]
      exact hA _ he hi⟩
  obtain ⟨T, hT, hmin⟩ := exists_minimal_orbit_cover M.gr _ hT
  have hinj : ∀ x ∈ T, ∀ x' ∈ T, IsConj4 (ρ x) (ρ x') → x = x' := fun x hx x' hx' hc =>
    hmin x hx x' hx' (horb x x' (hT.1 x hx) (hT.1 x' hx') hc)
  refine ⟨(shaCoc D hD hF).1, T.image ρ, ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hr
    exact (hρ x (hT.1 x hx)).1
  · intro r hr r' hr' hc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hr
    obtain ⟨x', hx', rfl⟩ := Finset.mem_image.1 hr'
    rw [hinj x hx x' hx' hc]
  · have e2 : ∑ r ∈ T.image ρ, -Real.log ‖D.aVal g r‖ = ∑ x ∈ T, -Real.log ‖x a‖ := by
      rw [Finset.sum_image fun x hx x' hx' e => hinj x hx x' hx' ⟨1, fun g => by
        rw [e, inv_one, Units.val_one, one_mul, mul_one]⟩]
      exact Finset.sum_congr rfl fun x hx => by rw [(hρ x (hT.1 x hx)).2]
    rw [e2]
    have hs := hle T hT
    rw [← Finset.sum_div, ← Finset.sum_mul] at hs
    obtain ⟨-, -, -, -, -, e0, e1, -⟩ := dvrFacts l c.O
    have he : 0 < (eO l c.O).toNat :=
      ENat.toNat_pos e0 (ne_top_of_le_ne_top (ENat.coe_ne_top _) e1)
    exact real_ratio_bound _ _ _ _ _ (Nat.cast_pos.2 he) (Real.log_pos (by exact_mod_cast hl.out.one_lt))
      (Nat.cast_le.2 (ENat.toNat_le_toNat (mPrime D hD M hM' hF) hfin)) hs

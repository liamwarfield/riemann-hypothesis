module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.TpSingle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.ConjHom
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.ZOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.BarOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.FElMap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.EigChp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.Lam0
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.HasOp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.ResidualRepOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.PresCnts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.LcOfOpen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AutomorphicDetection.ArPl
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.PsiInj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.WeilCharactersModular.LocCFT
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ExistsAdjoinCoeffCharacterSubMemMaximalIdealPow

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.Imports
open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

theorem UpperTheory.V.Th.Coc.kill :
    ∀ {O R X : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing X] [Algebra O X] {n : ℕ} [IsDomain O] {G : Type} [Group G] (x : R →ₐ[O] O) (δ : R →ₗ[O] X) (ρ : G →* Matrix (Fin n) (Fin n) O) (τ : MonoidAlgebra R G → R) (c c₀ : O) (d : MonoidAlgebra R G →+ Matrix (Fin n) (Fin n) X), c₀ ≠ 0 → (∀ Z : Matrix (Fin n) (Fin n) O, c₀ • Z ∈ Submodule.span O (Set.range ρ)) → (∀ y, (repR x ρ y).trace = x (τ y)) → IsLift x δ (repR x ρ) τ c d → ∀ y, (∀ g, τ ((MonoidAlgebra.single g 1) * y) = 0) → repR x ρ y = 0 ∧ c₀ • d y = 0 := by
  intro O R X _ _ _ _ _ n _ G _ x δ ρ τ c c₀ d hc₀ hspan htr hd y hy
  obtain ⟨k1, k2⟩ := kill0 ρ c₀ hc₀ hspan
  have hs : ∀ g : G, repR x ρ (MonoidAlgebra.single g 1) = ρ g := by
    intro g
    rw [repR_single, map_one, one_smul]
  have h1 : repR x ρ y = 0 := by
    apply k1
    intro g
    rw [← hs, ← map_mul, htr, hy, map_zero]
  refine ⟨h1, k2 X (d y) ?_⟩
  intro g
  have e := hd.mul (MonoidAlgebra.single g 1) y
  rw [h1, hs] at e
  have hb0 : bar X (0 : Matrix (Fin n) (Fin n) O) = 0 := by
    ext i j
    simp [bar]
  rw [hb0, Matrix.mul_zero, zero_add] at e
  rw [← e, hd.tr, hy, map_zero, smul_zero]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.OrdinaryHeckeAlgebraIntegral
open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem coef_isCoef (l : ℕ) [hl : Fact l.Prime] (c : Coef l) : IsCoef l c.O := by
  obtain ⟨h1, h2, h3, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  refine ⟨h1, h2, ?_⟩
  rw [CharP.charP_iff_prime_eq_zero hl.out, ← map_natCast (residue c.O), residue_eq_zero_iff]
  exact h3

private theorem eps_ne {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A w) (hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) :
    ∃ g : Dec (F := L) A, cycZ L Ω l g ≠ 1 := by
  by_contra hn
  have hn' : ∀ g : Dec (F := L) A, cycBar L Ω l g = 1 := fun g => by
    have : cycZ L Ω l g = 1 := by
      by_contra h1
      exact hn ⟨g, h1⟩
    rw [cycBar, MonoidHom.comp_apply, this, map_one]
  have := UpperTheory.V.Ws.Eb.psiInj (l := l) A w h hw (n := 2) (fun _ => 1) ![0, 1] 1 (by decide) one_pos
    (fun i g _ => by rw [hn' g]; simp)
  exact absurd (@this 0 1 rfl) (by decide)

theorem UpperTheory.V.Th.b1O : ordinaryHeckeAlgebraIntegral := by
  intro hP l _ L Ω _ _ _ _ _ _ s V0 c n r T P y al hS _ _ hPL h4 heig hdet
  haveI := _root_.coef_isCoef l c
  choose a p h1 h2 h3 using arPres l L Ω s V0 c.O n r T P hS
  have S : Sys T (Module.finrank ℚ (Lp L)) V0.frame.D0 :=
    { a := a
      counts := fun N => presCnts hP l _ _ _ _ (a N) (Lp L) Ω (p N) s.odd (unrLoc l L Ω s V0 c.O n r)
      dv := fun v : Vl l L => locDeg v.1
      dv_eq := fun N => funext (h1 N)
      d0 := h2
      ph := fun N j => (h3 N j).1
      ta := fun N j => (h3 N j).2 }
  have hΦ := (arPl hP l L Ω s V0 c.O n r hS).1
  refine b1absO l _ _ T c.O n y al _ _ S s.odd hΦ (fun v => ?_) hPL h4 heig (detO l _ _ c n y _ s.odd hdet)
  have hw : ((l : ℕ) : 𝓞 L) ∈ (s.w v.1).asIdeal := by
    have h1 := (s.hA v.1 ((l : ℕ) : 𝓞 (Lp L))).2 v.2
    exact (s.hw v.1 _).1 (by simpa using h1)
  obtain ⟨g, hg⟩ := eps_ne (s.A v.1) (s.w v.1) (s.hw v.1) hw
  refine ⟨g, fun e => hg (Units.ext ?_)⟩
  have e1 : V0.ε (toGS Ω V0.S' (resP L Ω g)) = cycZ (Lp L) Ω l (resP L Ω g) := DFunLike.congr_fun V0.hε _
  have e2 : algebraMap ℤ_[l] c.O (V0.ε (toGS Ω V0.S' (resP L Ω g)) : ℤ_[l]) = 1 := e
  rw [e1, ← map_one (algebraMap ℤ_[l] c.O)] at e2
  exact (UpperTheory.V.abelian₂.dvr_finite l c.O).2.2.2.1 e2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.MapRingHomSingleMulPartialCharpoly
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.LiftSmul
open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

private theorem lift_smul {O R X : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing X] [Algebra O X] {n : ℕ}
    {E : Type} [Ring E] [Algebra R E] {x : R →ₐ[O] O} {δ : R →ₗ[O] X} {ρ : E →+* Matrix (Fin n) (Fin n) O}
    {τ : E → R} {c : O} {d : E →+ Matrix (Fin n) (Fin n) X} (h : IsLift x δ ρ τ c d) (a : O) :
    IsLift x δ ρ τ (a * c) (a • d) := by
  constructor
  · intro u v
    simp only [AddMonoidHom.smul_apply, h.mul, smul_add, Matrix.smul_mul, Matrix.mul_smul]
  · intro r u
    simp only [AddMonoidHom.smul_apply, h.smul, smul_add]
    rw [smul_comm a (x r), mul_smul, smul_assoc a]
  · intro u
    simp only [AddMonoidHom.smul_apply, Matrix.trace_smul, h.tr, mul_smul]

private theorem lc_mat {Γ R : Type} [TopologicalSpace Γ] {n : ℕ} (f : Γ → Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, IsLocallyConstant fun g => f g i j) : IsLocallyConstant f := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_
  have : ∀ᶠ g' in nhds g, ∀ i j, f g' i j = f g i j :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => (h i j).eventually_eq g
  exact this.mono fun g' e => Matrix.ext e

private theorem der_const {O R X : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup X] [Module O X] {x : R →ₐ[O] O}
    {δ : R →ₗ[O] X} (h : IsDer x δ) (a : O) : δ (algebraMap O R a) = 0 := by
  have h1 := h 1 1
  rw [mul_one, map_one x, one_smul] at h1
  have h2 : δ 1 = 0 := by simpa using h1
  rw [Algebra.algebraMap_eq_smul_one, map_smul, h2, smul_zero]

theorem UpperTheory.V.Th.coc :
    Coc := by
  intro l hl L G0 n O _ _ _ hO _ y h2 hn
  classical
  obtain ⟨c₀, hc₀, hsp⟩ := y.span
  choose c₁ hc₁ hloc using fun v => locAt y v
  have h2O : (2 : O) ≠ 0 := by
    intro e
    haveI := hO.char
    have h3 : ((2 : ℕ) : ResidueField O) = 0 := by
      rw [← map_natCast (residue O), Nat.cast_ofNat, e, map_zero]
    exact h2 ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).1 ((CharP.cast_eq_zero_iff _ l 2).1 h3))
  refine ⟨(∏ v, c₁ v) * (c₀ * (2 * (c₀ ^ (2 * n) * c₀ ^ (2 * n)))),
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun v _ => hc₁ v) (mul_ne_zero hc₀ (mul_ne_zero h2O
      (mul_ne_zero (pow_ne_zero _ hc₀) (pow_ne_zero _ hc₀)))), ?_⟩
  intro G h rN R _ _ _ p x hI hp m δ hδ
  have hsurj : Function.Surjective h.p₀ := fun g => by
    obtain ⟨g', e⟩ := h.surj g
    exact ⟨⟨g', by rw [MonoidHom.mem_ker, ← h.η, e]; exact g.2⟩, Subtype.ext e⟩
  have hcont : Continuous h.p₀ := (h.cont.comp continuous_subtype_val).subtype_mk _
  have hsp' : ∀ Z : Matrix (Fin n) (Fin n) O, c₀ • Z ∈ Submodule.span O (Set.range (mat (y.ρ.comp h.p₀))) := fun Z => by
    have e : Set.range (mat (y.ρ.comp h.p₀)) = Set.range (mat y.ρ) := hsurj.range_comp (mat y.ρ)
    rw [e]
    exact hsp Z
  have hform : G.frame.IsForm O n (y.ρ.comp h.p₀) y.P := fun g => by
    have e1 : h.p₀ (G.frame.conj g) = G0.frame.conj (h.p₀ g) := Subtype.ext (by
      change h.p (G.c * g * G.c⁻¹) = G0.c * h.p g * G0.c⁻¹
      rw [map_mul, map_mul, map_inv, h.c])
    have e2 : G.frame.eps O O g = G0.frame.eps O O (h.p₀ g) := by
      change Units.map _ (G.ε g) = Units.map _ (G0.ε (h.p g))
      rw [h.ε]
    have := y.form (h.p₀ g)
    rw [← e1, ← e2] at this
    exact this
  obtain ⟨htr, -, t, ht⟩ := trRep p.D x _ hn hp.1
  have ht' : (t : _ → R) = p.D.tr := funext ht
  obtain ⟨d1, hd1⟩ := liftG p.D rN.chib x δ _ c₀ hn rN.chib_inj p.red hp.1 hc₀ hsp' hδ
  obtain ⟨d2, hd2, hpol⟩ := polar G.frame x δ _ y.P t _ d1 y.sgn hform (fun g => by rw [ht, ht]; exact p.P 1 g) (ht' ▸ hd1)
  rw [ht'] at hd2
  have hk := kill x δ _ _ _ c₀ d2 hc₀ hsp' htr hd2
  have hd3 := lift_smul hd2 c₀
  have hd4 := lift_smul hd3 (∏ v, c₁ v)
  obtain ⟨h1, hcoc, hP, hT⟩ := zOf G.frame x δ _ y.P _ _ _
    (fun g => ((∏ v, c₁ v) • c₀ • d2) (MonoidAlgebra.single g 1) * bar (Om O m) (mat (y.ρ.comp h.p₀) g⁻¹)) hδ hform hd4
    (fun a => by simp only [AddMonoidHom.smul_apply, Matrix.mul_smul, Matrix.transpose_smul, Matrix.smul_mul, hpol]) fun _ => rfl
  have hρlc : IsLocallyConstant fun g => bar (Om O m) (mat (y.ρ.comp h.p₀) g) :=
    (lc_mat _ fun i j => (lcDer (R := R) m).1 _ (y.cont i j)).comp_continuous hcont
  refine ⟨_, ⟨?_, hcoc, hP, fun u g hg => ?_, fun v => ?_⟩, hT⟩
  · have hl2 := lc x δ _ _ _ c₀ d2 hsp' hd2 hρlc ((lcDer m).2 x δ hδ _ (p.cont 1))
    exact (hl2.comp fun Z => (∏ v, c₁ v) • Z).mul (hρlc.comp_continuous continuous_inv)
  · have h4 := (hk _ (p.I u g (hI u ▸ hg))).2
    have h5 : d2 1 = 0 := by
      have := hd2.mul 1 1
      simpa using this
    rw [map_sub, h5, sub_zero] at h4
    simp only [AddMonoidHom.smul_apply, h4, smul_zero, Matrix.zero_mul]
  · obtain ⟨Y, hY⟩ := hloc v G h R x m δ _ _ _ (p.ψ v) hd3
      (fun i g => congrArg Units.val (DFunLike.congr_fun (hp.2 v i) g))
      (fun g => hk _ (p.Ord v g)) fun i g hg => by
        rw [(p.psi v i).mu ⟨g, hg⟩]
        exact der_const hδ _
    refine ⟨(∏ v' ∈ Finset.univ.erase v, c₁ v') • Y, fun g => ?_⟩
    have e : ((∏ v, c₁ v) • c₀ • d2) (MonoidAlgebra.single (G.frame.φ v g) 1) *
          bar (Om O m) (mat (y.ρ.comp h.p₀) (G.frame.φ v g)⁻¹) -
        dY G.frame (y.ρm h m) ((∏ v' ∈ Finset.univ.erase v, c₁ v') • Y) (G.frame.φ v g) =
        (∏ v' ∈ Finset.univ.erase v, c₁ v') • (c₁ v • ((c₀ • d2) (MonoidAlgebra.single (G.frame.φ v g) 1) *
          y.ρm h m (G.frame.φ v g)⁻¹) - dY G.frame (y.ρm h m) Y (G.frame.φ v g)) := by
      rw [smul_sub, smul_smul (∏ v' ∈ Finset.univ.erase v, c₁ v'), Finset.prod_erase_mul _ _ (Finset.mem_univ v),
        AddMonoidHom.smul_apply, Matrix.smul_mul]
      simp only [dY, smul_sub, Matrix.mul_smul, Matrix.smul_mul]
      rfl
    rw [e]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply]
    refine ⟨fun i j hij => ?_, fun hg i => ?_⟩
    · have := (hY g).1 i j hij
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply] at this
      rw [this, smul_zero]
    · have := (hY g).2 hg i
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply] at this
      rw [this, smul_zero]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.Imports
open UpperTheory.V UpperTheory.V.Th
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev

theorem UpperTheory.V.Th.split :
    Split := by
  intro l _ L G0 T n O _ _ _ _ _ r B _ _ _ u J D b y x al E hn hgen hmap hJ ⟨t₀, ht₀, hEt⟩ hPL heig
  haveI : Module.Finite B b.M := by
    letI : Algebra (abelian₂ O Empty D) B := b.lam.toRingHom.toAlgebra
    haveI : IsScalarTower (abelian₂ O Empty D) B b.M := ⟨fun a c m => by
      rw [b.smul_lam, ← mul_smul]; rfl⟩
    haveI := b.fin
    exact Module.Finite.of_restrictScalars_finite (abelian₂ O Empty D) B b.M
  obtain ⟨lam, m₀, hlam, hm₀⟩ := Sp.lam0 O B b.M x ((b.supp _ (RingHom.ker_isPrime x)).2 hJ)
  obtain ⟨F, hF, hev⟩ := Sp.eig l L G0 T n O y al hPL heig
  refine ⟨x t₀ ^ 2 * lam m₀ * F ^ (3 * E + 6), mul_ne_zero (mul_ne_zero (pow_ne_zero _ ht₀) hm₀) (pow_ne_zero _ hF), fun m => ?_⟩
  filter_upwards [hev, eventually_ge_atTop m] with N ⟨α, hα, hd⟩ hN A hA
  exact ⟨α, Sp.one l L G0 _ (T.h N) n O r B u J D b T.q N A y x _ _ _ E α t₀ lam m₀ m _ hn hgen hmap hEt hlam
    (fun j => Subtype.ext (T.ta_ker N j)) hα hA hN (mul_dvd_mul_left _ (pow_dvd_pow_of_dvd hd _))⟩
end

open IsLocalRing Filter UpperTheory.V UpperTheory.V.Th UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev

private theorem cnt (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)]
    (c : O) (hc : c ≠ 0) (D0 C : ℕ) : ∃ m : ℕ, ∀ (ι : Type) [Fintype ι] (Y : Type) [AddCommGroup Y] [Module O Y]
      (Φ : (ι → O) →ₗ[O] Y) (S : Set Y), Fintype.card ι = D0 + 1 →
      (∀ t, Φ t = 0 → ∀ a, c * t a ∈ maximalIdeal O ^ m) → (∀ t, Φ t ∈ S) → S.Finite →
      ¬ S.ncard ≤ Nat.card (ResidueField O) ^ (m * D0 + C) := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨v, e, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
  refine ⟨v + (v * D0 + C + 1), fun ι _ Y _ _ Φ S hι hker hS hfin hle => ?_⟩
  set k := v * D0 + C + 1 with hk
  have hcard : Nat.card (O ⧸ maximalIdeal O ^ k) = Nat.card (ResidueField O) ^ k :=
    cardQuot_pow_of_prime (IsDiscreteValuationRing.not_a_field O)
  choose s hs using Ideal.Quotient.mk_surjective (I := maximalIdeal O ^ k)
  let f : (ι → O ⧸ maximalIdeal O ^ k) → S := fun t => ⟨Φ fun a => s (t a), hS _⟩
  have hf : Function.Injective f := fun t t' h => by
    have h1 : Φ ((fun a => s (t a)) - fun a => s (t' a)) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact congrArg Subtype.val h
    funext a
    have h2 := hker _ h1 a
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton, pow_add, mul_assoc,
      Units.dvd_mul_left, mul_dvd_mul_iff_left (pow_ne_zero _ hϖ.ne_zero)] at h2
    rw [← hs (t a), ← hs (t' a), Ideal.Quotient.eq, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    exact h2
  haveI := hfin.to_subtype
  have h3 := (Nat.card_le_card_of_injective f hf).trans (le_of_eq_of_le (Nat.card_coe_set_eq S) hle)
  rw [Nat.card_fun, hcard, Nat.card_eq_fintype_card (α := ι), hι, ← pow_mul,
    Nat.pow_le_pow_iff_right Finite.one_lt_card] at h3
  nlinarith

section Tr

variable {n : ℕ} {R G : Type} [CommRing R] [Group G]

private theorem tr_lin (D : GDet n R G) (hn : 1 ≤ n) : ∃ t : MonoidAlgebra R G →ₗ[R] R, ∀ z, D.tr z = t z := by
  obtain ⟨t, ht⟩ := (UpperTheory.V.CA.d_tr D.toDet).1 hn
  exact ⟨t, fun z => ((UpperTheory.V.CA.d_toDet D z).2.2.1.symm.trans (ht z).symm)⟩

private theorem comap_tr {H : Type} [Group H] (D : GDet n R H) (φ : G →* H)
    (z : MonoidAlgebra R G) : (D.comap φ).tr z = D.tr (MonoidAlgebra.mapDomainRingHom R φ z) := by
  have hc : (D.comap φ).chi z = D.chi (MonoidAlgebra.mapDomainRingHom R φ z) := by
    change D.D _ (MonoidAlgebra.mapDomainRingHom (Polynomial R) φ _) = D.D _ _
    congr 1
    rw [map_sub]
    congr 1
    · simp
    · induction z using MonoidAlgebra.induction_linear with
      | zero => simp
      | add a b ha hb => simp only [map_add (f := _), ha, hb]
      | single g r => simp
  simp only [GDet.tr, GDet.lam, hc]

private theorem map_tr {S : Type} [CommRing S] (D : GDet n R G) (f : R →+* S) (z : MonoidAlgebra R G) :
    f (D.tr z) = (D.map f).tr (MonoidAlgebra.mapRingHom G f z) :=
  (((UpperTheory.V.CA.d_gmap D).2.2.1 f z).2 1).symm

private theorem ofRep_comap' {H : Type} [Group H] (ρ : G →* Matrix (Fin n) (Fin n) R) (φ : H →* G) :
    (GDet.ofRep ρ).comap φ = GDet.ofRep (ρ.comp φ) := by
  ext B _ _ z
  change (GDet.repAlg ρ B (MonoidAlgebra.mapDomainRingHom B φ z)).det = (GDet.repAlg (ρ.comp φ) B z).det
  congr 1
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | single g r => simp [GDet.repAlg]

private theorem mapRingHom_single_mul_partial_charpoly {S : Type} [CommRing S] (f : R →+* S) (E : ℕ) (ph ta : G) (u : Fin n → R) (i : Fin n) :
    MonoidAlgebra.mapRingHom G f (twoPowerModulus E ph ta u i 0) = twoPowerModulus E ph ta (fun k => f (u k)) i 0 := by
  have hs : ∀ (g : G) (c : R), MonoidAlgebra.mapRingHom G f (MonoidAlgebra.single g c) =
      MonoidAlgebra.single g (f c) := fun g c => by simp
  simp only [twoPowerModulus, map_mul, map_pow, map_sub, map_one, map_list_prod, List.map_ofFn, hs, map_zero]
  congr 4
  funext k
  by_cases hk : k = i
  · simp only [Function.comp_apply, if_pos hk, map_one]
  · simp only [Function.comp_apply, if_neg hk, map_sub, hs, map_one]

private theorem mapDomain_partial_charpoly_power_zero {H : Type} [Group H] (φ : G →* H) (E : ℕ) (ph ta : G) (u : Fin n → R) (i : Fin n)
    (h : φ ta = 1) : MonoidAlgebra.mapDomainRingHom R φ (twoPowerModulus E ph ta u i 0) = 0 := by
  have hs : MonoidAlgebra.mapDomainRingHom R φ (MonoidAlgebra.single ta 1) = 1 := by
    simp [h, MonoidAlgebra.one_def]
  simp only [twoPowerModulus, map_mul, map_sub, map_one, hs, MonoidAlgebra.single_zero, map_zero, sub_self, mul_zero]

private theorem kill_tr {O X : Type} [CommRing O] [Algebra O R] [AddCommGroup X] [Module O X] (D : GDet n R G)
    (hn : 1 ≤ n) (δ : R →ₗ[O] X) (h : ∀ g, δ (D.tr (MonoidAlgebra.single g 1)) = 0) (z : MonoidAlgebra O G) :
    δ (D.tr (MonoidAlgebra.mapRingHom G (algebraMap O R) z)) = 0 := by
  obtain ⟨t, ht⟩ := tr_lin D hn
  simp only [ht] at h ⊢
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb, add_zero]
  | single g a =>
    have : MonoidAlgebra.mapRingHom G (algebraMap O R) (MonoidAlgebra.single g a) =
        algebraMap O R a • MonoidAlgebra.single g (1 : R) := by
      rw [MonoidAlgebra.mapRingHom_single, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
    rw [this, map_smul, algebraMap_smul, map_smul, h, smul_zero]

end Tr

section Der

variable {O R X : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup X] [Module O X] {x : R →ₐ[O] O}

private theorem der_one {δ : R →ₗ[O] X} (h : IsDer x δ) : δ 1 = 0 := by
  have := h 1 1
  simpa using this

private theorem der_sum {ι : Type} [Fintype ι] (d : ι → R →ₗ[O] X) (h : ∀ a, IsDer x (d a)) (t : ι → O) :
    IsDer x (∑ a, t a • d a) := fun a b => by
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, h _ a b, smul_add, Finset.sum_add_distrib, Finset.smul_sum,
    smul_smul, mul_comm]

private theorem der_smul {δ : R →ₗ[O] X} (h : IsDer x δ) (c : O) : IsDer x (c • δ) := fun a b => by
  simp only [LinearMap.smul_apply, h a b, smul_add, smul_smul, mul_comm]

private theorem der_wt {δ : R →ₗ[O] X} (h : IsDer x δ) (c : O) (a : R) : δ (algebraMap O R c * a - 1) = c • δ a := by
  rw [map_sub, der_one h, sub_zero, ← Algebra.smul_def, map_smul]

end Der

theorem UpperTheory.V.Th.count :
    Count := by
  intro l _ L G0 T n O _ _ _ _ _ r B _ _ _ u J D b y x al hl hn had ⟨E, hA⟩ hgen hu hJ hEt hPL hEig ⟨C, hB⟩ δ0 hδ0 hw g0
  classical
  by_contra hd
  haveI : Finite (ResidueField O) := IsCoef.finite
  choose A hA using hA
  obtain ⟨c1, hc1, h1⟩ := coc l L G0 n O y hl hn
  obtain ⟨c2, hc2, h2⟩ := trPsi l L G0 n O y hn
  obtain ⟨c3, hc3, h3⟩ := split l L G0 T n O r B u J D b y x al E hn hgen hu hJ hEt hPL hEig
  set d := δ0 (u.D.tr (MonoidAlgebra.single g0 1)) with hdd
  obtain ⟨m, hm⟩ := cnt O (c1 * c2 * c3 * d) (mul_ne_zero (mul_ne_zero (mul_ne_zero hc1 hc2) hc3) hd) (D + n * T.q) C
  obtain ⟨N, ⟨hfin, hle⟩, h3N⟩ := ((hB m).and (h3 m)).exists
  obtain ⟨α, hα⟩ := h3N (A N) (hA N)
  clear hA
  generalize A N = A at hα
  choose δ hδ hδw hδq using hα
  have hIp : ∀ w, A.rN.Ip w = (T.GN N).frame.Iu w := fun w => by
    refine inf_eq_left.2 (le_iInf fun i => ?_)
    rintro _ ⟨g, hg, rfl⟩
    have e : (T.h N).p₀ ((T.GN N).φu w g) = G0.φu w g := Subtype.ext ((T.h N).φu w g)
    have hm : G0.φu w g ∈ r.Ip w := by
      rw [had.2 w]
      exact ⟨g, hg, rfl⟩
    rw [MonoidHom.mem_ker, A.compat.1 i, MonoidHom.comp_apply, e]
    exact (Subgroup.mem_iInf.1 hm.2) i
  have hmaps : A.p.Maps (x.comp A.β).toRingHom (GDet.ofRep (mat (y.ρ.comp (T.h N).p₀))) y.ψ := by
    refine ⟨?_, fun v i => ?_⟩
    · have e1 : A.p.D.map (x.comp A.β).toRingHom = (A.p.D.map A.β.toRingHom).map x.toRingHom := rfl
      have e2 : (u.D.comap (T.h N).p₀).map x.toRingHom = (u.D.map x.toRingHom).comap (T.h N).p₀ := rfl
      rw [e1, A.β_pair.1, e2, hu.1, ofRep_comap']
      rfl
    · rw [← hu.2 v i, ← A.β_pair.2 v i]
      rfl
  have hβtr : ∀ z, A.β (A.p.D.tr z) =
      u.D.tr (MonoidAlgebra.mapDomainRingHom B (T.h N).p₀ (MonoidAlgebra.mapRingHom _ A.β.toRingHom z)) := fun z => by
    rw [← comap_tr, ← A.β_pair.1]
    exact map_tr A.p.D A.β.toRingHom z
  let δs : A.R →ₗ[O] Om O m := Algebra.linearMap O (Om O m) ∘ₗ δ0 ∘ₗ A.β.toLinearMap
  have hδs_apply : ∀ a, δs a = algebraMap O (Om O m) (δ0 (A.β a)) := fun _ => rfl
  have hδs : IsDer (x.comp A.β) δs := fun a a' => by
    simp only [hδs_apply, map_mul, hδ0 _ _, map_add (f := _), smul_eq_mul, AlgHom.comp_apply, Algebra.smul_def]
  let ι := Option (Fin D ⊕ Fin T.q × Fin n)
  let e : ι → A.R →ₗ[O] Om O m := fun a => a.elim δs δ
  have he : ∀ a, IsDer (x.comp A.β) (e a) := fun a => by
    cases a
    · exact hδs
    · exact hδ _
  let Φ : (ι → O) →ₗ[O] ((T.GN N).G₀ → Om O m) :=
    Fintype.linearCombination O fun a g => c1 • e a (A.p.D.tr (MonoidAlgebra.single g 1))
  have hΦ : ∀ t g, Φ t g = c1 • (∑ a, t a • e a) (A.p.D.tr (MonoidAlgebra.single g 1)) := fun t g => by
    simp only [Φ, Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, Finset.smul_sum, smul_comm c1]
  have hev : ∀ (t : ι → O) z, (∑ a, t a • e a) z = t none • δs z + ∑ a, t (some a) • δ a z := fun t z => by
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    exact Fintype.sum_option _
  have hmem : ∀ a : O, a • (1 : Om O m) = 0 ↔ a ∈ maximalIdeal O ^ m := fun a => by
    rw [← Algebra.algebraMap_eq_smul_one]
    exact Ideal.Quotient.eq_zero_iff_mem
  refine hm ι _ Φ _ (by simp [ι, mul_comm]) (fun t ht => ?_) (fun t => ?_) hfin hle
  swap
  · obtain ⟨z, hz, hz'⟩ := h1 _ (T.h N) A.rN A.R A.p _ hIp hmaps m _ (der_sum e he t)
    exact ⟨z, hz, funext fun g => (hz' g).trans (hΦ t g).symm⟩
  have hk : ∀ g, (c1 • ∑ a, t a • e a) (A.p.D.tr (MonoidAlgebra.single g 1)) = 0 := fun g =>
    (hΦ t g).symm.trans (congrFun ht g)
  have hder := der_smul (der_sum e he t) c1
  have hsome : ∀ a, (c1 * c2 * c3 * t (some a)) • (1 : Om O m) = 0 := by
    rintro (k | ⟨j, i⟩)
    · have k1 := h2 _ (T.h N) A.rN A.R A.p _ hmaps _ _ hder hk (b.wt.v k) (b.wt.i k) (b.wt.γ k)
      have k2 : c2 • (c1 • ∑ a, t a • e a) (algebraMap (abelian₂ O Empty D) A.R (MvPowerSeries.X (.inr k))) = 0 := by
        rw [A.segmentWeightExponent, der_wt hder, smul_comm, k1, smul_zero]
      have k3 : δs (algebraMap (abelian₂ O Empty D) A.R (MvPowerSeries.X (.inr k))) = 0 := by
        have k4 : A.β (A.p.ψ (b.wt.v k) (b.wt.i k) (b.wt.γ k) : A.Rˣ) = (u.ψ (b.wt.v k) (b.wt.i k) (b.wt.γ k) : Bˣ) := by
          rw [← A.β_pair.2]
          rfl
        rw [A.segmentWeightExponent, der_wt hδs, hδs_apply, k4, hw, map_zero, smul_zero]
      rw [LinearMap.smul_apply, hev, k3] at k2
      simp only [hδw, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, zero_add] at k2
      simp only [Algebra.algebraMap_eq_smul_one, smul_smul] at k2
      rw [← k2]
      congr 1
      ring
    · have k1 := kill_tr A.p.D hn _ hk (twoPowerModulus E (T.ph N j) (T.ta N j) (α j) i 0)
      rw [mapRingHom_single_mul_partial_charpoly] at k1
      have k3 : δs (A.p.D.tr (twoPowerModulus E (T.ph N j) (T.ta N j) (fun k => algebraMap O A.R (α j k)) i 0)) = 0 := by
        obtain ⟨τ, hτ⟩ := tr_lin u.D hn
        rw [hδs_apply, hβtr, mapRingHom_single_mul_partial_charpoly, mapDomain_partial_charpoly_power_zero _ _ _ _ _ _ (Subtype.ext (T.ta_ker N j)), hτ, map_zero, map_zero, map_zero]
      rw [LinearMap.smul_apply, hev, k3] at k1
      simp only [hδq, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, zero_add] at k1
      simp only [Algebra.algebraMap_eq_smul_one, smul_smul] at k1
      have : c1 * c2 * c3 * t (some (.inr (j, i))) = c2 * (c1 * (t (some (.inr (j, i))) * c3)) := by ring
      rw [this, mul_smul, k1, smul_zero]
  rintro (_ | a)
  · obtain ⟨g', hg'⟩ := (T.h N).surj g0
    have hη : g' ∈ (T.GN N).η.ker := by
      rw [MonoidHom.mem_ker, ← (T.h N).η, hg']
      exact g0.2
    have e0 : (T.h N).p₀ ⟨g', hη⟩ = g0 := Subtype.ext hg'
    have k1 := hk ⟨g', hη⟩
    have k3 : δs (A.p.D.tr (MonoidAlgebra.single ⟨g', hη⟩ 1)) = d • (1 : Om O m) := by
      rw [hδs_apply, hβtr, MonoidAlgebra.mapRingHom_single, map_one, MonoidAlgebra.mapDomainRingHom_apply,
        MonoidAlgebra.mapDomain_single, e0, Algebra.algebraMap_eq_smul_one]
    rw [LinearMap.smul_apply, hev, k3] at k1
    have k4 := congrArg (fun w => (c2 * c3) • w) k1
    have k5 : ∀ a (w : Om O m), (c2 * c3) • c1 • t (some a) • w = 0 := fun a w => by
      have : (c2 * c3) • c1 • t (some a) • w = ((c1 * c2 * c3 * t (some a)) • (1 : Om O m)) * w := by
        rw [smul_mul_assoc, one_mul, smul_smul, smul_smul]
        congr 1
        ring
      rw [this, hsome, zero_mul]
    simp only [smul_add, Finset.smul_sum, k5, Finset.sum_const_zero, add_zero, smul_zero] at k4
    rw [← hmem, ← k4]
    simp only [smul_smul]
    congr 1
    ring
  · rw [← hmem]
    have : c1 * c2 * c3 * d * t (some a) = d * (c1 * c2 * c3 * t (some a)) := by ring
    rw [this, mul_smul, hsome, smul_zero]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.DerAdjoin
open UpperTheory.V UpperTheory.V.Th

namespace UpperTheory.V.Th.EtaleDerivations

open IsLocalRing Polynomial

variable {O B X : Type} [CommRing O] [CommRing B] [Algebra O B] [AddCommGroup X] [Module O X]

private theorem der_alg {x : B →ₐ[O] O} {δ : B →ₗ[O] X} (h : IsDer x δ) (c : O) : δ (algebraMap O B c) = 0 := by
  have h1 : δ 1 = 0 := by
    have := h 1 1
    simpa using this
  rw [Algebra.algebraMap_eq_smul_one, map_smul, h1, smul_zero]

private theorem der_adjoin {x : B →ₐ[O] O} {δ : B →ₗ[O] X} (h : IsDer x δ) {S : Set B} (hS : ∀ s ∈ S, δ s = 0)
    {a : B} (ha : a ∈ Algebra.adjoin O S) : δ a = 0 := by
  induction ha using Algebra.adjoin_induction with
  | mem s hs => exact hS s hs
  | algebraMap c => exact der_alg h c
  | add a b _ _ ha hb => rw [map_add (f := _), ha, hb, add_zero]
  | mul a b _ _ ha hb => rw [h, ha, hb, smul_zero, smul_zero, add_zero]

private theorem der_fg [IsNoetherianRing B] {x : B →ₐ[O] O} {δ : B →ₗ[O] X} (h : IsDer x δ) :
    (LinearMap.range δ).FG := by
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian (RingHom.ker x : Ideal B)
  have key : ∀ p ∈ Submodule.span B (s : Set B), δ p ∈ Submodule.span O (δ '' (s : Set B)) := by
    intro p hp
    induction hp using Submodule.span_induction with
    | mem a ha => exact Submodule.subset_span ⟨a, ha, rfl⟩
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul r a ha0 ha =>
      rw [hs] at ha0
      have : x a = 0 := ha0
      rw [smul_eq_mul, h, this, zero_smul, add_zero]
      exact Submodule.smul_mem _ _ ha
  have : LinearMap.range δ = Submodule.span O (δ '' (s : Set B)) := by
    apply le_antisymm
    · rintro _ ⟨b, rfl⟩
      have hb : b - algebraMap O B (x b) ∈ Submodule.span B (s : Set B) := by
        rw [hs]; show x _ = 0; simp
      have := key _ hb
      rwa [map_sub, der_alg h, sub_zero] at this
    · rw [Submodule.span_le]
      rintro _ ⟨b, _, rfl⟩
      exact ⟨b, rfl⟩
  rw [this]
  exact Submodule.fg_span (s.finite_toSet.image _)

private theorem der_zero [IsNoetherianRing B] [IsLocalRing O] [IsLocalRing B] [IsLocalHom (algebraMap O B)]
    {x : B →ₐ[O] O} {δ : B →ₗ[O] X} (h : IsDer x δ) {S : Set B} (hS : ∀ s ∈ S, δ s = 0)
    (hgen : ∀ b : B, ∃ a ∈ Algebra.adjoin O S, b - a ∈ maximalIdeal B ^ 2) (b : B) : δ b = 0 := by
  have hx : ∀ a ∈ maximalIdeal B, x a ∈ maximalIdeal O := by
    intro a ha hu
    have h1 : a - algebraMap O B (x a) ∈ maximalIdeal B := by
      intro hu'
      have := hu'.map x
      simp at this
    have h2 : algebraMap O B (x a) ∈ maximalIdeal B := by simpa using Ideal.sub_mem _ ha h1
    exact h2 (hu.map _)
  have hle : LinearMap.range δ ≤ maximalIdeal O • LinearMap.range δ := by
    rintro _ ⟨b, rfl⟩
    obtain ⟨a, ha, hb⟩ := hgen b
    have e : δ b = δ (b - a) := by rw [map_sub, der_adjoin h hS ha, sub_zero]
    rw [e]
    rw [pow_two] at hb
    refine Submodule.mul_induction_on hb (fun m hm k hk => ?_) (fun m k hm hk => ?_)
    · rw [h]
      exact add_mem (Submodule.smul_mem_smul (hx m hm) ⟨k, rfl⟩) (Submodule.smul_mem_smul (hx k hk) ⟨m, rfl⟩)
    · rw [map_add]; exact add_mem hm hk
  have := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal O) _ (der_fg h) hle
    (maximalIdeal_le_jacobson _)
  have hb : δ b ∈ LinearMap.range δ := ⟨b, rfl⟩
  rw [this] at hb
  simpa using hb

private theorem kill_red [IsDomain O] (x : B →ₐ[O] O) (I : Ideal B) (A : Subalgebra O B)
    (hred : ∀ t ∈ A, ∀ k : ℕ, t ^ k ∈ I → t ∈ I) {a : B} (ha : a ∈ A) (hx : x a = 0)
    (q : O[X]) (hq : q ≠ 0) (hI : aeval a q ∈ I) : ∃ s : B, x s ≠ 0 ∧ s * a ∈ I := by
  obtain ⟨g, hg, hd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd q hq 0
  refine ⟨aeval a g, ?_, ?_⟩
  · rw [← aeval_algHom_apply, hx]
    intro h0
    apply hd
    rw [dvd_iff_isRoot]
    simpa [coe_aeval_eq_eval] using h0
  · set k := rootMultiplicity 0 q
    have hgA : aeval a g ∈ A := (Algebra.adjoin_le (Set.singleton_subset_iff.2 ha)) (aeval_mem_adjoin_singleton O a)
    apply hred _ (A.mul_mem hgA ha) (k + 1)
    have e : (aeval a g * a) ^ (k + 1) = (aeval a g ^ k * a) * aeval a q := by
      conv_rhs => rw [hg]
      simp only [map_mul, map_pow, map_sub, aeval_X, aeval_C, map_zero, sub_zero]
      ring
    rw [e]
    exact I.mul_mem_left _ hI

private theorem det_trick [IsDomain O] [IsNoetherianRing B] (x : B →ₐ[O] O) (I : Ideal B)
    (h : ∀ a, x a = 0 → ∃ c : O, c ≠ 0 ∧ c • a ∈ RingHom.ker x * RingHom.ker x ⊔ I) :
    ∃ t : B, x t ≠ 0 ∧ ∀ a, x a = 0 → t * a ∈ I := by
  classical
  set P : Ideal B := RingHom.ker x with hP
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian P
  have h' : ∀ a : B, ∃ c : O, c ≠ 0 ∧ (a ∈ P → c • a ∈ P * P ⊔ I) := by
    intro a
    by_cases ha : x a = 0
    · obtain ⟨c, h1, h2⟩ := h a ha
      exact ⟨c, h1, fun _ => h2⟩
    · exact ⟨1, one_ne_zero, fun h => absurd h ha⟩
  choose f hf0 hf using h'
  set c : O := ∏ a ∈ s, f a
  have hc : c ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hf0 a
  have hcP : ∀ a ∈ P, algebraMap O B c * a ∈ P * P ⊔ I := by
    intro a ha
    rw [← hs] at ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
      have haP : a ∈ P := hs ▸ Submodule.subset_span ha
      obtain ⟨d, hd⟩ : f a ∣ c := Finset.dvd_prod_of_mem f ha
      rw [hd, mul_comm (f a), map_mul, mul_assoc, ← Algebra.smul_def (f a)]
      exact Ideal.mul_mem_left _ _ (hf a haP)
    | zero => simp
    | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
    | smul r a _ ha => rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_left _ _ ha
  let N : Submodule B (B ⧸ I) := Submodule.map (Submodule.mkQ I) P
  let φ : Module.End B N := algebraMap B _ (algebraMap O B c)
  have hφ : LinearMap.range φ ≤ P • ⊤ := by
    rintro _ ⟨⟨_, a, ha, rfl⟩, rfl⟩
    obtain ⟨y, hy, z, hz, e⟩ := Submodule.mem_sup.1 (hcP a ha)
    rw [Submodule.mem_smul_top_iff]
    have : ((φ ⟨_, a, ha, rfl⟩ : N) : B ⧸ I) = Submodule.mkQ I y := by
      show algebraMap O B c • Submodule.mkQ I a = _
      rw [← map_smul, smul_eq_mul, ← e, map_add (f := _)]
      have : Submodule.mkQ I z = 0 := (Submodule.Quotient.mk_eq_zero I).2 hz
      rw [this, add_zero]
    rw [this]
    refine Submodule.mul_induction_on hy (fun m hm k hk => ?_) (fun m k hm hk => ?_)
    · rw [← smul_eq_mul, map_smul]
      exact Submodule.smul_mem_smul hm ⟨k, hk, rfl⟩
    · rw [map_add]; exact add_mem hm hk
  obtain ⟨p, hp, -, hco, hev⟩ := LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero B φ P hφ
  refine ⟨p.eval (algebraMap O B c), ?_, fun a ha => ?_⟩
  · have e : p.map (x : B →+* O) = Polynomial.X ^ p.natDegree := by
      ext k
      rw [coeff_map, coeff_X_pow]
      rcases lt_trichotomy k p.natDegree with hk | hk | hk
      · rw [if_neg hk.ne]
        exact Ideal.pow_le_self (Nat.sub_ne_zero_of_lt hk) (hco k)
      · rw [if_pos hk, hk, hp.coeff_natDegree, map_one]
      · rw [if_neg hk.ne', coeff_eq_zero_of_natDegree_lt hk, map_zero]
    have e2 : x (p.eval (algebraMap O B c)) = c ^ p.natDegree := by
      have := (eval₂_at_apply (x : B →+* O) (algebraMap O B c) (p := p)).symm
      rw [eval₂_eq_eval_map, e] at this
      simpa using this
    rw [e2]
    exact pow_ne_zero _ hc
  · have := congrArg (fun ψ : Module.End B N => ((ψ ⟨_, a, ha, rfl⟩ : N) : B ⧸ I)) hev
    simp only [φ, aeval_algebraMap_apply, coe_aeval_eq_eval] at this
    have h2 : p.eval (algebraMap O B c) • Submodule.mkQ I a = 0 := this
    rw [← map_smul] at h2
    exact (Submodule.Quotient.mk_eq_zero I).1 h2

private theorem core [IsDomain O] [IsLocalRing O] [IsNoetherianRing B] [IsLocalRing B] [IsLocalHom (algebraMap O B)]
    (x : B →ₐ[O] O) (I : Ideal B) (S0 S : Set B)
    (hint : ∀ a : B, ∃ q : O[X], q ≠ 0 ∧ aeval a q ∈ I)
    (hred : ∀ t ∈ Algebra.adjoin O S0, ∀ k : ℕ, t ^ k ∈ I → t ∈ I)
    (hgen : ∀ b : B, ∃ a ∈ Algebra.adjoin O S, b - a ∈ maximalIdeal B ^ 2)
    (hder : ∀ (Y : Type) [AddCommGroup Y] [Module O Y] (δ : B →ₗ[O] Y), IsDer x δ →
      (∀ (c : O) (y : Y), c ≠ 0 → c • y = 0 → y = 0) → (∀ s ∈ S0, δ s = 0) → ∀ s ∈ S, δ s = 0) :
    ∃ t : B, x t ≠ 0 ∧ ∀ a, x a = 0 → t * a ∈ I := by
  apply det_trick x I
  let K : Ideal B := RingHom.ker x * RingHom.ker x ⊔ I
  let N : Submodule O B :=
    { carrier := {a | ∃ c : O, c ≠ 0 ∧ c • a ∈ K}
      add_mem' := by
        rintro a b ⟨c, hc, ha⟩ ⟨d, hd, hb⟩
        refine ⟨c * d, mul_ne_zero hc hd, ?_⟩
        rw [smul_add]
        refine add_mem ?_ ?_
        · rw [mul_comm, mul_smul]; exact Submodule.smul_of_tower_mem _ _ ha
        · rw [mul_smul]; exact Submodule.smul_of_tower_mem _ _ hb
      zero_mem' := ⟨1, one_ne_zero, by simp⟩
      smul_mem' := by
        rintro r a ⟨c, hc, ha⟩
        exact ⟨c, hc, by rw [smul_comm]; exact Submodule.smul_of_tower_mem _ _ ha⟩ }
  have hKN : ∀ a ∈ K, a ∈ N := fun a ha => ⟨1, one_ne_zero, by simpa using ha⟩
  let δ : B →ₗ[O] B ⧸ N := N.mkQ ∘ₗ (LinearMap.id - (Algebra.linearMap O B) ∘ₗ x.toLinearMap)
  have hδ : ∀ b, δ b = N.mkQ (b - algebraMap O B (x b)) := fun b => rfl
  have hδ0 : ∀ b, x b = 0 → (δ b = 0 ↔ b ∈ N) := by
    intro b hb
    rw [hδ, hb, map_zero, sub_zero]
    exact Submodule.Quotient.mk_eq_zero N
  have hk : ∀ b, x (b - algebraMap O B (x b)) = 0 := fun b => by simp
  have hD : IsDer x δ := by
    intro a b
    rw [hδ, hδ, hδ, ← map_smul, ← map_smul, ← map_add (f := _)]
    apply (Submodule.Quotient.eq N).2
    apply hKN
    have e : a * b - algebraMap O B (x (a * b)) - (x a • (b - algebraMap O B (x b)) + x b • (a - algebraMap O B (x a))) =
        (a - algebraMap O B (x a)) * (b - algebraMap O B (x b)) := by
      simp only [Algebra.smul_def, map_mul]; ring
    rw [e]
    exact Ideal.mem_sup_left (Ideal.mul_mem_mul (hk a) (hk b))
  have htf : ∀ (c : O) (y : B ⧸ N), c ≠ 0 → c • y = 0 → y = 0 := by
    intro c y hc hy
    obtain ⟨a, rfl⟩ := N.mkQ_surjective y
    rw [← map_smul] at hy
    obtain ⟨d, hd, h⟩ := (Submodule.Quotient.mk_eq_zero N).1 hy
    exact (Submodule.Quotient.mk_eq_zero N).2 ⟨d * c, mul_ne_zero hd hc, by rwa [mul_smul]⟩
  have h0 : ∀ s ∈ S0, δ s = 0 := by
    intro s hs
    have hsA : s - algebraMap O B (x s) ∈ Algebra.adjoin O S0 :=
      sub_mem (Algebra.subset_adjoin hs) (Subalgebra.algebraMap_mem _ _)
    obtain ⟨q, hq, hqI⟩ := hint (s - algebraMap O B (x s))
    obtain ⟨t, ht, hta⟩ := kill_red x I _ hred hsA (hk s) q hq hqI
    have h1 : δ (t * (s - algebraMap O B (x s))) = 0 :=
      (hδ0 _ (by rw [map_mul, hk, mul_zero])).2 (hKN _ (Ideal.mem_sup_right hta))
    rw [hD, hk, zero_smul, add_zero, map_sub, der_alg hD, sub_zero] at h1
    exact htf _ _ ht h1
  intro a ha
  exact (hδ0 a ha).1 (der_zero hD (hder _ δ hD htf h0) hgen a)

private theorem integ {Λ M : Type} [CommRing Λ] [Algebra O Λ] [Nontrivial O] [AddCommGroup M] [Module B M] [Module Λ M]
    [Module.Finite Λ M] (lam : Λ →ₐ[O] B) (hl : ∀ (a : Λ) (m : M), a • m = lam a • m) (ξ : Λ →ₐ[O] O) (a : B) :
    ∃ q : O[X], q ≠ 0 ∧ ∀ m : M, aeval a q • m ∈ (RingHom.ker ξ • ⊤ : Submodule Λ M) := by
  let φ : Module.End Λ M :=
    { toFun := fun m => a • m
      map_add' := fun m k => smul_add _ _ _
      map_smul' := fun r m => by simp only [RingHom.id_apply, hl]; rw [smul_comm] }
  obtain ⟨p, hp, hev⟩ := LinearMap.exists_monic_and_aeval_eq_zero Λ φ
  have hpow : ∀ (k : ℕ) (m : M), (φ ^ k) m = a ^ k • m := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => intro m; rw [pow_succ, pow_succ, Module.End.mul_apply, ih, mul_smul]; rfl
  have key : ∀ (p : Λ[X]) (m : M), aeval φ p m - aeval a (p.map (ξ : Λ →+* O)) • m ∈
      (RingHom.ker ξ • ⊤ : Submodule Λ M) := by
    intro p m
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      rw [Polynomial.map_add (f := _), map_add (f := _), map_add (f := _), add_smul, LinearMap.add_apply, add_sub_add_comm]
      exact add_mem hp hq
    | monomial k c =>
      have e : aeval φ (monomial k c) m - aeval a ((monomial k c).map (ξ : Λ →+* O)) • m =
          (c - algebraMap O Λ (ξ c)) • (a ^ k • m) := by
        rw [Polynomial.map_monomial, aeval_monomial, aeval_monomial, Module.End.mul_apply, hpow, sub_smul,
          hl (algebraMap O Λ (ξ c)), AlgHom.commutes, mul_smul]
        rfl
      rw [e]
      exact Submodule.smul_mem_smul (by show ξ _ = 0; simp) trivial
  refine ⟨p.map (ξ : Λ →+* O), (hp.map _).ne_zero, fun m => ?_⟩
  have := key p m
  rw [hev, LinearMap.zero_apply, zero_sub] at this
  exact neg_mem_iff.1 this

end UpperTheory.V.Th.EtaleDerivations

open UpperTheory.V.Th.EtaleDerivations UpperTheory.V.Pa UpperTheory.V.W UpperTheory.V.Alg in
theorem UpperTheory.V.Th.etOf :
    EtOf := by
  intro l _ L G0 n O _ _ _ _ _ r B _ _ _ u J D b y x hn hmap hgen hctrl
  let I : Ideal B :=
    { carrier := {a | ∀ m : b.M, a • m ∈ wtSub b x}
      add_mem' := fun ha hb m => by rw [add_smul]; exact add_mem (ha m) (hb m)
      zero_mem' := fun m => by rw [zero_smul]; exact zero_mem _
      smul_mem' := fun c a ha m => by rw [smul_eq_mul, mul_comm, mul_smul]; exact ha _ }
  obtain ⟨c, hc, hψ⟩ := trPsi l L G0 n O y hn
  haveI := b.fin
  refine core x I {a : B | ∃ i g, a = u.D.lam i (MonoidAlgebra.single g 1)} (pairVals u)
    (fun a => integ b.lam b.smul_lam (x.comp b.lam) a) hctrl (hgen 2) ?_
  intro Y _ _ δ hδ htf h0 s hs
  rcases hs with hs | ⟨v, i, g, rfl⟩
  · exact h0 s hs
  · exact htf c _ hc (hψ G0 (Glob.Hom.refl G0) r B u x hmap Y δ hδ (fun g => h0 _ ⟨1, g, rfl⟩) v i g)
end

open UpperTheory.V UpperTheory.V.Th

namespace UpperTheory.V.Th.NormTraceLemmas

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem coef_isCoef (l : ℕ) [hl : Fact l.Prime] (c : HV.Coef l) : Pa.IsCoef l c.O := by
  obtain ⟨hc, hf, hlm, -, -, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  refine ⟨hc, hf, (CharP.charP_iff_prime_eq_zero hl.out).2 ?_⟩
  rw [← map_natCast (IsLocalRing.residue c.O), IsLocalRing.residue_eq_zero_iff]
  exact hlm

private theorem locP_of (P : GlobalTheory.Mem.LiteralAutomorphy.LitN) : Pa.LocP :=
  ⟨GlobalTheory.LocLanglandsBridge.localLanglandsGL_of_depthZero_zelevinsky_bernstein P.loc.llc P.loc.conv P.loc.dzc P.loc.dzi P.loc.brauer P.loc.chev P.aut.art
               P.loc.exh P.loc.multi P.loc.cos P.loc.zel P.loc.geo P.loc.bz,
    P.loc.bz, P.loc.geo, GlobalTheory.Published.TameLocal_of_duality P.coh.lt⟩

private theorem chi_ofRep {n : ℕ} {A G : Type} [CommRing A] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    (GDet.ofRep ρ).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly := by
  change (GDet.repAlg ρ (Polynomial A) _).det = _
  rw [map_sub, MonoidAlgebra.mapRingHom_single, Matrix.charpoly]
  congr 1
  ext i j : 2
  by_cases h : i = j <;> simp [GDet.repAlg, Matrix.charmatrix, h, Matrix.one_apply, Matrix.diagonal_apply]

private theorem map_ofRep {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A)
    (f : A →+* B) : (GDet.ofRep ρ).map f = GDet.ofRep (f.mapMatrix.toMonoidHom.comp ρ) := by
  refine GDet.ext fun C _ _ x => ?_
  letI : Algebra A C := ((algebraMap B C).comp f).toAlgebra
  change (GDet.repAlg ρ C x).det = (GDet.repAlg _ C x).det
  congr 2

private theorem unip_pow (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] (n m : ℕ)
    (M : Matrix (Fin n) (Fin n) O) (hM : (M.map (residue O)).charpoly = (Polynomial.X - 1) ^ n) (i j : Fin n) :
    (M ^ l ^ (n + m) - 1) i j ∈ maximalIdeal O ^ m := by
  have hl : l.Prime := Fact.out
  haveI : Nonempty (Fin n) := ⟨i⟩
  have h0 := Matrix.aeval_self_charpoly (M.map (residue O))
  rw [hM] at h0
  simp only [map_pow, map_sub, Polynomial.aeval_X, map_one] at h0
  have h1 : (residue O).mapMatrix (M ^ l ^ n) = 1 := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Nat.lt_pow_self hl.one_lt (n := n)).le
    have h4 := sub_pow_char_pow_of_commute l n (Commute.one_right (M.map (residue O)))
    rw [one_pow] at h4
    rw [map_pow, ← sub_eq_zero]
    refine h4.symm.trans ?_
    rw [hd, pow_add, h0, zero_mul]
  have h2 : ∀ k, (residue O).mapMatrix (M ^ l ^ (n + k)) = 1 := fun k => by
    rw [pow_add, pow_mul, map_pow, h1, one_pow]
  induction m generalizing i j with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, pow_succ l, pow_mul, ← mul_geom_sum, Matrix.mul_apply, pow_succ]
    refine Ideal.sum_mem _ fun a _ => Ideal.mul_mem_mul (ih i a) ?_
    have h3 : (residue O).mapMatrix (∑ t ∈ Finset.range l, (M ^ l ^ (n + k)) ^ t) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_pow (residue O).mapMatrix (M ^ l ^ (n + k)), h2, one_pow]
      simp
    exact (residue_eq_zero_iff _).1 (congrFun (congrFun h3 a) j)

private theorem rhoPLO (l : ℕ) [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [CharP (ResidueField O) l] (n : ℕ) (ρ : F.G₀ →* GL (Fin n) O)
    (hc : ∀ i j, AdicCont (maximalIdeal O) fun g => mat ρ g i j) (H : OpenNormalSubgroup F.Γ)
    (hH : ∀ g ∈ H, ∃ h : F.η g = 1, ((mat ρ ⟨g, h⟩).map (residue O)).charpoly = (Polynomial.X - 1) ^ n)
    (g : F.G₀) (hg : (g : F.Γ) ∈ PL l H.toSubgroup) : ρ g = 1 := by
  have key : ∀ (m : ℕ) (i j : Fin n), (mat ρ g - 1) i j ∈ maximalIdeal O ^ m := by
    intro m
    let π := Ideal.Quotient.mk (maximalIdeal O ^ m)
    let Km : Subgroup F.G₀ := (π.mapMatrix.toMonoidHom.comp (mat ρ)).toHomUnits.ker
    have hKm : ∀ a : F.G₀, a ∈ Km ↔ ∀ i j, π (mat ρ a i j) = π ((1 : Matrix (Fin n) (Fin n) O) i j) := by
      intro a
      rw [MonoidHom.mem_ker, Units.ext_iff, MonoidHom.coe_toHomUnits, Units.val_one, ← map_one π.mapMatrix,
        ← Matrix.ext_iff]
      rfl
    have hKm' : ∀ a : F.G₀, a ∈ Km ↔ ∀ i j, (mat ρ a - 1) i j ∈ maximalIdeal O ^ m := by
      intro a
      simp only [hKm, Matrix.sub_apply, π, Ideal.Quotient.eq]
    have ho : IsOpen (Km : Set F.G₀) := by
      have : (Km : Set F.G₀) = ⋂ i, ⋂ j, {a | π (mat ρ a i j) = π ((1 : Matrix (Fin n) (Fin n) O) i j)} := by
        ext a
        simp only [SetLike.mem_coe, hKm, Set.mem_iInter, Set.mem_setOf_eq]
      rw [this]
      exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => (hc i j m).isOpen_fiber _
    let K' : Subgroup F.Γ := Km.map F.η.ker.subtype
    have ho' : IsOpen (K' : Set F.Γ) := F.η_open.isOpenMap_subtype_val _ ho
    haveI : Finite (F.Γ ⧸ K') := Subgroup.quotient_finite_of_isOpen K' ho'
    haveI : K'.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    have hc : IsOpen (K'.normalCore : Set F.Γ) :=
      Subgroup.isOpen_of_isClosed_of_finiteIndex _ (K'.normalCore_isClosed (K'.isClosed_of_isOpen ho'))
    let U : OpenNormalSubgroup F.Γ := ⟨⟨K'.normalCore, hc⟩, K'.normalCore_normal⟩
    have hU : ∀ h ∈ H.toSubgroup, ∃ e : ℕ, h ^ l ^ e ∈ U := by
      intro h hh
      refine ⟨n + m, fun b => ?_⟩
      obtain ⟨h1, h2⟩ := hH (b * h * b⁻¹) (H.isNormal'.conj_mem h hh b)
      refine ⟨(⟨b * h * b⁻¹, h1⟩ : F.G₀) ^ l ^ (n + m), ?_, ?_⟩
      · rw [SetLike.mem_coe, hKm', map_pow]
        exact unip_pow l O n m _ h2
      · simp only [Subgroup.coe_subtype, SubgroupClass.coe_pow, conj_pow]
    have h3 : (g : F.Γ) ∈ K'.normalCore := Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hg U) hU
    obtain ⟨a, ha, hag⟩ := K'.normalCore_le h3
    obtain rfl : a = g := Subtype.ext hag
    exact (hKm' a).1 ha
  apply Units.ext
  ext1 i j
  have h0 : (mat ρ g - 1) i j ∈ (⨅ m : ℕ, maximalIdeal O ^ m) := Ideal.mem_iInf.2 fun m => key m i j
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal O).ne_top, Ideal.mem_bot, Matrix.sub_apply,
    sub_eq_zero] at h0
  exact h0

private theorem red_unip {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] [Algebra ℤ_[l] O] {n : ℕ} {r : Resid F O n} {B : Type} [CommRing B] [Algebra O B]
    [IsCO O B] (u : Pair r B) (x : B →ₐ[O] O) (ρ : F.G₀ →* GL (Fin n) O) (h : u.D.map x.toRingHom = GDet.ofRep (mat ρ))
    (g : F.G₀) (hg : ∀ i, r.chib i g = 1) : ((mat ρ g).map (residue O)).charpoly = (Polynomial.X - 1) ^ n := by
  have e0 : (residue O).comp x.toRingHom = (res O B : B →+* ResidueField O) := RingHom.ext fun a =>
    ((res O O).commutes (x a)).symm.trans (res_map x a)
  have e3 : (GDet.ofRep (mat ρ)).map (residue O) = r.Dbar := by
    rw [← h, ← u.red, ← e0]
    rfl
  rw [map_ofRep, Resid.Dbar] at e3
  have e4 := congrArg (·.chi (MonoidAlgebra.single g 1)) e3
  simp only [chi_ofRep] at e4
  refine e4.trans ?_
  have e5 : W.diagRep r.chib g = 1 := by
    change Matrix.diagonal _ = _
    simp only [hg, Units.val_one, Matrix.diagonal_one]
  rw [e5, Matrix.charpoly_one, Fintype.card_fin]

end UpperTheory.V.Th.NormTraceLemmas

open UpperTheory.V.Th.NormTraceLemmas UpperTheory.V.Pa UpperTheory.V.W UpperTheory.V.Alg in
theorem UpperTheory.V.Th.coreO :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → CoreO := by
  intro hN l _ L Ω _ _ _ _ _ _ s V0 c n r B J y x h q sg al hS hn hLev hJ hAr hmap hN4 hsg hdet δ hδ h0
  have hC : Pa.CohP := ⟨hN.coh.lf, hN.coh.lt, hN.coh.le, hN.coh.gf, hN.coh.ge, hN.coh.gw, hN.coh.pt,
    GlobalTheory.Published.TameLocal_of_duality hN.coh.lt⟩
  haveI := _root_.coef_isCoef l c
  haveI := IsCoef.char (l := l) (O := c.O)
  haveI := IsCoef.finite (l := l) (O := c.O)
  haveI := IsCoef.complete (l := l) (O := c.O)
  obtain ⟨b, hb, hγ, hctrl⟩ := hLev
  obtain ⟨T, ⟨Pl⟩, rfl, hTs⟩ := (arPl hC l L Ω s V0 c.O n r hS).2 q sg fun j => (hsg j).1
  obtain rfl : T.sg = sg := funext hTs
  have hI := (ipEq l L Ω s V0 c.O n r).1
  have hgen : GenBy c.O (pairVals (pairOf B.u)) := fun N b => by
    obtain ⟨c, hc, hb⟩ := CA.exists_adjoin_coeff_character_sub_mem_maximalIdeal_pow r B N b
    refine ⟨c, Algebra.adjoin_mono ?_ hc, hb⟩
    rintro _ (⟨a, g, -, -, rfl⟩ | e)
    · exact Or.inl ⟨a, g, rfl⟩
    · exact Or.inr e
  have hmap' : (pairOf B.u).Maps x.toRingHom (GDet.ofRep (mat y.ρ)) y.ψ := hmap
  have hker : ∀ g : V0.frame.G₀, (g : V0.frame.Γ) ∈ PL l T.H.toSubgroup → y.ρ g = 1 := by
    refine rhoPLO l (globOf r V0).frame c.O n y.ρ y.cont T.H fun g hg => ?_
    obtain ⟨e1, e2, -⟩ := (Pl.H_eq g).1 hg
    exact ⟨e1, red_unip (pairOf B.u) x y.ρ hmap'.1 ⟨g, e1⟩ e2⟩
  have heig : Eig y T al := fun j => (hsg j).2
  exact count l _ (globOf r V0) T n c.O (residOf r) B.B (pairOf B.u) J _ b y x al s.odd hn
    ⟨fun g hg a => ((Pl.H_eq g).1 hg).2.1 a, fun u => (hI u).2⟩
    (hasOp (locP_of hN) l L Ω s V0 c.O n r B J _ b hb T Pl) hgen hmap' hJ
    (etOf l _ (globOf r V0) n c.O (residOf r) B.B (pairOf B.u) J _ b y x hn hmap' hgen (hctrl x h hAr)) hker heig
    (b1O hC l L Ω s V0 c n r T Pl y al hS (W.locCFT hN.aut.art hC l L Ω s) hn hker hN4 heig hdet)
    δ hδ fun k => h0 _ _ _ (hγ k)

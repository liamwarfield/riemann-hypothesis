module

public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CubWeilOfInjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BiadditiveOfTrivAxes
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyPolAVGenericFibreWithLieBasis
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBMapPf

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsTorusExtensionPointsPullbackFieldPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsTorusExtensionPointsPullbackFieldPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaPair

theorem exists_pullEquiv {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {f : S' ⟶ S} {t : SAB H S} {t' : SAB H S'} (m : SABMap t' t f) (n : ℕ) {Y : Scheme.{0}} (a : Y ⟶ S')
    (u : Y ⟶ S) (hu : a ≫ f = u) :
    ∃ e : (Over.mk u ⟶ t.G) ≃* (Over.mk a ⟶ t'.G), (∀ x, (e x).left ≫ m.cm.F = x.left) ∧
      ∀ x y, CubWeil t.cub n x y 1 → CubWeil t'.cub n (e x) (e y) 1 := by
  subst hu
  have hw : m.cm.F ≫ t.G.hom = t'.G.hom ≫ f := m.cart.1.w
  have mul : ∀ (T : Over S') (x y : T ⟶ t'.G), Out.toBase hw (x * y) = Out.toBase hw x * Out.toBase hw y :=
    fun T x y => Over.OverMorphism.ext (m.cart.2 T x y (Out.toBase hw x) (Out.toBase hw y) rfl rfl).symm
  let β : (Over.mk a ⟶ t'.G) →* (Over.mk (a ≫ f) ⟶ t.G) := GlobalTheory.UU.toBaseHom mul (Over.mk a)
  have hβ : Function.Bijective β := by
    refine ⟨fun x y e => Over.OverMorphism.ext
      (m.cart.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w])), fun x => ?_⟩
    exact ⟨Over.homMk (m.cart.1.lift x.left a (Over.w x)) (m.cart.1.lift_snd _ _ _),
      Over.OverMorphism.ext (m.cart.1.lift_fst _ _ _)⟩
  let e := (MulEquiv.ofBijective β hβ).symm
  have he : ∀ x, β (e x) = x := fun x => (MulEquiv.ofBijective β hβ).apply_symm_apply x
  refine ⟨e, fun x => congrArg (fun q => q.left) (he x), fun x y h => ?_⟩
  obtain ⟨ζ, hζ, -⟩ := GlobalTheory.UU.existsUnique_cubWeil t'.cub (N := n) (x := e x) (y := e y)
    (by rw [← map_pow, h.1, map_one]) (by rw [← map_pow, h.2.1, map_one])
  have h' : CubWeil t.cub n (β (e x)) (β (e y)) ζ :=
    GlobalTheory.UU.cubWeil_of_isPullCubical S S' f t.G t'.G m.cm hw mul _ _ t.cub t'.cub m.lin n _ _ _ ζ hζ
  rw [he, he] at h'
  obtain rfl : ζ = 1 := h'.unique h
  exact hζ

theorem exists_isTorExt_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (f : S' ⟶ S) (t : SAB H S) (t' : SAB H S') (_ : SABMap t' t f) (Ω : Type) [Field Ω] (s : Sp Ω ⟶ S) (s' : Sp Ω ⟶ S'), s' ≫ f = s → ∀ n : ℕ, ∃ (τ : PtHom s s' t.G t'.G) (io : TorHom s t.G PUnit), IsTorExt s s' t.G t'.G PUnit τ io ∧ Transfer n t.cub t'.cub τ := by
  intro E _ _ _ H S S' f t t' m Ω _ s s' hs n
  have key : ∀ (A : Type) [CommRing A] [Algebra Ω A], ∃ e : (overAt s A ⟶ t.G) ≃* (overAt s' A ⟶ t'.G),
      (∀ x, (e x).left ≫ m.cm.F = x.left) ∧ ∀ x y, CubWeil t.cub n x y 1 → CubWeil t'.cub n (e x) (e y) 1 :=
    fun A _ _ => exists_pullEquiv m n _ _ (by rw [Category.assoc, hs])
  choose e he hc using key
  have nat : ∀ (A A' : Type) [CommRing A] [Algebra Ω A] [CommRing A'] [Algebra Ω A'] (g : A →ₐ[Ω] A')
      (x : overAt s A ⟶ t.G), e A' (homAt s g ≫ x) = homAt s' g ≫ e A x := by
    intro A A' _ _ _ _ g x
    refine Over.OverMorphism.ext (m.cart.1.hom_ext ?_ (by rw [Over.w, Over.w]))
    rw [he, Over.comp_left, Over.comp_left, Category.assoc, he]
    rfl
  refine ⟨fun A _ _ => (e A).toMonoidHom, fun A _ _ => 1, ⟨nat, ?_, ?_, ?_, ?_⟩, fun A _ _ => hc A⟩
  · intro A A' _ _ _ _ g χ
    exact (MonObj.comp_one _).symm
  · intro A _ _ χ χ' _
    exact MonoidHom.ext fun x => by rw [Subsingleton.elim x 1, map_one, map_one]
  · intro A _ _ x
    exact (e A).map_eq_one_iff.trans ⟨fun h => ⟨1, h.symm⟩, fun ⟨_, h⟩ => h.symm⟩
  · intro A _ _ π _ y hy
    refine ⟨(e A).symm y, (e Ω).map_eq_one_iff.1 ?_, (e A).apply_symm_apply y⟩
    rw [nat, (e A).apply_symm_apply, hy]

end GlobalTheory.AlphaPair
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsTorusExtensionPointsPullbackFieldPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torusExtension_points_pullback_fieldPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (f : S' ⟶ S) (t : SAB H S) (t' : SAB H S') (_ : SABMap t' t f) (Ω : Type) [Field Ω] (s : Sp Ω ⟶ S) (s' : Sp Ω ⟶ S'), s' ≫ f = s → ∀ n : ℕ, ∃ (τ : PtHom s s' t.G t'.G) (io : TorHom s t.G PUnit), IsTorExt s s' t.G t'.G PUnit τ io ∧ Transfer n t.cub t'.cub τ := by
  first | exact @GlobalTheory.AlphaPair.exists_isTorExt_pull | exact GlobalTheory.AlphaPair.exists_isTorExt_pull | (intros; apply GlobalTheory.AlphaPair.exists_isTorExt_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsGeneratorOfRosatiAdjointLambdaBundle
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsGeneratorOfRosatiAdjointLambdaBundle
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RosGen

private theorem lbIso_of_local {O : Type} [CommRing O] [IsLocalRing O] {A : Over (Geo.Tor.Sp O)} [GrpObj A]
    [IsCommMonObj A] {L : LB A.left} (hL : L.IsLB) (f g : A ⟶ A) (h : Out.RosatiAdj A L f g) :
    Geo.Tor.LBIso (cubeLB A ![fst A A ≫ f, snd A A] L) (cubeLB A ![fst A A, snd A A ≫ g] L) := by
  obtain ⟨U, hs, t, ht⟩ := h (IsLocalRing.closedPoint O)
  have hU : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).1 hs
  obtain ⟨n, hn⟩ : ∃ n : (A ⊗ A).left ⟶ ((A ⊗ A).hom ⁻¹ᵁ U).toScheme,
      n ≫ ((A ⊗ A).hom ⁻¹ᵁ U).ι = 𝟙 _ :=
    ⟨IsOpenImmersion.lift ((A ⊗ A).hom ⁻¹ᵁ U).ι (𝟙 _) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι, hU]
      trivial), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨u, hu, -⟩ := Geo.Tor.exists_gen hL (φ' := Out.rosatiφ A f g) (ε' := Out.rosatiε)
    (fun V _ k => Finset.prod_congr rfl fun i _ => by
      show k (n ≫ _ ≫ _) ^ _ = k _ ^ _
      rw [← Category.assoc, hn, Category.id_comp])
    (LB.pullGen L _ _ t n) (DVR.pullGen_isGen _ _ _ _ ht n)
  exact GlobalTheory.RosLam.lbIso_of_gen hL f g u hu

private theorem prod_two {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {T : Over S} (x y : T ⟶ G)
    {U : Type 1} [CommGroup U] (h : (T.left ⟶ G.left) → U) :
    ∏ I : ULift.{0} (Finset (Fin 2)), h (psum G ![x, y] I.down).left ^ ((-1 : ℤ) ^ (2 - I.down.card)) =
      h (x * y).left * (h x.left)⁻¹ * (h y.left)⁻¹ * h (1 : T ⟶ G).left := by
  have key := GlobalTheory.NormRos.prod_square x y (U := Multiplicative (FreeAbelianGroup (T.left ⟶ G.left)))
    (fun ψ => Multiplicative.ofAdd (FreeAbelianGroup.of ψ))
  have k := congrArg (AddMonoidHom.toMultiplicativeLeft
    (FreeAbelianGroup.lift fun ψ : T.left ⟶ G.left => Additive.ofMul (h ψ))) key
  simpa only [map_mul, map_inv, map_prod, map_zpow, AddMonoidHom.coe_toMultiplicativeLeft, Function.comp_apply,
    toAdd_ofAdd, FreeAbelianGroup.lift_apply_of, toMul_ofMul] using k

theorem exists_gen_of_rosatiAdj : ∀ (O : Type) [CommRing O] [IsLocalRing O] (P : Out.PolAV (Geo.Tor.Sp O)) (Z : Scheme.{0}) (Q : LB Z) (ψ₂ : (P.A ⊗ P.A).left ⟶ Z), Q.IsLB → Geo.Tor.LBIso (abelian₂ P.A P.L) (Q.pull ψ₂) → ∀ f f' : P.A ⟶ P.A, IsMonHom f → IsMonHom f' → Out.RosatiAdj P.A P.L f f' → ∃ t : LB.Gen (LB.LinComb Q (K := Fin 2) ![(lift (fst P.A P.A ≫ f) (snd P.A P.A)).left ≫ ψ₂, (lift (fst P.A P.A) (snd P.A P.A ≫ f')).left ≫ ψ₂] ![1, -1]), t.IsGen := by
  intro O _ _ P Z Q ψ₂ hQ hI f f' _ _ h
  have := P.isAb.comm
  have H := lbIso_of_local P.isLB f f' h
  obtain ⟨Pic, _, cl, pl, h₁, h₂, -, h₄, h₅, -⟩ := GlobalTheory.CechPicMul.exists_picardGroup
  obtain ⟨a, a'⟩ : (abelian₂ P.A P.L).IsLB ∧ cl (abelian₂ P.A P.L) = _ := h₅ _ _ P.L P.isLB _ _ _
  obtain ⟨q, q'⟩ : (Q.pull ψ₂).IsLB ∧ cl (Q.pull ψ₂) = _ := h₅ _ _ Q hQ _ _ _
  have e₀ : pl ψ₂ (cl Q) = cl (abelian₂ P.A P.L) := by
    rw [(h₁ _ _ _ a q).2 hI, q']; simp
  have key : ∀ x y : P.A ⊗ P.A ⟶ P.A, (cubeLB P.A ![x, y] P.L).IsLB ∧
      pl ((lift x y).left ≫ ψ₂) (cl Q) = cl (cubeLB P.A ![x, y] P.L) := fun x y => by
    obtain ⟨b, b'⟩ : (cubeLB P.A ![x, y] P.L).IsLB ∧ cl (cubeLB P.A ![x, y] P.L) = _ := h₅ _ _ P.L P.isLB _ _ _
    refine ⟨b, ?_⟩
    rw [h₄, e₀, a', b']
    have p₁ := prod_two x y (fun φ => pl φ (cl P.L))
    have p₂ := prod_two (fst P.A P.A) (snd P.A P.A) (fun φ => pl φ (cl P.L))
    refine Eq.trans (congrArg (pl (lift x y).left) p₂) (Eq.trans ?_ p₁.symm)
    simp only [map_mul, map_inv, ← h₄, ← Over.comp_left, MonObj.comp_mul, MonObj.comp_one, lift_fst, lift_snd]
  obtain ⟨c, c'⟩ := h₅ _ _ Q hQ (Fin 2)
    ![(lift (fst P.A P.A ≫ f) (snd P.A P.A)).left ≫ ψ₂, (lift (fst P.A P.A) (snd P.A P.A ≫ f')).left ≫ ψ₂] ![1, -1]
  refine (h₂ _ _ c).1 ?_
  rw [c', Fin.prod_univ_two]
  show pl ((lift (fst P.A P.A ≫ f) (snd P.A P.A)).left ≫ ψ₂) (cl Q) ^ (1 : ℤ) *
    pl ((lift (fst P.A P.A) (snd P.A P.A ≫ f')).left ≫ ψ₂) (cl Q) ^ (-1 : ℤ) = 1
  rw [(key _ _).2, (key _ _).2, (h₁ _ _ _ (key _ _).1 (key _ _).1).2 H]
  simp

end GlobalTheory.RosGen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsGeneratorOfRosatiAdjointLambdaBundleStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_of_rosatiAdjoint_lambdaBundle : ∀ (O : Type) [CommRing O] [IsLocalRing O] (P : Out.PolAV (Geo.Tor.Sp O)) (Z : Scheme.{0}) (Q : LB Z) (ψ₂ : (P.A ⊗ P.A).left ⟶ Z), Q.IsLB → Geo.Tor.LBIso (abelian₂ P.A P.L) (Q.pull ψ₂) → ∀ f f' : P.A ⟶ P.A, IsMonHom f → IsMonHom f' → Out.RosatiAdj P.A P.L f f' → ∃ t : LB.Gen (LB.LinComb Q (K := Fin 2) ![(lift (fst P.A P.A ≫ f) (snd P.A P.A)).left ≫ ψ₂, (lift (fst P.A P.A) (snd P.A P.A ≫ f')).left ≫ ψ₂] ![1, -1]), t.IsGen := by
  first | exact @GlobalTheory.RosGen.exists_gen_of_rosatiAdj | exact GlobalTheory.RosGen.exists_gen_of_rosatiAdj | (intros; apply GlobalTheory.RosGen.exists_gen_of_rosatiAdj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.JetRingHomExistsUniqueSpec
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.JetRingHomExistsUniqueSpec
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaPair.JetEv

theorem prod_pow_mem_span_pow {A κ : Type} [CommRing A] [Fintype κ] (a : κ → A) (e : κ → ℕ) :
    ∏ i, a i ^ e i ∈ Ideal.span (Set.range a) ^ (∑ i, e i) := by
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self i)) _

theorem jet_hom_spec : ∀ (V Ω A : Type) [CommRing V] [CommRing Ω] [CommRing A] [Algebra Ω A] (β : V →+* Ω) (κ : Type) [Fintype κ] [DecidableEq κ] (m : ℕ), (∀ a : κ → A, Ideal.span (Set.range a) ^ (m + 1) = ⊥ → ∃! ψ : Jet V κ m →+* A, (∀ v : V, ψ (algebraMap V _ v) = algebraMap Ω A (β v)) ∧ ∀ i, ψ (Ideal.Quotient.mk _ (MvPolynomial.X i)) = a i) ∧ ∀ ψ : Jet V κ m →+* A, (∀ v : V, ψ (algebraMap V _ v) = algebraMap Ω A (β v)) → Ideal.span (Set.range fun i => ψ (Ideal.Quotient.mk _ (MvPolynomial.X i))) ^ (m + 1) = ⊥ ∧ (∀ i, IsNilpotent (ψ (Ideal.Quotient.mk _ (MvPolynomial.X i)))) ∧ ∀ f : MvPowerSeries κ V, ψ (psJet m f) = nEval (MvPowerSeries.map β f) (fun i => ψ (Ideal.Quotient.mk _ (MvPolynomial.X i))) := by
  intro V Ω A _ _ _ _ β κ _ _ m
  refine ⟨fun a ha => ?_, fun ψ hψ => ?_⟩
  · letI : Algebra V A := ((algebraMap Ω A).comp β).toAlgebra
    let φ : Jet V κ m →ₐ[V] A := liftJet (MvPolynomial.aeval a) (by simpa using ha)
    have hφ : ∀ i, φ (Ideal.Quotient.mk _ (MvPolynomial.X i)) = a i := fun i =>
      MvPolynomial.aeval_X a i
    refine ⟨(φ : Jet V κ m →+* A), ⟨fun v => φ.commutes v, hφ⟩, ?_⟩
    rintro ψ ⟨h1, h2⟩
    refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun v => ?_) fun i => ?_)
    · exact (h1 v).trans (φ.commutes v).symm
    · exact (h2 i).trans (hφ i).symm
  · set a : κ → A := fun i => ψ (Ideal.Quotient.mk _ (MvPolynomial.X i)) with ha
    have h0 : Ideal.span (Set.range a) ^ (m + 1) = ⊥ := by
      have := map_orig_pow (ψ.comp (Ideal.Quotient.mk (orig V κ ^ (m + 1)))) (m + 1)
      rw [← Ideal.map_map, Ideal.map_quotient_self, Ideal.map_bot] at this
      exact this.symm
    have h1 : ∀ i, a i ^ (m + 1) = 0 := fun i => by
      have := Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self i) : a i ∈ Ideal.span (Set.range a)) (m + 1)
      rwa [h0, Ideal.mem_bot] at this
    refine ⟨h0, fun i => ⟨m + 1, h1 i⟩, fun f => ?_⟩
    have hm : ∀ (e : κ →₀ ℕ) (c : V), ψ (Ideal.Quotient.mk _ (MvPolynomial.monomial e c)) =
        algebraMap Ω A (β c) * ∏ i, a i ^ e i := fun e c => by
      rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), ← hψ]
      simp only [map_mul, map_prod, map_pow]
      rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [GlobalTheory.evBasic_nEval_eq_tEval _ a (m + 1) h1, psJet, psTrunc, map_sum, map_sum]
    simp only [hm]
    rw [degLE, Finset.sum_filter, Finset.sum_image, ReciprocityTheory.PGsh.Be2.tEval]
    · refine Finset.sum_congr rfl fun e _ => ?_
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl), MvPowerSeries.coeff_map]
      split_ifs with h
      · rfl
      · have h2 := prod_pow_mem_span_pow a fun i => (e i : ℕ)
        have h3 : m + 1 ≤ ∑ i, (e i : ℕ) := Nat.lt_of_not_le h
        have h4 := Ideal.pow_le_pow_right h3 h2
        rw [h0, Ideal.mem_bot] at h4
        rw [h4, mul_zero]
    · intro e _ e' _ h
      funext i
      exact Fin.ext (congrFun (Finsupp.equivFunOnFinite.symm.injective h) i)

end GlobalTheory.AlphaPair.JetEv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.JetRingHomExistsUniqueSpecStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jetRing_hom_exists_unique_spec : ∀ (V Ω A : Type) [CommRing V] [CommRing Ω] [CommRing A] [Algebra Ω A] (β : V →+* Ω) (κ : Type) [Fintype κ] [DecidableEq κ] (m : ℕ), (∀ a : κ → A, Ideal.span (Set.range a) ^ (m + 1) = ⊥ → ∃! ψ : Jet V κ m →+* A, (∀ v : V, ψ (algebraMap V _ v) = algebraMap Ω A (β v)) ∧ ∀ i, ψ (Ideal.Quotient.mk _ (MvPolynomial.X i)) = a i) ∧ ∀ ψ : Jet V κ m →+* A, (∀ v : V, ψ (algebraMap V _ v) = algebraMap Ω A (β v)) → Ideal.span (Set.range fun i => ψ (Ideal.Quotient.mk _ (MvPolynomial.X i))) ^ (m + 1) = ⊥ ∧ (∀ i, IsNilpotent (ψ (Ideal.Quotient.mk _ (MvPolynomial.X i)))) ∧ ∀ f : MvPowerSeries κ V, ψ (psJet m f) = nEval (MvPowerSeries.map β f) (fun i => ψ (Ideal.Quotient.mk _ (MvPolynomial.X i))) := by
  first | exact @GlobalTheory.AlphaPair.JetEv.jet_hom_spec | exact GlobalTheory.AlphaPair.JetEv.jet_hom_spec | (intros; apply GlobalTheory.AlphaPair.JetEv.jet_hom_spec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AlphaPMultiplicativeCharacterEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AlphaPMultiplicativeCharacterEqOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaChar
open Polynomial

theorem poly_eq_one {Ω : Type} [Field Ω] (p : ℕ) [CharP Ω p] (w : Polynomial Ω) (c : Ω)
    (hd : w.degree < p) (h0 : w.coeff 0 = 1) (h : derivative w = C c * w) : w = 1 := by
  have hw : w ≠ 0 := by rintro rfl; simp at h0
  have hc : c = 0 := by
    by_contra hc
    have h1 := degree_derivative_lt hw
    rw [h, degree_C_mul hc] at h1
    exact lt_irrefl _ h1
  rw [hc, C_0, zero_mul] at h
  ext n
  rcases n with _ | n
  · simpa using h0
  · simp only [coeff_one, Nat.succ_ne_zero, ite_false]
    by_cases hn : n + 1 < p
    · have h2 := congrArg (fun q : Polynomial Ω => q.coeff n) h
      simp only [coeff_derivative, coeff_zero] at h2
      have h3 : ((n : Ω) + 1) ≠ 0 := by
        intro h3
        have : ((n + 1 : ℕ) : Ω) = 0 := by exact_mod_cast h3
        rw [CharP.cast_eq_zero_iff Ω p] at this
        exact absurd (Nat.le_of_dvd (Nat.succ_pos n) this) (by omega)
      exact (mul_eq_zero.1 h2).resolve_right h3
    · apply coeff_eq_zero_of_degree_lt
      exact lt_of_lt_of_le hd (by exact_mod_cast (not_lt.1 hn))

theorem char_eq_one : ∀ (Ω : Type) [Field Ω] (p : ℕ) [Fact p.Prime] [CharP Ω p] (u : ∀ (A : Type) [CommRing A] [Algebra Ω A], A → Aˣ), (∀ (A B : Type) [CommRing A] [Algebra Ω A] [CommRing B] [Algebra Ω B] (f : A →ₐ[Ω] B) (a : A), a ^ p = 0 → u B (f a) = Units.map (f : A →* B) (u A a)) → (∀ (A : Type) [CommRing A] [Algebra Ω A] (a a' : A), a ^ p = 0 → a' ^ p = 0 → u A (a + a') = u A a * u A a') → ∀ (A : Type) [CommRing A] [Algebra Ω A] (a : A), a ^ p = 0 → u A a = 1 := by
  intro Ω _ p hp _ u hnat hadd
  have hp2 : 2 ≤ p := hp.out.two_le
  have hp0 : p ≠ 0 := by omega
  have hm : (X ^ p : Polynomial Ω).Monic := monic_X_pow p
  let R := AdjoinRoot (X ^ p : Polynomial Ω)
  let t : R := AdjoinRoot.root (X ^ p : Polynomial Ω)
  have ht : t ^ p = 0 := by
    have := AdjoinRoot.mk_self (f := (X ^ p : Polynomial Ω))
    rwa [map_pow, AdjoinRoot.mk_X] at this
  obtain ⟨w0, hw0⟩ := AdjoinRoot.mk_surjective (g := (X ^ p : Polynomial Ω)) (u R t : R)
  let w : Polynomial Ω := w0 %ₘ (X ^ p)
  have hwd : w.degree < p := by
    have := degree_modByMonic_lt w0 hm
    rwa [degree_X_pow] at this
  have hw : aeval t w = (u R t : R) := by
    rw [← hw0, AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_mk]
    have := modByMonic_add_div w0 (X ^ p)
    exact ⟨-(w0 /ₘ X ^ p), by simp only [w]; linear_combination this⟩
  have key : ∀ (A : Type) [CommRing A] [Algebra Ω A] (a : A), a ^ p = 0 →
      (u A a : A) = aeval a w := by
    intro A _ _ a ha
    let f : R →ₐ[Ω] A := Ideal.Quotient.liftₐ (Ideal.span {(X ^ p : Polynomial Ω)}) (aeval a) (by
      intro q hq
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.1 hq
      simp [ha])
    have hf : f t = a := by
      change aeval a (X : Polynomial Ω) = a
      simp
    have h1 := hnat R A f t ht
    rw [hf] at h1
    rw [h1, ← hf, aeval_algHom_apply, hw]
    rfl
  have h0 : w.coeff 0 = 1 := by
    have h1 := hadd Ω 0 0 (zero_pow hp0) (zero_pow hp0)
    rw [add_zero, left_eq_mul] at h1
    have h2 := key Ω 0 (zero_pow hp0)
    rw [h1] at h2
    rw [coeff_zero_eq_aeval_zero, ← h2]; rfl
  have hder : derivative w = C ((derivative w).coeff 0) * w := by
    let D := DualNumber R
    let e : D := DualNumber.eps
    let j : R →ₐ[Ω] D := TrivSqZeroExt.inlAlgHom Ω R R
    have he : e ^ 2 = 0 := by rw [pow_two]; exact DualNumber.eps_mul_eps
    have hep : e ^ p = 0 := pow_eq_zero_of_le hp2 he
    have hs : (j t) ^ p = 0 := by rw [← map_pow, ht, map_zero]
    have hpD : (p : D) = 0 := by
      rw [← map_natCast (algebraMap Ω D), CharP.cast_eq_zero, map_zero]
    have hse : (j t + e) ^ p = 0 := by
      obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp.out (j t) e
      rw [hr, hs, hep, hpD]; simp
    have h1 := congrArg Units.val (hadd D (j t) e hs hep)
    rw [Units.val_mul, key D _ hse, key D _ hs, key D _ hep,
      aeval_add_of_sq_eq_zero _ _ _ he] at h1
    have h2 : aeval e w = 1 + algebraMap Ω D ((derivative w).coeff 0) * e := by
      have := aeval_add_of_sq_eq_zero w 0 e he
      rw [zero_add] at this
      rw [this, ← coeff_zero_eq_aeval_zero', ← coeff_zero_eq_aeval_zero', h0, map_one]
    rw [h2, aeval_algHom_apply, aeval_algHom_apply, ← j.commutes, mul_add, _root_.mul_one,
      add_right_inj, ← _root_.mul_assoc, ← map_mul] at h1
    have hsnd : ∀ x : R, TrivSqZeroExt.snd (j x * e) = x := by
      intro x
      change TrivSqZeroExt.snd ((TrivSqZeroExt.inl x : DualNumber R) * DualNumber.eps) = x
      rw [DualNumber.snd_mul]; simp
    have h3 := congrArg TrivSqZeroExt.snd h1
    rw [hsnd, hsnd] at h3
    have h4 : aeval t (derivative w - C ((derivative w).coeff 0) * w) = 0 := by
      rw [map_sub, map_mul, aeval_C, h3]; ring
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero] at h4
    have h5 := eq_zero_of_dvd_of_degree_lt h4 (by
      rw [degree_X_pow]
      refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt ?_ ?_)
      · exact lt_of_le_of_lt degree_derivative_le hwd
      · rw [← smul_eq_C_mul]; exact lt_of_le_of_lt (degree_smul_le _ _) hwd)
    exact sub_eq_zero.1 h5
  have hone := poly_eq_one p w _ hwd h0 hder
  intro A _ _ a ha
  ext
  rw [key A a ha, hone]; simp

end GlobalTheory.AlphaChar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AlphaPMultiplicativeCharacterEqOneStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alphaP_multiplicativeCharacter_eq_one : ∀ (Ω : Type) [Field Ω] (p : ℕ) [Fact p.Prime] [CharP Ω p] (u : ∀ (A : Type) [CommRing A] [Algebra Ω A], A → Aˣ), (∀ (A B : Type) [CommRing A] [Algebra Ω A] [CommRing B] [Algebra Ω B] (f : A →ₐ[Ω] B) (a : A), a ^ p = 0 → u B (f a) = Units.map (f : A →* B) (u A a)) → (∀ (A : Type) [CommRing A] [Algebra Ω A] (a a' : A), a ^ p = 0 → a' ^ p = 0 → u A (a + a') = u A a * u A a') → ∀ (A : Type) [CommRing A] [Algebra Ω A] (a : A), a ^ p = 0 → u A a = 1 := by
  first | exact @GlobalTheory.AlphaChar.char_eq_one | exact GlobalTheory.AlphaChar.char_eq_one | (intros; apply GlobalTheory.AlphaChar.char_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsRingHomValuationRingOfEmbOK
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsRingHomValuationRingOfEmbOK
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem embOK_exists_ringHom :
    ∀ (T : CDVR) (C : Type) [Field C] [CharZero C] (V : VF C) (ι' : T.Fr →+* C), EmbOK T V ι' → ∃ j : T.V →+* V.RR, (∀ x, (j x : C) = ι' (algebraMap T.V T.Fr x)) ∧ ∀ x ∈ maximalIdeal T.V, V.MM (j x : C) := by
  intro T C _ _ V ι' h
  have hnn : ∀ a : T.V, 0 ≤ vV T.V (algebraMap T.V T.Fr a) := by
    intro a
    unfold vV
    by_cases ha : valV T.V (algebraMap T.V T.Fr a) = 0
    · simp [ha]
    have h1 : valV T.V (algebraMap T.V T.Fr a) ≤ 1 :=
      IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ a
    have := (WithZero.log_le_log ha one_ne_zero).2 h1
    simp at this
    omega
  have hl0 : vV T.V ((V.l : ℕ) : T.Fr) ≠ 0 := by
    intro h0
    have hl : ((V.l : ℕ) : T.Fr) ≠ 0 := Nat.cast_ne_zero.2 V.l_prime.ne_zero
    have := h _ hl
    rw [map_natCast, V.v_l, h0] at this
    simp at this
  have hl : (0 : ℝ) < (vV T.V ((V.l : ℕ) : T.Fr) : ℝ) := by
    have h0 := hnn (V.l : T.V)
    rw [map_natCast] at h0
    exact_mod_cast lt_of_le_of_ne h0 hl0.symm
  have hR : ∀ x : T.V, (ι'.comp (algebraMap T.V T.Fr)) x ∈ V.RR := by
    intro x
    show V.Ge 0 (ι' (algebraMap T.V T.Fr x))
    by_cases h0 : algebraMap T.V T.Fr x = 0
    · rw [h0, map_zero]; exact VF.Ge.zero 0
    unfold VF.Ge
    rw [h _ h0]
    exact WithTop.coe_le_coe.2 (div_nonneg (by exact_mod_cast hnn x) hl.le)
  refine ⟨(ι'.comp (algebraMap T.V T.Fr)).codRestrict V.RR hR, fun x => rfl, fun x hx => ?_⟩
  have key : ((0 : ℝ) : WithTop ℝ) < V.v (ι' (algebraMap T.V T.Fr x)) := by
    by_cases h0 : algebraMap T.V T.Fr x = 0
    · rw [h0, map_zero, V.v.map_zero]; exact WithTop.coe_lt_top _
    rw [h _ h0]
    have h2 : valV T.V (algebraMap T.V T.Fr x) < 1 := by
      unfold valV
      rw [IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
      exact hx
    have h3 := (WithZero.log_lt_log (valV_ne_zero h0) one_ne_zero).2 h2
    have h4 : 0 < vV T.V (algebraMap T.V T.Fr x) := by
      simp at h3
      unfold vV
      omega
    exact WithTop.coe_lt_coe.2 (div_pos (by exact_mod_cast h4) hl)
  exact key

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsRingHomValuationRingOfEmbOKStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringHom_valuationRing_of_embOK : ∀ (T : CDVR) (C : Type) [Field C] [CharZero C] (V : VF C) (ι' : T.Fr →+* C), EmbOK T V ι' → ∃ j : T.V →+* V.RR, (∀ x, (j x : C) = ι' (algebraMap T.V T.Fr x)) ∧ ∀ x ∈ maximalIdeal T.V, V.MM (j x : C) := by
  first | exact @GlobalTheory.embOK_exists_ringHom | exact GlobalTheory.embOK_exists_ringHom | (intros; apply GlobalTheory.embOK_exists_ringHom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CubicalWeilTrivialOfLocalArtinianPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CubicalWeilTrivialOfLocalArtinianPoints
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaPair

theorem exists_isPullback_spec_of_isFinite {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] (D : CommRingCat.{0})
    (e : Spec D ⟶ Y) :
    ∃ (H : CommRingCat.{0}) (φ : D ⟶ H) (y : Spec H ⟶ X), φ.hom.Finite ∧ IsPullback y (Spec.map φ) f e := by
  have : IsAffine (pullback f e) := isAffine_of_isAffineHom (pullback.snd f e)
  obtain ⟨φ, hφ⟩ := Spec.map_surjective ((pullback f e).isoSpec.inv ≫ pullback.snd f e)
  refine ⟨_, φ, (pullback f e).isoSpec.inv ≫ pullback.fst f e, ?_, ?_⟩
  · rw [← IsFinite.SpecMap_iff, hφ]
    infer_instance
  · rw [hφ]
    exact (IsPullback.of_hasPullback f e).of_iso (pullback f e).isoSpec (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp)

theorem eq_of_forall_nilpotent_aug {Ω O : Type} [Field Ω] [IsAlgClosed Ω] [CommRing O] [Algebra Ω O]
    [Module.Finite Ω O] {a b : O}
    (h : ∀ (A : Type) [CommRing A] [Algebra Ω A] (π : A →ₐ[Ω] Ω), IsNilpotent (RingHom.ker π) →
      ∀ g : O →ₐ[Ω] A, g a = g b) : a = b := by
  have : IsArtinianRing O := IsArtinianRing.of_finite Ω O
  refine sub_eq_zero.1 (eq_zero_of_localization _ fun q hq => ?_)
  rw [map_sub, sub_eq_zero]
  let A := Localization.AtPrime q
  let g : O →ₐ[Ω] A := IsScalarTower.toAlgHom Ω O A
  have hg : Function.Surjective g := IsArtinianRing.localization_surjective q.primeCompl A
  have : Module.Finite Ω A := Module.Finite.of_surjective g.toLinearMap hg
  have : IsArtinianRing A := IsArtinianRing.of_finite Ω A
  let r : A →ₐ[Ω] ResidueField A := IsScalarTower.toAlgHom Ω A (ResidueField A)
  have : Module.Finite Ω (ResidueField A) := Module.Finite.of_surjective r.toLinearMap residue_surjective
  let e : Ω ≃ₐ[Ω] ResidueField A :=
    AlgEquiv.ofBijective (Algebra.ofId Ω _) IsAlgClosed.algebraMap_bijective_of_isIntegral
  refine h A (e.symm.toAlgHom.comp r) ?_ g
  obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
  refine ⟨N, le_bot_iff.1 (le_trans (Ideal.pow_right_mono ?_ N) hN.le)⟩
  rw [jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  intro t ht
  have : e.symm (r t) = 0 := ht
  exact (residue_eq_zero_iff t).1 ((map_eq_zero_iff _ e.symm.injective).1 this)

theorem cubWeil_one_of_local_artinian : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (S : Scheme.{0}) (s : Sp Ω ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (c : CubicalStr G L) (n : ℕ), IsFinite ((𝟙 G) ^ n : G ⟶ G).left → ∀ (D : Type) [CommRing D] [Algebra Ω D] [Module.Finite Ω D] (x : overAt s D ⟶ G), x ^ n = 1 → (∀ (A : Type) [CommRing A] [Algebra Ω A] (π : A →ₐ[Ω] Ω), IsNilpotent (RingHom.ker π) → ∀ (f : D →ₐ[Ω] A) (y : overAt s A ⟶ G), y ^ n = 1 → CubWeil c n (homAt s f ≫ x) y 1) → ∀ (T' : Over S) (ρ : T' ⟶ overAt s D) (y : T' ⟶ G), y ^ n = 1 → CubWeil c n (ρ ≫ x) y 1 := by
  intro Ω _ _ S s G _ _ L c n hfin D _ _ _ x hx h T' ρ y hy
  obtain ⟨H, φ, y₀, hφ, hpb⟩ := exists_isPullback_spec_of_isFinite ((𝟙 G) ^ n : G ⟶ G).left (CommRingCat.of D)
    (1 : overAt s D ⟶ G).left
  let : Algebra D H := φ.hom.toAlgebra
  let : Algebra Ω H := (φ.hom.comp (algebraMap Ω D)).toAlgebra
  have : IsScalarTower Ω D H := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Finite D H := hφ
  have : Module.Finite Ω H := Module.Finite.trans D H
  let j : D →ₐ[Ω] H := IsScalarTower.toAlgHom Ω D H
  have hj : (homAt s j).left = Spec.map φ := rfl
  have hpow : ∀ {T : Over S} (z : T ⟶ G), z.left ≫ ((𝟙 G) ^ n : G ⟶ G).left = (z ^ n).left := by
    intro T z
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  have hone : ∀ {T : Over S} (r : T ⟶ overAt s D), r.left ≫ (1 : overAt s D ⟶ G).left = (1 : T ⟶ G).left := by
    intro T r
    rw [← Over.comp_left, MonObj.comp_one]
  have hw : y₀ ≫ G.hom = (overAt s H).hom := by
    rw [← Over.w ((𝟙 G) ^ n : G ⟶ G), ← Category.assoc, hpb.w, Category.assoc, Over.w (1 : overAt s D ⟶ G)]
    exact Over.w (homAt s j)
  let u : overAt s H ⟶ G := Over.homMk y₀ hw
  have hu : u ^ n = 1 := Over.OverMorphism.ext (by rw [← hpow, ← hone (homAt s j)]; exact hpb.w)
  have hx' : (homAt s j ≫ x) ^ n = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
  obtain ⟨ζ, hζ, -⟩ := UU.existsUnique_cubWeil c hx' hu
  have hζ1 : ζ = 1 := by
    refine Units.ext ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of H)).hom).1 ?_)
    refine eq_of_forall_nilpotent_aug (Ω := Ω) fun A _ _ π hπ g => ?_
    have h₁ := h A π hπ (g.comp j) (homAt s g ≫ u) (by rw [← MonObj.comp_pow, hu, MonObj.comp_one])
    rw [← hom_comp, Category.assoc] at h₁
    have e : (homAt s g).left.appTop.hom ζ.val = (homAt s g).left.appTop.hom (1 : Γ((overAt s H).left, ⊤)ˣ).val :=
      (congrArg Units.val ((hζ.comp (homAt s g)).unique h₁)).trans (map_one _).symm
    have nat := fun t => congrArg (fun q => q.hom t) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (g : H →+* A)))
    exact (nat _).symm.trans ((congrArg (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom e).trans (nat _))
  subst hζ1
  have hl : y.left ≫ ((𝟙 G) ^ n : G ⟶ G).left = ρ.left ≫ (1 : overAt s D ⟶ G).left := by rw [hpow, hy, hone]
  let l : T' ⟶ overAt s H := Over.homMk (hpb.lift _ _ hl) (by
    rw [← Over.w (homAt s j), hj, ← Over.w ρ]
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (hpb.lift_snd _ _ hl)))
  have e₁ : l ≫ homAt s j = ρ := Over.OverMorphism.ext (hpb.lift_snd _ _ hl)
  have e₂ : l ≫ u = y := Over.OverMorphism.ext (hpb.lift_fst _ _ hl)
  have := hζ.comp l
  rwa [← Category.assoc, e₁, e₂, map_one] at this

end GlobalTheory.AlphaPair
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CubicalWeilTrivialOfLocalArtinianPointsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubicalWeil_trivial_of_localArtinian_points : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (S : Scheme.{0}) (s : Sp Ω ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (c : CubicalStr G L) (n : ℕ), IsFinite ((𝟙 G) ^ n : G ⟶ G).left → ∀ (D : Type) [CommRing D] [Algebra Ω D] [Module.Finite Ω D] (x : overAt s D ⟶ G), x ^ n = 1 → (∀ (A : Type) [CommRing A] [Algebra Ω A] (π : A →ₐ[Ω] Ω), IsNilpotent (RingHom.ker π) → ∀ (f : D →ₐ[Ω] A) (y : overAt s A ⟶ G), y ^ n = 1 → CubWeil c n (homAt s f ≫ x) y 1) → ∀ (T' : Over S) (ρ : T' ⟶ overAt s D) (y : T' ⟶ G), y ^ n = 1 → CubWeil c n (ρ ≫ x) y 1 := by
  first | exact @GlobalTheory.AlphaPair.cubWeil_one_of_local_artinian | exact GlobalTheory.AlphaPair.cubWeil_one_of_local_artinian | (intros; apply GlobalTheory.AlphaPair.cubWeil_one_of_local_artinian <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.DegenerateDirectionOfNotNondegenerate
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.DegenerateDirectionOfNotNondegenerate
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaPair.Reduce

open Formalism.MainNotions.ModuliIntegralCharts.H1.FBMap

section Ring

variable {R S : Type} [CommRing R] [CommRing S] {d : ℕ}

def addDefect (F : Fin d → PS R 2 d) (ga : Fin d → PowerSeries R) (i : Fin d) : MvPowerSeries (Fin 2) R :=
  MvPowerSeries.subst (fun q : Fin 2 × Fin d =>
    MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X q.1 : MvPowerSeries (Fin 2) R)) (ga q.2)) (F i) -
    MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R)) (ga i)

def cob (F : Fin d → PS R 2 d) (b : PS R 1 d) : PS R 2 d :=
  ev (n := 2) ![addOf F (pt R d 0) (pt R d 1)] b - ev (n := 2) ![pt R d 0] b - ev (n := 2) ![pt R d 1] b

theorem map_addDefect (ψ : R →+* S) (F : Fin d → PS R 2 d) (ga : Fin d → PowerSeries R)
    (h0 : ∀ i, PowerSeries.constantCoeff (ga i) = 0) (i : Fin d) :
    MvPowerSeries.map ψ (addDefect F ga i) =
      addDefect (fun i => MvPowerSeries.map ψ (F i)) (fun i => PowerSeries.map ψ (ga i)) i := by
  have hX : ∀ k : Fin 2, MvPowerSeries.HasSubst
      (fun _ : Unit => (MvPowerSeries.X k : MvPowerSeries (Fin 2) R)) := fun k =>
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
  have hA : MvPowerSeries.HasSubst
      (fun _ : Unit => (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
  have hq : MvPowerSeries.HasSubst (fun q : Fin 2 × Fin d =>
      MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X q.1 : MvPowerSeries (Fin 2) R)) (ga q.2)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q =>
      MvPowerSeries.constantCoeff_subst_eq_zero (hX q.1) (fun _ => by simp) (h0 q.2))
  unfold addDefect
  rw [map_sub, MvPowerSeries.map_subst hq, MvPowerSeries.map_subst hA]
  simp only [MvPowerSeries.map_subst (hX _), map_add (f := _), MvPowerSeries.map_X]
  rfl

theorem map_cob (ψ : R →+* S) (F : Fin d → PS R 2 d) (hF : ∀ i, MvPowerSeries.constantCoeff (F i) = 0)
    (b : PS R 1 d) :
    MvPowerSeries.map ψ (cob F b) = cob (fun i => MvPowerSeries.map ψ (F i)) (MvPowerSeries.map ψ b) := by
  unfold cob
  rw [map_sub, map_sub,
    map_ev' ψ _ (by intro j k; fin_cases j; exact cz_add F hF _ _ (cz_pt _) (cz_pt _) k),
    map_ev' ψ _ (by intro j k; fin_cases j; exact cz_pt _ k),
    map_ev' ψ _ (by intro j k; fin_cases j; exact cz_pt _ k),
    mp_cons, mp_cons, mp_cons, mp_nil, mp_add ψ _ _ _ (cz_pt _) (cz_pt _), mp_pt, mp_pt]

theorem map_cubicalTermLinearAlongTangent (ψ : R →+* S) (ph2 : PS R 3 d) (u : Fin d → R) :
    MvPowerSeries.map ψ (c2 ph2 u) = c2 (MvPowerSeries.map ψ ph2) (fun i => ψ (u i)) := by
  ext mu
  rw [MvPowerSeries.coeff_map]
  change ψ (∑ i : Fin d, _) = ∑ i : Fin d, _
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, MvPowerSeries.coeff_map]

theorem map_map {T σ : Type} [CommRing T] (ψ : R →+* S) (χ : S →+* T) (f : MvPowerSeries σ R) :
    MvPowerSeries.map (χ.comp ψ) f = MvPowerSeries.map χ (MvPowerSeries.map ψ f) := by
  ext mu
  simp only [MvPowerSeries.coeff_map, RingHom.comp_apply]

end Ring

theorem exists_lift {C : Type} [Field C] (V : VF C) {σ : Type} (f : MvPowerSeries σ C)
    (hf : ∀ mu, V.Ge 0 (MvPowerSeries.coeff mu f)) :
    ∃ g : MvPowerSeries σ V.RR, MvPowerSeries.map V.RR.subtype g = f :=
  ⟨fun mu => ⟨MvPowerSeries.coeff mu f, hf mu⟩, by ext mu; rfl⟩

theorem degenerate_of_not_ndg : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (d : ℕ) (Y : FBChart C V O d) (R₀ : Type) [CommRing R₀] (j : R₀ →+* V.RR) (F : Fin d → PS R₀ 2 d) (ph2 : PS R₀ 3 d), (∀ i, MvPowerSeries.constantCoeff (F i) = 0) → (∀ i, Y.B.G.F i = MvPowerSeries.map (V.RR.subtype.comp j) (F i)) → Y.B.ph2 = MvPowerSeries.map (V.RR.subtype.comp j) ph2 → ∀ (Ω : Type) [Field Ω] (ρ : V.RR →+* Ω), (∀ x : V.RR, ρ x = 0 ↔ V.MM (x : C)) → ¬ NDG Y → Degenerate V.l (fun i => MvPowerSeries.map (ρ.comp j) (F i)) (MvPowerSeries.map (ρ.comp j) ph2) := by
  intro C _ _ V O _ _ d Y R₀ _ j F ph2 hF0 hF hph Ω _ ρ hρ hN
  unfold NDG at hN
  push Not at hN
  obtain ⟨ga, hcv, ⟨i₀, hi₀⟩, hadd, b, hb, hcob⟩ := hN
  have hlift : ∀ i, ∃ g : PowerSeries V.RR, PowerSeries.map V.RR.subtype g = ga i := fun i =>
    ⟨PowerSeries.mk fun n => ⟨PowerSeries.coeff n (ga i), (hcv i).2 n⟩, by ext n; simp⟩
  choose g hg using hlift
  obtain ⟨bR, rfl⟩ := exists_lift V b hb
  obtain rfl : ga = fun i => PowerSeries.map V.RR.subtype (g i) := funext fun i => (hg i).symm
  have hg0 : ∀ i, PowerSeries.constantCoeff (g i) = 0 := fun i => by
    have := (hcv i).1
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply] at this
    exact Subtype.ext this
  have hFR : Y.B.G.F = fun i => MvPowerSeries.map V.RR.subtype (MvPowerSeries.map j (F i)) :=
    funext fun i => by rw [hF i, map_map]
  have hFR0 : ∀ i, MvPowerSeries.constantCoeff (MvPowerSeries.map j (F i)) = 0 := fun i => by
    rw [MvPowerSeries.constantCoeff_map, hF0 i, map_zero]
  rw [map_map] at hph
  simp only [map_map]
  refine ⟨fun i => PowerSeries.map ρ (g i), fun i => ?_, ⟨i₀, ?_⟩, fun i mu h0 h1 => ?_,
    MvPowerSeries.map ρ bR, ?_⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hg0 i, map_zero]
  · rw [PowerSeries.coeff_map] at hi₀ ⊢
    exact fun h => hi₀ ((hρ _).1 h)
  · have h : V.MM (MvPowerSeries.coeff mu (addDefect Y.B.G.F (fun i => PowerSeries.map V.RR.subtype (g i)) i)) :=
      hadd i mu h0 h1
    rw [hFR, ← map_addDefect V.RR.subtype _ g hg0 i, MvPowerSeries.coeff_map] at h
    change MvPowerSeries.coeff mu (addDefect (fun i => MvPowerSeries.map ρ (MvPowerSeries.map j (F i)))
      (fun i => PowerSeries.map ρ (g i)) i) = 0
    rw [← map_addDefect ρ _ g hg0 i, MvPowerSeries.coeff_map]
    exact (hρ _).2 h
  · change _ = cob (fun i => MvPowerSeries.map ρ (MvPowerSeries.map j (F i))) (MvPowerSeries.map ρ bR)
    simp only [PowerSeries.coeff_map]
    rw [← map_cob ρ _ hFR0, ← map_cubicalTermLinearAlongTangent, ← sub_eq_zero, ← map_sub]
    ext mu
    have h : V.MM (MvPowerSeries.coeff mu (c2 Y.B.ph2 (fun i => PowerSeries.coeff 1
        (PowerSeries.map V.RR.subtype (g i))) - cob Y.B.G.F (MvPowerSeries.map V.RR.subtype bR))) := hcob mu
    simp only [PowerSeries.coeff_map] at h
    rw [hFR, hph, ← map_cob V.RR.subtype _ hFR0, ← map_cubicalTermLinearAlongTangent, ← map_sub, MvPowerSeries.coeff_map] at h
    rw [MvPowerSeries.coeff_map, map_zero]
    exact (hρ _).2 h

end GlobalTheory.AlphaPair.Reduce
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.DegenerateDirectionOfNotNondegenerateStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degenerate_direction_of_not_nondegenerate : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (d : ℕ) (Y : FBChart C V O d) (R₀ : Type) [CommRing R₀] (j : R₀ →+* V.RR) (F : Fin d → PS R₀ 2 d) (ph2 : PS R₀ 3 d), (∀ i, MvPowerSeries.constantCoeff (F i) = 0) → (∀ i, Y.B.G.F i = MvPowerSeries.map (V.RR.subtype.comp j) (F i)) → Y.B.ph2 = MvPowerSeries.map (V.RR.subtype.comp j) ph2 → ∀ (Ω : Type) [Field Ω] (ρ : V.RR →+* Ω), (∀ x : V.RR, ρ x = 0 ↔ V.MM (x : C)) → ¬ NDG Y → Degenerate V.l (fun i => MvPowerSeries.map (ρ.comp j) (F i)) (MvPowerSeries.map (ρ.comp j) ph2) := by
  first | exact @GlobalTheory.AlphaPair.Reduce.degenerate_of_not_ndg | exact GlobalTheory.AlphaPair.Reduce.degenerate_of_not_ndg | (intros; apply GlobalTheory.AlphaPair.Reduce.degenerate_of_not_ndg <;> assumption)
end
end

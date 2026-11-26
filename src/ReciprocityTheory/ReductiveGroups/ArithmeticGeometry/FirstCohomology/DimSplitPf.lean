module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.PhiPowSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.H1

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem torus_std (A X : Type) [CommRing A] [Nontrivial A] [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] :
    Algebra.IsStandardSmoothOfRelativeDimension (Module.finrank ℤ X) A (AddMonoidAlgebra A X) := by
  classical
  let b := Module.finBasis ℤ X
  let f : (Fin (Module.finrank ℤ X) →₀ ℕ) →+ X :=
    b.repr.symm.toLinearMap.toAddMonoidHom.comp (Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℤ))
  have hf : Function.Injective f := b.repr.symm.injective.comp (Finsupp.mapRange_injective _ Nat.cast_zero Nat.cast_injective)
  let P := MvPolynomial (Fin (Module.finrank ℤ X)) A
  let φ : P →ₐ[A] AddMonoidAlgebra A X := AddMonoidAlgebra.mapDomainAlgHom A A f
  have hφ : ∀ m a, φ (MvPolynomial.monomial m a) = AddMonoidAlgebra.single (f m) a := fun m a =>
    AddMonoidAlgebra.mapDomain_single
  let _ : Algebra P (AddMonoidAlgebra A X) := φ.toRingHom.toAlgebra
  have : IsScalarTower A P (AddMonoidAlgebra A X) := IsScalarTower.of_algebraMap_eq fun a => (φ.commutes a).symm
  let one : Fin (Module.finrank ℤ X) →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => 1
  have hr : ∀ n : ℕ, algebraMap P (AddMonoidAlgebra A X) (MvPolynomial.monomial one 1) ^ n =
      AddMonoidAlgebra.single (n • f one) 1 := fun n => by
    show φ _ ^ n = _
    rw [hφ, AddMonoidAlgebra.single_pow, one_pow]
  have : IsLocalization.Away (MvPolynomial.monomial one (1 : A) : P) (AddMonoidAlgebra A X) := by
    refine IsLocalization.Away.mk _ ?_ (fun s => ?_) (fun a c h => ⟨0, by rw [AddMonoidAlgebra.mapDomain_injective hf h]⟩)
    · refine IsUnit.of_mul_eq_one (AddMonoidAlgebra.single (-f one) 1) ?_
      show φ _ * _ = _
      rw [hφ, AddMonoidAlgebra.single_mul_single, add_neg_cancel, _root_.one_mul]; rfl
    · induction s using AddMonoidAlgebra.induction_linear with
      | zero => exact ⟨0, 0, by simp⟩
      | add s t hs ht =>
        obtain ⟨n, a, ha⟩ := hs
        obtain ⟨m, c, hc⟩ := ht
        refine ⟨n + m, a * MvPolynomial.monomial one 1 ^ m + c * MvPolynomial.monomial one 1 ^ n, ?_⟩
        rw [map_add (f := _), map_mul, map_mul, map_pow, map_pow, ← ha, ← hc]; ring
      | single x a =>
        let n : ℕ := ∑ i, (b.repr x i).natAbs
        refine ⟨n, MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun i => (b.repr x i + n).toNat) a, ?_⟩
        show _ = φ _
        rw [hr, hφ, AddMonoidAlgebra.single_mul_single, _root_.mul_one]
        congr 1
        apply b.repr.injective
        ext i
        have h₁ : (b.repr x i).natAbs ≤ n := Finset.single_le_sum (f := fun i => (b.repr x i).natAbs)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        simp [f, one]
        omega
  have : Algebra.IsStandardSmooth A P := Algebra.IsStandardSmooth.iff_exists_basis_kaehlerDifferential.2
    ⟨inferInstance, _, KaehlerDifferential.mvPolynomialBasis A _, by rintro _ ⟨i, rfl⟩; exact ⟨MvPolynomial.X i, (KaehlerDifferential.mvPolynomialBasis_apply A _ i).symm⟩⟩
  have : Algebra.IsStandardSmoothOfRelativeDimension (Module.finrank ℤ X) A P :=
    (Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth _).2 (by
      rw [rank_eq_card_basis (KaehlerDifferential.mvPolynomialBasis A _), Fintype.card_fin])
  have := Algebra.IsStandardSmoothOfRelativeDimension.localization_away (S := AddMonoidAlgebra A X)
    (MvPolynomial.monomial one (1 : A) : P)
  have h := Algebra.IsStandardSmoothOfRelativeDimension.trans (Module.finrank ℤ X) 0 A P (AddMonoidAlgebra A X)
  rwa [zero_add] at h

theorem torus_dim (S : Scheme.{0}) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] :
    SmoothOfRelativeDimension (Module.finrank ℤ X) (splitTorus S X).hom := by
  have h : SmoothOfRelativeDimension (Module.finrank ℤ X) (splitTorusAff ZU X).hom :=
    (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension (Module.finrank ℤ X))).2
      (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
        ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap _).2 (torus_std _ X)))
  exact (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) h

theorem dim_unique {X Y : Scheme.{0}} (f : X ⟶ Y) {n m : ℕ} (hn : SmoothOfRelativeDimension n f)
    (hm : SmoothOfRelativeDimension m f) (x : X) : n = m := by
  obtain ⟨U, hU, V, hV, hx, e, h⟩ := hm.exists_isStandardSmoothOfRelativeDimension x
  obtain ⟨s, hs, h'⟩ := HasRingHomProperty.appLE (@SmoothOfRelativeDimension n) f hn ⟨U, hU⟩ ⟨V, hV⟩ e
  have : Nonempty V := ⟨⟨x, hx⟩⟩
  obtain ⟨p, hp⟩ := Ideal.exists_maximal Γ(X, V)
  obtain ⟨t, ht, htp⟩ : ∃ t ∈ s, t ∉ p := by
    by_contra hc
    exact hp.ne_top (top_le_iff.1 (hs ▸ Ideal.span_le.2 fun t ht => by_contra fun h => hc ⟨t, ht, h⟩))
  have : Nontrivial (Localization.Away t) := by
    by_contra hc
    obtain ⟨k, hk⟩ := (IsLocalization.subsingleton_iff (M := Submonoid.powers t)).1 (not_nontrivial_iff_subsingleton.1 hc)
    exact htp (hp.isPrime.mem_of_pow_mem k (by rw [show t ^ k = 0 from hk]; exact p.zero_mem))
  have h₁ := h' t ht
  have h₂ := (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway m).right
    (Localization.Away t) t _ h
  let _ := ((algebraMap Γ(X, V) (Localization.Away t)).comp (f.appLE U V e).hom).toAlgebra
  have r₁ := @Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential _ _ _ _ _ _ n h₁
  have r₂ := @Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential _ _ _ _ _ _ m h₂
  exact_mod_cast r₁.symm.trans r₂

theorem exists_dim {X Y : Scheme.{0}} (f : X ⟶ Y) [Smooth f] (x : X) :
    ∃ (n : ℕ) (W : X.Opens), x ∈ W ∧ SmoothOfRelativeDimension n (W.ι ≫ f) := by
  obtain ⟨U, hU, V, hV, hx, e, h⟩ := Smooth.exists_isStandardSmooth f x
  have : Nonempty V := ⟨⟨x, hx⟩⟩
  let _ := (f.appLE U V e).hom.toAlgebra
  have : Algebra.IsStandardSmooth Γ(Y, U) Γ(X, V) := h
  obtain ⟨_, _, _, _, ⟨P⟩⟩ := this
  have h' : RingHom.IsStandardSmoothOfRelativeDimension P.dimension (f.appLE U V e).hom := ⟨_, _, _, ‹_›, P, rfl⟩
  have : IsAffine U := hU
  have : IsAffine V := hV
  have : SmoothOfRelativeDimension P.dimension (f.resLE U V e) :=
    (HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension P.dimension)).2
      (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
        ((RingHom.isStandardSmoothOfRelativeDimension_respectsIso.arrow_mk_iso_iff (arrowResLEAppIso f U V e)).2 h'))
  refine ⟨P.dimension + 0, V, hx, ?_⟩
  rw [← Scheme.Hom.resLE_comp_ι f e]; infer_instance

theorem dim_base {X S X' S' : Scheme.{0}} {f : X ⟶ S} {f' : X' ⟶ S'} {a : X' ⟶ X} {b : S' ⟶ S} (h : IsPullback a f' f b)
    {n m : ℕ} {W : X.Opens} (hW : SmoothOfRelativeDimension n (W.ι ≫ f)) (hm : SmoothOfRelativeDimension m f') (x : X')
    (hx : a x ∈ W) : n = m := by
  have h₁ : SmoothOfRelativeDimension n ((a ⁻¹ᵁ W).ι ≫ f') := (smoothOfRelativeDimension_isStableUnderBaseChange n).of_isPullback
    ((isPullback_morphismRestrict a W).paste_vert h) hW
  have h₂ : SmoothOfRelativeDimension (0 + m) ((a ⁻¹ᵁ W).ι ≫ f') := inferInstance
  exact (dim_unique _ h₁ h₂ ⟨x, hx⟩).trans (zero_add m)

theorem torsor_pullback {S : Scheme.{0}} {T G B : Over S} [GrpObj T] [GrpObj G] [GrpObj B] (i : T ⟶ G) (q : G ⟶ B)
    [IsMonHom q] (h : IsPullback i (toUnit _) q η[B]) : IsPullback ((fst T G ≫ i) * snd T G) (snd T G) q q := by
  have hi : i ≫ q = 1 := h.w
  have : Mono i := h.flip.mono_snd_of_mono
  refine IsPullback.of_isLimit' ⟨by rw [MonObj.mul_comp, Category.assoc, hi, MonObj.comp_one, _root_.one_mul]⟩
    (PullbackCone.IsLimit.mk _ (fun s => lift (h.lift (s.fst * s.snd⁻¹) (toUnit _) (by
      rw [MonObj.mul_comp, GrpObj.inv_comp, s.condition, mul_inv_cancel]; rfl)) s.snd) (fun s => ?_) (fun s => lift_snd _ _)
      (fun s m h₁ h₂ => ?_))
  · rw [MonObj.comp_mul, lift_fst_assoc, h.lift_fst, lift_snd, inv_mul_cancel_right]
  · apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst, ← cancel_mono i, h.lift_fst, ← h₁, ← h₂, MonObj.comp_mul, mul_inv_cancel_right, Category.assoc]
    · rw [lift_snd, h₂]

theorem dimSplit : DimSplitStatement := by
  intro E _ _ _ H V _ _ _ t P
  have := t.semi.smooth
  obtain ⟨n, W, hW, dW⟩ := exists_dim t.G.hom (eSec t.G (closedPoint V))
  have all : ∀ y : Sp V, eSec t.G y ∈ W := fun y =>
    (congrArg (fun U => y ∈ U) (Scheme.preimage_eq_top_of_closedPoint_mem (eSec t.G) hW)).mpr trivial
  have unit : ∀ {S' : Scheme.{0}} (b : S' ⟶ Sp V) (y : S'),
      pullback.fst t.G.hom b (eSec ((Over.pullback b).obj t.G) y) ∈ W := fun b y =>
    (congrArg (fun g => g y ∈ W) (cubeMapOf (isGrpPullback_pullback t.G b)).e_comm).mpr (all _)

  have g₁ : n = P.A.g := by
    have := P.A.smoothDim
    have : IsIso P.U.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map P.U.gen.hom))
    have d : SmoothOfRelativeDimension (0 + P.A.g) (pullback.snd t.G.hom (jK V)) := by
      rw [show pullback.snd t.G.hom (jK V) = P.U.gen.hom.left ≫ P.A.A.hom from (Over.w P.U.gen.hom).symm]
      infer_instance
    exact (dim_base (IsPullback.of_hasPullback _ _) dW d _ (unit (jK V) (default : PrimeSpectrum (FractionRing V)))).trans
      (zero_add _)

  let c := P.U.gt 0
  have := c.q_hom
  have := c.i_hom
  have := c.q_flat
  have := c.q_surj
  have := c.q_affine
  have dT := torus_dim (Spec (CommRingCat.of (V ⧸ maximalIdeal V ^ (0 + 1)))) P.D.toPre.X
  have : Smooth c.q.left := by
    have := dT.smooth
    refine MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      ((torsor_pullback c.i c.q c.isKernel).map (Over.forget _)).flip ⟨⟨‹_›, ‹_›⟩, inferInstanceAs (QuasiCompact c.q.left)⟩ ?_
    exact smooth_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) this
  have : Nontrivial (V ⧸ maximalIdeal V ^ (0 + 1)) :=
    Ideal.Quotient.nontrivial_iff.2 (by rw [zero_add, pow_one]; exact (maximalIdeal.isMaximal V).ne_top)
  obtain ⟨y⟩ : Nonempty (Spec (CommRingCat.of (V ⧸ maximalIdeal V ^ (0 + 1)))) :=
    inferInstanceAs (Nonempty (PrimeSpectrum _))
  obtain ⟨m, W₁, hW₁, d₁⟩ := exists_dim c.q.left (eSec (thickObj V (maximalIdeal V) 0 t.G) y)
  have g₂ : m = Module.finrank ℤ P.D.toPre.X := dim_base (c.isKernel.map (Over.forget _)) d₁ dT (eSec _ y)
    ((congrArg (fun g => g.left y ∈ W₁) (IsMonHom.one_hom c.i)).mpr hW₁)
  have dB : SmoothOfRelativeDimension P.D.toPre.P.g (thickObj V (maximalIdeal V) 0 P.D.toPre.P.A).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _)
      P.D.toPre.P.smoothDim
  have d₂ : SmoothOfRelativeDimension (m + P.D.toPre.P.g) (W₁.ι ≫ (thickObj V (maximalIdeal V) 0 t.G).hom) := by
    rw [← Over.w c.q, ← Category.assoc]; infer_instance
  have d₃ : SmoothOfRelativeDimension n ((pullback.fst t.G.hom (thick V (maximalIdeal V) 0) ⁻¹ᵁ W).ι ≫
      (thickObj V (maximalIdeal V) 0 t.G).hom) := (smoothOfRelativeDimension_isStableUnderBaseChange n).of_isPullback
    ((isPullback_morphismRestrict _ W).paste_vert (IsPullback.of_hasPullback _ _)) dW
  have g₃ : n = m + P.D.toPre.P.g := by
    let W₂ := pullback.fst t.G.hom (thick V (maximalIdeal V) 0) ⁻¹ᵁ W
    have e₁ : SmoothOfRelativeDimension (0 + n) ((W₂ ⊓ W₁).ι ≫ (thickObj V (maximalIdeal V) 0 t.G).hom) := by
      rw [← Scheme.homOfLE_ι _ (inf_le_left : W₂ ⊓ W₁ ≤ W₂), Category.assoc]; infer_instance
    have e₂ : SmoothOfRelativeDimension (0 + (m + P.D.toPre.P.g)) ((W₂ ⊓ W₁).ι ≫ (thickObj V (maximalIdeal V) 0 t.G).hom) := by
      rw [← Scheme.homOfLE_ι _ (inf_le_right : W₂ ⊓ W₁ ≤ W₁), Category.assoc]; infer_instance
    simpa using dim_unique _ e₁ e₂ ⟨_, unit _ y, hW₁⟩
  rw [← g₁, g₃, g₂]

end ReciprocityTheory.ChartRestriction.G.H1
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.GenProd
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.H1

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {X Y : Scheme.{0}} (L : LB X)

theorem exists_gen_prod (K : ℕ → Type) [∀ i, Fintype (K i)] (φ : ∀ i, K i → (Y ⟶ X)) (ε : ∀ i, K i → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i))) (ht : ∀ i, (t i).IsGen) (n : ℕ) :
    ∃ (K' : Type) (_ : Fintype K') (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) (t' : LB.Gen (LB.LinComb L φ' ε')),
      t'.IsGen ∧
      (∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U),
        ∏ k, h (φ' k) ^ ε' k = ∏ i ∈ Finset.range n, ∏ k, h (φ i k) ^ ε i k) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
        val t' r z J = ∏ i ∈ Finset.range n, val (t i) r z J := by
  induction n with
  | zero =>
    refine ⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim, LB.oneGen L, ?_, ?_, ?_⟩
    · rintro (i : PEmpty.{1} → L.ι) (j : PEmpty.{1} → L.ι)
      have h0 : (LB.LinComb L (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim).g i j = 1 :=
        rfl
      rw [h0, one_mul]
      simp only [LB.oneGen, map_one]
    · intro U _ h
      simp
    · intro Z r z J _
      simp [val, LB.oneGen]
      exact map_one (gm r z _)
  | succ n ih =>
    obtain ⟨K', hK', φ', ε', t', ht', hprod, hval⟩ := ih
    refine ⟨K' ⊕ K n, inferInstance, Sum.elim φ' (φ n), Sum.elim ε' (ε n),
      LB.mulGen L φ' ε' (φ n) (ε n) t' (t n),
      ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen L φ' ε' (φ n) (ε n) t' (t n) ht' (ht n), ?_, ?_⟩
    · intro U _ h
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.prod_range_succ, hprod U h]
    · intro Z r z J hJ
      rw [val_mul, Finset.prod_range_succ, hval Z r z J hJ]
      exact hJ

theorem exists_const {S₀ : Scheme.{0}} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (p : Y ⟶ S₀) (hp : Function.Surjective p.appTop.hom) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen)
    (hf : ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), ∏ k, h (φ k) ^ ε k = 1) :
    ∃ a : Γ(S₀, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      (val t r z J).val = gs (r ≫ p) z ⊤ a := by
  classical
  have hcov : (⊤ : Y.Opens) ≤ ⨆ c : (Y ⟶ X) → L.ι, LB.wchart L φ (fun k => c (φ k)) := by
    intro y _
    have hc : ∀ ψ : Y ⟶ X, ∃ i, ψ.base y ∈ L.U i := by
      intro ψ
      have hy : ψ.base y ∈ (⨆ i, L.U i) := by rw [hL.cover]; simp
      exact TopologicalSpace.Opens.mem_iSup.1 hy
    choose c hc using hc
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨c, Set.mem_iInter.2 fun k => hc (φ k)⟩
  have hcompat : ∀ c c' : (Y ⟶ X) → L.ι,
      res (inf_le_left : LB.wchart L φ (fun k => c (φ k)) ⊓ LB.wchart L φ (fun k => c' (φ k)) ≤
        LB.wchart L φ (fun k => c (φ k))) (t.s (fun k => c (φ k))) =
      res (inf_le_right : LB.wchart L φ (fun k => c (φ k)) ⊓ LB.wchart L φ (fun k => c' (φ k)) ≤
        LB.wchart L φ (fun k => c' (φ k))) (t.s (fun k => c' (φ k))) := by
    intro c c'
    have hg := ht (fun k => c (φ k)) (fun k => c' (φ k))
    have h1 : (LB.LinComb L φ ε).g (fun k => c (φ k)) (fun k => c' (φ k)) = 1 := by
      refine Eq.trans ?_ (hf (Γ(Y, LB.wchart L φ (fun k => c (φ k)) ⊓ LB.wchart L φ (fun k => c' (φ k)))ˣ)
        (fun ψ => if hψ : ∃ k, φ k = ψ then
          res (show LB.wchart L φ (fun k => c (φ k)) ⊓ LB.wchart L φ (fun k => c' (φ k)) ≤
              ψ ⁻¹ᵁ (L.U (c ψ) ⊓ L.U (c' ψ)) by
            obtain ⟨k, rfl⟩ := hψ
            exact le_inf (inf_le_left.trans (LB.wchart_le L φ _ k))
              (inf_le_right.trans (LB.wchart_le L φ _ k)))
            (pullU ψ _ (L.g (c ψ) (c' ψ)))
          else 1))
      refine Finset.prod_congr rfl fun k _ => ?_
      show _ = (dite _ _ _) ^ ε k
      rw [dite_eq_left (show ∃ k', φ k' = φ k from ⟨k, rfl⟩)]
      rfl
    rw [h1, one_mul] at hg
    exact hg
  have key := TopCat.Sheaf.existsUnique_gluing' Y.sheaf
    (fun c : (Y ⟶ X) → L.ι => LB.wchart L φ (fun k => c (φ k))) ⊤ (fun _ => homOfLE le_top) hcov
  obtain ⟨f, hf1, -⟩ := key (fun c => (t.s (fun k => c (φ k))).val)
    (fun c c' => congrArg Units.val (hcompat c c'))
  obtain ⟨g, hg1, -⟩ := key (fun c => ((t.s (fun k => c (φ k)))⁻¹).val)
    (fun c c' => congrArg (fun u => (u⁻¹).val) (hcompat c c'))
  obtain ⟨e, -, he⟩ := key (fun _ => 1) (fun c c' => (map_one _).trans (map_one _).symm)
  have hfg : f * g = 1 :=
    (he (f * g) fun c => by rw [map_mul, hf1 c, hg1 c]; exact (t.s _).mul_inv).trans
      (he 1 fun c => map_one _).symm
  let fU : Γ(Y, ⊤)ˣ := Units.mkOfMulEqOne f g hfg
  obtain ⟨a, ha⟩ := hp fU.val
  refine ⟨a, fun Z r z J hJ => ?_⟩
  have hmem : r.base z ∈ LB.wchart L φ (fun k => J (r ≫ φ k)) :=
    Set.mem_iInter.2 fun k => hJ (r ≫ φ k)
  have hres : res (le_top : LB.wchart L φ (fun k => J (r ≫ φ k)) ≤ ⊤) fU = t.s (fun k => J (r ≫ φ k)) :=
    Units.ext (hf1 (fun ψ => J (r ≫ ψ)))
  rw [val_of (t := t) (r := r) (z := z) (J := J) (j := fun k => J (r ≫ φ k)) (h := fun _ => rfl), ← hres,
    gm_res r z le_top hmem fU, ← gs_unit r z ⊤ (by simp) fU, ← ha]
  exact gs_pull r p z ⊤ (by simp) a

end ReciprocityTheory.ChartRestriction.G.H1
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ThetaMove
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.H1

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Move

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)

def psiO : Over.mk ((T ⊗ A).hom ≫ f) ⟶ T₀ ⊗ G :=
  lift (Over.homMk ((fst T A).left ≫ τ) (by
      show ((fst T A).left ≫ τ) ≫ T₀.hom = (T ⊗ A).hom ≫ f
      rw [Category.assoc, hτ, ← Category.assoc, Over.w (fst T A)]))
    (pushPt hp.1.w (snd T A))

theorem psi_fst : (psiO hp τ hτ).left ≫ (fst T₀ G).left = (fst T A).left ≫ τ := by
  rw [← Over.comp_left, psiO, lift_fst]; rfl

theorem psi_snd : (psiO hp τ hτ).left ≫ (snd T₀ G).left = (snd T A).left ≫ φ := by
  rw [← Over.comp_left, psiO, lift_snd]; rfl

theorem psi_tr (x : T ⟶ A) (x₀ : T₀ ⟶ G) (hx : τ ≫ x₀.left = x.left ≫ φ) :
    (psiO hp τ hτ).left ≫ (translPt G x₀).left = (translPt A x).left ≫ φ := by
  have e₁ : translPt G x₀ = (fst T₀ G ≫ x₀) * snd T₀ G := rfl
  have e₂ : translPt A x = (fst T A ≫ x) * snd T A := rfl
  rw [← Over.comp_left, e₁, MonObj.comp_mul, e₂]
  refine hp.2 _ _ _ _ _ ?_ ?_
  · rw [Over.comp_left, Over.comp_left, ← Category.assoc, psi_fst, Category.assoc, hx, Over.comp_left, Category.assoc]
  · rw [Over.comp_left, psi_snd]

theorem psi_transl (x : T ⟶ A) (x₀ : T₀ ⟶ G) (hx : τ ≫ x₀.left = x.left ≫ φ) :
    (translT A x).left ≫ (psiO hp τ hτ).left = (psiO hp τ hτ).left ≫ (translT G x₀).left := by
  let m : Over.mk ((T ⊗ A).hom ≫ f) ⟶ Over.mk ((T ⊗ A).hom ≫ f) :=
    Over.homMk (translT A x).left (by
      show (translT A x).left ≫ (T ⊗ A).hom ≫ f = (T ⊗ A).hom ≫ f
      rw [← Category.assoc, Over.w (translT A x)])
  have key : m ≫ psiO hp τ hτ = psiO hp τ hτ ≫ translT G x₀ := by
    apply CartesianMonoidalCategory.hom_ext
    · apply Over.OverMorphism.ext
      have e1 : (m ≫ psiO hp τ hτ ≫ fst T₀ G).left = (fst T A).left ≫ τ := by
        rw [psiO, lift_fst]
        show (translT A x).left ≫ (fst T A).left ≫ τ = _
        rw [← Category.assoc, ← Over.comp_left, translT, lift_fst]
      have e2 : (psiO hp τ hτ ≫ translT G x₀ ≫ fst T₀ G).left = (fst T A).left ≫ τ := by
        rw [translT, lift_fst, Over.comp_left, psi_fst]
      simpa only [Category.assoc] using e1.trans e2.symm
    · apply Over.OverMorphism.ext
      have e1 : (m ≫ psiO hp τ hτ ≫ snd T₀ G).left = (translPt A x).left ≫ φ := by
        rw [psiO, lift_snd]
        show (translT A x).left ≫ (snd T A).left ≫ φ = _
        rw [← Category.assoc, ← Over.comp_left, translT, lift_snd]
      have e2 : (psiO hp τ hτ ≫ translT G x₀ ≫ snd T₀ G).left = (translPt A x).left ≫ φ := by
        rw [translT, lift_snd, Over.comp_left, psi_tr hp τ hτ x x₀ hx]
      simpa only [Category.assoc] using e1.trans e2.symm
  exact congrArg CommaMorphism.left key

variable {L₀ : LB G.left} {L₁ : LB A.left}

theorem exists_theta_move (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (w : LB.Iso L₁ (L₀.pull φ)) (hw : w.IsGen) (k : ℤ)
    (x : T ⟶ A) (θ₀ : ThetaGrp G L₀ k T₀) (hx : τ ≫ θ₀.pt.left = x.left ≫ φ) :
    ∃ θ : ThetaGrp A L₁ k T, θ.pt = x ∧
      PMaps w ![(snd T A).left, (translPt A θ.pt).left] ![(snd T₀ G).left, (translPt G θ₀.pt).left] ![k, -k]
        θ.φ θ₀.φ (psiO hp τ hτ).left := by
  obtain ⟨a, ha, hm⟩ := exists_gen_move hL₀ hL₁ w ((isGen_iff w).1 hw)
    ![(snd T₀ G).left, (translPt G θ₀.pt).left] ![(snd T A).left, (translPt A x).left] ![k, -k]
    (psiO hp τ hτ).left (fun i => by
      fin_cases i
      · exact (psi_snd hp τ hτ).symm
      · exact (psi_tr hp τ hτ x θ₀.pt hx).symm) θ₀.φ θ₀.isGen
  exact ⟨⟨x, a, ha⟩, rfl, hm⟩

end Move

theorem cancel_cg {M : Type*} [CommGroup M] (P X Y Z a b c d C : M)
    (h : (P * X⁻¹ * a) * (X * Z⁻¹ * b) = (P * Y⁻¹ * c) * (Y * Z⁻¹ * d) * C) : a * b = c * d * C := by
  have e₁ : a * b = (P * X⁻¹ * a) * (X * Z⁻¹ * b) * (P * Z⁻¹)⁻¹ := by
    apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel
  have e₂ : (P * Y⁻¹ * c) * (Y * Z⁻¹ * d) * C * (P * Z⁻¹)⁻¹ = c * d * C := by
    apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel
  rw [e₁, h, e₂]

theorem val_constGen {S : Scheme.{0}} {A : Over S} [GrpObj A] (L : LB A.left) {T : Over S} (c : Γ(T.left, ⊤)ˣ)
    {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) (J : (Z ⟶ A.left) → L.ι) :
    val (constGen A L c) r z J = gm (r ≫ (fst T A).left) z ⊤ c := by
  show gm r z _ (res le_top (pullU (fst T A).left ⊤ c)) = _
  exact (gm_res r z _ (Set.mem_iInter.2 fun k => k.elim) _).trans (gm_pull r _ z ⊤ trivial c)

section Comm

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A] [IsCommMonObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left}

theorem transl_snd (x : T ⟶ A) : (translT A x).left ≫ (snd T A).left = (translPt A x).left := by
  rw [← Over.comp_left, translT, lift_snd]

theorem transl_comm (x y : T ⟶ A) :
    (translT A x).left ≫ (translPt A y).left = (translT A y).left ≫ (translPt A x).left := by
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  show translT A x ≫ ((fst T A ≫ y) * snd T A) = translT A y ≫ ((fst T A ≫ x) * snd T A)
  rw [MonObj.comp_mul, MonObj.comp_mul, translT, translT, lift_snd, lift_snd, ← Category.assoc, ← Category.assoc,
    lift_fst, lift_fst]
  exact mul_left_comm _ _ _

theorem commIsOf_move (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (w : LB.Iso L₁ (L₀.pull φ)) (k : ℤ)
    (θx₀ θy₀ : ThetaGrp G L₀ k T₀) (θx θy : ThetaGrp A L₁ k T)
    (hx : τ ≫ θx₀.pt.left = θx.pt.left ≫ φ) (hy : τ ≫ θy₀.pt.left = θy.pt.left ≫ φ)
    (mx : PMaps w ![(snd T A).left, (translPt A θx.pt).left] ![(snd T₀ G).left, (translPt G θx₀.pt).left] ![k, -k]
      θx.φ θx₀.φ (psiO hp τ hτ).left)
    (my : PMaps w ![(snd T A).left, (translPt A θy.pt).left] ![(snd T₀ G).left, (translPt G θy₀.pt).left] ![k, -k]
      θy.φ θy₀.φ (psiO hp τ hτ).left)
    (c₀ : Γ(T₀.left, ⊤)ˣ) (c : Γ(T.left, ⊤)ˣ)
    (hc : ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z), gm (r ≫ τ) z ⊤ c₀ = gm r z ⊤ c)
    (H : CommIsOf G L₀ k θx₀ θy₀ c₀) : CommIsOf A L₁ k θx θy c := by
  refine corr_of_val hL₁ fun y J hJ => ?_
  choose J₀ hJ₀ using fun χ : (T ⊗ A).left ⟶ G.left => exists_chart hL₀ (χ y)
  have hG : Good L₀ y J₀ := hJ₀
  let W : ((T ⊗ A).left ⟶ A.left) → ((T ⊗ A).left.presheaf.stalk y)ˣ := fun ψ => gw w ψ y (J₀ (ψ ≫ φ)) (J ψ)
  have rel : ∀ (θ₀ : ThetaGrp G L₀ k T₀) (θ : ThetaGrp A L₁ k T), τ ≫ θ₀.pt.left = θ.pt.left ≫ φ →
      PMaps w ![(snd T A).left, (translPt A θ.pt).left] ![(snd T₀ G).left, (translPt G θ₀.pt).left] ![k, -k]
        θ.φ θ₀.φ (psiO hp τ hτ).left →
      ∀ r : (T ⊗ A).left ⟶ (T ⊗ A).left, val θ₀.φ (r ≫ (psiO hp τ hτ).left) y J₀ =
        (W (r ≫ (snd T A).left) ^ k * W (r ≫ (translPt A θ.pt).left) ^ (-k)) * val θ.φ r y J := by
    intro θ₀ θ hθ m r
    have e₀ : (r ≫ (psiO hp τ hτ).left) ≫ (snd T₀ G).left = (r ≫ (snd T A).left) ≫ φ := by
      rw [Category.assoc, Category.assoc, psi_snd]
    have e₁ : (r ≫ (psiO hp τ hτ).left) ≫ (translPt G θ₀.pt).left = (r ≫ (translPt A θ.pt).left) ≫ φ := by
      rw [Category.assoc, Category.assoc, psi_tr hp τ hτ _ _ hθ]
    have e : ∀ i, (r ≫ (psiO hp τ hτ).left) ≫ ![(snd T₀ G).left, (translPt G θ₀.pt).left] i =
        (r ≫ ![(snd T A).left, (translPt A θ.pt).left] i) ≫ φ := fun i => by
      fin_cases i
      · exact e₀
      · exact e₁
    calc val θ₀.φ (r ≫ (psiO hp τ hτ).left) y J₀ = _ :=
          m _ r y _ (fun i => J (r ≫ ![(snd T A).left, (translPt A θ.pt).left] i)) (fun i => by
            show _ ∈ L₀.U (J₀ ((r ≫ (psiO hp τ hτ).left) ≫ _))
            rw [e i]; exact hG _) (fun i => hJ _)
      _ = _ := by
        congr 1
        simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [e₀, e₁]
  have a₁ := rel θx₀ θx hx mx (𝟙 _)
  have a₂ := rel θy₀ θy hy my (translT A θx.pt).left
  have a₃ := rel θy₀ θy hy my (𝟙 _)
  have a₄ := rel θx₀ θx hx mx (translT A θy.pt).left
  rw [Category.id_comp, Category.id_comp, Category.id_comp] at a₁ a₃
  rw [transl_snd] at a₂ a₄
  have hL : val (Z := (T ⊗ A).left) θx₀.φ (psiO hp τ hτ).left y J₀ *
        val θy₀.φ ((translT A θx.pt).left ≫ (psiO hp τ hτ).left) y J₀ =
      val (Z := (T ⊗ A).left) θy₀.φ (psiO hp τ hτ).left y J₀ *
        val θx₀.φ ((translT A θy.pt).left ≫ (psiO hp τ hτ).left) y J₀ *
        val (Z := (T ⊗ A).left) (constGen G L₀ c₀) (psiO hp τ hτ).left y J₀ := by
    have h0 := val_corr hG H (psiO hp τ hτ).left
    rw [psi_transl hp τ hτ _ _ hx, psi_transl hp τ hτ _ _ hy]
    exact ((val_mul hG _ _ _).trans (congrArg (val (Z := (T ⊗ A).left) θx₀.φ (psiO hp τ hτ).left y J₀ * ·) (val_pull hG _ _ _))).symm.trans
      (h0.trans ((val_mul hG _ _ _).trans (congrArg (· * _) ((val_mul hG _ _ _).trans
        (congrArg (val (Z := (T ⊗ A).left) θy₀.φ (psiO hp τ hτ).left y J₀ * ·) (val_pull hG _ _ _))))))
  have hcst : val (Z := (T ⊗ A).left) (constGen G L₀ c₀) (psiO hp τ hτ).left y J₀ = val (constGen A L₁ c) (𝟙 _) y J := by
    rw [val_constGen, val_constGen, psi_fst, hc, Category.id_comp]
  rw [a₁, a₂, a₃, a₄, transl_comm θx.pt θy.pt, hcst] at hL
  simp only [zpow_neg] at hL
  refine ((val_mul hJ _ _ _).trans (congrArg (val θx.φ (𝟙 _) y J * ·) (val_pull hJ _ _ _))).trans
    (Eq.trans ?_ ((val_mul hJ _ _ _).trans (congrArg (· * _) ((val_mul hJ _ _ _).trans
      (congrArg (val θy.φ (𝟙 _) y J * ·) (val_pull hJ _ _ _))))).symm)
  rw [Category.id_comp, Category.id_comp]
  exact cancel_cg _ _ _ _ _ _ _ _ _ hL

end Comm

theorem commIsOf_unique {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) {k : ℤ} {T : Over S}
    (θx θy : ThetaGrp A L k T) (c c' : Γ(T.left, ⊤)ˣ) (h : CommIsOf A L k θx θy c) (h' : CommIsOf A L k θx θy c') :
    c = c' := by
  let s : T.left ⟶ (T ⊗ A).left := (lift (𝟙 T) (toUnit T ≫ η[A])).left
  have hs : s ≫ (fst T A).left = 𝟙 _ := by rw [← Over.comp_left, lift_fst, Over.id_left]
  refine unit_ext fun z _ => ?_
  choose J hJ using fun χ : T.left ⟶ A.left => exists_chart hL (χ z)
  have hJ' : Good L z J := hJ
  have e := (val_mul hJ' _ _ s).symm.trans ((val_corr hJ' h s).symm.trans ((val_corr hJ' h' s).trans (val_mul hJ' _ _ s)))
  have e' := mul_left_cancel e
  rw [val_constGen, val_constGen, hs] at e'
  exact e'

end ReciprocityTheory.ChartRestriction.G.H1
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.AlphaPair
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj IsLocalRing NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.H1

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Act

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {T : Over S}

theorem comp_mulMon (f : A ⟶ A) [IsMonHom f] (x y : T ⟶ A) : (x * y) ≫ f = (x ≫ f) * (y ≫ f) := by
  rw [Hom.mul_def, Hom.mul_def, Category.assoc, IsMonHom.mul_hom, ← Category.assoc, lift_map]

theorem one_compMon (f : A ⟶ A) [IsMonHom f] : (1 : T ⟶ A) ≫ f = 1 := by
  rw [Hom.one_def, Category.assoc, IsMonHom.one_hom]

theorem comp_padd (x : T ⟶ A) (f g : A ⟶ A) : x ≫ padd A f g = (x ≫ f) * (x ≫ g) := by
  simp only [padd]
  rw [← Category.assoc, comp_lift, Hom.mul_def]

variable {O : Type} [Ring O] (ρ : RingAct A O)

theorem act_add_apply (x : T ⟶ A) (a b : O) : x ≫ ρ.act (a + b) = (x ≫ ρ.act a) * (x ≫ ρ.act b) := by
  rw [ρ.map_add, comp_padd]

theorem act_mul_apply (x : T ⟶ A) (a b : O) : x ≫ ρ.act (a * b) = (x ≫ ρ.act b) ≫ ρ.act a := by
  rw [ρ.map_mul, Category.assoc]

theorem act_one_apply (x : T ⟶ A) : x ≫ ρ.act 1 = x := by
  rw [ρ.map_one, Category.comp_id]

theorem act_zero_apply (x : T ⟶ A) : x ≫ ρ.act 0 = 1 := by
  have h := act_add_apply ρ x 0 0
  rw [add_zero] at h
  exact (_root_.mul_left_cancel (a := x ≫ ρ.act 0) (by rw [_root_.mul_one]; exact h)).symm

theorem act_nat_apply (x : T ⟶ A) (n : ℕ) : x ≫ ρ.act (n : O) = x ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, act_zero_apply, _root_.pow_zero]
  | succ n ih => rw [Nat.cast_succ, act_add_apply, ih, act_one_apply, _root_.pow_succ]

theorem pow_eq_one_of_kill {a b : O} {N : ℕ} (hab : a * b = (N : O)) (x : T ⟶ A) (hx : x ≫ ρ.act b = 1) :
    x ^ N = 1 := by
  rw [← act_nat_apply ρ x N, ← hab, act_mul_apply, hx]
  haveI := ρ.hom a
  exact one_compMon (ρ.act a)

end Act

theorem unitOn_injective {K : Type} [CommRing K] : Function.Injective (unitOn (R := K)) := by
  intro u v h
  apply Units.ext
  have h1 := congrArg (fun w : (Γ(Sp K, ⊤))ˣ =>
    (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (w : Γ(Sp K, ⊤))) h
  simpa [unitOn] using h1

section Sep

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem mem_nsmul_of_dvd (Dw : Datum H) (N : ℕ) (d : Dw.La)
    (h : ∀ b, (N : ℤ) ∣ Dw.EF b d) : ∃ f : Dw.La, d = N • f := by
  have skew : ∀ x y, Dw.EF x y = - Dw.EF y x := by
    intro x y
    have hxy := Dw.alt (x + y)
    simp only [map_add (f := _), LinearMap.add_apply, Dw.alt] at hxy
    linarith
  have hdiv : ∀ y, (N : ℤ) ∣ Dw.EF d y := fun y => by
    rw [skew]
    exact dvd_neg.mpr (h y)
  let φ : Dw.La →ₗ[ℤ] ℤ :=
    { toFun := fun y => Dw.EF d y / N
      map_add' := fun y z => by
        simp only [map_add (f := _)]
        exact Int.add_ediv_of_dvd_left (hdiv y)
      map_smul' := fun m y => by
        simp only [map_smul, smul_eq_mul, RingHom.id_apply]
        exact Int.mul_ediv_assoc _ (hdiv y) }
  obtain ⟨f, hf⟩ := Dw.unimod.2 φ
  refine ⟨f, Dw.unimod.1 (LinearMap.ext fun y => ?_)⟩
  rw [map_nsmul, LinearMap.smul_apply, hf]
  show Dw.EF d y = N • (Dw.EF d y / N)
  rw [nsmul_eq_mul, Int.mul_ediv_cancel' (hdiv y)]

theorem sep_core (A : PolAV (Sp (FractionRing R))) : letI := H.starRing
    ∀ (oA : A.OAct (𝓞 E)) (Dw : Datum H) (_I : TateIso Dw F (TFK (R := R) F ⟶ A.A) (fun a g => g ≫ oA.act a)
        (fun n g g' c => WeilIs A.A A.L n g g' (unitOn c))) (N : ℕ), 1 ≤ N →
      ∀ β u u' : 𝓞 E, β * star β = (N : 𝓞 E) → u * β + u' * star β = 1 →
      ∀ x x' : TFK (R := R) F ⟶ A.A, x ≫ oA.act (star β) = 1 → x' ≫ oA.act (star β) = 1 → x ≠ x' →
        ∃ z : TFK (R := R) F ⟶ A.A, z ≫ oA.act β = 1 ∧
          ∃ c c' : Γ((TFK (R := R) F).left, ⊤)ˣ,
            WeilIs A.A A.L N z x c ∧ WeilIs A.A A.L N z x' c' ∧ c ≠ c' := by
  let _ := H.starRing
  intro oA Dw I N hN β u u' hβ huu x x' hx hx' hne
  have hN0 : 0 < N := hN
  have hlin : ∀ (c : 𝓞 E) b, I.ev N (c • b) = I.ev N b ≫ oA.act c := fun c b => I.lin N c b
  obtain ⟨a, rfl⟩ := (I.onto N hN0 x).1 (pow_eq_one_of_kill oA.toRingAct hβ x hx)
  obtain ⟨a', rfl⟩ := (I.onto N hN0 x').1 (pow_eq_one_of_kill oA.toRingAct hβ x' hx')
  obtain ⟨e, he⟩ := (I.ker N hN0 (star β • a)).1 (by rw [hlin]; exact hx)
  obtain ⟨e', he'⟩ := (I.ker N hN0 (star β • a')).1 (by rw [hlin]; exact hx')
  have hdN : ∀ f : Dw.La, a - a' ≠ N • f := by
    intro f hf
    apply hne
    have : a = a' + N • f := by rw [← hf]; abel
    rw [this, I.add, (I.ker N hN0 _).2 ⟨f, rfl⟩, _root_.mul_one]
  obtain ⟨b0, hb0⟩ : ∃ b0 : Dw.La, ¬ ((N : ℤ) ∣ Dw.EF b0 (a - a')) := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    obtain ⟨f, hf⟩ := mem_nsmul_of_dvd Dw N (a - a') hcon
    exact hdN f hf
  have h1 : Dw.EF b0 (a - a') = Dw.EF ((u * β) • b0) (a - a') + Dw.EF ((u' * star β) • b0) (a - a') := by
    rw [← LinearMap.add_apply, ← map_add (f := _), ← add_smul, huu, one_smul]
  have h2 : (N : ℤ) ∣ Dw.EF ((u * β) • b0) (a - a') := by
    have hd' : H.bar (u * β) • (a - a') = N • (H.bar u • (e - e')) := by
      rw [map_mul, mul_smul, smul_sub]
      change H.bar u • (star β • a - star β • a') = _
      rw [he, he', ← smul_sub]
      exact smul_comm _ _ _
    rw [Dw.adj, hd', map_nsmul, nsmul_eq_mul]
    exact Dvd.intro _ rfl
  have hb : ¬ (N : ℤ) ∣ Dw.EF ((u' * star β) • b0) (a - a') := fun h => hb0 (by rw [h1]; exact dvd_add h2 h)
  refine ⟨I.ev N ((u' * star β) • b0), ?_, ?_⟩
  · rw [← hlin, smul_smul, show β * (u' * star β) = (N : 𝓞 E) * u' by rw [← hβ]; ring, mul_smul,
      Nat.cast_smul_eq_nsmul]
    exact (I.ker N hN0 _).2 ⟨_, rfl⟩
  · refine ⟨unitOn (I.ζ N ^ Dw.EF ((u' * star β) • b0) a), unitOn (I.ζ N ^ Dw.EF ((u' * star β) • b0) a'),
      I.isom N hN0 _ _, I.isom N hN0 _ _, fun hc => hb ?_⟩
    have hc' := unitOn_injective hc
    rw [← (I.ζ_prim N hN0).zpow_eq_one_iff_dvd, map_sub, zpow_sub, hc', _root_.mul_inv_cancel]

end Sep

theorem alphaPair_holds : AlphaPairStatement := by
  intro E _ _ _ H V _ _ _ t P _ α N hN hαN hu _ F _ _ _ Dw I x x' hx hx' hne
  obtain ⟨u, u', hu⟩ := hu
  exact sep_core (H := H) (R := V) (F := F) P.A P.oA Dw I N hN α u u' hαN hu x x' hx hx' hne

end ReciprocityTheory.ChartRestriction.G.H1
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SquareUnits
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TopologicalSpace Opposite

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.H1.SquareUnits

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic

variable {X Y Z : Scheme.{0}}

def UnitAt (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (y : Y) : Prop :=
  ∃ s : LB.Sec (LB.LinComb L φ ε), ∀ J, Good L y J → IsUnit (sval s (𝟙 Y) y J)

variable {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem UnitAt.mul {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} {y : Y}
    (h : UnitAt L φ ε y) (h' : UnitAt L φ' ε' y) : UnitAt L (Sum.elim φ φ') (Sum.elim ε ε') y := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨s', hs'⟩ := h'
  exact ⟨mulSec s s', fun J hJ => by rw [sval_mulSec s s' _ y hJ]; exact (hs J hJ).mul (hs' J hJ)⟩

theorem UnitAt.congr (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} {y : Y}
    (hf : FormEq φ ε φ' ε') (h : UnitAt L φ ε y) : UnitAt L φ' ε' y := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨s', hs'⟩ := exists_sec hL hf s
  exact ⟨s', fun J hJ => by rw [hs' Y (𝟙 Y) y J hJ]; exact hs J hJ⟩

theorem formEq_of_add {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (H : ∀ (U : Type) [AddCommGroup U] (h : (Y ⟶ X) → U), ∑ k, ε k • h (φ k) = ∑ k, ε' k • h (φ' k)) :
    FormEq φ ε φ' ε' := by
  intro U _ h
  apply Additive.ofMul.injective
  simpa only [ofMul_prod, ofMul_zpow] using H (Additive U) (fun ψ => Additive.ofMul (h ψ))

theorem exists_sec_of_pullGen {Y' : Scheme.{0}} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (h : Y' ⟶ Y)
    (c : LB.Gen ((LB.LinComb L φ ε).pull h)) (hc : c.IsGen) :
    ∃ s : LB.Sec (LB.LinComb L (fun k => h ≫ φ k) ε), ∀ (r : Z ⟶ Y') (z : Z) (J : (Z ⟶ X) → L.ι),
      Good L z J → IsUnit (sval s r z J) := by
  have l : ∀ j : K → L.ι, LB.wchart L (fun k => h ≫ φ k) j ≤
      LB.wchart (LB.LinComb L φ ε) (K := PUnit) (fun _ => h) (fun _ => j) :=
    fun _ _ hy => Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  have e1 : ∀ (j : K → L.ι) (y : Y'), y ∈ LB.wchart L (fun k => h ≫ φ k) j →
      gs (𝟙 Y') y _ (res (l j) (c.s (fun _ => j))).val =
        (gm (𝟙 Y') y (LB.wchart (LB.LinComb L φ ε) (K := PUnit) (fun _ => h) (fun _ => j)) (c.s (fun _ => j))).val :=
    fun j y hj => (gs_unit _ y _ hj _).trans (congrArg Units.val (gm_res _ y (l j) hj _))
  refine ⟨⟨fun j => (res (l j) (c.s (fun _ => j))).val, fun j j' => fn_ext fun y hy => ?_⟩, ?_⟩
  · refine ((gs_res (𝟙 Y') y _ hy _).trans (e1 j y hy.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Y') y _ hy _ _).trans
      (congrArg₂ (· * ·) ((gs_unit (𝟙 Y') y _ hy _).trans
        (congrArg Units.val (gm_linComb L _ _ (𝟙 Y') y j j' hy.1 hy.2))) ((gs_res (𝟙 Y') y _ hy _).trans
          (e1 j' y hy.2)))).symm)
    have m : ∀ j : K → L.ι, y ∈ LB.wchart L (fun k => h ≫ φ k) j → (𝟙 Y' ≫ h) y ∈ LB.wchart L φ j :=
      fun j hj => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hj k
    rw [gen_trans hc (𝟙 Y') y (l j hy.1) (l j' hy.2), Units.val_mul]
    congr 2
    simp only [trF, Finset.univ_unique, Finset.prod_singleton, zpow_one]
    exact (gm_linComb L φ ε (𝟙 Y' ≫ h) y j j' (m j hy.1) (m j' hy.2)).trans (by simp only [Category.assoc])
  · intro r z J hJ
    have hm := hJ.mem (fun k => h ≫ φ k) r
    exact (congrArg IsUnit (gs_unit r z _ hm _)).mpr (Units.isUnit _)

section Square

variable {k : Type} [Field k]

theorem spec_pt_eq (q q' : Spec (CommRingCat.of k)) : q = q' := by
  have h1 : PrimeSpectrum.asIdeal (R := k) q = ⊥ := @Ideal.eq_bot_of_prime k _ _ (PrimeSpectrum.isPrime (R := k) q)
  have h2 : PrimeSpectrum.asIdeal (R := k) q' = ⊥ := @Ideal.eq_bot_of_prime k _ _ (PrimeSpectrum.isPrime (R := k) q')
  exact PrimeSpectrum.ext (h1.trans h2.symm)

theorem unitAt_square (hsq : SquareSt) (P : PolAV (Spec (CommRingCat.of k)))
    (x₁ x₂ : baseOver (Spec (CommRingCat.of k)) ⟶ P.A) (y : (baseOver (Spec (CommRingCat.of k)) ⊗ P.A).left) :
    UnitAt P.L ![(translPt P.A (x₁ * x₂)).left, (snd (baseOver (Spec (CommRingCat.of k))) P.A).left,
      (translPt P.A x₁).left, (translPt P.A x₂).left] ![1, 1, -1, -1] y := by
  obtain ⟨V, hpV, c, hc⟩ := hsq (Spec (CommRingCat.of k)) P (baseOver (Spec (CommRingCat.of k))) x₁ x₂
    (IsLocalRing.closedPoint k)
  have hV : V = ⊤ := eq_top_iff.2 fun q _ => by rw [spec_pt_eq q (IsLocalRing.closedPoint k)]; exact hpV
  subst hV
  obtain ⟨s, hs⟩ := exists_sec_of_pullGen (Z := (baseOver (Spec (CommRingCat.of k)) ⊗ P.A).left)
    ((fst (baseOver (Spec (CommRingCat.of k))) P.A).left ⁻¹ᵁ ⊤).ι c hc
  let e := IsOpenImmersion.lift ((fst (baseOver (Spec (CommRingCat.of k))) P.A).left ⁻¹ᵁ ⊤).ι (𝟙 _)
    (by rintro _ ⟨q, rfl⟩; rw [Scheme.Opens.range_ι]; trivial)
  have he : e ≫ ((fst (baseOver (Spec (CommRingCat.of k))) P.A).left ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    IsOpenImmersion.lift_fac _ _ _
  refine UnitAt.congr P.isLB ?_ ⟨pullSec s e, fun J hJ => ?_⟩
  · refine formEq_of_add fun U _ hh => ?_
    simp only [← Category.assoc, he, Category.id_comp]
  · rw [sval_pullSec s e (𝟙 _) y hJ]
    exact hs _ y J hJ

theorem unitAt_iter (hsq : SquareSt) (P : PolAV (Spec (CommRingCat.of k)))
    (b : baseOver (Spec (CommRingCat.of k)) ⟶ P.A) (y : (baseOver (Spec (CommRingCat.of k)) ⊗ P.A).left) :
    ∀ n : ℕ, UnitAt P.L ![(translPt P.A (b ^ (n + 2))).left, (snd (baseOver (Spec (CommRingCat.of k))) P.A).left,
      (translPt P.A b).left] ![1, (n : ℤ) + 1, -((n : ℤ) + 2)] y
  | 0 => by
    refine UnitAt.congr P.isLB (formEq_of_add fun U _ hh => ?_) (unitAt_square hsq P b b y)
    simp [Fin.sum_univ_succ, pow_two]
    module
  | n + 1 => by
    refine UnitAt.congr P.isLB (formEq_of_add fun U _ hh => ?_)
      ((unitAt_iter hsq P b y n).mul (unitAt_square hsq P (b ^ (n + 2)) b y))
    have e : b ^ (n + 2) * b = b ^ (n + 1 + 2) := by rw [← pow_succ]
    simp [Fin.sum_univ_succ, e]
    module

end Square

end ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.FinOrdExists
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace ReciprocityTheory.ChartRestriction.G.H1

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR

theorem finOrdExists_of (hΦ : DVR.PhiFunStatement) (hP : PhiPowStatement) : FinOrdExistsStatement := by
  intro V _ _ _ D F _ _ _ k hk p w hw
  obtain ⟨Φ, hΦr⟩ := hΦ V (maximalIdeal V) D F k hk p w hw
  obtain ⟨c, hc, hcp⟩ := hP V (maximalIdeal V) D F k hk p w hw
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_pow_nat_eq (c⁻¹) (by omega : 0 < k)
  have hζc : ζ ^ k * c = 1 := by rw [hζ, inv_mul_cancel₀ hc]
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega), zero_mul] at hζc
    exact zero_ne_one hζc
  refine ⟨ζ, hζ0, k, hk, ?_⟩
  intro ss ts h

  have hpow : (Φ ^ k) (ss 0) = c • ss 0 := by
    have := hcp (fun i => (Φ ^ (i : ℕ)) (ss 0)) (by
      intro i
      rw [hΦr]
      simp only [Fin.val_succ, Fin.coe_castSucc, pow_succ', Module.End.mul_apply])
    rw [isSmul_iff] at this
    simpa using this
  have key : ∀ n : ℕ, (hn : n ≤ k) → ss ⟨n, by omega⟩ = ζ ^ n • (Φ ^ n) (ss 0) := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      obtain ⟨h1, h2⟩ := h ⟨n, by omega⟩
      rw [hΦr] at h1
      rw [isSmul_iff] at h2
      have e : ss ⟨n + 1, by omega⟩ = ss (Fin.succ ⟨n, by omega⟩) := rfl
      have e0 : ss ⟨n, by omega⟩ = ss (Fin.castSucc ⟨n, by omega⟩) := rfl
      rw [e, h2, h1, ← e0, ih (by omega), LinearMap.map_smul, smul_smul, pow_succ' ζ n, pow_succ' Φ n,
        Module.End.mul_apply]
  have hlast : ss (Fin.last k) = ss 0 := by
    have := key k le_rfl
    have e : ss (Fin.last k) = ss ⟨k, by omega⟩ := rfl
    rw [e, this, hpow, smul_smul, hζc, one_smul]
  intro α j
  rw [hlast]

end ReciprocityTheory.ChartRestriction.G.H1
end
end

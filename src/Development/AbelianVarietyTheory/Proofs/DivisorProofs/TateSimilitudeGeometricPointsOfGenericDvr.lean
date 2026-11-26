module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsReductionPointsAbelianSchemeValuationRing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaLocal
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory.WeilSpecialise

open ReciprocityTheory.ChartRestriction.G.Out

theorem exists_theta_local {S : Scheme.{0}} (G : Over S) [GrpObj G] (hA : IsAbelianScheme G)
    (L : LB G.left) (hL : L.IsLB) (U : Type) [CommRing U] [IsLocalRing U] (u : Sp U ⟶ S) (n : ℕ)
    (x : Over.mk u ⟶ G) (hx : x ^ n = 1) : ∃ θ : ThetaGrp G L (n : ℤ) (Over.mk u), θ.pt = x := by
  have := hA.comm
  set a : Over.mk u ⊗ G ⟶ G := fst (Over.mk u) G ≫ x with ha
  set y : Over.mk u ⊗ G ⟶ G := snd (Over.mk u) G with hy
  have cube := GlobalTheory.CubeTop.cubeTheorem S G hA L hL (Over.mk u ⊗ G)
  have key : ∀ m : ℕ, ∃ t : LB.Gen (LB.LinComb L
      ![(a ^ m * y).left, (a ^ m).left, (a * y).left, a.left, y.left, (1 : Over.mk u ⊗ G ⟶ G).left]
      ![1, -1, -(m : ℤ), (m : ℤ), (m : ℤ) - 1, 1 - (m : ℤ)]), t.IsGen := by
    intro m
    induction m with
    | zero =>
      obtain ⟨t, ht⟩ := cube 1 a y
      obtain ⟨t', ht', -⟩ := Geo.Tor.exists_gen hL (K' := Fin 6)
        (φ' := ![(a ^ 0 * y).left, (a ^ 0).left, (a * y).left, a.left, y.left, (1 : Over.mk u ⊗ G ⟶ G).left])
        (ε' := ![1, -1, -((0 : ℕ) : ℤ), ((0 : ℕ) : ℤ), ((0 : ℕ) : ℤ) - 1, 1 - ((0 : ℕ) : ℤ)]) (fun V _ g => by
          simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
            Matrix.cons_val_one, pow_zero, _root_.one_mul]
          apply Additive.ofMul.injective
          simp only [ofMul_mul, ofMul_zpow, ofMul_one]
          push_cast
          module) t ht
      exact ⟨t', ht'⟩
    | succ m ih =>
      obtain ⟨t, ht⟩ := ih
      obtain ⟨c, hc⟩ := cube (a ^ m) a y
      have e₁ : a ^ m * a * y = a ^ (m + 1) * y := by rw [pow_succ]
      have e₂ : a ^ m * a = a ^ (m + 1) := by rw [pow_succ]
      obtain ⟨t', ht', -⟩ := Geo.Tor.exists_gen hL (K' := Fin 6)
        (φ' := ![(a ^ (m + 1) * y).left, (a ^ (m + 1)).left, (a * y).left, a.left, y.left,
          (1 : Over.mk u ⊗ G ⟶ G).left])
        (ε' := ![1, -1, -((m + 1 : ℕ) : ℤ), ((m + 1 : ℕ) : ℤ), ((m + 1 : ℕ) : ℤ) - 1, 1 - ((m + 1 : ℕ) : ℤ)])
        (fun V _ g => by
          rw [Fintype.prod_sum_type]
          simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
            Matrix.cons_val_succ, Matrix.cons_val_one, e₁, e₂]
          apply Additive.ofMul.injective
          simp only [ofMul_mul, ofMul_zpow, ofMul_one]
          push_cast
          module)
        (LB.mulGen L _ _ _ _ t c) (DVR.mulGen_isGen _ _ _ _ _ _ _ ht hc)
      exact ⟨t', ht'⟩
  obtain ⟨t, ht⟩ := key n
  have han : a ^ n = 1 := by rw [ha, ← MonObj.comp_pow, hx, MonObj.comp_one]
  obtain ⟨e, he⟩ := DVR.exists_gen_of_local (V := U) L hL (K := Fin 2)
    ![x.left, (1 : Over.mk u ⟶ G).left] ![-(n : ℤ), n]
  have h1 : (fst (Over.mk u) G).left ≫ (1 : Over.mk u ⟶ G).left = (1 : Over.mk u ⊗ G ⟶ G).left := by
    rw [← Over.comp_left, MonObj.comp_one]
  have h2 : (fst (Over.mk u) G).left ≫ x.left = a.left := rfl
  have h3 : translPt G x = a * y := rfl
  obtain ⟨w, hw, -⟩ := Geo.Tor.exists_gen hL (K' := Fin 2)
    (φ' := ![(snd (Over.mk u) G).left, (translPt G x).left]) (ε' := ![(n : ℤ), -(n : ℤ)]) (fun V _ g => by
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, Matrix.cons_val_one, han, h1, h2, h3, _root_.one_mul]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow, ofMul_one]
      module)
    (LB.mulGen L _ _ _ _ t (LB.pullGen L _ _ e (fst (Over.mk u) G).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.pullGen_isGen _ _ _ _ he _))
  exact ⟨⟨x, w, hw⟩, rfl⟩

end GlobalTheory.WeilSpecialise

namespace GlobalTheory.WeilSpecialise

open ReciprocityTheory.ChartRestriction.G.Out

theorem unitOn_surjective {R : Type} [CommRing R] : Function.Surjective (unitOn (R := R)) :=
  (Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.toMulEquiv).bijective.2

theorem map_unitOn {R R' : Type} [CommRing R] [CommRing R'] (j : R →+* R') (c : Rˣ) :
    Units.map (spMap j).appTop.hom.toMonoidHom (unitOn c) = unitOn (Units.map j.toMonoidHom c) :=
  Units.ext (congrArg (fun q => q.hom c.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom j))).symm

theorem unitOn_inj {R : Type} [CommRing R] : Function.Injective (unitOn (R := R)) := fun _ _ h =>
  Units.ext ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).1 (congrArg Units.val h))

theorem weilIs_specialise : ∀ (U Ω : Type) [CommRing U] [IsDomain U] [ValuationRing U] [Field Ω] [Algebra U Ω] [IsFractionRing U Ω] (S : Scheme.{0}) (G : Over S) [GrpObj G], IsAbelianScheme G → ∀ (Lb : LB G.left), Lb.IsLB → ∀ (u : Sp U ⟶ S) (n : ℕ), IsUnit (n : U) → ∀ (P Q : Over.mk u ⟶ G) (c : Uˣ), P ^ n = 1 → Q ^ n = 1 → ∀ (P' Q' : Over.mk (spMap (algebraMap U Ω) ≫ u) ⟶ G), P'.left = spMap (algebraMap U Ω) ≫ P.left → Q'.left = spMap (algebraMap U Ω) ≫ Q.left → Out.WeilIs G Lb n P' Q' (unitOn (Units.map (algebraMap U Ω : U →* Ω) c)) → ∀ (k : Type) [Field k] (h : U →+* k) (P₀ Q₀ : Over.mk (spMap h ≫ u) ⟶ G), P₀.left = spMap h ≫ P.left → Q₀.left = spMap h ≫ Q.left → Out.WeilIs G Lb n P₀ Q₀ (unitOn (Units.map (h : U →* k) c)) := by
  intro U Ω _ _ _ _ _ _ S G _ hA Lb hLb u n _ P Q c hP hQ P' Q' hP' hQ' HΩ k _ h P₀ Q₀ hP₀ hQ₀
  have hG := globalFns_holds
  have loc : ∀ z : Over.mk u ⟶ G, z ^ n = 1 → ∀ p : (Over.mk u).left, ∃ V : (Over.mk u).left.Opens, p ∈ V ∧
      ∃ θ : ThetaGrp G Lb (n : ℤ) (overRes V), θ.pt = overResι V ≫ z := fun z hz p => by
    obtain ⟨θ, hθ⟩ := exists_theta_local G hA Lb hLb U u n z hz
    obtain ⟨θ', h'⟩ := GlobalTheory.CommutatorPairing.exists_pull hLb θ (overResι (⊤ : (Over.mk u).left.Opens))
    exact ⟨⊤, trivial, θ', h'.trans (by rw [hθ])⟩
  obtain ⟨c₀, hc₀⟩ := GlobalTheory.CommutatorPairing.exists_weilIs hG hA hLb (loc P hP) (loc Q hQ)
  obtain ⟨c₁, rfl⟩ := unitOn_surjective c₀
  let iΩ : Over.mk (spMap (algebraMap U Ω) ≫ u) ⟶ Over.mk u := Over.homMk (spMap (algebraMap U Ω)) rfl
  have eP : P' = iΩ ≫ P := Over.OverMorphism.ext hP'
  have eQ : Q' = iΩ ≫ Q := Over.OverMorphism.ext hQ'
  have H₁ := GlobalTheory.CommPairing.weilIs_pull hG hA hLb iΩ hc₀
  rw [← eP, ← eQ] at H₁
  have H₁' : Out.WeilIs G Lb n P' Q' (unitOn (Units.map (algebraMap U Ω).toMonoidHom c₁)) := by
    rw [← map_unitOn]; exact H₁
  have e := GlobalTheory.CommutatorPairing.weilIs_unique hG hA hLb H₁' HΩ
  have e' := unitOn_inj e
  have hc : c₁ = c := Units.ext (IsFractionRing.injective U Ω (congrArg Units.val e'))
  subst hc
  let ik : Over.mk (spMap h ≫ u) ⟶ Over.mk u := Over.homMk (spMap h) rfl
  have eP₀ : P₀ = ik ≫ P := Over.OverMorphism.ext hP₀
  have eQ₀ : Q₀ = ik ≫ Q := Over.OverMorphism.ext hQ₀
  have H₂ := GlobalTheory.CommPairing.weilIs_pull hG hA hLb ik hc₀
  rw [← eP₀, ← eQ₀] at H₂
  have := map_unitOn h c₁
  exact this ▸ H₂

end GlobalTheory.WeilSpecialise
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLiftUniqueValuationRingAlgClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLiftUniqueValuationRingAlgClosed
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.TorsionLiftVal

theorem sections_restrict_bijective (U Ω k : Type) [CommRing U] [IsDomain U] [ValuationRing U] [Field Ω]
    [IsAlgClosed Ω] [Algebra U Ω] [IsFractionRing U Ω] [Field k] [IsAlgClosed k] (h : U →+* k)
    {X : Scheme.{0}} (p : X ⟶ Sp U) [IsFinite p] [Etale p] :
    Function.Bijective (fun s : {s : Sp U ⟶ X // s ≫ p = 𝟙 _} =>
      (⟨spMap h ≫ s.1, by rw [Category.assoc, s.2, Category.comp_id]⟩ : {x : Sp k ⟶ X // x ≫ p = spMap h})) := by
  have inj : Function.Injective (fun s : {s : Sp U ⟶ X // s ≫ p = 𝟙 _} =>
      (⟨spMap h ≫ s.1, by rw [Category.assoc, s.2, Category.comp_id]⟩ : {x : Sp k ⟶ X // x ≫ p = spMap h})) := by
    rintro ⟨s₁, h₁⟩ ⟨s₂, h₂⟩ e
    have e' : spMap h ≫ s₁ = spMap h ≫ s₂ := congrArg Subtype.val e
    haveI : LocallyOfFiniteType (Over.mk p).hom := inferInstanceAs (LocallyOfFiniteType p)
    haveI : FormallyUnramified (Over.mk p).hom := inferInstanceAs (FormallyUnramified p)
    haveI : IsSeparated (Over.mk p).hom := inferInstanceAs (IsSeparated p)
    let f₁ : Over.mk (𝟙 (Sp U)) ⟶ Over.mk p := Over.homMk s₁ h₁
    let f₂ : Over.mk (𝟙 (Sp U)) ⟶ Over.mk p := Over.homMk s₂ h₂
    have hr := (FinEt.comp_eq_comp_iff_range f₁ f₂ (spMap h)).1 e'
    haveI : PreconnectedSpace (Over.mk (𝟙 (Sp U))).left := inferInstanceAs (PreconnectedSpace (Sp U))
    have hc : IsClopen (Set.range (FinEt.agreeι f₁ f₂)) :=
      ⟨(FinEt.agreeι f₁ f₂).isClosedEmbedding.isClosed_range, (FinEt.agreeι f₁ f₂).isOpenEmbedding.isOpen_range⟩
    obtain ⟨z⟩ : Nonempty (Sp k) := inferInstance
    have hu : Set.range (FinEt.agreeι f₁ f₂) = Set.univ := hc.eq_univ ⟨_, hr ⟨z, rfl⟩⟩
    have := (FinEt.comp_eq_comp_iff_range f₁ f₂ (𝟙 _)).2 (by rw [hu]; exact Set.subset_univ _)
    apply Subtype.ext
    simpa [f₁, f₂] using this
  obtain ⟨z⟩ : Nonempty (Sp k) := inferInstance
  obtain ⟨w⟩ : Nonempty (Sp Ω) := inferInstance
  obtain ⟨hBfin, hB⟩ := FinEt.card_points_eq_finrank p (spMap h) z
  obtain ⟨-, hC⟩ := FinEt.card_points_eq_finrank p (spMap (algebraMap U Ω)) w
  haveI := hBfin
  haveI : Finite {s : Sp U ⟶ X // s ≫ p = 𝟙 _} := Finite.of_injective _ inj
  have hv : ValuativeCriterion p := by
    have hp : IsProper p := inferInstance
    rw [IsProper.eq_valuativeCriterion] at hp
    exact hp.1.1.1
  let r : {s : Sp U ⟶ X // s ≫ p = 𝟙 _} → {x : Sp Ω ⟶ X // x ≫ p = spMap (algebraMap U Ω)} :=
    fun s => ⟨spMap (algebraMap U Ω) ≫ s.1, by rw [Category.assoc, s.2, Category.comp_id]⟩
  have hrs : Function.Surjective r := by
    rintro ⟨x, hx⟩
    let Q : ValuativeCommSq p :=
      { R := U, K := Ω, i₁ := x, i₂ := 𝟙 _, commSq := ⟨hx.trans (Category.comp_id _).symm⟩ }
    obtain ⟨W⟩ := hv Q
    exact ⟨⟨W.default.l, W.default.fac_right⟩, Subtype.ext W.default.fac_left⟩
  have hle := Nat.card_le_card_of_surjective r hrs
  have hrank := (Scheme.Hom.isLocallyConstant_finrank p).apply_eq_of_preconnectedSpace (spMap h z)
    (spMap (algebraMap U Ω) w)
  refine inj.bijective_of_nat_card_le ?_
  rw [hB, hrank, ← hC]
  exact hle

theorem torsion_lift_unique : ∀ (U Ω k : Type) [CommRing U] [IsDomain U] [ValuationRing U] [Field Ω] [IsAlgClosed Ω] [Algebra U Ω] [IsFractionRing U Ω] [Field k] [IsAlgClosed k] (h : U →+* k) (S : Scheme.{0}) (G : Over S) [GrpObj G], IsAbelianScheme G → ∀ (u : Sp U ⟶ S) (n : ℕ), IsUnit (n : U) → ∀ y : Over.mk (spMap h ≫ u) ⟶ G, y ^ n = 1 → ∃! P : Over.mk u ⟶ G, P ^ n = 1 ∧ y.left = spMap h ≫ P.left := by
  intro U Ω k _ _ _ _ _ _ _ _ _ h S G _ hA u n hn y hy
  letI : GrpObj ((Over.pullback u).obj G) := Functor.grpObjObj
  have hgp : IsGrpPullback ((Over.pullback u).obj G) G u (pullback.fst G.hom u) := isGrpPullback_pullback G u
  haveI : IsAbelianScheme ((Over.pullback u).obj G) := GlobalTheory.isAbelianScheme_pullback_obj u G hA
  have hnU : IsUnit (n : Γ(Sp U, ⊤)) := by
    simpa using hn.map (Scheme.ΓSpecIso (CommRingCat.of U)).inv.hom
  obtain ⟨-, hfin, het⟩ := GrpTangent.finiteEtale_mulN_torsion ((Over.pullback u).obj G) hnU
  have key : ∀ {X : Scheme.{0}} (t : X ⟶ Sp U) (b : X ⟶ S), b = t ≫ u →
      ∃ Φ : (Over.mk t ⟶ torsion ((Over.pullback u).obj G) n) → (Over.mk b ⟶ G),
        Function.Injective Φ ∧ (∀ a, Φ a ^ n = 1) ∧ (∀ w : Over.mk b ⟶ G, w ^ n = 1 → ∃ a, Φ a = w) ∧
        ∀ a, (Φ a).left = a.left ≫ (torsion.ι ((Over.pullback u).obj G) n).left ≫ pullback.fst G.hom u := by
    intro X t b hb
    obtain ⟨e, he⟩ := exists_mulEquiv_of_isGrpPullback hgp t b hb
    refine ⟨fun a => e ((TorsionUnram.torsionEquiv _ n _) a).1, ?_, ?_, ?_, ?_⟩
    · intro a₁ a₂ h12
      exact (TorsionUnram.torsionEquiv _ n _).injective (Subtype.ext (e.injective h12))
    · intro a
      rw [← map_pow, ((TorsionUnram.torsionEquiv _ n _) a).2, map_one]
    · intro w hw
      refine ⟨(TorsionUnram.torsionEquiv _ n _).symm ⟨e.symm w, by rw [← map_pow, hw, map_one]⟩, ?_⟩
      simp
    · intro a
      rw [he, ← Category.assoc]
      rfl
  obtain ⟨Φk, injk, -, surjk, hk⟩ := key (spMap h) (spMap h ≫ u) rfl
  obtain ⟨ΦU, -, powU, surjU, hUl⟩ := key (𝟙 (Sp U)) u (Category.id_comp u).symm
  obtain ⟨τ, rfl⟩ := surjk y hy
  have hb := sections_restrict_bijective U Ω k h (torsion ((Over.pullback u).obj G) n).hom
  obtain ⟨⟨s, hs⟩, hs'⟩ := hb.2 ⟨τ.left, Over.w τ⟩
  have hs'' : spMap h ≫ s = τ.left := congrArg Subtype.val hs'
  let σ : Over.mk (𝟙 (Sp U)) ⟶ torsion ((Over.pullback u).obj G) n := Over.homMk s hs
  refine ⟨ΦU σ, ⟨powU σ, ?_⟩, ?_⟩
  · rw [hk, hUl, ← hs'']
    simp [σ]
  · rintro P ⟨hP, hPy⟩
    obtain ⟨σ', rfl⟩ := surjU P hP
    have hσ' : σ'.left ≫ (torsion ((Over.pullback u).obj G) n).hom = 𝟙 _ := Over.w σ'
    let τ' : Over.mk (spMap h) ⟶ torsion ((Over.pullback u).obj G) n :=
      Over.homMk (spMap h ≫ σ'.left) (by rw [Category.assoc, hσ']; exact Category.comp_id _)
    have e0 : Φk τ' = Φk τ := by
      apply Over.OverMorphism.ext
      rw [hk, hPy, hUl]
      simp [τ']
    have e1 : spMap h ≫ σ'.left = τ.left := congrArg (fun q => q.left) (injk e0)
    have e2 := hb.1 (a₁ := ⟨σ'.left, hσ'⟩) (a₂ := ⟨s, hs⟩) (Subtype.ext (e1.trans hs''.symm))
    have e3 : σ' = σ := Over.OverMorphism.ext (congrArg Subtype.val e2)
    rw [e3]

end GlobalTheory.TorsionLiftVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLiftUniqueValuationRingAlgClosedStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_lift_unique_valuationRing_algClosed : ∀ (U Ω k : Type) [CommRing U] [IsDomain U] [ValuationRing U] [Field Ω] [IsAlgClosed Ω] [Algebra U Ω] [IsFractionRing U Ω] [Field k] [IsAlgClosed k] (h : U →+* k) (S : Scheme.{0}) (G : Over S) [GrpObj G], IsAbelianScheme G → ∀ (u : Sp U ⟶ S) (n : ℕ), IsUnit (n : U) → ∀ y : Over.mk (spMap h ≫ u) ⟶ G, y ^ n = 1 → ∃! P : Over.mk u ⟶ G, P ^ n = 1 ∧ y.left = spMap h ≫ P.left := by
  first | exact @GlobalTheory.TorsionLiftVal.torsion_lift_unique | exact GlobalTheory.TorsionLiftVal.torsion_lift_unique | (intros; apply GlobalTheory.TorsionLiftVal.torsion_lift_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsReductionPointsAbelianSchemeValuationRing
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.ValReduction

theorem reduction_points : ∀ (U Ω k : Type) [CommRing U] [IsDomain U] [ValuationRing U] [Field Ω] [IsAlgClosed Ω] [Algebra U Ω] [IsFractionRing U Ω] [Field k] [IsAlgClosed k] (h : U →+* k) (S : Scheme.{0}) (G : Over S) [GrpObj G], IsAbelianScheme G → ∀ u : Sp U ⟶ S, ∃ r : (Over.mk (spMap (algebraMap U Ω) ≫ u) ⟶ G) →* (Over.mk (spMap h ≫ u) ⟶ G), (∀ (P : Over.mk u ⟶ G) y y₀, y.left = spMap (algebraMap U Ω) ≫ P.left → y₀.left = spMap h ≫ P.left → r y = y₀) ∧ (∀ (f : G ⟶ G) y, r (y ≫ f) = r y ≫ f) ∧ (∀ n : ℕ, IsUnit (n : U) → Set.BijOn r {y | y ^ n = 1} {y | y ^ n = 1}) ∧ ∀ (Lb : LB G.left), Lb.IsLB → ∀ n : ℕ, IsUnit (n : U) → ∀ y y' (c : Uˣ), y ^ n = 1 → y' ^ n = 1 → Out.WeilIs G Lb n y y' (unitOn (Units.map (algebraMap U Ω : U →* Ω) c)) → Out.WeilIs G Lb n (r y) (r y') (unitOn (Units.map (h : U →* k) c)) := by
  intro U Ω k _ _ _ _ _ _ _ _ _ h S G _ hA u
  obtain ⟨e, he⟩ := GlobalTheory.ValPts.points_generic_mulEquiv U Ω S G hA.proper u
  let Vk : Over.mk (spMap h ≫ u) ⟶ Over.mk u := Over.homMk (spMap h) rfl
  let φ : (Over.mk u ⟶ G) →* (Over.mk (spMap h ≫ u) ⟶ G) :=
    MonoidHom.mk' (Vk ≫ ·) fun x y => MonObj.comp_mul Vk x y
  have hφ : ∀ P, (φ P).left = spMap h ≫ P.left := fun P => rfl
  have hes : ∀ (P : Over.mk u ⟶ G) y, y.left = spMap (algebraMap U Ω) ≫ P.left → e.symm y = P := by
    intro P y hy
    rw [MulEquiv.symm_apply_eq]
    exact Over.OverMorphism.ext (hy.trans (he P).symm)
  have hey : ∀ y, y.left = spMap (algebraMap U Ω) ≫ (e.symm y).left := fun y => by
    rw [← he]; simp
  refine ⟨φ.comp e.symm.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · intro P y y₀ hy hy₀
    apply Over.OverMorphism.ext
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [hes P y hy, hφ, hy₀]
  · intro f y
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    have : e.symm (y ≫ f) = e.symm y ≫ f := hes _ _ (by
      rw [Over.comp_left, hey y, Category.assoc, Over.comp_left])
    rw [this]
    exact (Category.assoc Vk (e.symm y) f).symm
  · intro n hn
    refine ⟨fun y (hy : y ^ n = 1) => (show _ ^ n = 1 by rw [← map_pow, hy, map_one]), ?_, ?_⟩
    · intro y (hy : y ^ n = 1) y' (hy' : y' ^ n = 1) hyy
      have hP : (e.symm y) ^ n = 1 := by rw [← map_pow, hy, map_one]
      have hP' : (e.symm y') ^ n = 1 := by rw [← map_pow, hy', map_one]
      obtain ⟨Q, -, hQ⟩ := GlobalTheory.T.torsion_lift_unique_valuationRing_algClosed U Ω k h S G hA u n hn
        ((φ.comp e.symm.toMonoidHom) y) (by rw [← map_pow, hy, map_one])
      have h1 := hQ (e.symm y) ⟨hP, rfl⟩
      have h2 := hQ (e.symm y') ⟨hP', by rw [hyy]; rfl⟩
      exact e.symm.injective (h1.trans h2.symm)
    · intro y₀ (hy₀ : y₀ ^ n = 1)
      obtain ⟨P, ⟨hP, hPy⟩, -⟩ := GlobalTheory.T.torsion_lift_unique_valuationRing_algClosed U Ω k h S G hA u n hn y₀ hy₀
      refine ⟨e P, (show e P ^ n = 1 by rw [← map_pow, hP, map_one]), ?_⟩
      apply Over.OverMorphism.ext
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
      rw [hφ, hPy]
  · intro Lb hLb n hn y y' c hy hy' H
    have hP : (e.symm y) ^ n = 1 := by rw [← map_pow, hy, map_one]
    have hP' : (e.symm y') ^ n = 1 := by rw [← map_pow, hy', map_one]
    exact GlobalTheory.WeilSpecialise.weilIs_specialise U Ω S G hA Lb hLb u n hn (e.symm y) (e.symm y') c hP hP' y y'
      (hey y) (hey y') H k h _ _ rfl rfl

end GlobalTheory.ValReduction
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsReductionPointsAbelianSchemeValuationRingStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_reduction_points_abelianScheme_valuationRing : ∀ (U Ω k : Type) [CommRing U] [IsDomain U] [ValuationRing U] [Field Ω] [IsAlgClosed Ω] [Algebra U Ω] [IsFractionRing U Ω] [Field k] [IsAlgClosed k] (h : U →+* k) (S : Scheme.{0}) (G : Over S) [GrpObj G], IsAbelianScheme G → ∀ u : Sp U ⟶ S, ∃ r : (Over.mk (spMap (algebraMap U Ω) ≫ u) ⟶ G) →* (Over.mk (spMap h ≫ u) ⟶ G), (∀ (P : Over.mk u ⟶ G) y y₀, y.left = spMap (algebraMap U Ω) ≫ P.left → y₀.left = spMap h ≫ P.left → r y = y₀) ∧ (∀ (f : G ⟶ G) y, r (y ≫ f) = r y ≫ f) ∧ (∀ n : ℕ, IsUnit (n : U) → Set.BijOn r {y | y ^ n = 1} {y | y ^ n = 1}) ∧ ∀ (Lb : LB G.left), Lb.IsLB → ∀ n : ℕ, IsUnit (n : U) → ∀ y y' (c : Uˣ), y ^ n = 1 → y' ^ n = 1 → Out.WeilIs G Lb n y y' (unitOn (Units.map (algebraMap U Ω : U →* Ω) c)) → Out.WeilIs G Lb n (r y) (r y') (unitOn (Units.map (h : U →* k) c)) := by
  first | exact @GlobalTheory.ValReduction.reduction_points | exact GlobalTheory.ValReduction.reduction_points | (intros; apply GlobalTheory.ValReduction.reduction_points <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricPointDvrFactorsValuationSubringClosure
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsValuationSubringExtendingRingHom
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsValuationSubringExtendingRingHom
namespace GlobalTheory.ValExt

theorem ker_isMaximal (Ω k : Type) [Field Ω] [Field k] (A : Subring Ω) (h : A →+* k)
    (hloc : ∀ a : A, h a ≠ 0 → (a : Ω)⁻¹ ∈ A) : (RingHom.ker h).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  refine ⟨by simp, fun J a hJ ha haJ => ?_⟩
  have ha' : h a ≠ 0 := fun e => ha (RingHom.mem_ker.2 e)
  have hinv := hloc a ha'
  have ha0 : (a : Ω) ≠ 0 := fun e => ha' (by rw [show a = 0 from Subtype.ext e, map_zero])
  have : (1 : A) = ⟨(a : Ω)⁻¹, hinv⟩ * a := Subtype.ext (by simp [inv_mul_cancel₀ ha0])
  rw [this]
  exact J.mul_mem_left _ haJ

theorem exists_ext_local (Ω k : Type) [Field Ω] [Field k] (A : Subring Ω) (h : A →+* k) :
    ∃ (B : Subring Ω) (hAB : A ≤ B) (h' : B →+* k), (∀ b : B, h' b ≠ 0 → (b : Ω)⁻¹ ∈ B) ∧
      ∀ a : A, h' (Subring.inclusion hAB a) = h a := by
  let p := RingHom.ker h
  haveI : p.IsPrime := RingHom.ker_isPrime h
  let L := Localization.AtPrime p
  have hs : ∀ s : p.primeCompl, h s ≠ 0 := fun s e => s.2 (RingHom.mem_ker.2 e)
  have hs' : ∀ s : p.primeCompl, ((s : A) : Ω) ≠ 0 := fun s e =>
    hs s (by rw [show (s : A) = 0 from Subtype.ext e, map_zero])
  let ι : L →+* Ω := IsLocalization.lift (M := p.primeCompl) (g := A.subtype) (fun s => (hs' s).isUnit)
  let hL : L →+* k := IsLocalization.lift (M := p.primeCompl) (g := h) (fun s => (hs s).isUnit)
  have hι : ∀ a : A, ι (algebraMap A L a) = a := fun a => IsLocalization.lift_eq _ _
  have hhL : ∀ a : A, hL (algebraMap A L a) = h a := fun a => IsLocalization.lift_eq _ _
  have hmk : ∀ (a : A) (s : p.primeCompl), ι (IsLocalization.mk' L a s) * ((s : A) : Ω) = a := by
    intro a s
    rw [← hι, ← map_mul, IsLocalization.mk'_spec, hι]
  have hmkL : ∀ (a : A) (s : p.primeCompl), hL (IsLocalization.mk' L a s) * h s = h a := by
    intro a s
    rw [← hhL, ← map_mul, IsLocalization.mk'_spec, hhL]
  have hinj : Function.Injective ι := by
    intro z z' e
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl z
    obtain ⟨⟨a', s'⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl z'
    rw [IsLocalization.mk'_eq_iff_eq]
    congr 1
    apply Subtype.ext
    have h1 := hmk a s
    have h2 := hmk a' s'
    simp only [Subring.coe_mul]
    rw [← h1, ← h2, e]
    ring
  let B : Subring Ω := ι.range
  let e : L ≃+* B := RingEquiv.ofBijective ι.rangeRestrict
    ⟨fun a b e' => hinj (congrArg Subtype.val e'), ι.rangeRestrict_surjective⟩
  have hAB : A ≤ B := fun a ha => ⟨algebraMap A L ⟨a, ha⟩, hι _⟩
  refine ⟨B, hAB, hL.comp e.symm.toRingHom, fun b hb => ?_, fun a => ?_⟩
  · obtain ⟨z, rfl⟩ : ∃ z, e z = b := e.surjective b
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      RingEquiv.symm_apply_apply] at hb
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl z
    have ha : h a ≠ 0 := fun e0 => hb (by
      have := hmkL a s
      rw [e0] at this
      exact (mul_eq_zero.1 this).resolve_right (hs s))
    let t : p.primeCompl := ⟨a, fun e0 => ha (RingHom.mem_ker.1 e0)⟩
    refine ⟨IsLocalization.mk' L (s : A) t, ?_⟩
    show ι _ = (ι (IsLocalization.mk' L a s))⁻¹
    have h1 := hmk a s
    have h2 := hmk (s : A) t
    have ha0 : ((a : A) : Ω) ≠ 0 := hs' t
    apply eq_inv_of_mul_eq_one_left
    have : ι (IsLocalization.mk' L (s : A) t) * ι (IsLocalization.mk' L a s) * (((a : A) : Ω) * ((s : A) : Ω)) =
        1 * (((a : A) : Ω) * ((s : A) : Ω)) := by
      calc _ = (ι (IsLocalization.mk' L (s : A) t) * ((t : A) : Ω)) * (ι (IsLocalization.mk' L a s) * ((s : A) : Ω)) := by
              simp only [t]; ring
        _ = _ := by rw [h1, h2]; ring
    exact mul_right_cancel₀ (mul_ne_zero ha0 (hs' s)) this
  · have : e.symm (Subring.inclusion hAB a) = algebraMap A L a := by
      apply e.injective
      rw [RingEquiv.apply_symm_apply]
      exact Subtype.ext (hι a).symm
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, this, hhL]

theorem exists_ext_adjoin (Ω k : Type) [Field Ω] [Field k] [IsAlgClosed k] (A : Subring Ω) (h : A →+* k)
    (hloc : ∀ a : A, h a ≠ 0 → (a : Ω)⁻¹ ∈ A) (y : Ω) (M : Ideal (Algebra.adjoin A {y})) [M.IsMaximal]
    (hM : RingHom.ker h ≤ M.comap (algebraMap A (Algebra.adjoin A {y}))) :
    ∃ h' : Algebra.adjoin A {y} →+* k, ∀ a : A, h' (algebraMap A _ a) = h a := by
  haveI := ker_isMaximal Ω k A h hloc
  let K₀ := A ⧸ RingHom.ker h
  let K₁ := (Algebra.adjoin A {y}) ⧸ M
  letI : Field K₁ := Ideal.Quotient.field M
  letI : Field K₀ := Ideal.Quotient.field _
  let f₀ : K₀ →+* K₁ := Ideal.quotientMap M (algebraMap A (Algebra.adjoin A {y})) hM
  letI : Algebra K₀ K₁ := f₀.toAlgebra
  let hb : K₀ →+* k := Ideal.Quotient.lift (RingHom.ker h) h (fun a ha => ha)
  letI : Algebra K₀ k := hb.toAlgebra
  haveI : IsScalarTower A K₀ K₁ := IsScalarTower.of_algebraMap_eq (fun a => rfl)
  haveI : Algebra.FiniteType A (Algebra.adjoin A {y}) := .adjoin_of_finite (Set.finite_singleton y)
  haveI : Algebra.FiniteType A K₁ :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ A M) Ideal.Quotient.mk_surjective
  haveI : Algebra.FiniteType K₀ K₁ := Algebra.FiniteType.of_restrictScalars_finiteType A K₀ K₁
  haveI : Module.Finite K₀ K₁ := finite_of_finite_type_of_isJacobsonRing K₀ K₁
  haveI : Algebra.IsIntegral K₀ K₁ := Algebra.IsIntegral.of_finite K₀ K₁
  haveI : Module.IsTorsionFree K₀ K₁ := DivisionSemiring.to_moduleIsTorsionFree
  haveI : Module.IsTorsionFree K₀ k := DivisionSemiring.to_moduleIsTorsionFree
  haveI : Algebra.IsAlgebraic K₀ K₁ := Algebra.IsIntegral.isAlgebraic
  let L : K₁ →ₐ[K₀] k := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨L.toRingHom.comp (Ideal.Quotient.mk M), fun a => ?_⟩
  have e1 : Ideal.Quotient.mk M (algebraMap A (Algebra.adjoin A {y}) a) = algebraMap K₀ K₁ (Ideal.Quotient.mk _ a) := rfl
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, e1, L.commutes]
  rfl

theorem dichotomy (Ω k : Type) [Field Ω] [Field k] (A : Subring Ω) (h : A →+* k)
    (hloc : ∀ a : A, h a ≠ 0 → (a : Ω)⁻¹ ∈ A) (x : Ω) (hx : x ≠ 0) :
    ∃ y : Ω, (y = x ∨ y = x⁻¹) ∧ ∃ M : Ideal (Algebra.adjoin A {y}), M.IsMaximal ∧
      RingHom.ker h ≤ M.comap (algebraMap A (Algebra.adjoin A {y})) := by
  have hmax : (RingHom.ker h).IsMaximal := by
    rw [Ideal.isMaximal_iff]
    refine ⟨by simp, fun J a hJ ha haJ => ?_⟩
    have ha' : h a ≠ 0 := fun e => ha (RingHom.mem_ker.2 e)
    have hinv := hloc a ha'
    have ha0 : (a : Ω) ≠ 0 := fun e => ha' (by rw [show a = 0 from Subtype.ext e, map_zero])
    have : (1 : A) = ⟨(a : Ω)⁻¹, hinv⟩ * a := Subtype.ext (by simp [inv_mul_cancel₀ ha0])
    rw [this]
    exact J.mul_mem_left _ haJ
  by_cases hT : (RingHom.ker h).map (algebraMap A (Algebra.adjoin A {x})) = ⊤
  · letI := invertibleOfNonzero hx
    have htop : (RingHom.ker h).map (algebraMap A (Algebra.adjoin A {x})) ⊔
        Ideal.span {⟨x, Algebra.subset_adjoin rfl⟩} = ⊤ := by rw [hT]; exact top_sup_eq _
    obtain ⟨p, hp, hpx⟩ :=
      Algebra.exists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top x _ hmax.ne_top htop
    have hlc : h p.leadingCoeff ≠ 0 := by
      intro e
      have h1 := sub_mem (RingHom.mem_ker.2 e) hp
      simp only [sub_sub_cancel] at h1
      exact hmax.ne_top ((Ideal.eq_top_iff_one _).2 h1)
    have hu : IsUnit p.leadingCoeff := by
      have hinv := hloc _ hlc
      have h0 : (p.leadingCoeff : Ω) ≠ 0 := fun e => hlc (by
        rw [show p.leadingCoeff = 0 from Subtype.ext e, map_zero])
      exact IsUnit.of_mul_eq_one (⟨_, hinv⟩ : A) (Subtype.ext (by simp [mul_inv_cancel₀ h0]))
    have hint : IsIntegral A x⁻¹ := by
      refine ⟨Polynomial.C (hu.unit⁻¹ : Aˣ).1 * p, ?_, ?_⟩
      · exact Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one (by simp)
      · rw [← Polynomial.aeval_def, map_mul]
        rw [invOf_eq_inv] at hpx
        rw [hpx, mul_zero]
    haveI : Algebra.IsIntegral A (Algebra.adjoin A {x⁻¹}) := Algebra.IsIntegral.adjoin (by simpa using hint)
    have hker : RingHom.ker (algebraMap A (Algebra.adjoin A {x⁻¹})) ≤ RingHom.ker h := by
      intro a ha
      have e := congrArg Subtype.val (RingHom.mem_ker.1 ha)
      have : a = 0 := Subtype.ext (by simpa using e)
      rw [this]; exact zero_mem _
    obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (RingHom.ker h) hker
    exact ⟨x⁻¹, Or.inr rfl, Q, hQ, hQc.ge⟩
  · obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hT
    exact ⟨x, Or.inl rfl, M, hM, Ideal.map_le_iff_le_comap.1 hle⟩

theorem exists_valuationSubring_ext : ∀ (W Ω k : Type) [CommRing W] [Field Ω] [Field k] [IsAlgClosed k]
    (j : W →+* Ω), Function.Injective j → ∀ g : W →+* k, ∃ (U : ValuationSubring Ω) (hU : ∀ w, j w ∈ U)
      (h : U →+* k), ∀ w, h ⟨j w, hU w⟩ = g w := by
  intro W Ω k _ _ _ _ j hj g
  let S : Set (Subring (Ω × k)) :=
    {G | (∀ a ∈ G, ∀ b ∈ G, a.1 = b.1 → a.2 = b.2) ∧ ∀ w, (j w, g w) ∈ G}
  have G0 : (RingHom.prod j g).range ∈ S := by
    refine ⟨?_, fun w => ⟨w, rfl⟩⟩
    rintro _ ⟨w, rfl⟩ _ ⟨w', rfl⟩ e
    have : w = w' := hj e
    subst this; rfl
  obtain ⟨G, -, hG⟩ := zorn_le_nonempty₀ S (fun c hcS hc y hy => by
    have hne : c.Nonempty := ⟨y, hy⟩
    have hd : DirectedOn (· ≤ ·) c := hc.directedOn
    refine ⟨sSup c, ⟨?_, fun w => le_sSup hy ((hcS hy).2 w)⟩, fun z hz => le_sSup hz⟩
    intro a ha b hb e
    obtain ⟨s₁, hs₁, ha₁⟩ := (Subring.mem_sSup_of_directedOn hne hd).1 ha
    obtain ⟨s₂, hs₂, hb₂⟩ := (Subring.mem_sSup_of_directedOn hne hd).1 hb
    obtain ⟨s₃, hs₃, h13, h23⟩ := hd s₁ hs₁ s₂ hs₂
    exact (hcS hs₃).1 a (h13 ha₁) b (h23 hb₂) e) _ G0
  obtain ⟨⟨hGf, hGb⟩, hGm⟩ := hG
  let π : G →+* Ω := (RingHom.fst Ω k).comp G.subtype
  have hπ : Function.Injective π := fun p q e =>
    Subtype.ext (Prod.ext e (hGf p.1 p.2 q.1 q.2 e))
  let A : Subring Ω := π.range
  let e : G ≃+* A := RingEquiv.ofBijective π.rangeRestrict
    ⟨fun a b e' => hπ (congrArg Subtype.val e'), π.rangeRestrict_surjective⟩
  let h : A →+* k := ((RingHom.snd Ω k).comp G.subtype).comp e.symm.toRingHom
  have hA : ∀ a : A, ((a : Ω), h a) ∈ G := fun a => by
    have e1 : π (e.symm a) = a := congrArg Subtype.val (e.apply_symm_apply a)
    have : ((a : Ω), h a) = ((e.symm a : G) : Ω × k) := Prod.ext e1.symm rfl
    rw [this]; exact (e.symm a).2
  have hG2 : ∀ p ∈ G, ∃ a : A, (a : Ω) = p.1 ∧ h a = p.2 := fun p hp =>
    ⟨π.rangeRestrict ⟨p, hp⟩, rfl, by
      show ((e.symm (e ⟨p, hp⟩) : G) : Ω × k).2 = p.2
      rw [e.symm_apply_apply]⟩
  have ext_le : ∀ (B : Subring Ω) (hAB : A ≤ B) (h' : B →+* k),
      (∀ a : A, h' (Subring.inclusion hAB a) = h a) → B ≤ A := by
    intro B hAB h' hh' b hb
    let G' : Subring (Ω × k) := (RingHom.prod B.subtype h').range
    have hG' : G' ∈ S := by
      refine ⟨?_, fun w => ?_⟩
      · rintro _ ⟨b₁, rfl⟩ _ ⟨b₂, rfl⟩ e'
        have : b₁ = b₂ := Subtype.ext e'
        subst this; rfl
      · obtain ⟨a, ha1, ha2⟩ := hG2 _ (hGb w)
        refine ⟨Subring.inclusion hAB a, ?_⟩
        exact Prod.ext ha1 ((hh' a).trans ha2)
    have hle : G ≤ G' := fun p hp => by
      obtain ⟨a, ha1, ha2⟩ := hG2 p hp
      exact ⟨Subring.inclusion hAB a, Prod.ext ha1 ((hh' a).trans ha2)⟩
    have hmem : ((b : Ω), h' ⟨b, hb⟩) ∈ G := hGm hG' hle ⟨⟨b, hb⟩, rfl⟩
    exact ⟨⟨_, hmem⟩, rfl⟩
  have hloc : ∀ a : A, h a ≠ 0 → (a : Ω)⁻¹ ∈ A := by
    intro a ha
    obtain ⟨B, hAB, h', hB, hh'⟩ := exists_ext_local Ω k A h
    have := hB (Subring.inclusion hAB a) (by rw [hh']; exact ha)
    exact ext_le B hAB h' hh' this
  have hval : ∀ x : Ω, x ∈ A ∨ x⁻¹ ∈ A := by
    intro x
    by_cases hx : x = 0
    · exact Or.inl (hx ▸ zero_mem A)
    obtain ⟨y, hy, M, hM, hMc⟩ := dichotomy Ω k A h hloc x hx
    obtain ⟨h', hh'⟩ := exists_ext_adjoin Ω k A h hloc y M hMc
    let B : Subring Ω := (Algebra.adjoin A {y}).toSubring
    have hAB : A ≤ B := fun a ha => (Algebra.adjoin A {y}).algebraMap_mem (⟨a, ha⟩ : A)
    have hyA : y ∈ A := ext_le B hAB h' hh' (Algebra.subset_adjoin rfl)
    rcases hy with rfl | rfl
    · exact Or.inl hyA
    · exact Or.inr hyA
  let U : ValuationSubring Ω := { A with mem_or_inv_mem' := hval }
  have hU : ∀ w, j w ∈ U := fun w => by
    obtain ⟨a, ha1, -⟩ := hG2 _ (hGb w)
    show j w ∈ A
    rw [← show (a : Ω) = j w from ha1]; exact a.2
  refine ⟨U, hU, h.comp (Subring.inclusion (le_refl A)), fun w => ?_⟩
  have m1 := hA ⟨j w, hU w⟩
  exact hGf _ m1 _ (hGb w) rfl

end GlobalTheory.ValExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsValuationSubringExtendingRingHomStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_valuationSubring_extending_ringHom : ∀ (W Ω k : Type) [CommRing W] [Field Ω] [Field k] [IsAlgClosed k] (j : W →+* Ω), Function.Injective j → ∀ g : W →+* k, ∃ (U : ValuationSubring Ω) (hU : ∀ w, j w ∈ U) (h : U →+* k), ∀ w, h ⟨j w, hU w⟩ = g w := by
  first | exact @GlobalTheory.ValExt.exists_valuationSubring_ext | exact GlobalTheory.ValExt.exists_valuationSubring_ext | (intros; apply GlobalTheory.ValExt.exists_valuationSubring_ext <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricPointDvrFactorsValuationSubringClosure
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem geomPoint_factors_valuationSubring_algClosure :
    ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L]
      [IsFractionRing W L] (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp W),
      ∃ (U : ValuationSubring (AlgebraicClosure L)) (j : W →+* U) (h : U →+* k),
        (algebraMap U (AlgebraicClosure L)).comp j = (algebraMap L (AlgebraicClosure L)).comp (algebraMap W L) ∧
          x = spMap h ≫ spMap j := by
  intro W L _ _ _ _ _ _ k _ _ x
  set j' : W →+* AlgebraicClosure L := (algebraMap L (AlgebraicClosure L)).comp (algebraMap W L) with hj'
  have hinj : Function.Injective j' :=
    (algebraMap L (AlgebraicClosure L)).injective.comp (IsFractionRing.injective W L)
  set g : W →+* k := (Spec.preimage x).hom with hg
  obtain ⟨U, hU, h, hh⟩ := GlobalTheory.T.exists_valuationSubring_extending_ringHom W (AlgebraicClosure L) k j' hinj g
  refine ⟨U, j'.codRestrict U.toSubring hU, h, ?_, ?_⟩
  · ext w; rfl
  · have hcomp : h.comp (j'.codRestrict U.toSubring hU) = g := by
      ext w; exact hh w
    have hx : x = Spec.map (Spec.preimage x) := (Spec.map_preimage x).symm
    rw [hx]
    simp only [spMap, Sp]
    rw [← Spec.map_comp]
    congr 1
    ext w
    change g w = h (j'.codRestrict U.toSubring hU w)
    rw [← hcomp]; rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricPointDvrFactorsValuationSubringClosureStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_point_dvr_factors_valuation_subring_closure : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp W), ∃ (U : ValuationSubring (AlgebraicClosure L)) (j : W →+* U) (h : U →+* k), (algebraMap U (AlgebraicClosure L)).comp j = (algebraMap L (AlgebraicClosure L)).comp (algebraMap W L) ∧ x = spMap h ≫ spMap j := by
  first | exact @GlobalTheory.geomPoint_factors_valuationSubring_algClosure | exact GlobalTheory.geomPoint_factors_valuationSubring_algClosure | (intros; apply GlobalTheory.geomPoint_factors_valuationSubring_algClosure <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationRingRootOfUnityLiftReduce
open NumberField

namespace GlobalTheory

theorem isPrimitiveRoot_map_of_isUnit_order' {o K : Type} [CommRing o] [IsDomain o] [CommRing K] [IsDomain K]
    (φ : o →+* K) {m : ℕ} (hm : 0 < m) {q : o} (hq : IsPrimitiveRoot q m) (hu : IsUnit (m : o)) :
    IsPrimitiveRoot (φ q) m := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  refine IsPrimitiveRoot.mk_of_lt _ hm (by rw [← map_pow, hq.pow_eq_one, map_one]) fun l hl hlt h1 => ?_
  have hp := congrArg φ hq.prod_one_sub_pow_eq_order
  rw [map_prod] at hp
  have hz : ∏ k ∈ Finset.range n, φ (1 - q ^ (k + 1)) = 0 := by
    refine Finset.prod_eq_zero (i := l - 1) (Finset.mem_range.2 (by omega)) ?_
    rw [map_sub, map_one, map_pow, Nat.sub_add_cancel hl, h1, sub_self]
  rw [hz] at hp
  have hu' : IsUnit (φ ((n : o) + 1)) := by
    have := hu.map φ; simpa using this
  exact hu'.ne_zero hp.symm

theorem valuationRing_rootOfUnity_lift_reduce : ∀ (U Ω k : Type) [CommRing U] [IsDomain U] [ValuationRing U] [Field Ω]
    [Algebra U Ω] [IsFractionRing U Ω] [Field k] (h : U →+* k) (n : ℕ), IsUnit (n : U) → ∀ ζ : Ωˣ, ζ ^ n = 1 →
    ∃! z : Uˣ, algebraMap U Ω z = ζ ∧ (IsPrimitiveRoot ζ n → IsPrimitiveRoot (Units.map (h : U →* k) z) n) := by
  intro U Ω k _ _ _ _ _ _ _ h n hn ζ hζ
  have hinj : Function.Injective (algebraMap U Ω) := IsFractionRing.injective U Ω
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp at hn
    · exact h0

  have unitOf : ∀ a : U, (algebraMap U Ω a) ^ n = 1 → IsUnit a := by
    intro a ha
    have : a ^ n = 1 := hinj (by rw [map_pow, ha, map_one])
    exact IsUnit.of_mul_eq_one (a ^ (n - 1)) (by rw [← pow_succ', Nat.sub_add_cancel hn0, this])
  have hex : ∃ z : Uˣ, algebraMap U Ω z = ζ := by
    rcases (ValuationRing.iff_isInteger_or_isInteger U Ω).1 inferInstance (ζ : Ω) with ⟨a, ha⟩ | ⟨b, hb⟩
    · have hu := unitOf a (by rw [ha, ← Units.val_pow_eq_pow_val, hζ, Units.val_one])
      exact ⟨hu.unit, by simpa using ha⟩
    · have hb' : (algebraMap U Ω b) ^ n = 1 := by
        rw [hb, ← Units.val_inv_eq_inv_val, ← Units.val_pow_eq_pow_val, inv_pow, hζ, inv_one, Units.val_one]
      have hu := unitOf b hb'
      refine ⟨hu.unit⁻¹, ?_⟩
      have : algebraMap U Ω (hu.unit : U) = (ζ : Ω)⁻¹ := by simpa using hb
      have key : algebraMap U Ω (hu.unit : U) * algebraMap U Ω ((hu.unit⁻¹ : Uˣ) : U) = 1 := by
        rw [← map_mul, Units.mul_inv, map_one]
      rw [this, inv_mul_eq_one₀ ζ.ne_zero] at key
      exact key.symm
  obtain ⟨z, hz⟩ := hex
  refine ⟨z, ⟨hz, fun hp => ?_⟩, fun w ⟨hw, _⟩ => Units.ext (hinj (by rw [hw, hz]))⟩
  have hpz : IsPrimitiveRoot (z : U) n := by
    rw [← IsPrimitiveRoot.map_iff_of_injective hinj, hz]
    exact IsPrimitiveRoot.coe_units_iff.2 hp
  rw [← IsPrimitiveRoot.coe_units_iff]
  exact isPrimitiveRoot_map_of_isUnit_order' h hn0 hpz hn

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateSimilitudeGeometricPointsOfGenericDvr
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

namespace GlobalTheory.HTGeomExt

variable {p : ℕ} [Fact p.Prime] {D : Datum p}

theorem tateIsoO_transport {k k' : Type} [Field k] [Field k'] {Q Q' : Type} [Group Q] [Group Q']
    {act : D.O → Q → Q} {act' : D.O → Q' → Q'} {e : ℕ → Q → Q → kˣ → Prop} {e' : ℕ → Q' → Q' → k'ˣ → Prop}
    (I : TateIsoO D k Q act e) (r : Q →* Q') (hact : ∀ c q, r (act c q) = act' c (r q))
    (hbij : ∀ n, 0 < n → n.Coprime p → Set.BijOn r {y : Q | y ^ n = 1} {y : Q' | y ^ n = 1})
    (ζ' : ℕ → k'ˣ) (hprim : ∀ n, 0 < n → n.Coprime p → IsPrimitiveRoot (ζ' n) n)
    (hpow : ∀ n m, 0 < n → 0 < m → (n * m).Coprime p → ζ' (n * m) ^ m = ζ' n)
    (hisom : ∀ n, 0 < n → n.Coprime p → ∀ x y,
      e' n (r (I.ev n x)) (r (I.ev n y)) (ζ' n ^ (2 * D.EF x y))) :
    ∃ I' : TateIsoO D k' Q' act' e', ∀ n x, I'.ev n x = r (I.ev n x) := by
  have htor : ∀ n, 0 < n → n.Coprime p → ∀ x, I.ev n x ^ n = 1 :=
    fun n h1 h2 x => (I.onto n h1 h2 _).2 ⟨x, rfl⟩
  refine ⟨
    { ζ := ζ'
      ζ_prim := hprim
      ζ_pow := hpow
      ev := fun n x => r (I.ev n x)
      add := fun n x y => by simp only [I.add, map_mul]
      lin := fun n c x => by simp only [I.lin, hact]
      ker := fun n h1 h2 x => ?_
      onto := fun n h1 h2 q => ?_
      tower := fun n m h1 h2 h3 x => by simp only [← map_pow, I.tower n m h1 h2 h3]
      isom := hisom }, fun n x => rfl⟩
  · rw [← I.ker n h1 h2 x]
    constructor
    · intro h
      refine (hbij n h1 h2).injOn (htor n h1 h2 x) (show (1 : Q) ^ n = 1 from one_pow n) ?_
      rw [h, map_one]
    · intro h
      show r (I.ev n x) = 1
      rw [h, map_one]
  · constructor
    · intro hq
      obtain ⟨y, hy, rfl⟩ := (hbij n h1 h2).surjOn hq
      obtain ⟨x, hx⟩ := (I.onto n h1 h2 y).1 hy
      exact ⟨x, by rw [hx]⟩
    · rintro ⟨x, rfl⟩
      show r (I.ev n x) ^ n = 1
      rw [← map_pow, htor n h1 h2 x, map_one]

end GlobalTheory.HTGeomExt

namespace GlobalTheory.HTGeomExt

theorem tateIsoO_geom_of_generic : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (gm : R →+* W) (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G], IsAbelianScheme G → ∀ (act : OActN D.O G) (P : LB (G2 G).left), P.IsLB → ∀ (y : D.La → (𝟙_ (Over (Sp W)) ⟶ G)), (∀ x x', y (x + x') = y x * y x') → (∀ (k : Type) [Field k] [IsAlgClosed k] (β : L →+* k), ∃ I : TateIsoO D k (Over.mk (spMap (β.comp (algebraMap W L))) ⟶ G) (fun c g => g ≫ act.act c) (fun n g g' z => Out.WeilIs G (P.pull (lift (𝟙 G) (𝟙 G)).left) n g g' (unitOn z)), ∀ x, toUnit _ ≫ y x = I.ev N x) → ∀ (k : Type) [Field k] [IsAlgClosed k] (β : W →+* k), ∃ I : TateIsoO D k (Over.mk (spMap β) ⟶ G) (fun c g => g ≫ act.act c) (fun n g g' z => Out.WeilIs G (P.pull (lift (𝟙 G) (𝟙 G)).left) n g g' (unitOn z)), ∀ x, toUnit _ ≫ y x = I.ev N x := by
  intro p _ D R _ b N W L _ _ _ _ _ _ gm G _ _ hab act P hP y hy hgen k _ _ β
  obtain ⟨V, j, h, hj, hx⟩ := GlobalTheory.T.geometric_point_dvr_factors_valuation_subring_closure W L k (spMap β)
  have hunit : ∀ n : ℕ, n.Coprime p → IsUnit (n : V) := fun n hn => by
    simpa using (b.unit n hn).map (j.comp gm)
  obtain ⟨r, hr1, hr2, hr3, hr4⟩ := GlobalTheory.T.exists_reduction_points_abelianScheme_valuationRing V (AlgebraicClosure L) k h (Sp W) G hab (spMap j)
  have hs : spMap ((algebraMap V (AlgebraicClosure L)).comp j) =
      spMap (algebraMap V (AlgebraicClosure L)) ≫ spMap j := by
    dsimp only [spMap]
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  have hg := hgen (AlgebraicClosure L) (algebraMap L (AlgebraicClosure L))
  rw [← hj, hs] at hg
  obtain ⟨I, hI⟩ := hg
  rw [hx]
  have hz : ∀ n, ∃ z : Vˣ, 0 < n → n.Coprime p →
      (algebraMap V (AlgebraicClosure L) (z : V) = (I.ζ n : AlgebraicClosure L) ∧
        IsPrimitiveRoot (Units.map (h : V →* k) z) n) := by
    intro n
    by_cases hn : 0 < n ∧ n.Coprime p
    · obtain ⟨z, ⟨hz1, hz2⟩, -⟩ := valuationRing_rootOfUnity_lift_reduce V (AlgebraicClosure L) k h n
        (hunit n hn.2) (I.ζ n) (I.ζ_prim n hn.1 hn.2).pow_eq_one
      exact ⟨z, fun _ _ => ⟨hz1, hz2 (I.ζ_prim n hn.1 hn.2)⟩⟩
    · exact ⟨1, fun h1 h2 => absurd ⟨h1, h2⟩ hn⟩
  choose z hz using hz
  have hzU : ∀ n, 0 < n → n.Coprime p →
      Units.map (algebraMap V (AlgebraicClosure L) : V →* AlgebraicClosure L) (z n) = I.ζ n :=
    fun n h1 h2 => Units.ext (hz n h1 h2).1
  have hinj : Function.Injective (algebraMap V (AlgebraicClosure L)) :=
    IsFractionRing.injective V (AlgebraicClosure L)
  have hLb := LB.isLB_pull hP (lift (𝟙 G) (𝟙 G)).left
  have hpow : ∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p →
      Units.map (h : V →* k) (z (n * m)) ^ m = Units.map (h : V →* k) (z n) := by
    intro n m h1 h2 h3
    have hn : n.Coprime p := Nat.Coprime.coprime_dvd_left (Dvd.intro m rfl) h3
    rw [← map_pow]
    congr 1
    apply Units.ext
    apply hinj
    rw [Units.val_pow_eq_pow_val, map_pow, (hz _ (Nat.mul_pos h1 h2) h3).1, (hz n h1 hn).1,
      ← Units.val_pow_eq_pow_val, I.ζ_pow n m h1 h2 h3]
  have hisom : ∀ n : ℕ, 0 < n → n.Coprime p → ∀ x x', Out.WeilIs G (P.pull (lift (𝟙 G) (𝟙 G)).left) n (r (I.ev n x)) (r (I.ev n x'))
      (unitOn (Units.map (h : V →* k) (z n) ^ (2 * D.EF x x'))) := by
    intro n h1 h2 x x'
    have hi := I.isom n h1 h2 x x'
    rw [← hzU n h1 h2, ← map_zpow] at hi
    have ho := hr4 _ hLb n (hunit n h2) _ _ (z n ^ (2 * D.EF x x'))
      ((I.onto n h1 h2 _).2 ⟨x, rfl⟩) ((I.onto n h1 h2 _).2 ⟨x', rfl⟩) hi
    rw [map_zpow] at ho
    exact ho
  obtain ⟨I', hI'⟩ := tateIsoO_transport (act' := fun c g => g ≫ act.act c)
    (e' := fun n g g' z => Out.WeilIs G (P.pull (lift (𝟙 G) (𝟙 G)).left) n g g' (unitOn z)) I r (fun c q => hr2 (act.act c) q)
    (fun n _ h2 => hr3 n (hunit n h2)) (fun n => Units.map (h : V →* k) (z n))
    (fun n h1 h2 => (hz n h1 h2).2) hpow hisom
  refine ⟨I', fun x => ?_⟩
  rw [hI', ← hI x]
  refine (hr1 (toUnit _ ≫ y x) _ _ ?_ ?_).symm
  · rw [Over.comp_left, Over.comp_left]
    exact Category.assoc _ _ _
  · rw [Over.comp_left, Over.comp_left]
    exact Category.assoc _ _ _

end GlobalTheory.HTGeomExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateSimilitudeGeometricPointsOfGenericDvrStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateSimilitude_geometric_points_of_generic_dvr : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (gm : R →+* W) (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G], IsAbelianScheme G → ∀ (act : OActN D.O G) (P : LB (G2 G).left), P.IsLB → ∀ (y : D.La → (𝟙_ (Over (Sp W)) ⟶ G)), (∀ x x', y (x + x') = y x * y x') → (∀ (k : Type) [Field k] [IsAlgClosed k] (β : L →+* k), ∃ I : TateIsoO D k (Over.mk (spMap (β.comp (algebraMap W L))) ⟶ G) (fun c g => g ≫ act.act c) (fun n g g' z => Out.WeilIs G (P.pull (lift (𝟙 G) (𝟙 G)).left) n g g' (unitOn z)), ∀ x, toUnit _ ≫ y x = I.ev N x) → ∀ (k : Type) [Field k] [IsAlgClosed k] (β : W →+* k), ∃ I : TateIsoO D k (Over.mk (spMap β) ⟶ G) (fun c g => g ≫ act.act c) (fun n g g' z => Out.WeilIs G (P.pull (lift (𝟙 G) (𝟙 G)).left) n g g' (unitOn z)), ∀ x, toUnit _ ≫ y x = I.ev N x := by
  first | exact @GlobalTheory.HTGeomExt.tateIsoO_geom_of_generic | exact GlobalTheory.HTGeomExt.tateIsoO_geom_of_generic | (intros; apply GlobalTheory.HTGeomExt.tateIsoO_geom_of_generic <;> assumption)
end

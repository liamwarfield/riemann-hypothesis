module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpCoordinatesTangentFieldHolomorphicPeriodMap

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionExpansionScaleBaseElement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionExpansionScaleBaseElement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.UU.expT_scale : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU I D A G) (k : ℕ) (q : R) (σ τ : U.SecGT (𝟙_ _) k) (f g : ∀ α, GlobalTheory.UU.SecBT D (𝟙_ _) k α), ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ G).hom q σ τ → (∀ α, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom q (f α) (g α)) → U.ExpT (𝟙_ _) k τ g → U.ExpT (𝟙_ _) k σ f := by
  intro R _ _ I D A G _ _ U k q σ τ f g hσ hf hE e
  obtain ⟨s, hs⟩ := hE e
  refine ⟨s, fun Z x rG rB h1 h2 h3 z JG J hG hB => ?_⟩
  obtain ⟨H1, H2⟩ := hs Z x rG rB h1 h2 h3 z JG J hG hB
  have hc : cst (rB ≫ (𝟙_ _ ⊗ D.P.A).hom) z q = cst (rG ≫ (𝟙_ _ ⊗ G).hom) z q := by
    rw [← Over.w (fst (𝟙_ (Over (Spec (CommRingCat.of R)))) D.P.A), ← Over.w (fst (𝟙_ (Over (Spec (CommRingCat.of R)))) G),
      ← Category.assoc, ← Category.assoc, h3]
  have hF : ∀ α, sval (f α) rB z J = cst (rG ≫ (𝟙_ _ ⊗ G).hom) z q * sval (g α) rB z J := fun α => by
    rw [← hc]
    exact GlobalTheory.secIsMul_gs (hf α) rB z _ (hB.mem _ _)
  have hS : sval σ rG z JG = cst (rG ≫ (𝟙_ _ ⊗ G).hom) z q * sval τ rG z JG :=
    GlobalTheory.secIsMul_gs hσ rG z _ (hG.mem _ _)
  refine ⟨fun α hα => by rw [hF, H1 α hα, mul_zero], ?_⟩
  rw [hS, mul_left_comm, H2, Finset.mul_sum]
  exact Finset.sum_congr rfl fun α _ => by rw [hF, _root_.mul_assoc]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionExpansionScaleBaseElementStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionExpansion_scale_base_element : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU I D A G) (k : ℕ) (q : R) (σ τ : U.SecGT (𝟙_ _) k) (f g : ∀ α, GlobalTheory.UU.SecBT D (𝟙_ _) k α), ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ G).hom q σ τ → (∀ α, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom q (f α) (g α)) → U.ExpT (𝟙_ _) k τ g → U.ExpT (𝟙_ _) k σ f := by
  first | exact @GlobalTheory.UU.expT_scale | exact GlobalTheory.UU.expT_scale | (intros; apply GlobalTheory.UU.expT_scale <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSectionBaseMulCancelFlatDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSectionBaseMulCancelFlatDomain
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem secIsMul_cancel : ∀ (R : Type) [CommRing R] [IsDomain R] (X : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of R)), Flat p → ∀ (L : LB X) (q : R), q ≠ 0 → ∀ s t t' : LB.Sec L, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul p q s t → ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul p q s t' → t = t' := by
  intro R _ _ X p hp L q hq s t t' h h'
  haveI := hp
  have key : ∀ j, t.f j = t'.f j := by
    intro j
    refine fn_ext fun x hx => ?_
    have e1 := GlobalTheory.secIsMul_gs h (𝟙 X) x j hx
    have e2 := GlobalTheory.secIsMul_gs h' (𝟙 X) x j hx
    rw [Category.id_comp] at e1 e2
    have h0 : cst p x q * (gs (𝟙 X) x (L.U j) (t.f j) - gs (𝟙 X) x (L.U j) (t'.f j)) = 0 := by
      rw [mul_sub, ← e1, ← e2, sub_self]
    obtain ⟨u, hu⟩ := GlobalTheory.cst_dvd_of_cst_mul_eq_zero p x (a := q) (b := 0)
      (fun c hc => by
        rcases mul_eq_zero.1 hc with h1 | h1
        · exact absurd h1 hq
        · rw [h1]) h0
    have hz : cst p x (0 : R) = 0 := by
      rw [cst, map_zero, gs_eq _ _ ⊤ trivial, map_zero, map_zero]
    rw [hz, zero_mul, sub_eq_zero] at hu
    exact hu
  cases t; cases t'
  congr 1
  exact funext key

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSectionBaseMulCancelFlatDomainStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleSection_baseMul_cancel_flat_domain : ∀ (R : Type) [CommRing R] [IsDomain R] (X : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of R)), Flat p → ∀ (L : LB X) (q : R), q ≠ 0 → ∀ s t t' : LB.Sec L, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul p q s t → ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul p q s t' → t = t' := by
  first | exact @GlobalTheory.Mum.secIsMul_cancel | exact GlobalTheory.Mum.secIsMul_cancel | (intros; apply GlobalTheory.Mum.secIsMul_cancel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermDvdOfSectionExpansionDvdClosedFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermDvdOfSectionExpansionDvdClosedFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.ClosedFibreDvd

theorem mem_span_of_forall_pow {O : Type} [CommRing O] [IsNoetherianRing O] [IsLocalRing O] (a s : O)
    (h : ∀ n : ℕ, s ∈ Ideal.span {a} ⊔ maximalIdeal O ^ (n + 1)) : s ∈ Ideal.span {a} := by
  by_cases ht : Ideal.span {a} = ⊤
  · rw [ht]; trivial
  haveI : Nontrivial (O ⧸ Ideal.span {a}) := Ideal.Quotient.nontrivial_iff.2 ht
  haveI : IsLocalRing (O ⧸ Ideal.span {a}) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hl : IsLocalHom (Ideal.Quotient.mk (Ideal.span {a})) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_bot, ← Ideal.iInf_pow_eq_bot_of_isLocalRing
    (maximalIdeal (O ⧸ Ideal.span {a})) (maximalIdeal.isMaximal _).ne_top, Ideal.mem_iInf]
  intro n
  have hle : Ideal.map (Ideal.Quotient.mk (Ideal.span {a})) (Ideal.span {a} ⊔ maximalIdeal O ^ (n + 1)) ≤
      maximalIdeal (O ⧸ Ideal.span {a}) ^ n := by
    rw [Ideal.map_sup, Ideal.map_pow]
    refine sup_le ?_ ?_
    · rw [Ideal.map_quotient_self]; exact bot_le
    · refine le_trans ?_ (Ideal.pow_le_pow_right (Nat.le_succ n))
      exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 fun r hr => map_nonunit _ r hr) _
  exact hle (Ideal.mem_map_of_mem _ (h n))

theorem ker_stalkMap_le {X H : Scheme.{0}} (j : H ⟶ X) [IsClosedImmersion j] (z : H)
    (I : Ideal (X.presheaf.stalk (j z))) (hI : I ≠ ⊤)
    (ℓ : Spec (CommRingCat.of (X.presheaf.stalk (j z) ⧸ I)) ⟶ H)
    (hℓ : ℓ ≫ j = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ X.fromSpecStalk (j z)) :
    RingHom.ker (j.stalkMap z).hom ≤ I := by
  intro a ha
  haveI : Nontrivial (X.presheaf.stalk (j z) ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI
  haveI : IsLocalRing (X.presheaf.stalk (j z) ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hl : IsLocalHom (Ideal.Quotient.mk I) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have e : ℓ (IsLocalRing.closedPoint _) = z := by
    apply j.isEmbedding.injective
    refine (congrArg (fun q => q (IsLocalRing.closedPoint _)) hℓ).trans ?_
    exact (congrArg (X.fromSpecStalk (j z)) (IsLocalRing.comap_closedPoint (Ideal.Quotient.mk I))).trans
      Scheme.fromSpecStalk_closedPoint
  let ψ := H.presheaf.stalkSpecializes (specializes_of_eq e) ≫ Scheme.stalkClosedPointTo ℓ
  have hψ : j.stalkMap z ≫ ψ = CommRingCat.ofHom (Ideal.Quotient.mk I) := by
    apply Spec.map_injective
    rw [← cancel_mono (X.fromSpecStalk (j z)), ← hℓ, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkMap_fromSpecStalk, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk_assoc]
  have hψ' := congrArg (fun q => q.hom a) hψ
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hψ'
  rw [RingHom.mem_ker.1 ha, map_zero] at hψ'
  exact Ideal.Quotient.eq_zero_iff_mem.1 hψ'.symm

def cstHom {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (x : X) : R →+* X.presheaf.stalk x :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Sp R).presheaf.germ ⊤ (p x) trivial ≫ p.stalkMap x).hom

theorem cstHom_apply {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (x : X) (c : R) :
    cstHom p x c = cst p x c := by
  rw [cst, gs_stalkMap p x ⊤ trivial, gs_eq _ _ ⊤ trivial]; rfl

theorem fromSpecStalk_comp {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (x : X) :
    X.fromSpecStalk x ≫ p = Spec.map (CommRingCat.ofHom (cstHom p x)) := by
  rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, Spec.fromSpecStalk_eq, ← Spec.map_comp]; rfl

theorem exists_lift {R : Type} [CommRing R] (J : Ideal R) {X Y P : Scheme.{0}} (π : Y ⟶ Sp R) (p : X ⟶ Sp R)
    (fs : P ⟶ Y) (sn : P ⟶ Spec (CommRingCat.of (R ⧸ J)))
    (hP : IsPullback fs sn π (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))
    (k : Y ⟶ X) (h : X ⟶ Y) (hh : h ≫ π = p) (hk : h ≫ k = 𝟙 X) (z : P)
    (I : Ideal (X.presheaf.stalk ((fs ≫ k) z))) (hJ : Ideal.map (cstHom p _) J ≤ I) :
    ∃ ℓ : Spec (CommRingCat.of (X.presheaf.stalk ((fs ≫ k) z) ⧸ I)) ⟶ P,
      ℓ ≫ (fs ≫ k) = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ X.fromSpecStalk _ := by
  let L : R ⧸ J →+* X.presheaf.stalk ((fs ≫ k) z) ⧸ I := Ideal.Quotient.lift J ((Ideal.Quotient.mk I).comp (cstHom p _))
    (fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (hJ (Ideal.mem_map_of_mem _ ha)))
  have w : ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ X.fromSpecStalk _) ≫ h) ≫ π =
      Spec.map (CommRingCat.ofHom L) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) := by
    rw [Category.assoc, Category.assoc, hh, fromSpecStalk_comp, ← Spec.map_comp, ← Spec.map_comp]
    rfl
  refine ⟨hP.lift _ _ w, ?_⟩
  rw [← Category.assoc, hP.lift_fst, Category.assoc, hk, Category.comp_id]

theorem cst_stalkMap' {V : Type} [CommRing V] {X Z : Scheme.{0}} (r : Z ⟶ X) (p : X ⟶ Sp V) (z : Z) (a : V) :
    (r.stalkMap z).hom (cst p (r z) a) = cst (r ≫ p) z a := by
  have e := gs_pull (𝟙 X) p (r z) ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a)
  rw [Category.id_comp] at e
  exact (congrArg (r.stalkMap z).hom e.symm).trans ((gs_stalkMap r z (p ⁻¹ᵁ ⊤) trivial _).symm.trans
    (gs_pull r p z ⊤ trivial _))

theorem germ_dvd_of_expT_dvd : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G) (σ : U.SecGT (𝟙_ _) 1) (f g : ∀ α, GlobalTheory.UU.SecBT D (𝟙_ _) 1 α) (q : R), U.ExpT (𝟙_ _) 1 σ f → (∀ α, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom q (f α) (g α)) → ∀ (x : (𝟙_ (Over (Sp R)) ⊗ G).left), (𝟙_ (Over (Sp R)) ⊗ G).hom x = closedPoint R → ∀ (j : Fin 1 → U.P.L.L.ι), x ∈ LB.wchart U.P.L.L (fun _ : Fin 1 => (snd (𝟙_ (Over (Sp R))) G).left) j → ∃ t, gs (𝟙 _) x (LB.wchart U.P.L.L (fun _ : Fin 1 => (snd (𝟙_ (Over (Sp R))) G).left) j) (σ.f j) = cst (𝟙_ (Over (Sp R)) ⊗ G).hom x q * t := by
  intro R _ _ _ hR D A G _ _ U σ f g q hE hM x hx j hxj
  haveI : IsNoetherianRing R := hR.1.1
  haveI : Smooth G.hom := U.semi.smooth
  have lam : (snd (𝟙_ (Over (Sp R))) G).left ≫ (λ_ G).inv.left = 𝟙 _ := by
    rw [← Over.comp_left, ← leftUnitor_hom, Iso.hom_inv_id, Over.id_left]
  have lam' : (λ_ G).inv.left ≫ (snd (𝟙_ (Over (Sp R))) G).left = 𝟙 _ := by
    rw [← Over.comp_left, ← leftUnitor_hom, Iso.inv_hom_id, Over.id_left]
  have lamA' : (λ_ D.P.A).inv.left ≫ (snd (𝟙_ (Over (Sp R))) D.P.A).left = 𝟙 _ := by
    rw [← Over.comp_left, ← leftUnitor_hom, Iso.inv_hom_id, Over.id_left]
  have toU : ∀ {Y : Over (Sp R)} (h : Y ⟶ 𝟙_ (Over (Sp R))), h.left = Y.hom := fun h => by simpa using Over.w h
  have hpG : (snd (𝟙_ (Over (Sp R))) G).left ≫ G.hom = (𝟙_ (Over (Sp R)) ⊗ G).hom := Over.w _
  haveI : IsIso (snd (𝟙_ (Over (Sp R))) G).left := ⟨⟨(λ_ G).inv.left, lam, lam'⟩⟩
  haveI : LocallyOfFiniteType (𝟙_ (Over (Sp R)) ⊗ G).hom := by rw [← hpG]; infer_instance
  haveI : IsLocallyNoetherian (𝟙_ (Over (Sp R)) ⊗ G).left :=
    LocallyOfFiniteType.isLocallyNoetherian (𝟙_ (Over (Sp R)) ⊗ G).hom
  suffices H : gs (𝟙 _) x (LB.wchart U.P.L.L (fun _ : Fin 1 => (snd (𝟙_ (Over (Sp R))) G).left) j) (σ.f j) ∈
      Ideal.span {cst (𝟙_ (Over (Sp R)) ⊗ G).hom x q} by
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 H
    exact ⟨t, by rw [← ht, mul_comm]⟩
  refine mem_span_of_forall_pow _ _ fun e => ?_
  have hxg : G.hom ((snd (𝟙_ (Over (Sp R))) G).left x) = closedPoint R := by
    rw [← Scheme.Hom.comp_apply, hpG]; exact hx
  haveI : Nontrivial (R ⧸ maximalIdeal R ^ (e + 1)) := Ideal.Quotient.nontrivial_iff.2
    (ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top (Ideal.pow_le_self (Nat.succ_ne_zero e)))
  haveI : IsLocalRing (R ⧸ maximalIdeal R ^ (e + 1)) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hl : IsLocalHom (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1))) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hw : thick R (maximalIdeal R) e (closedPoint _) = closedPoint R := by
    have := IsLocalRing.comap_closedPoint (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1)))
    exact this
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := G.hom) (g := thick R (maximalIdeal R) e) _ _
    (hxg.trans hw.symm)
  have hzx : (pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left) z = x := by
    rw [Scheme.Hom.comp_apply, hz, ← Scheme.Hom.comp_apply, lam]; rfl
  subst hzx

  have hc : IsClosedImmersion (thick R (maximalIdeal R) e) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

  haveI : IsIso (λ_ G).inv.left := ⟨⟨(snd (𝟙_ (Over (Sp R))) G).left, lam', lam⟩⟩
  haveI : IsClosedImmersion (pullback.fst G.hom (thick R (maximalIdeal R) e)) := inferInstance
  haveI : IsClosedImmersion (pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left) := inferInstance

  have hmap : Ideal.map (cstHom (𝟙_ (Over (Sp R)) ⊗ G).hom
      ((pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left) z)) (maximalIdeal R ^ (e + 1)) ≤
      maximalIdeal _ ^ (e + 1) := by
    rw [Ideal.map_pow]
    refine Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 fun c hc' => ?_) _
    rw [Ideal.mem_comap, cstHom_apply]
    exact (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 (cst_not_isUnit _ _ hx hc'))
  have hker : RingHom.ker ((pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left).stalkMap z).hom ≤
      maximalIdeal _ ^ (e + 1) := by
    have hI : Ideal.map (cstHom (𝟙_ (Over (Sp R)) ⊗ G).hom
        ((pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left) z)) (maximalIdeal R ^ (e + 1)) ≠ ⊤ :=
      ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top (hmap.trans (Ideal.pow_le_self (Nat.succ_ne_zero e)))
    obtain ⟨ℓ, hℓ⟩ := exists_lift (maximalIdeal R ^ (e + 1)) G.hom (𝟙_ (Over (Sp R)) ⊗ G).hom
      (pullback.fst _ _) (pullback.snd _ _) (IsPullback.of_hasPullback _ _) (λ_ G).inv.left
      (snd (𝟙_ (Over (Sp R))) G).left hpG lam z _ le_rfl
    exact (ker_stalkMap_le _ z _ hI ℓ hℓ).trans hmap

  obtain ⟨S, hS⟩ := hE e
  obtain ⟨JG, hJG⟩ := GlobalTheory.UU.exists_good_pt U.P.L.isLB z
  obtain ⟨J, hJ⟩ := GlobalTheory.UU.exists_good_pt D.P.isLB z
  have h3 : ((U.gt e).pG.left ≫ (λ_ D.P.A).inv.left) ≫ (fst (𝟙_ (Over (Sp R))) D.P.A).left =
      (pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left) ≫ (fst (𝟙_ (Over (Sp R))) G).left := by
    rw [toU, toU, Category.assoc, Category.assoc, Over.w (λ_ D.P.A).inv, Over.w (λ_ G).inv, Over.w (U.gt e).pG,
      pullback.condition]
    rfl
  have key := (hS _ (𝟙 _) (pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left)
    ((U.gt e).pG.left ≫ (λ_ D.P.A).inv.left)
    (by rw [Category.assoc, lam', Category.comp_id, Category.id_comp]; rfl)
    (by rw [Category.assoc, lamA', Category.comp_id, Category.id_comp]) h3 z JG J hJG hJ).2

  have aux : ∀ {O : Type} [CommRing O] (u : Oˣ) (a b : O) (I : Ideal O), (u : O) ^ 1 * a = b → b ∈ I → a ∈ I :=
    fun u a b I h hb => by
      rw [pow_one] at h
      rw [← u.inv_mul_cancel_left a, h]
      exact I.mul_mem_left _ hb
  have hq : ((U.gt e).pG.left ≫ (λ_ D.P.A).inv.left) ≫ (𝟙_ (Over (Sp R)) ⊗ D.P.A).hom =
      (pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left) ≫ (𝟙_ (Over (Sp R)) ⊗ G).hom := by
    rw [Category.assoc, Category.assoc, Over.w (λ_ D.P.A).inv, Over.w (λ_ G).inv, Over.w (U.gt e).pG,
      pullback.condition]
    rfl
  have hmem : sval σ (pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left) z JG ∈
      Ideal.span {cst ((pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left) ≫
        (𝟙_ (Over (Sp R)) ⊗ G).hom) z q} := by
    refine aux _ _ _ _ key (Ideal.sum_mem _ fun α _ => ?_)
    have hF : sval (f α) ((U.gt e).pG.left ≫ (λ_ D.P.A).inv.left) z J =
        cst (((U.gt e).pG.left ≫ (λ_ D.P.A).inv.left) ≫ (𝟙_ (Over (Sp R)) ⊗ D.P.A).hom) z q *
          sval (g α) ((U.gt e).pG.left ≫ (λ_ D.P.A).inv.left) z J :=
      secIsMul_gs (hM α) _ z _ (hJ.mem _ _)
    rw [hF, hq, _root_.mul_assoc]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hπ : ((pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left).stalkMap z).hom
      (gs (𝟙 _) ((pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left) z)
        (LB.wchart U.P.L.L (fun _ : Fin 1 => (snd (𝟙_ (Over (Sp R))) G).left) j) (σ.f j)) ∈
      Ideal.span {cst ((pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left) ≫
        (𝟙_ (Over (Sp R)) ⊗ G).hom) z q} := by
    have e1 := gs_stalkMap (pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left) z _ hxj (σ.f j)
    erw [← e1, sec_trans σ _ z hxj (hJG.mem _ _)]
    exact Ideal.mul_mem_left _ _ hmem
  obtain ⟨t', ht'⟩ := Ideal.mem_span_singleton'.1 hπ
  obtain ⟨t, rfl⟩ := (pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left).stalkMap_surjective z t'
  refine Submodule.mem_sup.2 ⟨t * cst (𝟙_ (Over (Sp R)) ⊗ G).hom
    ((pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left) z) q,
    Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _), _, hker ?_, add_sub_cancel _ _⟩
  rw [RingHom.mem_ker, map_sub, map_mul, cst_stalkMap', ht', sub_self]

end GlobalTheory.ClosedFibreDvd

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermDvdOfSectionExpansionDvdClosedFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.germ_dvd_of_sectionExpansion_dvd_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G) (σ : U.SecGT (𝟙_ _) 1) (f g : ∀ α, GlobalTheory.UU.SecBT D (𝟙_ _) 1 α) (q : R), U.ExpT (𝟙_ _) 1 σ f → (∀ α, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom q (f α) (g α)) → ∀ (x : (𝟙_ (Over (Sp R)) ⊗ G).left), (𝟙_ (Over (Sp R)) ⊗ G).hom x = closedPoint R → ∀ (j : Fin 1 → U.P.L.L.ι), x ∈ LB.wchart U.P.L.L (fun _ : Fin 1 => (snd (𝟙_ (Over (Sp R))) G).left) j → ∃ t, gs (𝟙 _) x (LB.wchart U.P.L.L (fun _ : Fin 1 => (snd (𝟙_ (Over (Sp R))) G).left) j) (σ.f j) = cst (𝟙_ (Over (Sp R)) ⊗ G).hom x q * t := by
  first | exact @GlobalTheory.ClosedFibreDvd.germ_dvd_of_expT_dvd | exact GlobalTheory.ClosedFibreDvd.germ_dvd_of_expT_dvd | (intros; apply GlobalTheory.ClosedFibreDvd.germ_dvd_of_expT_dvd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSectionDvdEverywhereSmoothConnectedFib
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSectionDvdEverywhereSmoothConnectedFib
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.DivSpread

theorem dvd_of_specializes {X : Scheme.{0}} {V : Type} [CommRing V] (p : X ⟶ Spec (CommRingCat.of V)) {L : LB X}
    (hL : L.IsLB) (s : LB.Sec L) (a : V) {x y : X} (hyx : y ⤳ x)
    (h : ∀ j, x ∈ L.U j → cst p x a ∣ gs (𝟙 X) x (L.U j) (s.f j)) :
    ∀ j, y ∈ L.U j → cst p y a ∣ gs (𝟙 X) y (L.U j) (s.f j) := by
  intro i hyi
  obtain ⟨k, hxk⟩ : ∃ k, x ∈ L.U k := by
    have : x ∈ (⨆ k, L.U k) := hL.cover ▸ trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  have hyk : y ∈ L.U k := hyx.mem_open (L.U k).isOpen hxk
  have sp : ∀ (U : X.Opens) (hx : x ∈ U) (b : Γ(X, U)),
      gs (𝟙 X) y U b = (X.presheaf.stalkSpecializes hyx).hom (gs (𝟙 X) x U b) := by
    intro U hx b
    rw [gs_eq _ y U (hyx.mem_open U.isOpen hx), gs_eq _ x U hx]
    exact (congrArg (fun φ => φ.hom ((Scheme.Hom.app (𝟙 X) U).hom b))
      (X.presheaf.germ_stalkSpecializes _ hyx)).symm
  let c : Γ(X, p ⁻¹ᵁ ⊤) := (p.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a)
  have hc : ∀ z, gs (𝟙 X) z (p ⁻¹ᵁ ⊤) c = cst p z a := fun z =>
    (gs_pull (𝟙 X) p z ⊤ trivial _).trans (by rw [Category.id_comp]; rfl)
  obtain ⟨t, ht⟩ := h k hxk
  have hk : cst p y a ∣ gs (𝟙 X) y (L.U k) (s.f k) := by
    refine ⟨(X.presheaf.stalkSpecializes hyx).hom t, ?_⟩
    rw [sp _ hxk, ht, map_mul, ← hc, ← hc, ← sp (p ⁻¹ᵁ ⊤) (show p x ∈ (⊤ : (Spec (CommRingCat.of V)).Opens) from trivial)]
  have hm : y ∈ L.U i ⊓ L.U k := ⟨hyi, hyk⟩
  have e := congrArg (gs (𝟙 X) y (L.U i ⊓ L.U k)) (s.compat i k)
  rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm] at e
  rw [e]
  exact Dvd.dvd.mul_left hk _

theorem exists_specializes_not_dvd {X : Scheme.{0}} {U W : X.Opens} (c : Γ(X, W)) (f : Γ(X, U)) {x : X}
    (hxU : x ∈ U) (hxW : x ∈ W) [IsDomain (X.presheaf.stalk x)] [IsIntegrallyClosed (X.presheaf.stalk x)]
    [IsNoetherianRing (X.presheaf.stalk x)] (h : ¬ gs (𝟙 X) x W c ∣ gs (𝟙 X) x U f) :
    ∃ y, y ⤳ x ∧ Order.coheight y ≤ 1 ∧ ¬ gs (𝟙 X) y W c ∣ gs (𝟙 X) y U f := by
  by_contra H
  push Not at H
  apply h
  obtain ⟨V, hV, hxV, hVle⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := U ⊓ W) (x := x) ⟨hxU, hxW⟩
  have hVU : V ≤ U := fun z hz => (hVle hz).1
  have hVW : V ≤ W := fun z hz => (hVle hz).2
  let fV : Γ(X, V) := (X.presheaf.map (homOfLE hVU).op).hom f
  let cV : Γ(X, V) := (X.presheaf.map (homOfLE hVW).op).hom c
  have hgf : ∀ z (hz : z ∈ V), gs (𝟙 X) z U f = (X.presheaf.germ V z hz).hom fV := fun z hz => by
    rw [← gs_res (𝟙 X) z hVU hz, gs_eq _ z V hz]; rfl
  have hgc : ∀ z (hz : z ∈ V), gs (𝟙 X) z W c = (X.presheaf.germ V z hz).hom cV := fun z hz => by
    rw [← gs_res (𝟙 X) z hVW hz, gs_eq _ z V hz]; rfl
  let : Algebra Γ(X, V) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hxV⟩
  have hlocx := hV.isLocalization_stalk ⟨x, hxV⟩
  rw [← Ideal.mem_span_singleton]
  refine GlobalTheory.PrincipalHartogs.mem_span_singleton_of_forall_height_le_one _ _ fun Q hQ hQ1 => ?_
  let P : Ideal Γ(X, V) := Q.comap (algebraMap Γ(X, V) (X.presheaf.stalk x))
  have hPp : P.IsPrime := Ideal.comap_isPrime _ Q
  let Pt : PrimeSpectrum Γ(X, V) := ⟨P, hPp⟩
  have hyV : hV.fromSpec Pt ∈ V := by
    have : hV.fromSpec Pt ∈ Set.range hV.fromSpec := ⟨Pt, rfl⟩
    rwa [hV.range_fromSpec] at this
  let yV : V := ⟨hV.fromSpec Pt, hyV⟩
  have hPt : hV.primeIdealOf yV = Pt := hV.fromSpec.isOpenEmbedding.injective (hV.fromSpec_primeIdealOf yV)
  have hsp : yV.1 ⤳ x := by
    have hle : Pt ≤ hV.primeIdealOf ⟨x, hxV⟩ := by
      show P ≤ (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
      rw [← IsLocalization.AtPrime.under_maximalIdeal (X.presheaf.stalk x) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal]
      exact Ideal.comap_mono (IsLocalRing.le_maximalIdeal hQ.ne_top)
    have := ((PrimeSpectrum.le_iff_specializes _ _).1 hle).map hV.fromSpec.continuous
    rwa [hV.fromSpec_primeIdealOf] at this
  let : Algebra Γ(X, V) (X.presheaf.stalk yV.1) := X.presheaf.algebra_section_stalk yV
  have hlocy := hV.isLocalization_stalk yV
  rw [hPt] at hlocy
  have hdim : Order.coheight yV.1 ≤ 1 := by
    rw [← GlobalTheory.ringKrullDim_stalk_le_one_iff, IsLocalization.AtPrime.ringKrullDim_eq_height P (X.presheaf.stalk yV.1)]
    have := IsLocalization.height_under (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl Q
    change (P.height : WithBot ℕ∞) ≤ 1
    rw [show P = Ideal.under Γ(X, V) Q from rfl, this]
    exact_mod_cast hQ1
  obtain ⟨t, ht⟩ := H yV.1 hsp hdim
  rw [hgf _ hyV, hgc _ hyV] at ht
  change algebraMap Γ(X, V) _ fV = algebraMap Γ(X, V) _ cV * t at ht
  obtain ⟨⟨a, w⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl t
  rw [IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.eq_mk'_iff_mul_eq, ← map_mul] at ht
  obtain ⟨m, hm⟩ := IsLocalization.exists_of_eq (M := P.primeCompl) ht
  refine ⟨algebraMap Γ(X, V) (X.presheaf.stalk x) (m * w), ?_, ?_⟩
  · exact (P.primeCompl.mul_mem m.2 w.2 : (m : Γ(X, V)) * w ∉ P)
  · rw [Ideal.mem_span_singleton, hgf x hxV, hgc x hxV]
    change algebraMap Γ(X, V) _ cV ∣ algebraMap Γ(X, V) _ (m * w) * algebraMap Γ(X, V) _ fV
    refine ⟨algebraMap Γ(X, V) (X.presheaf.stalk x) (m * a), ?_⟩
    rw [← map_mul, ← map_mul, show (m : Γ(X, V)) * w * fV = m * (fV * w) by ring, hm,
      show (m : Γ(X, V)) * (cV * a) = cV * (m * a) by ring]

theorem eq_of_specializes_of_coheight_le_one {X S : Scheme.{0}} (p : X ⟶ S) [Flat p] {y w : X}
    (hy : Order.coheight y ≤ 1) {P' : S} (hP' : P' ⤳ p y) (hne : P' ≠ p y) (hw : w ⤳ y) (he : p w = p y) :
    w = y := by
  by_contra hne'
  have hlt : y < w := lt_of_le_not_ge (show y ≤ w from hw) (fun h => hne' (hw.antisymm h).eq)
  have hmaxw : IsMax w := by simpa using (Order.coheight_le_coe_iff (n := 1)).1 hy w hlt
  obtain ⟨z, hz, hpz⟩ := Flat.generalizingMap p (show P' ⤳ p w from he ▸ hP')
  have h1 : w ≤ z := hz
  have h2 : z = w := (hz.antisymm (hmaxw h1)).eq
  exact hne (hpz.symm.trans (h2 ▸ he))

theorem mem_of_not_isUnit_cst {X : Scheme.{0}} {R : Type} [CommRing R] (p : X ⟶ Spec (CommRingCat.of R)) (y : X)
    (a : R) (h : ¬ IsUnit (cst p y a)) : a ∈ (p y).asIdeal := by
  by_contra ha
  apply h
  have hy : y ∈ p ⁻¹ᵁ ⊤ := show p y ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) from trivial
  rw [cst, gs_eq p y ⊤ hy]
  refine (X.mem_basicOpen _ y hy).1 ?_
  rw [← Scheme.preimage_basicOpen]
  show p y ∈ (Spec (CommRingCat.of R)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)
  rw [basicOpen_eq_of_affine]
  exact ha

theorem specializes_of_mem_fibre {X S : Scheme.{0}} (p : X ⟶ S) [GeometricallyIrreducible p] {y : X}
    (hmax : ∀ w, w ⤳ y → p w = p y → w = y) {z : X} (hz : p z = p y) : y ⤳ z := by
  obtain ⟨y', hy'⟩ : y ∈ Set.range (p.fiberι (p y)) := by rw [Scheme.Hom.range_fiberι]; rfl
  obtain ⟨z', hz'⟩ : z ∈ Set.range (p.fiberι (p y)) := by rw [Scheme.Hom.range_fiberι]; exact hz
  have hg : ∀ t, genericPoint (p.fiber (p y)) ⤳ t := fun t => (genericPoint_spec _).specializes trivial
  have hgm : p (p.fiberι (p y) (genericPoint (p.fiber (p y)))) = p y := by
    have : p.fiberι (p y) (genericPoint (p.fiber (p y))) ∈ Set.range (p.fiberι (p y)) := ⟨_, rfl⟩
    rw [Scheme.Hom.range_fiberι] at this
    exact this
  have h1 : p.fiberι (p y) (genericPoint (p.fiber (p y))) = y :=
    hmax _ (by have := (hg y').map (p.fiberι (p y)).continuous; rwa [hy'] at this) hgm
  rw [← h1, ← hz']
  exact (hg z').map (p.fiberι (p y)).continuous

end GlobalTheory.DivSpread

open GlobalTheory.DivSpread in
theorem GlobalTheory.DivSpread.dvd_everywhere : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] (X : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of R)), Smooth p → GeometricallyConnected p → ∀ (e : Spec (CommRingCat.of R) ⟶ X), e ≫ p = 𝟙 _ → ∀ (L : LB X), L.IsLB → ∀ (s : LB.Sec L) (q : R), q ≠ 0 → (∀ (x : X), p x = closedPoint R → ∀ j, x ∈ L.U j → ∃ t, gs (𝟙 X) x (L.U j) (s.f j) = cst p x q * t) → ∀ (x : X) j, x ∈ L.U j → ∃ t, gs (𝟙 X) x (L.U j) (s.f j) = cst p x q * t := by
  intro R _ _ _ _ _ X p hsm hgc e he L hL s q hq hcl x j hxj
  have : GeometricallyIntegral p := GlobalTheory.geometricallyIntegral_of_smooth p
  have : GlobalTheory.IsNormalScheme X := GlobalTheory.isNormalScheme_of_smooth p
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  by_contra hnot
  let c : Γ(X, p ⁻¹ᵁ ⊤) := (p.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom q)
  have hc : ∀ z, gs (𝟙 X) z (p ⁻¹ᵁ ⊤) c = cst p z q := fun z =>
    (gs_pull (𝟙 X) p z ⊤ trivial _).trans (by rw [Category.id_comp]; rfl)
  obtain ⟨y, hyx, hy1, hyn⟩ := exists_specializes_not_dvd c (s.f j) hxj trivial (by rw [hc]; exact hnot)
  rw [hc] at hyn
  have hyj : y ∈ L.U j := hyx.mem_open (L.U j).isOpen hxj
  have hqP : q ∈ (p y).asIdeal := mem_of_not_isUnit_cst p y q fun hu =>
    hyn ⟨hu.unit⁻¹ * gs (𝟙 X) y (L.U j) (s.f j), by rw [← _root_.mul_assoc, IsUnit.mul_val_inv, _root_.one_mul]⟩
  let P0 : Spec (CommRingCat.of R) := ⟨⊥, Ideal.isPrime_bot⟩
  have hP0 : P0 ⤳ p y := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  have hP0' : P0 ≠ p y := fun h => hq (by
    have : q ∈ P0.asIdeal := h ▸ hqP
    exact this)
  have hmax : ∀ w, w ⤳ y → p w = p y → w = y := fun w hw hpe =>
    eq_of_specializes_of_coheight_le_one p hy1 hP0 hP0' hw hpe
  have hey : p (e (p y)) = p y := by
    rw [← Scheme.Hom.comp_apply, he]; rfl
  have h1 : y ⤳ e (p y) := specializes_of_mem_fibre p hmax hey
  have h2 : e (p y) ⤳ e (closedPoint R) := (IsLocalRing.specializes_closedPoint (p y)).map e.continuous
  have hcm : p (e (closedPoint R)) = closedPoint R := by
    show (e ≫ p) (closedPoint R) = _
    rw [he]; rfl
  exact hyn (dvd_of_specializes p hL s q (h1.trans h2) (fun k hk => hcl _ hcm k hk) j hyj)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSectionDvdEverywhereSmoothConnectedFibStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundle_section_dvd_everywhere_smooth_connected_fibres : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] (X : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of R)), Smooth p → GeometricallyConnected p → ∀ (e : Spec (CommRingCat.of R) ⟶ X), e ≫ p = 𝟙 _ → ∀ (L : LB X), L.IsLB → ∀ (s : LB.Sec L) (q : R), q ≠ 0 → (∀ (x : X), p x = closedPoint R → ∀ j, x ∈ L.U j → ∃ t, gs (𝟙 X) x (L.U j) (s.f j) = cst p x q * t) → ∀ (x : X) j, x ∈ L.U j → ∃ t, gs (𝟙 X) x (L.U j) (s.f j) = cst p x q * t := by
  first | exact @GlobalTheory.DivSpread.dvd_everywhere | exact GlobalTheory.DivSpread.dvd_everywhere | (intros; apply GlobalTheory.DivSpread.dvd_everywhere <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseMulSectionOfGermDvdFlatDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseMulSectionOfGermDvdFlatDomain
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_secIsMul_of_germ_dvd : ∀ (R : Type) [CommRing R] [IsDomain R] (X : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of R)), Flat p → ∀ (L : LB X) (s : LB.Sec L) (q : R), q ≠ 0 → (∀ (x : X) j, x ∈ L.U j → ∃ t, gs (𝟙 X) x (L.U j) (s.f j) = cst p x q * t) → ∃ t : LB.Sec L, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul p q s t := by
  intro R _ _ X p hp L s q hq h
  haveI : Flat (X := X) (Y := Sp R) p := hp
  have loc : ∀ j, ∃ g : Γ(X, L.U j), s.f j = constFn p (L.U j) q * g := fun j =>
    exists_div p hq (L.U j) (s.f j) (fun x hx => h x j hx)
  choose t ht using loc
  have hg : ∀ j (x : X), x ∈ L.U j → gs (𝟙 X) x (L.U j) (s.f j) = cst p x q * gs (𝟙 X) x (L.U j) (t j) := by
    intro j x hx
    rw [ht j, gs_mul _ _ _ hx, gs_constFn p (L.U j) (𝟙 X) x hx, Category.id_comp]
  refine ⟨⟨t, fun i j => ?_⟩, fun j => ?_⟩
  · refine fn_ext fun x hx => ?_
    have e := congrArg (gs (𝟙 X) x (L.U i ⊓ L.U j)) (s.compat i j)
    rw [gs_mul _ _ _ hx, gs_res _ _ _ hx, gs_res _ _ _ hx] at e ⊢
    rw [hg i x hx.1, hg j x hx.2, mul_left_comm] at e
    exact cst_regular p x hq e
  · exact ht j

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseMulSectionOfGermDvdFlatDomainStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_baseMul_section_of_germ_dvd_flat_domain : ∀ (R : Type) [CommRing R] [IsDomain R] (X : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of R)), Flat p → ∀ (L : LB X) (s : LB.Sec L) (q : R), q ≠ 0 → (∀ (x : X) j, x ∈ L.U j → ∃ t, gs (𝟙 X) x (L.U j) (s.f j) = cst p x q * t) → ∃ t : LB.Sec L, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul p q s t := by
  first | exact @GlobalTheory.Mum.exists_secIsMul_of_germ_dvd | exact GlobalTheory.Mum.exists_secIsMul_of_germ_dvd | (intros; apply GlobalTheory.Mum.exists_secIsMul_of_germ_dvd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionQuotientOfExpansionDvd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.SecDiv

theorem resTop_map {Y : Scheme.{0}} {V W : Y.Opens} (h : W ≤ V) (c : Γ(Y, ⊤)) :
    (Y.presheaf.map (homOfLE h).op).hom (ReciprocityTheory.ChartRestriction.G.Out.resTop V c) = ReciprocityTheory.ChartRestriction.G.Out.resTop W c := by
  unfold ReciprocityTheory.ChartRestriction.G.Out.resTop
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem exists_secIsMul {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) {L : LB Y}
    (a : R) (τ : LB.Sec L) : ∃ σ : LB.Sec L, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul p a σ τ := by
  unfold ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul
  refine ⟨⟨fun j => ReciprocityTheory.ChartRestriction.G.Out.resTop (L.U j) (scal p a) * τ.f j, fun i j => ?_⟩, fun j => rfl⟩
  simp only [map_mul, resTop_map]
  rw [τ.2 i j]
  ring

theorem exists_expT_of_dvd : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G) (σ : U.SecGT (𝟙_ _) 1) (f g : ∀ α, GlobalTheory.UU.SecBT D (𝟙_ _) 1 α) (q : R), q ≠ 0 → U.ExpT (𝟙_ _) 1 σ f → (∀ α, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom q (f α) (g α)) → ∃ τ : U.SecGT (𝟙_ _) 1, U.ExpT (𝟙_ _) 1 τ g := by
  intro R _ _ _ hB D A G _ _ U σ f g q hq hσ hfg
  have hB' : AdmBase R (maximalIdeal R) ∧ CharZero R := hB
  have h1 : IsNoetherianRing R ∧ IsDomain R ∧ IsIntegrallyClosed R ∧ IsAdicComplete (maximalIdeal R) R := hB'.1
  obtain ⟨hN, -, hIC, hC⟩ := h1
  haveI := hN
  haveI := hIC
  have hs := U.semi
  haveI := hs.smooth
  haveI := hs.geomConnected
  haveI : IsIso (λ_ G).hom.left := inferInstanceAs (IsIso ((Over.forget _).mapIso (λ_ G)).hom)
  have hSm : Smooth (𝟙_ (Over (Sp R)) ⊗ G).hom := by
    rw [← Over.w (λ_ G).hom]
    infer_instance
  have hGC : GeometricallyConnected (𝟙_ (Over (Sp R)) ⊗ G).hom := by
    have hsq : IsPullback (λ_ G).hom.left (𝟙_ (Over (Sp R)) ⊗ G).hom G.hom (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [Over.w, Category.comp_id]⟩
    exact MorphismProperty.of_isPullback (P := @GeometricallyConnected) hsq inferInstance
  have he : (η[G].left ≫ (λ_ G).inv.left) ≫ (𝟙_ (Over (Sp R)) ⊗ G).hom = 𝟙 _ := by
    simp only [Category.assoc, Over.w]
    rfl
  have hLB : (LB.LinComb U.P.L.L (K := Fin 1) (fun _ : Fin 1 => (snd (𝟙_ (Over (Sp R))) G).left)
      (fun _ => ((1 : ℕ) : ℤ))).IsLB := by
    first
    | exact ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ U.P.L.isLB _ _
    | exact ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ _ _
  have hloc := GlobalTheory.T.germ_dvd_of_sectionExpansion_dvd_closedFibre R hB D A G U σ f g q hσ hfg
  have hall := GlobalTheory.T.lineBundle_section_dvd_everywhere_smooth_connected_fibres R _ (𝟙_ (Over (Sp R)) ⊗ G).hom hSm hGC _ he _ hLB σ q hq hloc
  have hflat : Flat (𝟙_ (Over (Sp R)) ⊗ G).hom := inferInstance
  obtain ⟨τ, hτ⟩ := GlobalTheory.T.exists_baseMul_section_of_germ_dvd_flat_domain R _ (𝟙_ (Over (Sp R)) ⊗ G).hom hflat _ σ q hq hall
  have hEga : GlobalTheory.LN.AlgSt ∧ GlobalTheory.LN.MorAlgSt ∧ GlobalTheory.LN.SecAlgSt ∧ GlobalTheory.LN.PicardZeroDegenerationCondition := GlobalTheory.LN.ega_holds
  obtain ⟨h, hh⟩ := GlobalTheory.CompleteBaseExpansion.exists_expT hEga.2.2.1 hC U 1 τ
  choose f' hf' using fun α => exists_secIsMul (𝟙_ (Over (Sp R)) ⊗ D.P.A).hom q (h α)
  have hσf' : U.ExpT (𝟙_ _) 1 σ f' := GlobalTheory.T.sectionExpansion_scale_base_element R (maximalIdeal R) D A G U 1 q σ τ f' h hτ hf' hh
  have hjac : maximalIdeal R ≤ Ideal.jacobson ⊥ := (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
  have hff' : f' = f := GlobalTheory.CompleteBaseExpansion.expT_unique hjac U 1 σ f' f hσf' hσ
  have hflatD : Flat (𝟙_ (Over (Sp R)) ⊗ D.P.A).hom := by
    haveI : IsIso (λ_ D.P.A).hom.left := inferInstanceAs (IsIso ((Over.forget _).mapIso (λ_ D.P.A)).hom)
    haveI : Smooth D.P.A.hom := D.P.isAb.smooth
    rw [← Over.w (λ_ D.P.A).hom]
    infer_instance
  have hhg : h = g := by
    funext α
    have hfa := hf' α
    rw [hff'] at hfa
    exact GlobalTheory.T.lineBundleSection_baseMul_cancel_flat_domain R _ _ hflatD _ q hq (f α) (h α) (g α) hfa (hfg α)
  refine ⟨τ, ?_⟩
  rw [← hhg]
  exact hh

end GlobalTheory.SecDiv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionQuotientOfExpansionDvdStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_quotient_of_expansion_dvd : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G) (σ : U.SecGT (𝟙_ _) 1) (f g : ∀ α, GlobalTheory.UU.SecBT D (𝟙_ _) 1 α) (q : R), q ≠ 0 → U.ExpT (𝟙_ _) 1 σ f → (∀ α, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom q (f α) (g α)) → ∃ τ : U.SecGT (𝟙_ _) 1, U.ExpT (𝟙_ _) 1 τ g := by
  first | exact @GlobalTheory.SecDiv.exists_expT_of_dvd | exact GlobalTheory.SecDiv.exists_expT_of_dvd | (intros; apply GlobalTheory.SecDiv.exists_expT_of_dvd <;> assumption)
end

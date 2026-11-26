module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinimalSiegelCompactificationExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalModelCartierDivisorThetaSetup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealSheafDescendingDivisorPowerThetaSetup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormDescentIdealSheafFiniteOpenClosedImageStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinimalBlowupSmoothWithSemiAbelianCharts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDescentFromCompleteRegularCharts

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedBlowupAmpleDivisorCompactification
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFanOrderIdealThetaCompactification
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSetupIdealOverClopenComponent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealOrdersOfProperModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

theorem _root_.GlobalTheory.Poinc.ideal_orders_of_proper_model : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W8 : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (φ : InvFun ℤ) (X₁ : Setup F W8 i) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY → IsProper πY → ∀ (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), (∀ y ∈ (J₁.comap πY).support, X₁.π (πY y) ∉ Set.range i) → (∀ (T : Trait F) (ξ : Sp T.V ⟶ Y.Z), jK T.V ≫ ξ ≫ πY ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong (J₁.comap πY) ξ = Ideal.span {T.ϖ ^ a}) → (∀ (T : Trait F) (k : ℕ), 1 ≤ k → φ.evalZ ((k : ℤ) • T.β) = k * φ.evalZ T.β) → (∀ x ∈ J₁.support, X₁.π x ∉ Set.range i) ∧ ∀ (T : Trait F) (ξ₁ : Sp T.V ⟶ X₁.M.Z), jK T.V ≫ ξ₁ ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong J₁ ξ₁ = Ideal.span {T.ϖ ^ a} := by
  intro g n F W8 Z i φ X₁ Y πY hhom hprop ι J₁ hsupp hord hφ
  haveI := hprop

  have hsurj : Function.Surjective πY := by
    have hgen : genericPoint X₁.M.Z ∈ Set.range πY := by
      have w : Sp X₁.Ω₁ := IsLocalRing.closedPoint X₁.Ω₁
      refine ⟨Y.pt w, ?_⟩
      have h := congrArg (fun h : Sp X₁.Ω₁ ⟶ X₁.M.Z => h w) (show Y.pt ≫ πY = _ from hhom)
      simp only [Scheme.Hom.comp_apply] at h
      rw [h]
      exact X₁.M.pt_apply _
    have hcl : IsClosed (Set.range πY) := πY.isClosedMap.isClosed_range
    intro x
    have : x ∈ closure (Set.range πY) :=
      closure_mono (Set.singleton_subset_iff.2 hgen) (by rw [genericPoint_spec X₁.M.Z]; trivial)
    rwa [hcl.closure_eq] at this
  refine ⟨fun x hx => ?_, fun T ξ₁ hT => ?_⟩
  · obtain ⟨y, rfl⟩ := hsurj x
    exact hsupp y (by rw [Scheme.IdealSheafData.support_comap]; exact hx)
  ·
    obtain ⟨K', _, σ, yK, hσ, hy⟩ := GlobalTheory.T.exists_finiteExt_point_lift_of_surjective_locFinType πY inferInstance hsurj (FractionRing T.V) (jK T.V ≫ ξ₁)
    obtain ⟨V', _, _, _, _, f, τ, hc', hfi, hfl, hff, hτ⟩ := GlobalTheory.T.exists_complete_dvr_integralClosure_finite_fractionRing T.V T.complete K' σ hσ
    have hfK : ∀ a, (τ.comp σ) (algebraMap T.V _ a) = algebraMap V' _ (f a) := hτ
    obtain ⟨ξ', hξπ, hξg⟩ := GlobalTheory.T.proper_lift_trait_of_generic_lift πY hprop T.V V' f (τ.comp σ) hfK ξ₁ (spMap τ ≫ yK) (by
      rw [Category.assoc, hy, spMap_comp, Category.assoc])
    have hB' : GlobalTheory.Mum.Base V' := ⟨⟨inferInstance, inferInstance, inferInstance, hc'⟩, inferInstance⟩
    obtain ⟨T₂, f₂, fK₂, hf₂i, hf₂l, -, hf₂K, hT₂y⟩ :=
      GlobalTheory.T.traitExistsAfterFiniteExtension_of_completeDVR g n _ _ F V' hB' inferInstance (spMap (τ.comp σ) ≫ T.y)
    haveI := hfl
    haveI := hf₂l
    have hjK : ∀ {R S : Type} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] (u : R →+* S)
        (uK : FractionRing R →+* FractionRing S), (∀ a, uK (algebraMap R _ a) = algebraMap S _ (u a)) →
        jK S ≫ spMap u = spMap uK ≫ jK R := by
      intro R S _ _ _ _ u uK hu
      change spMap (algebraMap S (FractionRing S)) ≫ spMap u = spMap uK ≫ spMap (algebraMap R (FractionRing R))
      rw [← spMap_comp, ← spMap_comp]
      exact congrArg spMap (RingHom.ext fun a => (hu a).symm)

    have hcomm : jK T₂.V ≫ (spMap f₂ ≫ ξ') ≫ πY ≫ X₁.π = T₂.y ≫ i := by
      have e1 := hjK f₂ fK₂ hf₂K
      calc jK T₂.V ≫ (spMap f₂ ≫ ξ') ≫ πY ≫ X₁.π = (jK T₂.V ≫ spMap f₂) ≫ ξ' ≫ πY ≫ X₁.π := by
            simp only [Category.assoc]
        _ = spMap fK₂ ≫ (jK V' ≫ ξ') ≫ πY ≫ X₁.π := by rw [e1]; simp only [Category.assoc]
        _ = spMap fK₂ ≫ spMap τ ≫ (yK ≫ πY) ≫ X₁.π := by rw [hξg]; simp only [Category.assoc]
        _ = spMap fK₂ ≫ spMap τ ≫ spMap σ ≫ (jK T.V ≫ ξ₁ ≫ X₁.π) := by rw [hy]; simp only [Category.assoc]
        _ = T₂.y ≫ i := by rw [hT, hT₂y, spMap_comp]; simp only [Category.assoc]
    obtain ⟨a', ha', hid⟩ := hord T₂ (spMap f₂ ≫ ξ') hcomm
    rw [GlobalTheory.PullAlong.idlAlong_comap_eq, Category.assoc, hξπ, ← Category.assoc, ← spMap_comp,
      GlobalTheory.TraitOrder.idlAlong_comp] at hid

    set h := f₂.comp f with hh
    have hinj : Function.Injective h := hf₂i.comp hfi
    have hloc : IsLocalHom h := inferInstance
    have hne : h T.ϖ ≠ 0 := (map_ne_zero_iff h hinj).2 T.irr.ne_zero
    obtain ⟨e, he⟩ := IsDiscreteValuationRing.associated_pow_irreducible hne T₂.irr
    have he1 : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with rfl | hpos
      · exact absurd ((isUnit_map_iff h T.ϖ).1 (he.isUnit_iff.2 (by simp))) T.irr.not_isUnit
      · exact hpos
    obtain ⟨b, hb, hI⟩ := GlobalTheory.T.ideal_map_eq_span_pow_uniformizer_dvr T.V T₂.V h hinj T.ϖ T₂.ϖ e a' _ T.irr T₂.irr he hid

    have hB₂ : GlobalTheory.Mum.Base T₂.V := ⟨⟨inferInstance, inferInstance, inferInstance, T₂.complete⟩, inferInstance⟩
    obtain ⟨eq, heq⟩ := GlobalTheory.T.trait_lattices_iso_forms_proportional_ramification g n _ _ F T T₂ T₂.V h (RingHom.id _) (fK₂.comp (τ.comp σ)) (RingHom.id _)
      hB₂ inferInstance hinj Function.injective_id hloc inferInstance
      (fun a => by rw [RingHom.comp_apply, hfK, hf₂K]; rfl) (fun _ => rfl)
      (by
        rw [hT₂y, spMap_comp, Category.assoc]
        have hid1 : spMap (RingHom.id (FractionRing T₂.V)) = 𝟙 _ := by
          simp [spMap]
        rw [hid1, Category.id_comp]) T₂.ϖ e 1 T₂.irr he (by simp)
    have hval : φ.evalZ T₂.β = e * φ.evalZ T.β := by
      rw [← hφ T e he1]
      unfold InvFun.evalZ
      rw [← φ.eval_equiv eq.toIntLinearEquiv]
      congr 1
      ext a c
      have := heq a c
      simp only [Nat.cast_one, one_mul] at this
      simp [AddEquiv.coe_toIntLinearEquiv, ← this]
    refine ⟨b, ?_, hI⟩
    have h1 : (e : ℝ) * b = e * (ι * φ.evalZ T.β) := by
      rw [← Nat.cast_mul, hb, ha', hval]; ring
    have h2 : (e : ℝ) ≠ 0 := by exact_mod_cast (by omega : e ≠ 0)
    exact mul_left_cancel₀ h2 h1
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTailTail
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem Setup.range_π_eq : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W8 : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W8 i) (η : F.X) (W : Set Z), (∀ w, (spMap X₁.S.R.val.toRingHom ≫ X₁.u) w = η) → closure {i η} = W → Set.range X₁.π = W := by
  intro g n F W8 Z i X₁ η W hη hW
  haveI := X₁.fin
  have hc : IsClosedMap X₁.π.base := X₁.π.isClosedMap
  let w₀ : Sp X₁.Ω₁ := IsLocalRing.closedPoint X₁.Ω₁
  have hgen : X₁.M.pt w₀ = genericPoint X₁.M.Z := X₁.M.pt_apply w₀
  have hpt : X₁.π (X₁.M.pt w₀) = i η := by
    have h := congrArg (fun f => f.base w₀) X₁.comp
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
    rw [← hη w₀]
    simpa using h
  have huniv : closure ({genericPoint X₁.M.Z} : Set X₁.M.Z) = Set.univ := genericPoint_spec X₁.M.Z
  rw [← hW, ← hpt, hgen, ← Set.image_singleton, ← Set.image_univ, ← huniv]
  exact (hc.closure_image_eq_of_continuous X₁.π.continuous _).symm

end GlobalTheory.Poinc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemGenericPointsClosureEqOfIsClopen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory

theorem exists_mem_genericPoints_closure_eq_of_isClopen :
    ∀ (X Z : Scheme.{0}) (i : X ⟶ Z), IsOpenImmersion i → Dense (Set.range i) → ∀ W : Set Z, IsClopen W → IsIrreducible W → ∃ η ∈ genericPoints X, closure {i η} = W := by
  intro X Z i hi hd W hWc hWi
  have he : Topology.IsOpenEmbedding i := i.isOpenEmbedding

  have hgen : IsGenericPoint hWi.genericPoint W :=
    hWi.isGenericPoint_genericPoint hWc.isClosed
  have hne : (W ∩ Set.range i).Nonempty :=
    hd.inter_open_nonempty W hWc.isOpen hWi.nonempty
  have hmem : hWi.genericPoint ∈ Set.range i :=
    (hgen.mem_open_set_iff he.isOpen_range).2 hne
  obtain ⟨η, hη⟩ := hmem
  have hcl : closure {i η} = W := by rw [hη]; exact hgen
  refine ⟨η, ?_, hcl⟩

  have hpre : closure ({η} : Set X) = i ⁻¹' W := by
    rw [← hcl, he.isOpenMap.preimage_closure_eq_closure_preimage he.continuous,
      ← Set.image_singleton, he.injective.preimage_image]
  show closure ({η} : Set X) ∈ irreducibleComponents X
  have hirr : IsIrreducible (closure ({η} : Set X)) := isIrreducible_singleton.closure
  have hclo : IsClopen (closure ({η} : Set X)) := by
    rw [hpre]; exact hWc.preimage he.continuous
  refine ⟨hirr, fun T hT hsub => ?_⟩
  refine hT.2.isPreconnected.subset_isClopen hclo ?_
  exact ⟨η, hsub (subset_closure rfl), subset_closure rfl⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSetupIdealOverClopenComponent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

theorem _root_.GlobalTheory.Poinc.exists_setup_ideal_over_component : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z), IsThetaCompact F z i → ∀ φ : InvFun ℤ, IsPolFan id g φ → ∀ W : Set Z, IsClopen W → IsIrreducible W → ∃ (W8 : Matrix (Fin 8) (Fin 8) ℤ) (X₁ : Setup F W8 i) (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι ∧ Set.range X₁.π = W ∧ (∀ x ∈ J₁.support, X₁.π x ∉ Set.range i) ∧ ∀ (T : Trait F) (ξ₁ : Sp T.V ⟶ X₁.M.Z), jK T.V ≫ ξ₁ ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong J₁ ξ₁ = Ideal.span {T.ϖ ^ a} := by
  intro g n hg hn hodd F Z z i hθ φ hφ W hWc hWi
  obtain ⟨hproj, hnorm, hopen, hcomp, hdense, W8, hE8, hTI⟩ := id hθ
  obtain ⟨η, hη, hcl⟩ := GlobalTheory.exists_mem_genericPoints_closure_eq_of_isClopen F.X Z i hopen hdense W hWc hWi
  obtain ⟨X₁, -, hX₁⟩ := GlobalTheory.Poinc.GSetup.exists_setup g n hg hn hodd F Z z i hproj
    (fun x => ⟨hnorm.isDomain_stalk x, hnorm.isIntegrallyClosed_stalk x⟩) hopen hcomp hdense W8 hE8 hTI η hη 0
  have hr := GlobalTheory.Poinc.Setup.range_π_eq g n F W8 Z i X₁ η W hX₁ hcl
  obtain ⟨ι, Y, πY, D, hι, hhom, hprop, hnY, hsupp, hord⟩ := GlobalTheory.T.exists_normal_model_cartierDivisor_thetaSetup g n hg hn hodd F Z z i hθ φ hφ W8 hE8 hTI X₁
  obtain ⟨ι', J₁, hι', hsupp', hord'⟩ :=
    GlobalTheory.T.exists_idealSheaf_descending_divisor_power_thetaSetup g n hg hn hodd F Z z i hθ φ hφ W8 hE8 hTI X₁ ι Y πY D hι X₁.projM hhom hprop hnY hsupp hord
  have hhomog : ∀ (T : Trait F) (k : ℕ), 1 ≤ k → φ.evalZ ((k : ℤ) • T.β) = k * φ.evalZ T.β := by
    intro T k _
    have hrk : Module.finrank ℤ T.D.toPre.X ≤ g := by
      have := GlobalTheory.Poinc.Trait.dim_add_rank (by omega : 2 ≤ n) F T
      omega
    have hβ : T.β ∈ balForms (id : ℤ → ℤ) T.D.toPre.X := ⟨T.symm, fun a y z => by simp⟩
    rw [natCast_zsmul, StrictData.evalZ_eq, StrictData.evalZ_eq, StrictData.toReal_nsmul]
    exact (hφ _ hrk).homog _ (StrictData.toReal_mem_psdCone hβ fun y => T.mono.nonneg 0 y) _ (Nat.cast_nonneg k)
  obtain ⟨hs, ho⟩ := GlobalTheory.Poinc.ideal_orders_of_proper_model g n F W8 Z i φ X₁ Y πY hhom hprop ι' J₁ hsupp' hord' hhomog
  exact ⟨W8, X₁, ι', J₁, hι', hr, hs, ho⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSetupIdealOverClopenComponentStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaSetup_ideal_over_clopen_component : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z), IsThetaCompact F z i → ∀ φ : InvFun ℤ, IsPolFan id g φ → ∀ W : Set Z, IsClopen W → IsIrreducible W → ∃ (W8 : Matrix (Fin 8) (Fin 8) ℤ) (X₁ : Setup F W8 i) (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι ∧ Set.range X₁.π = W ∧ (∀ x ∈ J₁.support, X₁.π x ∉ Set.range i) ∧ ∀ (T : Trait F) (ξ₁ : Sp T.V ⟶ X₁.M.Z), jK T.V ≫ ξ₁ ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong J₁ ξ₁ = Ideal.span {T.ϖ ^ a} := by
  first | exact @GlobalTheory.Poinc.exists_setup_ideal_over_component | exact GlobalTheory.Poinc.exists_setup_ideal_over_component | (intros; apply GlobalTheory.Poinc.exists_setup_ideal_over_component <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealDescentThetaModelToComponentTraitOrders
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormDescentIdealThetaModelToClopenComponent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormDescentIdealThetaModelToClopenComponent
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.NormDown

theorem dvd_of_map_dvd {V V' : Type} [CommRing V] [IsDomain V] [ValuationRing V] [CommRing V'] [IsDomain V']
    (h : V →+* V') (hi : Function.Injective h) [IsLocalHom h] {x y : V} (hxy : h x ∣ h y) : x ∣ y := by
  rcases ValuationRing.dvd_total x y with hd | ⟨c, rfl⟩
  · exact hd
  · by_cases hy : y = 0
    · simp [hy]
    obtain ⟨e, he⟩ := hxy
    have hy' : h y ≠ 0 := fun h0 => hy (hi (by rw [h0, map_zero]))
    have h1 : h y * 1 = h y * (h c * e) := by rw [mul_one, ← mul_assoc, ← map_mul, ← he]
    have hu : IsUnit (h c) := isUnit_iff_exists_inv.2 ⟨e, (mul_left_cancel₀ hy' h1).symm⟩
    have hc : IsUnit c := (isUnit_map_iff h c).1 hu
    exact ⟨↑hc.unit⁻¹, by rw [mul_assoc, IsUnit.mul_val_inv, mul_one]⟩

theorem map_injective {V V' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing V'] [IsDomain V']
    (h : V →+* V') (hi : Function.Injective h) [IsLocalHom h] {I I' : Ideal V} (e : I.map h = I'.map h) : I = I' := by
  obtain ⟨x, rfl⟩ : ∃ x, I = Ideal.span {x} := ⟨_, (Submodule.IsPrincipal.span_singleton_generator I).symm⟩
  obtain ⟨y, rfl⟩ : ∃ y, I' = Ideal.span {y} := ⟨_, (Submodule.IsPrincipal.span_singleton_generator I').symm⟩
  rw [Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton,
    Ideal.span_singleton_eq_span_singleton] at e
  rw [Ideal.span_singleton_eq_span_singleton]
  exact associated_of_dvd_dvd (dvd_of_map_dvd h hi e.dvd) (dvd_of_map_dvd h hi e.symm.dvd)

theorem jK_spMap {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (fK : FractionRing R →+* FractionRing S)
    (hc : ∀ a, fK (algebraMap R _ a) = algebraMap S _ (f a)) : jK S ≫ spMap f = spMap fK ≫ jK R := by
  simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext a
  exact (hc a).symm

theorem normDescent : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z), IsThetaCompact F z i → ∀ φ : InvFun ℤ, IsPolFan id g φ → ∀ W : Set Z, IsClopen W → IsIrreducible W → ∀ (W8 : Matrix (Fin 8) (Fin 8) ℤ) (X₁ : Setup F W8 i) (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι → Set.range X₁.π = W → (∀ x ∈ J₁.support, X₁.π x ∉ Set.range i) → (∀ (T : Trait F) (ξ₁ : Sp T.V ⟶ X₁.M.Z), jK T.V ≫ ξ₁ ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong J₁ ξ₁ = Ideal.span {T.ϖ ^ a}) → ∃ (k : ℕ) (J : Z.IdealSheafData), 1 ≤ k ∧ (∀ x ∈ J.support, x ∈ W ∧ x ∉ Set.range i) ∧ ∀ (T : Trait F) (ξ₁ : Sp T.V ⟶ X₁.M.Z), jK T.V ≫ ξ₁ ≫ X₁.π = T.y ≫ i → idlAlong J (ξ₁ ≫ X₁.π) = idlAlong J₁ ξ₁ ^ k := by
  intro g n hg hn hodd F Z z i hZ φ hφ W hWc hWi W8 X₁ ι J₁ hι hπ hsupp hord
  have idlAlong_eq_map_local {X : Scheme.{0}} (J : X.IdealSheafData) {R : Type} [CommRing R] [IsLocalRing R] (χ : Sp R ⟶ X)
      (U : X.affineOpens) (hle : ⊤ ≤ χ ⁻¹ᵁ U.1) :
      idlAlong J χ = (J.ideal U).map (χ.appLE U.1 ⊤ hle ≫ (Scheme.ΓSpecIso (.of R)).hom).hom := by
    have hx : χ (closedPoint R) ∈ U.1 := hle trivial
    unfold idlAlong
    rw [ds_stalkId_eq_map J U _ hx, Ideal.map_map, ← CommRingCat.hom_comp, Scheme.germ_stalkClosedPointTo]
    congr 2
  have idlAlong_comp_local {X : Scheme.{0}} (J : X.IdealSheafData) {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S]
      [IsLocalRing S] (χ : Sp R ⟶ X) (f : R →+* S) : idlAlong J (spMap f ≫ χ) = (idlAlong J χ).map f := by
    obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
      (show χ (closedPoint R) ∈ (⊤ : X.Opens) from trivial)
    have hle : ⊤ ≤ χ ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem χ hx).ge
    have hle' : ⊤ ≤ (spMap f ≫ χ) ⁻¹ᵁ U := fun x _ => hle (show spMap f x ∈ (⊤ : (Sp R).Opens) from trivial)
    rw [idlAlong_eq_map_local J χ ⟨U, hU⟩ hle, idlAlong_eq_map_local J _ ⟨U, hU⟩ hle', Ideal.map_map]
    congr 1
    have e : (spMap f ≫ χ).appLE U ⊤ hle' = χ.appLE U ⊤ hle ≫ (spMap f).appTop := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    rw [e, Category.assoc, Scheme.ΓSpecIso_naturality, ← Category.assoc, CommRingCat.hom_comp]
    rfl
  have hne : ((⊤ : X₁.M.Z.Opens) : Set X₁.M.Z).Nonempty := Set.univ_nonempty
  haveI : CharZero X₁.Ω₁ := X₁.ar.char
  haveI hchar : CharZero Γ(X₁.M.Z, ⊤) := RingHom.charZero (X₁.M.res ⊤ hne)
  haveI : IsDedekindDomain X₁.o₁ := X₁.ar.ded
  haveI := X₁.M.lft
  have hLN : IsLocallyNoetherian X₁.M.Z := LocallyOfFiniteType.isLocallyNoetherian X₁.M.s
  obtain ⟨d, J, hd, hJs, hJl⟩ := GlobalTheory.T.norm_descent_idealSheaf_finite_open_closed_image X₁.M.Z Z X₁.π X₁.fin inferInstance hLN X₁.normal hZ.2.1
    (by rw [hπ]; exact hWc.isOpen) hchar J₁
  refine ⟨d, J, hd, fun x hx => ?_, ?_⟩
  · obtain ⟨y, hy, rfl⟩ := hJs x hx
    exact ⟨hπ ▸ ⟨y, rfl⟩, hsupp y hy⟩
  intro T ξ₁ hgen
  obtain ⟨V', _, _, _, _, f, ψ, hc', hfi, hfl, hψ, hprod⟩ :=
    hJl T.V T.complete (ξ₁ ≫ X₁.π) ⟨ξ₁ (closedPoint T.V), rfl⟩
  let fK : FractionRing T.V →+* FractionRing V' :=
    IsLocalization.map (FractionRing V') f (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective f hfi)
  have hfK : ∀ a, fK (algebraMap T.V _ a) = algebraMap V' _ (f a) := fun a => IsLocalization.map_eq _ a
  have hB : GlobalTheory.Mum.Base V' := ⟨⟨inferInstance, inferInstance, inferInstance, hc'⟩, inferInstance⟩
  obtain ⟨T₂, f₂, fK₂, hi₂, hl₂, -, hc₂, hy₂⟩ := GlobalTheory.T.traitExistsAfterFiniteExtension_of_completeDVR g n _ _ F V' hB inferInstance (spMap fK ≫ T.y)

  have hover : ∀ χ : Sp V' ⟶ X₁.M.Z, χ ≫ X₁.π = spMap f ≫ ξ₁ ≫ X₁.π →
      jK T₂.V ≫ (spMap f₂ ≫ χ) ≫ X₁.π = T₂.y ≫ i := by
    intro χ hχ
    rw [Category.assoc, hχ, ← Category.assoc, jK_spMap f₂ fK₂ hc₂, Category.assoc, ← Category.assoc (jK V'),
      jK_spMap f fK hfK, Category.assoc, hgen, hy₂]
    simp only [Category.assoc]
  obtain ⟨a₀, ha₀, h₀⟩ := hord T₂ _ (hover (spMap f ≫ ξ₁) (Category.assoc _ _ _))
  have hj : ∀ j, idlAlong J₁ (spMap f₂ ≫ ψ j) = Ideal.span {T₂.ϖ ^ a₀} := by
    intro j
    obtain ⟨a, ha, h⟩ := hord T₂ _ (hover (ψ j) (hψ j))
    rw [h, show a = a₀ from by exact_mod_cast ha.trans ha₀.symm]
  have hcomp : spMap (f₂.comp f) = spMap f₂ ≫ spMap f := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  haveI : IsLocalHom (f₂.comp f) := RingHom.isLocalHom_comp f₂ f
  apply map_injective (f₂.comp f) (hi₂.comp hfi)
  have hmp := map_prod (Ideal.mapHom f₂) (fun j => idlAlong J₁ (ψ j)) Finset.univ
  simp only [Ideal.mapHom_apply] at hmp
  rw [← Ideal.map_map, hprod, Ideal.map_pow, ← idlAlong_comp_local, hcomp, Category.assoc, h₀, hmp]
  simp only [← idlAlong_comp_local, hj, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end GlobalTheory.NormDown
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormDescentIdealThetaModelToClopenComponentStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_descent_ideal_thetaModel_to_clopen_component : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z), IsThetaCompact F z i → ∀ φ : InvFun ℤ, IsPolFan id g φ → ∀ W : Set Z, IsClopen W → IsIrreducible W → ∀ (W8 : Matrix (Fin 8) (Fin 8) ℤ) (X₁ : Setup F W8 i) (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι → Set.range X₁.π = W → (∀ x ∈ J₁.support, X₁.π x ∉ Set.range i) → (∀ (T : Trait F) (ξ₁ : Sp T.V ⟶ X₁.M.Z), jK T.V ≫ ξ₁ ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong J₁ ξ₁ = Ideal.span {T.ϖ ^ a}) → ∃ (k : ℕ) (J : Z.IdealSheafData), 1 ≤ k ∧ (∀ x ∈ J.support, x ∈ W ∧ x ∉ Set.range i) ∧ ∀ (T : Trait F) (ξ₁ : Sp T.V ⟶ X₁.M.Z), jK T.V ≫ ξ₁ ≫ X₁.π = T.y ≫ i → idlAlong J (ξ₁ ≫ X₁.π) = idlAlong J₁ ξ₁ ^ k := by
  first | exact @GlobalTheory.NormDown.normDescent | exact GlobalTheory.NormDown.normDescent | (intros; apply GlobalTheory.NormDown.normDescent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalZEqMul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc.TraitRam

variable {g n : ℕ} {o : Type} [CommRing o] {ζ : o} {F : SFam g n ζ}

theorem dim_eq (hn : 2 ≤ n) (hζ : IsUnit ζ) (T : Trait F) : T.A.g = g := by
  let K := AlgebraicClosure (FractionRing T.V)
  let k : Sp K ⟶ Sp (FractionRing T.V) := spMap (algebraMap (FractionRing T.V) K)
  have hK : (n : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hp := (IsPullback.of_hasPullback T.A.A.hom k).paste_horiz T.cart.1
  have h1 : SmoothOfRelativeDimension T.A.g (pullback.snd T.A.A.hom k) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
      (IsPullback.of_hasPullback T.A.A.hom k) T.A.smoothDim
  refine GlobalTheory.SiegDim.dim_geometric_fibre F.univ hn hζ hK (k ≫ T.y) ?_
  change SmoothOfRelativeDimension T.A.g (pullback.snd F.univ.A.hom (k ≫ T.y))
  rw [← hp.isoPullback_inv_snd]
  exact (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
    (IsPullback.of_horiz_isIso (fst := hp.isoPullback.inv) (g := 𝟙 _) ⟨by simp⟩) h1

theorem finrank_le (hn : 2 ≤ n) (hζ : IsUnit ζ) (T : Trait F) : Module.finrank ℤ T.D.toPre.X ≤ g := by
  have hR : AdmBase T.V (maximalIdeal T.V) := ⟨inferInstance, inferInstance, inferInstance, T.complete⟩
  have h := GlobalTheory.TateUnif.rank_add_dim hR T.semi T.U
  have e := dim_eq hn hζ T
  omega

theorem evalZ_eq_mul : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o), 2 ≤ n → IsUnit ζ → ∀ (F : SFam g n ζ) (T T' : Trait F) (f : T.V →+* T'.V) (fK : FractionRing T.V →+* FractionRing T'.V), Function.Injective f → IsLocalHom f → (∀ a, fK (algebraMap T.V (FractionRing T.V) a) = algebraMap T'.V (FractionRing T'.V) (f a)) → T'.y = spMap fK ≫ T.y → ∀ m : ℕ, Associated (f T.ϖ) (T'.ϖ ^ m) → ∀ φ : InvFun ℤ, IsPolFan id g φ → φ.evalZ T'.β = m * φ.evalZ T.β := by
  intro g n o _ ζ hn hζ F T T' f fK hf hl hK hy m hm φ hφ
  have hB : GlobalTheory.Mum.Base T'.V := ⟨⟨inferInstance, inferInstance, inferInstance, T'.complete⟩, inferInstance⟩
  have hid : spMap (RingHom.id (FractionRing T'.V)) = 𝟙 _ := Spec.map_id _
  obtain ⟨e, he⟩ := GlobalTheory.T.trait_lattices_iso_forms_proportional_ramification g n o ζ F T T' T'.V f (RingHom.id _) fK (RingHom.id _) hB inferInstance hf
    Function.injective_id hl inferInstance hK (fun _ => rfl) (by rw [hid, Category.id_comp, hy]) T'.ϖ m 1 T'.irr hm
    (by rw [pow_one]; rfl)
  have hon := hφ T.D.toPre.X (finrank_le hn hζ T)
  have hc : toReal T.β ∈ psdCone (bar := (id : ℤ → ℤ)) (X := T.D.toPre.X) :=
    GlobalTheory.PolFan.TameZ.toReal_mem_psdCone_int (mem_balForms_int.2 T.symm) fun x => by simpa using T.mono.nonneg 0 x
  rw [← evalR_toReal φ T.β, ← hon.homog _ hc m m.cast_nonneg,
    ← evalZ_pull φ (r := e.toIntLinearEquiv.toLinearMap) e.surjective, ← evalR_toReal]
  congr 1
  refine LinearMap.ext₂ fun a b => ?_
  have h := he a b
  rw [Nat.cast_one, one_mul] at h
  simp only [toReal_apply, pull_apply, LinearMap.smul_apply, smul_eq_mul]
  exact_mod_cast h.symm

end GlobalTheory.Poinc.TraitRam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealDescentThetaModelToComponentTraitOrders
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.PoincDown

theorem exists_assoc_pow {V V' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing V'] [IsDomain V']
    [IsDiscreteValuationRing V'] (f : V →+* V') (hf : Function.Injective f) [IsLocalHom f] {ϖ : V} (hϖ : Irreducible ϖ)
    {ϖ' : V'} (hϖ' : Irreducible ϖ') : ∃ m : ℕ, 1 ≤ m ∧ Associated (f ϖ) (ϖ' ^ m) := by
  have h0 : f ϖ ≠ 0 := fun h => hϖ.ne_zero (hf (by rw [h, map_zero]))
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible h0 hϖ'
  refine ⟨m, Nat.one_le_iff_ne_zero.2 fun e => ?_, hm⟩
  subst e
  rw [pow_zero] at hm
  exact hϖ.not_isUnit ((isUnit_map_iff f ϖ).1 (associated_one_iff_isUnit.1 hm))

theorem map_eq_span_pow {V V' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing V'] [IsDomain V']
    [IsDiscreteValuationRing V'] (f : V →+* V') {ϖ : V} (hϖ : Irreducible ϖ) {ϖ' : V'} (hϖ' : Irreducible ϖ') {m : ℕ}
    (hm : Associated (f ϖ) (ϖ' ^ m)) {I : Ideal V} {b : ℕ} (h : I.map f = Ideal.span {ϖ' ^ b}) :
    ∃ a : ℕ, b = m * a ∧ I = Ideal.span {ϖ ^ a} := by
  have hI : I ≠ ⊥ := by
    rintro rfl
    rw [Ideal.map_bot, eq_comm, Ideal.span_singleton_eq_bot] at h
    exact pow_ne_zero _ hϖ'.ne_zero h
  obtain ⟨a, rfl⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI hϖ
  refine ⟨a, ?_, rfl⟩
  rw [Ideal.map_span, Set.image_singleton, map_pow, Ideal.span_singleton_eq_span_singleton] at h
  have h2 : Associated (ϖ' ^ (m * a)) (ϖ' ^ b) := by
    rw [pow_mul]; exact (hm.pow_pow (n := a)).symm.trans h
  have e1 := (pow_dvd_pow_iff hϖ'.ne_zero hϖ'.not_isUnit).1 h2.dvd
  have e2 := (pow_dvd_pow_iff hϖ'.ne_zero hϖ'.not_isUnit).1 h2.symm.dvd
  omega

theorem idealDescent : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z), IsThetaCompact F z i → ∀ φ : InvFun ℤ, IsPolFan id g φ → ∀ W : Set Z, IsClopen W → IsIrreducible W → ∀ (W8 : Matrix (Fin 8) (Fin 8) ℤ) (X₁ : Setup F W8 i) (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι → Set.range X₁.π = W → (∀ x ∈ J₁.support, X₁.π x ∉ Set.range i) → (∀ (T : Trait F) (ξ₁ : Sp T.V ⟶ X₁.M.Z), jK T.V ≫ ξ₁ ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong J₁ ξ₁ = Ideal.span {T.ϖ ^ a}) → ∃ (d : ℕ) (J : Z.IdealSheafData), 1 ≤ d ∧ (∀ x ∈ J.support, x ∈ W ∧ x ∉ Set.range i) ∧ ∀ (T : Trait F) (ξ : Sp T.V ⟶ Z), jK T.V ≫ ξ = T.y ≫ i → ξ (closedPoint T.V) ∈ W → ∃ a : ℕ, (a : ℝ) = d * φ.evalZ T.β ∧ idlAlong J ξ = Ideal.span {T.ϖ ^ a} := by
  intro g n hg hn hodd F Z z i hZ φ hφ W hWc hWi W8 X₁ ι J₁ hι hπ hsupp hord
  obtain ⟨k, J, hk, hJs, hJo⟩ := GlobalTheory.T.norm_descent_ideal_thetaModel_to_clopen_component g n hg hn hodd F Z z i hZ φ hφ W hWc hWi W8 X₁ ι J₁ hι hπ hsupp hord
  refine ⟨k * ι, J, Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), hJs, ?_⟩
  intro T ξ hξ hW
  have hc : IsClopen (Set.range X₁.π) := by rw [hπ]; exact hWc
  obtain ⟨T', f, fK, ξ₁, hf, hfl, hfK, hy, hsq, hgen⟩ := GlobalTheory.T.exists_trait_lift_thetaSetup_model_after_extension g n F Z i W8 X₁ hc T ξ hξ (by rw [hπ]; exact hW)
  obtain ⟨a₁, ha₁, hJ₁⟩ := hord T' ξ₁ hgen
  have hJ := hJo T' ξ₁ hgen
  obtain ⟨m, hm1, hm⟩ := exists_assoc_pow f hf T.irr T'.irr
  have hφ' := GlobalTheory.Poinc.TraitRam.evalZ_eq_mul g n _ _ (by omega) (cycBase (show n ≠ 0 by omega)).ζ.isUnit F T T' f fK hf hfl hfK hy m hm φ hφ
  have e1 : (idlAlong J ξ).map f = Ideal.span {T'.ϖ ^ (a₁ * k)} := by
    rw [← GlobalTheory.TraitOrder.idlAlong_comp, hsq, hJ, hJ₁, Ideal.span_singleton_pow, ← pow_mul]
  obtain ⟨a, hb, ha⟩ := map_eq_span_pow f T.irr T'.irr hm e1
  refine ⟨a, ?_, ha⟩
  have hb' : ((a₁ : ℝ) * k) = m * a := by exact_mod_cast hb
  rw [ha₁, hφ'] at hb'
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  push_cast
  apply mul_left_cancel₀ hm0.ne'
  linarith [hb']

end GlobalTheory.PoincDown
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealDescentThetaModelToComponentTraitOrdersStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idealDescent_thetaModel_to_component_traitOrders : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z), IsThetaCompact F z i → ∀ φ : InvFun ℤ, IsPolFan id g φ → ∀ W : Set Z, IsClopen W → IsIrreducible W → ∀ (W8 : Matrix (Fin 8) (Fin 8) ℤ) (X₁ : Setup F W8 i) (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι → Set.range X₁.π = W → (∀ x ∈ J₁.support, X₁.π x ∉ Set.range i) → (∀ (T : Trait F) (ξ₁ : Sp T.V ⟶ X₁.M.Z), jK T.V ≫ ξ₁ ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong J₁ ξ₁ = Ideal.span {T.ϖ ^ a}) → ∃ (d : ℕ) (J : Z.IdealSheafData), 1 ≤ d ∧ (∀ x ∈ J.support, x ∈ W ∧ x ∉ Set.range i) ∧ ∀ (T : Trait F) (ξ : Sp T.V ⟶ Z), jK T.V ≫ ξ = T.y ≫ i → ξ (closedPoint T.V) ∈ W → ∃ a : ℕ, (a : ℝ) = d * φ.evalZ T.β ∧ idlAlong J ξ = Ideal.span {T.ϖ ^ a} := by
  first | exact @GlobalTheory.PoincDown.idealDescent | exact GlobalTheory.PoincDown.idealDescent | (intros; apply GlobalTheory.PoincDown.idealDescent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFanOrderIdealThetaCompactification
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem idealSt_holds : IdealSt := by
  intro g hg n hn hodd F Z z i hθ φ hφ
  obtain ⟨ι, _, W, hclo, hirr, hpart⟩ := GlobalTheory.T.exists_clopen_irreducible_partition_of_normal_proj n Z z hθ.1 hθ.2.1
  have key : ∀ c, ∃ (d : ℕ) (J : Z.IdealSheafData), 1 ≤ d ∧ (∀ x ∈ J.support, x ∈ W c ∧ x ∉ Set.range i) ∧
      ∀ (T : Trait F) (ξ : Sp T.V ⟶ Z), jK T.V ≫ ξ = T.y ≫ i → ξ (closedPoint T.V) ∈ W c →
        ∃ a : ℕ, (a : ℝ) = d * φ.evalZ T.β ∧ idlAlong J ξ = Ideal.span {T.ϖ ^ a} := by
    intro c
    obtain ⟨W8, X₁, ι₁, J₁, h1, h2, h4, h5⟩ :=
      GlobalTheory.T.exists_thetaSetup_ideal_over_clopen_component g n hg hn hodd F Z z i hθ φ hφ (W c) (hclo c) (hirr c)
    exact GlobalTheory.T.idealDescent_thetaModel_to_component_traitOrders g n hg hn hodd F Z z i hθ φ hφ (W c) (hclo c) (hirr c) W8 X₁ ι₁ J₁ h1 h2 h4 h5
  choose d J hd hJ hv using key
  exact GlobalTheory.T.exists_fanOrder_ideal_glued_clopen_pieces F i φ W J d hclo hpart hd hJ hv

end GlobalTheory.Poinc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFanOrderIdealThetaCompactificationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fanOrder_ideal_thetaCompactification : IdealSt := by
  first | exact @GlobalTheory.Poinc.idealSt_holds | exact GlobalTheory.Poinc.idealSt_holds | (intros; apply GlobalTheory.Poinc.idealSt_holds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedBlowupAmpleDivisorCompactification
noncomputable section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

namespace GlobalTheory.PoincTop

theorem poinSt : PoinSt := by
  intro g hg n hn hodd F Z z i hth OZ hOZ hamp φ hφ
  obtain ⟨hproj, hnorm, hoi, hiz, hdense, W8, hW8, hthi⟩ := hth
  obtain ⟨d, J, hd, hJ, hval⟩ :=
    GlobalTheory.T.exists_fanOrder_ideal_thetaCompactification g hg n hn hodd F Z z i ⟨hproj, hnorm, hoi, hiz, hdense, W8, hW8, hthi⟩ φ hφ
  haveI := hoi
  let W : Z.Opens := i.opensRange
  have hWset : (W : Set Z) = Set.range i := by simp [W]
  obtain ⟨S, π, BD, hbl, hpS, hBD, hiso, hdS⟩ :=
    GlobalTheory.T.exists_normalised_blowup_cyclotomicAway_projective n Z z hproj (GlobalTheory.IsNormalScheme.pred Z) J W (by rw [hWset]; exact hdense)
      (fun x hx hxW => hJ x hx (by have h : x ∈ (W : Set Z) := hxW; rwa [hWset] at h))
  haveI := hiso
  let A : F.X ⟶ (π ⁻¹ᵁ W).toScheme := i.isoOpensRange.hom ≫ inv (π ∣_ W)
  let j : F.X ⟶ S := A ≫ (π ⁻¹ᵁ W).ι
  have hjπ : j ≫ π = i := by
    simp only [j, A, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
    simp [W]
  have hrj : Set.range j = π ⁻¹' Set.range i := by
    have hA : Function.Surjective A := A.surjective
    change Set.range ((π ⁻¹ᵁ W).ι ∘ A) = _
    rw [Set.range_comp, hA.range_eq, Set.image_univ, Scheme.Opens.range_ι, ← hWset]
    rfl
  refine ⟨d, J, S, π, j, BD, hd, hJ, hval, hbl, hpS, inferInstance, ?_, hjπ, hrj.symm, hBD, ?_, ?_⟩
  · rw [hrj, ← hWset]; exact hdS
  · intro T ξ hξ
    obtain ⟨a, ha, hid⟩ := hval T (ξ ≫ π) (by rw [← Category.assoc, hξ, Category.assoc, hjπ])
    refine ⟨a, ha, ?_⟩
    rw [hBD, GlobalTheory.PullAlong.idlAlong_comap_eq]
    exact hid
  · obtain ⟨S₀, π₀, ν, U, hb, hνπ, hfin, -⟩ := hbl.2
    haveI : Algebra.FiniteType ℤ (cycAway n) := finiteType_cycAway n
    haveI : IsNoetherianRing (cycAway n) := Algebra.FiniteType.isNoetherianRing ℤ _
    obtain ⟨T₀, hT⟩ := GlobalTheory.T.ample_twist_normalisedBlowup_noetherian_domain (cycAway n) Z S₀ S z J π₀ ν BD hproj hb hfin
      (by rw [hνπ]; exact hBD) OZ hamp
    refine ⟨T₀, fun k hk => ?_⟩
    have h := hT k hk
    rwa [hνπ] at h

end GlobalTheory.PoincTop
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedBlowupAmpleDivisorCompactificationStatement
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedBlowup_ampleDivisor_compactification : PoinSt := by
  first | exact @GlobalTheory.PoincTop.poinSt | exact GlobalTheory.PoincTop.poinSt | (intros; apply GlobalTheory.PoincTop.poinSt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescSt5
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescSt
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc GlobalTheory.SiegJoin

namespace GlobalTheory.SiegDescent

theorem exists_chart {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {F : SFam g n ζ} {S : Scheme.{0}} {s : S ⟶ Sp o}
    {j : F.X ⟶ S} [IsOpenImmersion j] {φ : InvFun ℤ} {BD : EffCartierData S} {d : ℕ} {x : S}
    (h : GlobalTheory.PolDeg.PreChart F s j φ BD d x) :
    ∃ C : Chart j F.univ.A x, ∀ p : Sp C.R, p ∈ abLocus C.G ↔ C.ξ p ∈ Set.range j := by
  obtain ⟨R, _, _, _, b, ξ, m, t, Q, δ, a, G₁, _, y, α₁, ⟨hc, h0, -, hx, het, hun⟩, ⟨-, -, hr⟩, ⟨hs, hab, hy, hgen⟩, -⟩ := h
  exact ⟨{ R := R, complete := hc, charZero := h0, ξ := ξ, centre := hx, etc := het, unr := hun, G := G₁, semi := hs,
           y := y, hy := hy, α := α₁, gen := hgen }, fun p => (hab p).trans (hr p).symm⟩

end GlobalTheory.SiegDescent
end
end

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc GlobalTheory.SiegJoin

namespace GlobalTheory.SiegDescent

theorem descSt5 : GlobalTheory.SiegJoin.DescSt5 := by
  intro g _ φ n hn _ F Z z i d S π j _ BD hB hC
  obtain ⟨J, -, -, -, ⟨hN, -⟩, hP, hD, -⟩ := hB
  have hn0 : n ≠ 0 := by omega
  haveI : IsDedekindDomain (cycAway n) := (arBase_cycAway n hn0).1
  haveI : IsProper (π ≫ z) := GlobalTheory.SchemeWords.isProper_of_isProjOver hP
  haveI : IsNoetherianRing (CommRingCat.of (cycAway n)) := inferInstanceAs (IsNoetherianRing (cycAway n))
  haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (π ≫ z)
  haveI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace (π ≫ z)
  haveI : AlgebraicGeometry.IsNoetherian S := {}
  have hj : IsDominant j := ⟨hD⟩
  have hd : SmoothOfRelativeDimension g F.univ.A.hom :=
    GlobalTheory.SiegSharpCover.smoothDim F.univ (by omega) (cycBase hn0).ζ.isUnit (isUnit_natCast hn0)
  obtain ⟨G, _, e, hG, he, hπ⟩ := GlobalTheory.T.semiAbelian_descent_from_complete_regular_charts F.X S ((GlobalTheory.isNormalScheme_iff_pred S).1 hN) j hj F.univ.A F.univ.ab F.univ.diag (pull_isLB F.univ.isLB _)
    F.princ.1 fun x => ⟨(exists_chart (hC x)).choose⟩
  obtain ⟨h₁, h₂⟩ := GlobalTheory.T.descended_group_abelianLocus_and_relDim F.X S j hj F.univ.A G e g F.univ.ab hd hG he fun x => by
    obtain ⟨C, hab⟩ := exists_chart (hC x)
    obtain ⟨p, hp, -⟩ := hπ x C
    exact ⟨C.R, inferInstance, inferInstance, C.ξ, C.G, inferInstance, p, C.centre, hp, hab⟩
  exact ⟨G, inferInstance, e, hG, h₂, he, h₁⟩

end GlobalTheory.SiegDescent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelToroidalPolChartsOfSteps5
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGloballyGeneratedAmplePowerToroidalPullbac
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGloballyGeneratedAmplePowerToroidalPullbac
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PullPowGen

theorem exists_isGenerated_and_isAmpleLB : ∀ (o : Type) [CommRing o] [IsNoetherianRing o] (Z S : Scheme.{0}) (z : Z ⟶ Sp o) (π : S ⟶ Z) (OZ : LB Z) (W M : LB S) (a N : ℕ), IsProjOver z → OZ.IsLB → GlobalTheory.IsAmpleLB OZ → W.IsLB → M.IsLB → 1 ≤ a → 1 ≤ N → LBIso (lbPow W N) (lbPow (OZ.pull π) a) → (∃ k₀ : ℕ, ∀ k, k₀ ≤ k → GlobalTheory.IsAmpleLB (GlobalTheory.CechPic.tens (lbPow (OZ.pull π) k) M)) → ∃ N' : ℕ, 1 ≤ N' ∧ GlobalTheory.IsGenerated (lbPow W N') ∧ ∃ k : ℕ, GlobalTheory.IsAmpleLB (GlobalTheory.CechPic.tens (lbPow W (N' * k)) M) := by
  intro o _ _ Z S z π OZ W M a N _ hO hA hW hM ha hN H ⟨k₀, hk₀⟩
  obtain ⟨b, hb, hgen⟩ := hA.exists_isGenerated_pow
  have hP : (OZ.pull π).IsLB := LB.isLB_pull hO π
  have hcls : N • CechPic.cls W hW = a • CechPic.cls (OZ.pull π) hP := by
    have := (CechPic.cls_eq_iff (isLB_lbPow hW N) (isLB_lbPow hP a)).2 H
    rwa [CechPic.cls_lbPow hW, CechPic.cls_lbPow hP] at this
  refine ⟨N * b, Nat.mul_pos hN hb, ?_, k₀, ?_⟩
  · have hg := (hgen.pull π).pow a
    have hOb := isLB_lbPow hO b
    have hPb := LB.isLB_pull hOb π
    refine hg.of_lbIso (isLB_lbPow hW _) ((CechPic.cls_eq_iff (isLB_lbPow hW _) hg.isLB).1 ?_)
    have e : CechPic.cls ((lbPow OZ b).pull π) hPb = b • CechPic.cls (OZ.pull π) hP := by
      rw [CechPic.cls_pull hOb, CechPic.cls_pull hO, CechPic.cls_lbPow hO, map_nsmul]
    rw [CechPic.cls_lbPow hW, CechPic.cls_lbPow hPb, e, mul_nsmul, hcls, ← mul_nsmul, ← mul_nsmul, mul_comm]
  · have hamp := hk₀ (a * (b * k₀)) (Nat.le_mul_of_pos_left _ ha |>.trans' (Nat.le_mul_of_pos_left _ hb))
    have hT := CechPic.isLB_tens (isLB_lbPow hW (N * b * k₀)) hM
    refine hamp.of_lbIso hT ((CechPic.cls_eq_iff hT hamp.isLB).1 ?_)
    rw [CechPic.cls_tens (isLB_lbPow hW _) hM, CechPic.cls_tens (isLB_lbPow hP _) hM, CechPic.cls_lbPow hW,
      CechPic.cls_lbPow hP, Nat.mul_assoc, mul_nsmul, hcls, ← mul_nsmul]

end GlobalTheory.PullPowGen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGloballyGeneratedAmplePowerToroidalPullbacStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_globallyGenerated_ample_power_toroidalPullback : ∀ (o : Type) [CommRing o] [IsNoetherianRing o] (Z S : Scheme.{0}) (z : Z ⟶ Sp o) (π : S ⟶ Z) (OZ : LB Z) (W M : LB S) (a N : ℕ), IsProjOver z → OZ.IsLB → GlobalTheory.IsAmpleLB OZ → W.IsLB → M.IsLB → 1 ≤ a → 1 ≤ N → LBIso (lbPow W N) (lbPow (OZ.pull π) a) → (∃ k₀ : ℕ, ∀ k, k₀ ≤ k → GlobalTheory.IsAmpleLB (GlobalTheory.CechPic.tens (lbPow (OZ.pull π) k) M)) → ∃ N' : ℕ, 1 ≤ N' ∧ GlobalTheory.IsGenerated (lbPow W N') ∧ ∃ k : ℕ, GlobalTheory.IsAmpleLB (GlobalTheory.CechPic.tens (lbPow W (N' * k)) M) := by
  first | exact @GlobalTheory.PullPowGen.exists_isGenerated_and_isAmpleLB | exact GlobalTheory.PullPowGen.exists_isGenerated_and_isAmpleLB | (intros; apply GlobalTheory.PullPowGen.exists_isGenerated_and_isAmpleLB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPolarisedChartOfMonomialPreChartSemiAbelianEx
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPolarisedChartOfMonomialPreChartSemiAbelianEx
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg

theorem hasPolChart_of_preChart_of_extension : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {S : Scheme.{0}}
    (s : S ⟶ Sp o) (j : F.X ⟶ S) [IsOpenImmersion j] (G : Over S) [GrpObj G] (e : F.univ.A.left ⟶ G.left) (φ : InvFun ℤ)
    (BD : GlobalTheory.EffCartierData S) (d : ℕ) (x : S), n ≠ 0 → IsSemiAbelian G → SmoothOfRelativeDimension g G.hom →
    IsGrpPullback F.univ.A G j e → abLocus G = Set.range j → PreChart F s j φ BD d x → HasPolChart F s j e φ BD d x :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ hG _ he _ h => h.hasPolChart hG he

end GlobalTheory.PolDeg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPolarisedChartOfMonomialPreChartSemiAbelianExStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasPolarisedChart_of_monomialPreChart_semiAbelianExt : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {S : Scheme.{0}} (s : S ⟶ Sp o) (j : F.X ⟶ S) [IsOpenImmersion j] (G : Over S) [GrpObj G] (e : F.univ.A.left ⟶ G.left) (φ : InvFun ℤ) (BD : GlobalTheory.EffCartierData S) (d : ℕ) (x : S), n ≠ 0 → IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → IsGrpPullback F.univ.A G j e → abLocus G = Set.range j → PreChart F s j φ BD d x → HasPolChart F s j e φ BD d x := by
  first | exact @GlobalTheory.PolDeg.hasPolChart_of_preChart_of_extension | exact GlobalTheory.PolDeg.hasPolChart_of_preChart_of_extension | (intros; apply GlobalTheory.PolDeg.hasPolChart_of_preChart_of_extension <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemClosureModuliFibreOfMonomialPeriodPreChart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemClosureModuliFibreOfMonomialPeriodPreChart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FibreDense

theorem isPrime_map_of_flat {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (φ : A →+* R) (hf : φ.Flat) (hm : (maximalIdeal A).map φ = maximalIdeal R) (I : Ideal A)
    [IsRegularLocalRing (A ⧸ I)] : (I.map φ).IsPrime := by
  let _ := φ.toAlgebra
  have : Module.Flat A R := hf
  have hI : I ≤ maximalIdeal A := le_maximalIdeal (Ideal.Quotient.nontrivial_iff.1 inferInstance)
  have hJ : I.map (algebraMap A R) ≠ ⊤ := fun h =>
    (maximalIdeal.isMaximal R).ne_top (top_le_iff.1 (h.ge.trans ((Ideal.map_mono hI).trans hm.le)))
  have : Nontrivial (R ⧸ I.map (algebraMap A R)) := Ideal.Quotient.nontrivial_iff.2 hJ
  have : IsLocalRing (R ⧸ I.map (algebraMap A R)) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have : Module.Flat (A ⧸ I) (R ⧸ I.map (algebraMap A R)) :=
    Module.Flat.of_linearEquiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor R I).toLinearEquiv
  have hmap : (maximalIdeal (A ⧸ I)).map (algebraMap (A ⧸ I) (R ⧸ I.map (algebraMap A R))) = maximalIdeal _ := by
    rw [← map_maximalIdeal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective,
      ← map_maximalIdeal_of_surjective (Ideal.Quotient.mk (I.map (algebraMap A R))) Ideal.Quotient.mk_surjective,
      ← hm, Ideal.map_map, Ideal.map_map]
    rfl
  have : IsLocalHom (algebraMap (A ⧸ I) (R ⧸ I.map (algebraMap A R))) :=
    ((local_hom_tfae _).out 1 3).2 hmap.le
  have := GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.of_flat_of_map_maximalIdeal hmap
  have : IsDomain (R ⧸ I.map (algebraMap A R)) := GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.isDomain
  exact (Ideal.Quotient.isDomain_iff_prime _).1 this

theorem exists_toStalk (o : Type) [CommRing o] (x : Sp o) : ∃ τ : CommRingCat.of o ⟶ (Sp o).presheaf.stalk x,
    (Sp o).fromSpecStalk x = Spec.map τ ∧ x.asIdeal.map τ.hom = maximalIdeal ((Sp o).presheaf.stalk x) := by
  have := x.isPrime
  let _ : Algebra o ((Spec (CommRingCat.of o)).presheaf.stalk x) := (StructureSheaf.toStalk o x).hom.toAlgebra
  have : IsLocalization.AtPrime ((Spec (CommRingCat.of o)).presheaf.stalk x) x.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk o x
  exact ⟨StructureSheaf.toStalk o x, Spec.fromSpecStalk_eq' (CommRingCat.of o) x,
    IsLocalization.AtPrime.map_eq_maximalIdeal x.asIdeal ((Spec (CommRingCat.of o)).presheaf.stalk x)⟩

theorem isPrime_fibre {o : Type} [CommRing o] {S : Scheme.{0}} (s : S ⟶ Sp o) [Smooth s] {R : Type} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (b : o →+* R) (ξ : Sp R ⟶ S) (hb : ξ ≫ s = spMap b)
    (he : IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom) : (((maximalIdeal R).comap b).map b).IsPrime := by
  have hreg := GlobalTheory.FibreRegular.isRegularLocalRing_stalk_quot_maximalIdeal _ _ s (ξ (closedPoint R))
  have hp := isPrime_map_of_flat _ he.1 he.2.1
    ((maximalIdeal ((Sp o).presheaf.stalk (s (ξ (closedPoint R))))).map (s.stalkMap (ξ (closedPoint R))).hom)
  obtain ⟨τ, hτ, hmax⟩ := exists_toStalk o (s (ξ (closedPoint R)))
  have hc : τ ≫ s.stalkMap (ξ (closedPoint R)) ≫ Scheme.stalkClosedPointTo ξ = CommRingCat.ofHom b := by
    apply Spec.map_injective
    refine Eq.trans ?_ hb
    rw [Spec.map_comp, Spec.map_comp, Category.assoc, ← hτ, Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc]
    exact congrArg (· ≫ s) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of R) ξ)
  have hx : (s (ξ (closedPoint R))).asIdeal = (maximalIdeal R).comap b :=
    congrArg (fun f : Sp R ⟶ Sp o => (f (closedPoint R)).asIdeal) hb
  have hb' : (Scheme.stalkClosedPointTo ξ).hom.comp ((s.stalkMap (ξ (closedPoint R))).hom.comp τ.hom) = b :=
    congrArg (fun q => q.hom) hc
  rwa [← hmax, Ideal.map_map, Ideal.map_map, RingHom.comp_assoc, hb', hx] at hp

theorem mem_closure_fibre : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {S : Scheme.{0}} (s : S ⟶ Sp o) (j : F.X ⟶ S) [IsOpenImmersion j] (φ : InvFun ℤ) (BD : GlobalTheory.EffCartierData S) (d : ℕ) (x : S) [IsNoetherianRing o] [Smooth s], PreChart F s j φ BD d x → x ∈ closure (Set.range j ∩ s ⁻¹' {s x}) := by
  intro o _ ζ g n F S s j _ φ BD d x _ _ h
  obtain ⟨R, _, _, _, b, ξ, m, t, Q, δ, a, G₁, _, y, α₁, ⟨-, -, hb, rfl, he, -⟩, ⟨ht, -, hj⟩, -⟩ := h
  have hq := isPrime_fibre s b ξ hb he
  let q : Sp R := (⟨((maximalIdeal R).comap b).map b, hq⟩ : PrimeSpectrum R)
  have hs : ∀ p : Sp R, s (ξ p) = spMap b p := fun p => congrArg (fun f : Sp R ⟶ Sp o => f p) hb
  have h₁ : ξ q ∈ Set.range j := by
    refine (hj q).2 fun hmem => ?_
    obtain ⟨i, -, hi⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hq)).1 hmem
    have := ht.2 (Pi.single i 1) (Ideal.mem_sup_right (by simpa [Pi.single_apply] using hi)) i
    simp at this
  have h₂ : s (ξ q) = s (ξ (closedPoint R)) := by
    refine (hs q).trans (Eq.trans (PrimeSpectrum.ext (le_antisymm ?_ ?_)) (hs (closedPoint R)).symm)
    · exact Ideal.comap_mono (f := b) (Ideal.map_comap_le (f := b) (K := maximalIdeal R))
    · exact Ideal.le_comap_map (f := b) (I := (maximalIdeal R).comap b)
  have h₃ : ξ q ⤳ ξ (closedPoint R) := (specializes_closedPoint (R := R) q).map ξ.continuous
  exact closure_mono (Set.singleton_subset_iff.2 (Set.mem_inter h₁ h₂)) (specializes_iff_mem_closure.1 h₃)

end GlobalTheory.FibreDense
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemClosureModuliFibreOfMonomialPeriodPreChartStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_closure_moduliFibre_of_monomialPeriodPreChart : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {S : Scheme.{0}} (s : S ⟶ Sp o) (j : F.X ⟶ S) [IsOpenImmersion j] (φ : InvFun ℤ) (BD : GlobalTheory.EffCartierData S) (d : ℕ) (x : S) [IsNoetherianRing o] [Smooth s], PreChart F s j φ BD d x → x ∈ closure (Set.range j ∩ s ⁻¹' {s x}) := by
  first | exact @GlobalTheory.FibreDense.mem_closure_fibre | exact GlobalTheory.FibreDense.mem_closure_fibre | (intros; apply GlobalTheory.FibreDense.mem_closure_fibre <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

theorem GlobalTheory.SiegJoin.siegelToroidalPolCharts_of_steps5
    (hF : ∀ g n : ℕ, 1 ≤ g → 3 ≤ n → Odd n → Nonempty (SFam g n (zetaAway n))) (hMin : GlobalTheory.SiegJoin.MinSt5)
    (hPoin : GlobalTheory.Poinc.PoinSt) (hChart : GlobalTheory.SiegJoin.ChartSt5) (hDesc : GlobalTheory.SiegJoin.DescSt5) :
    GlobalTheory.Published.SiegelToroidalPolCharts := by
  intro g hg φ hφ hφ' n hn ho
  have hn0 : n ≠ 0 := by omega
  haveI : IsNoetherianRing (cycAway n) := by haveI := (GlobalTheory.SiegelTor.arBase_cycAway n hn0).1; infer_instance
  obtain ⟨F⟩ := hF g n hg hn ho
  obtain ⟨Z, z, i, OZ, hMA⟩ := hMin g hg n hn ho F
  have hMA' := hMA
  obtain ⟨o', _, β, S', s', U, c, π', G', _, e', _, N', ⟨hTh, hZp, hZn, hiz, hid, hOZ, hOZa⟩, -⟩ := hMA'
  obtain ⟨d, J, S, π, j, BD, hd, hJ, hV, hBl, hP, hj, hjd, hji, hjpre, hBD, hVj, k₀, hk₀⟩ :=
    hPoin g hg n hn ho F Z z i hTh OZ hOZ hOZa φ hφ
  haveI := hj
  have hBlow : BlowAt F z i φ d π j BD := ⟨J, hd, hJ, hV, hBl, hP, hjd, hji, hjpre, hBD, hVj⟩
  obtain ⟨hsm, hpre⟩ := hChart g hg φ hφ hφ' n hn ho F Z z i OZ d S π j BD hMA hBlow
  obtain ⟨G, _, e, hGs, hGd, hGe, hGab⟩ :=
    hDesc g hg φ n hn ho F Z z i d S π j BD hBlow hpre
  haveI := hsm
  haveI : Smooth (π ≫ z) := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) _
  haveI : QuasiSeparated G.hom := by haveI := hGs.separated; infer_instance
  obtain ⟨a, N, ha, hN, hiso⟩ := GlobalTheory.T.hodgeBundle_power_iso_minimalSiegelCompactification g n F Z z i OZ S π j G e hMA
    (fun x => ⟨hBl.1.isDomain_stalk x, hBl.1.isIntegrallyClosed_stalk x⟩) hP hjd hji hGs hGd hGe
  obtain ⟨N'', hN'', hgen, k, hk⟩ := GlobalTheory.T.exists_globallyGenerated_ample_power_toroidalPullback (cycAway n) Z S z π OZ (hodge G g) (GlobalTheory.CechPic.dual BD.lb) a N
    hZp hOZ hOZa (isLB_hodge G g) (GlobalTheory.CechPic.isLB_dual BD.isLB_lb) ha hN hiso ⟨k₀, hk₀⟩
  refine ⟨F, S, π ≫ z, j, hj, G, inferInstance, e, BD, d, N'', hP, hsm, by rw [← Category.assoc, hji, hiz], ?_,
    hGs, hGd, hGe, hGab, hd, ?_, hN'', hgen, k, hk⟩
  · intro x
    exact GlobalTheory.T.mem_closure_moduliFibre_of_monomialPeriodPreChart F (π ≫ z) j φ BD d x (hpre x)
  · intro x
    exact GlobalTheory.T.hasPolarisedChart_of_monomialPreChart_semiAbelianExt F (π ≫ z) j G e φ BD d x hn0 hGs hGd hGe hGab (hpre x)

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelToroidalCompactificationPolarisedCharts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.SiegJoin.siegelToroidalPolCharts : GlobalTheory.Published.SiegelToroidalPolCharts :=
  GlobalTheory.SiegJoin.siegelToroidalPolCharts_of_steps5 GlobalTheory.T.exists_siegelFamily_cyclotomicAway_odd_level GlobalTheory.T.minimalSiegelCompactification_exists GlobalTheory.T.normalisedBlowup_ampleDivisor_compactification
    GlobalTheory.T.minimalBlowup_smooth_with_semiAbelianCharts GlobalTheory.SiegDescent.descSt5
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelToroidalCompactificationPolarisedChartsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelToroidalCompactification_polarisedCharts : GlobalTheory.Published.SiegelToroidalPolCharts := by
  first | exact @GlobalTheory.SiegJoin.siegelToroidalPolCharts | exact GlobalTheory.SiegJoin.siegelToroidalPolCharts | (intros; apply GlobalTheory.SiegJoin.siegelToroidalPolCharts <;> assumption)
end

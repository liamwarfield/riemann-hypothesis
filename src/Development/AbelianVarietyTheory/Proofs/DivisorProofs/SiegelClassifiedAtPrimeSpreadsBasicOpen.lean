module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitIntCastStalkIff

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAwaySpreadPointLocalizationAtPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAwaySpreadPointLocalizationAtPrime
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.SpreadPoint

set_option backward.isDefEq.respectTransparency false

theorem isStalkMap_atPrime (R : Type) [CommRing R] (𝔭 : Ideal R) [𝔭.IsPrime] :
    GlobalTheory.UPoinc.LocSpread.IsStalkMap (algebraMap R (Localization.AtPrime 𝔭)) := by
  let x : PrimeSpectrum R := ⟨𝔭, inferInstance⟩
  let T := (Spec.structureSheaf R).presheaf.stalk x
  haveI : IsLocalization x.asIdeal.primeCompl T := StructureSheaf.IsLocalization.to_stalk R x
  let e : T ≃ₐ[R] Localization.AtPrime 𝔭 := IsLocalization.algEquiv x.asIdeal.primeCompl T _
  refine ⟨x, asIso (Spec.map (e.toRingEquiv.toCommRingCatIso).hom), ?_, fun a ha =>
    IsLocalization.map_units (Localization.AtPrime 𝔭) (⟨a, ha⟩ : 𝔭.primeCompl)⟩
  rw [Spec.fromSpecStalk_eq', asIso_hom, ← Spec.map_comp]
  congr 1
  ext a
  exact e.commutes a

end GlobalTheory.SpreadPoint

theorem GlobalTheory.SpreadPoint.exists_away : ∀ (B : Type) [CommRing B] (X : Scheme.{0}) (q : X ⟶ Sp B) [LocallyOfFinitePresentation q] (R : Type) [CommRing R] (β : B →+* R) (𝔭 : Ideal R) [𝔭.IsPrime] (f₀ : Sp (Localization.AtPrime 𝔭) ⟶ X), f₀ ≫ q = spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β) → ∃ r ∉ 𝔭, ∃ (j : Localization.Away r →+* Localization.AtPrime 𝔭) (f : Sp (Localization.Away r) ⟶ X), j.comp (algebraMap R (Localization.Away r)) = algebraMap R (Localization.AtPrime 𝔭) ∧ f ≫ q = spMap ((algebraMap R (Localization.Away r)).comp β) ∧ spMap j ≫ f = f₀ := by
  intro B _ X q _ R _ β 𝔭 _ f₀ hf₀
  set σ := algebraMap R (Localization.AtPrime 𝔭)
  have hσ := GlobalTheory.SpreadPoint.isStalkMap_atPrime R 𝔭
  let q' : pullback q (spMap β) ⟶ Sp R := pullback.snd q (spMap β)
  have hP : IsPullback (spMap σ) (𝟙 _) (𝟙 (Sp R)) (spMap σ) :=
    IsPullback.of_vert_isIso ⟨by simp⟩
  have hcomp : ∀ {A C D : Type} [CommRing A] [CommRing C] [CommRing D] (f : A →+* C) (g : C →+* D),
      spMap g ≫ spMap f = spMap (g.comp f) := fun f g => (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm
  let u₀ : Sp (Localization.AtPrime 𝔭) ⟶ pullback q (spMap β) :=
    pullback.lift f₀ (spMap σ) (by rw [hf₀, hcomp])
  obtain ⟨a, ha, H⟩ := GlobalTheory.UPoinc.LocSpread.exists_hom hσ (𝟙 (Sp R)) q' hP u₀ (by simp [u₀, q'])
  have ha' : a ∉ 𝔭 := by
    intro h
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime 𝔭) 𝔭 a).1 ha h
  let g := algebraMap R (Localization.Away a)
  obtain ⟨u, hu, hu₀⟩ := H (Localization.Away a) g (IsLocalization.Away.algebraMap_isUnit a) (Sp (Localization.Away a))
    (spMap g) (𝟙 _) (by simp)
  let j : Localization.Away a →+* Localization.AtPrime 𝔭 := IsLocalization.Away.lift a ha
  have hj : j.comp g = σ := IsLocalization.Away.lift_comp _ _
  refine ⟨a, ha', j, u ≫ pullback.fst q (spMap β), hj, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (u ≫ q') ≫ _ = _
    rw [hu, Category.comp_id, hcomp]
  · rw [← Category.assoc, hu₀ (spMap j) (by rw [hcomp, hj])]
    exact pullback.lift_fst _ _ _
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAwaySpreadPointLocalizationAtPrimeStatement
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_away_spread_point_localization_atPrime : ∀ (B : Type) [CommRing B] (X : Scheme.{0}) (q : X ⟶ Sp B) [LocallyOfFinitePresentation q] (R : Type) [CommRing R] (β : B →+* R) (𝔭 : Ideal R) [𝔭.IsPrime] (f₀ : Sp (Localization.AtPrime 𝔭) ⟶ X), f₀ ≫ q = spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β) → ∃ r ∉ 𝔭, ∃ (j : Localization.Away r →+* Localization.AtPrime 𝔭) (f : Sp (Localization.Away r) ⟶ X), j.comp (algebraMap R (Localization.Away r)) = algebraMap R (Localization.AtPrime 𝔭) ∧ f ≫ q = spMap ((algebraMap R (Localization.Away r)).comp β) ∧ spMap j ≫ f = f₀ := by
  first | exact @GlobalTheory.SpreadPoint.exists_away | exact GlobalTheory.SpreadPoint.exists_away | (intros; apply GlobalTheory.SpreadPoint.exists_away <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpreadOfPullbacks
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPullbackSpreadsToIntermediateSubring
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoSpread
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoSpread
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegBundleSpread

theorem lbIso_spread : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Type) [CommRing S] (R₀ : Subring S) (s₀ : Sp R₀ ⟶ Sp B) (d₀ : SiegPre g n ζ s₀) (Y : Scheme.{0}) (sY : Y ⟶ Sp B) (u : SiegPre g n ζ sY) (h₀ : Sp R₀ ⟶ Y) (ψ : d₀.A.left ⟶ u.A.left) (sE : Sp S ⟶ Sp B) (e : SiegPre g n ζ sE) (j : e.A.left ⟶ d₀.A.left), IsPullback ψ d₀.A.hom u.A.hom h₀ → ∀ (j₂ : (G2 e.A).left ⟶ (G2 d₀.A).left) (φ₂ : (G2 e.A).left ⟶ (G2 u.A).left), IsPullback j e.A.hom d₀.A.hom (spMap R₀.subtype) → IsSquare j j₂ → LBIso e.P (d₀.P.pull j₂) → IsSquare (j ≫ ψ) φ₂ → LBIso e.P (u.P.pull φ₂) → ∃ F : Finset S, ∀ (R₁ : Subring S) (hle : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (s₁ : Sp R₁ ⟶ Sp B) (d₁ : SiegPre g n ζ s₁) (φ₁ : d₁.A.left ⟶ d₀.A.left) (φ₁₂ : (G2 d₁.A).left ⟶ (G2 d₀.A).left) (χ₂ : (G2 d₁.A).left ⟶ (G2 u.A).left), IsPullback φ₁ d₁.A.hom d₀.A.hom (spMap (Subring.inclusion hle)) → IsSquare φ₁ φ₁₂ → LBIso d₁.P (d₀.P.pull φ₁₂) → IsSquare (φ₁ ≫ ψ) χ₂ → LBIso d₁.P (u.P.pull χ₂) := by
  intro g n B _ ζ S _ R₀ s₀ d₀ Y sY u h₀ ψ sE e j hψ j₂ φ₂ hj hj₂ hej hφ₂ heφ
  obtain ⟨ψ₂, hψ₂⟩ := GlobalTheory.SiegDesc.exists_isSquare hψ.w
  have hcomp : j₂ ≫ ψ₂ = φ₂ := GlobalTheory.SiegDesc.isSquare_comp rfl hj₂ hψ₂ hφ₂
  have hpb : IsPullback j₂ (G2 e.A).hom (G2 d₀.A).hom (spMap R₀.subtype) :=
    GlobalTheory.SiegDesc.isPullback_of_isSquare hj hj₂
  haveI : IsProper d₀.A.hom := d₀.ab.proper
  haveI : IsProper (G2 d₀.A).hom := by
    change IsProper (pullback.fst d₀.A.hom d₀.A.hom ≫ d₀.A.hom)
    infer_instance
  have hN : (u.P.pull ψ₂).IsLB := pull_isLB u.isLB ψ₂
  have H : LBIso (d₀.P.pull j₂) ((u.P.pull ψ₂).pull j₂) := by
    have a : LBIso (d₀.P.pull j₂) (u.P.pull φ₂) :=
      LBIso.trans (pull_isLB d₀.isLB _) e.isLB (pull_isLB u.isLB _) (LBIso.symm hej) heφ
    have b : LBIso (u.P.pull φ₂) ((u.P.pull ψ₂).pull j₂) := by
      rw [← hcomp]
      exact LBIso.symm (GlobalTheory.SiegelPullComp.iso_pull_pull u.isLB ψ₂ j₂)
    exact LBIso.trans (pull_isLB d₀.isLB _) (pull_isLB u.isLB _) (pull_isLB hN _) a b
  obtain ⟨F, hF⟩ := GlobalTheory.lbIso_descends_to_subring_containing_finset S R₀ (G2 e.A).left (G2 d₀.A).left
    (G2 e.A).hom (G2 d₀.A).hom j₂ d₀.P (u.P.pull ψ₂) hpb d₀.isLB hN H
  refine ⟨F, fun R₁ hle hFR s₁ d₁ φ₁ φ₁₂ χ₂ hφ₁ hφ₁₂ hd₁ hχ₂ => ?_⟩
  have hcomp₁ : φ₁₂ ≫ ψ₂ = χ₂ := GlobalTheory.SiegDesc.isSquare_comp rfl hφ₁₂ hψ₂ hχ₂
  have H₁ := hF R₁ hle hFR (G2 d₁.A).left (G2 d₁.A).hom φ₁₂
    (GlobalTheory.SiegDesc.isPullback_of_isSquare hφ₁ hφ₁₂)
  have c : LBIso ((u.P.pull ψ₂).pull φ₁₂) (u.P.pull χ₂) := by
    rw [← hcomp₁]
    exact GlobalTheory.SiegelPullComp.iso_pull_pull u.isLB ψ₂ φ₁₂
  exact LBIso.trans d₁.isLB (pull_isLB hN _) (pull_isLB u.isLB _)
    (LBIso.trans d₁.isLB (pull_isLB d₀.isLB _) (pull_isLB hN _) hd₁ H₁) c

end GlobalTheory.SiegBundleSpread
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoSpreadStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lbIso_spread_alt : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Type) [CommRing S] (R₀ : Subring S) (s₀ : Sp R₀ ⟶ Sp B) (d₀ : SiegPre g n ζ s₀) (Y : Scheme.{0}) (sY : Y ⟶ Sp B) (u : SiegPre g n ζ sY) (h₀ : Sp R₀ ⟶ Y) (ψ : d₀.A.left ⟶ u.A.left) (sE : Sp S ⟶ Sp B) (e : SiegPre g n ζ sE) (j : e.A.left ⟶ d₀.A.left), IsPullback ψ d₀.A.hom u.A.hom h₀ → ∀ (j₂ : (G2 e.A).left ⟶ (G2 d₀.A).left) (φ₂ : (G2 e.A).left ⟶ (G2 u.A).left), IsPullback j e.A.hom d₀.A.hom (spMap R₀.subtype) → IsSquare j j₂ → LBIso e.P (d₀.P.pull j₂) → IsSquare (j ≫ ψ) φ₂ → LBIso e.P (u.P.pull φ₂) → ∃ F : Finset S, ∀ (R₁ : Subring S) (hle : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (s₁ : Sp R₁ ⟶ Sp B) (d₁ : SiegPre g n ζ s₁) (φ₁ : d₁.A.left ⟶ d₀.A.left) (φ₁₂ : (G2 d₁.A).left ⟶ (G2 d₀.A).left) (χ₂ : (G2 d₁.A).left ⟶ (G2 u.A).left), IsPullback φ₁ d₁.A.hom d₀.A.hom (spMap (Subring.inclusion hle)) → IsSquare φ₁ φ₁₂ → LBIso d₁.P (d₀.P.pull φ₁₂) → IsSquare (φ₁ ≫ ψ) χ₂ → LBIso d₁.P (u.P.pull χ₂) := by
  first | exact @GlobalTheory.SiegBundleSpread.lbIso_spread | exact GlobalTheory.SiegBundleSpread.lbIso_spread | (intros; apply GlobalTheory.SiegBundleSpread.lbIso_spread <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackCompSpreadToSubring
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackCompSpreadToSubring
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GrpMulSpread

attribute [local instance] Over.cartesianMonoidalCategory

theorem isPullback_pullbackMap {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} {f : S' ⟶ S}
    {F : G'.left ⟶ G.left} (cart : IsPullback F G'.hom G.hom f) :
    IsPullback (pullback.map G'.hom G'.hom G.hom G.hom F F f cart.w.symm cart.w.symm)
      (G' ⊗ G').hom (G ⊗ G).hom f := by
  have p : IsPullback (pullback.snd G.hom G.hom) (pullback.fst G.hom G.hom) G.hom G.hom :=
    (IsPullback.of_hasPullback G.hom G.hom).flip
  have p' : IsPullback (pullback.snd G'.hom G'.hom) (pullback.fst G'.hom G'.hom) G'.hom G'.hom :=
    (IsPullback.of_hasPullback G'.hom G'.hom).flip
  have c₁ : pullback.map G'.hom G'.hom G.hom G.hom F F f cart.w.symm cart.w.symm ≫ pullback.fst G.hom G.hom =
      pullback.fst G'.hom G'.hom ≫ F := pullback.lift_fst _ _ _
  have c₂ : pullback.map G'.hom G'.hom G.hom G.hom F F f cart.w.symm cart.w.symm ≫ pullback.snd G.hom G.hom =
      pullback.snd G'.hom G'.hom ≫ F := pullback.lift_snd _ _ _
  have q : IsPullback (pullback.map G'.hom G'.hom G.hom G.hom F F f cart.w.symm cart.w.symm ≫
      pullback.snd G.hom G.hom) (pullback.fst G'.hom G'.hom) G.hom (F ≫ G.hom) := by
    rw [c₂, cart.w]
    exact p'.paste_horiz cart
  exact (IsPullback.of_right q c₁ p).paste_vert cart

theorem pullbackMap_comp {S₁ S₀ Y : Scheme.{0}} {A₁ : Over S₁} {D : Over S₀} {U : Over Y} {k : S₁ ⟶ S₀}
    {h₀ : S₀ ⟶ Y} {φ : A₁.left ⟶ D.left} {ψ : D.left ⟶ U.left} (hφ : IsPullback φ A₁.hom D.hom k)
    (cart : IsPullback ψ D.hom U.hom h₀) :
    pullback.map A₁.hom A₁.hom D.hom D.hom φ φ k hφ.w.symm hφ.w.symm ≫
        pullback.map D.hom D.hom U.hom U.hom ψ ψ h₀ cart.w.symm cart.w.symm =
      pullback.map A₁.hom A₁.hom U.hom U.hom (φ ≫ ψ) (φ ≫ ψ) (k ≫ h₀)
        (hφ.paste_horiz cart).w.symm (hφ.paste_horiz cart).w.symm := by
  apply pullback.hom_ext <;> simp only [Category.assoc, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]

theorem isGrpPullback_comp_spread_to_subring :
    ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Type) [CommRing S] (R₀ : Subring S) (s₀ : Sp R₀ ⟶ Sp B) (d₀ : SiegPre g n ζ s₀) (Y : Scheme.{0}) (sY : Y ⟶ Sp B) (u : SiegPre g n ζ sY) (h₀ : Sp R₀ ⟶ Y) (ψ : d₀.A.left ⟶ u.A.left) (sE : Sp S ⟶ Sp B) (e : SiegPre g n ζ sE) (j : e.A.left ⟶ d₀.A.left), IsPullback ψ d₀.A.hom u.A.hom h₀ → IsGrpPullback e.A d₀.A (spMap R₀.subtype) j → IsGrpPullback e.A u.A (spMap R₀.subtype ≫ h₀) (j ≫ ψ) → ∃ F : Finset S, ∀ (R₁ : Subring S) (hle : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (A₁ : Over (Sp R₁)) [GrpObj A₁] (φ₁ : A₁.left ⟶ d₀.A.left), IsGrpPullback A₁ d₀.A (spMap (Subring.inclusion hle)) φ₁ → IsGrpPullback A₁ u.A (spMap (Subring.inclusion hle) ≫ h₀) (φ₁ ≫ ψ) := by
  intro g n B _ ζ S _ R₀ s₀ d₀ Y sY u h₀ ψ sE e j cart hj hjψ
  haveI := d₀.ab.proper
  haveI := u.ab.smooth
  haveI hqc : QuasiCompact (pullback.fst d₀.A.hom d₀.A.hom ≫ d₀.A.hom) := inferInstance
  haveI hlft : LocallyOfFiniteType (pullback.snd u.A.hom h₀) := inferInstance
  set f₀ : pullback d₀.A.hom d₀.A.hom ⟶ Sp R₀ := pullback.fst d₀.A.hom d₀.A.hom ≫ d₀.A.hom with hf₀
  have hμd : (μ[d₀.A]).left ≫ d₀.A.hom = f₀ := Over.w μ[d₀.A]
  have hμu : (μ[u.A]).left ≫ u.A.hom = pullback.fst u.A.hom u.A.hom ≫ u.A.hom := Over.w μ[u.A]
  set mψ := pullback.map d₀.A.hom d₀.A.hom u.A.hom u.A.hom ψ ψ h₀ cart.w.symm cart.w.symm with hmψ
  have w₁ : ((μ[d₀.A]).left ≫ ψ) ≫ u.A.hom = f₀ ≫ h₀ := by
    rw [Category.assoc, cart.w, ← Category.assoc, hμd]
  have w₂ : (mψ ≫ (μ[u.A]).left) ≫ u.A.hom = f₀ ≫ h₀ := by
    rw [Category.assoc, hμu, ← Category.assoc, hmψ, pullback.lift_fst, Category.assoc, cart.w, hf₀,
      Category.assoc]
  let a : pullback d₀.A.hom d₀.A.hom ⟶ pullback u.A.hom h₀ := pullback.lift _ _ w₁
  let b : pullback d₀.A.hom d₀.A.hom ⟶ pullback u.A.hom h₀ := pullback.lift _ _ w₂
  have key : ∀ {S₁ : Scheme.{0}} {A₁ : Over S₁} [GrpObj A₁] {k : S₁ ⟶ Sp R₀} {φ : A₁.left ⟶ d₀.A.left}
      (hφ : IsPullback φ A₁.hom d₀.A.hom k),
      pullback.map A₁.hom A₁.hom d₀.A.hom d₀.A.hom φ φ k hφ.w.symm hφ.w.symm ≫ mψ =
        pullback.map A₁.hom A₁.hom u.A.hom u.A.hom (φ ≫ ψ) (φ ≫ ψ) (k ≫ h₀)
          (hφ.paste_horiz cart).w.symm (hφ.paste_horiz cart).w.symm := by
    intro S₁ A₁ _ k φ hφ
    exact pullbackMap_comp hφ cart
  have hab : pullback.map e.A.hom e.A.hom d₀.A.hom d₀.A.hom j j (spMap R₀.subtype) hj.1.w.symm hj.1.w.symm ≫ a =
      pullback.map e.A.hom e.A.hom d₀.A.hom d₀.A.hom j j (spMap R₀.subtype) hj.1.w.symm hj.1.w.symm ≫ b := by
    have m₁ := (GlobalTheory.PullDegCompare.isGrpPullback_iff hj.1).1 hj
    have m₂ := (GlobalTheory.PullDegCompare.isGrpPullback_iff hjψ.1).1 hjψ
    apply pullback.hom_ext
    · simp only [a, b, Category.assoc, pullback.lift_fst]
      rw [← Category.assoc, ← m₁, Category.assoc, m₂]
      exact (congrArg (· ≫ (μ[u.A]).left) (key hj.1).symm).trans (Category.assoc _ _ _)
    · simp only [a, b, Category.assoc, pullback.lift_snd]
  obtain ⟨F, hF⟩ := GlobalTheory.morphisms_eq_spread_to_subring S R₀ (pullback e.A.hom e.A.hom)
    (pullback d₀.A.hom d₀.A.hom) (pullback u.A.hom h₀) (e.A ⊗ e.A).hom f₀ (pullback.snd u.A.hom h₀)
    (pullback.map e.A.hom e.A.hom d₀.A.hom d₀.A.hom j j (spMap R₀.subtype) hj.1.w.symm hj.1.w.symm) a b
    (isPullback_pullbackMap hj.1) (pullback.lift_snd _ _ _) (pullback.lift_snd _ _ _) hab
  refine ⟨F, fun R₁ hle hFs A₁ _ φ₁ hφ ↦ ?_⟩
  have cart₁ := hφ.1.paste_horiz cart
  refine (GlobalTheory.PullDegCompare.isGrpPullback_iff cart₁).2 ?_
  have H := hF R₁ hle hFs (pullback A₁.hom A₁.hom) (A₁ ⊗ A₁).hom
    (pullback.map A₁.hom A₁.hom d₀.A.hom d₀.A.hom φ₁ φ₁ _ hφ.1.w.symm hφ.1.w.symm)
    (isPullback_pullbackMap hφ.1)
  have H' := congrArg (· ≫ pullback.fst u.A.hom h₀) H
  simp only [a, b, Category.assoc, pullback.lift_fst] at H'
  have m := (GlobalTheory.PullDegCompare.isGrpPullback_iff hφ.1).1 hφ
  rw [← Category.assoc, m, Category.assoc, H']
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (μ[u.A]).left) (key hφ.1))

end GlobalTheory.GrpMulSpread
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackCompSpreadToSubringStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_isGrpPullback_comp_of_subring_le : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Type) [CommRing S] (R₀ : Subring S) (s₀ : Sp R₀ ⟶ Sp B) (d₀ : SiegPre g n ζ s₀) (Y : Scheme.{0}) (sY : Y ⟶ Sp B) (u : SiegPre g n ζ sY) (h₀ : Sp R₀ ⟶ Y) (ψ : d₀.A.left ⟶ u.A.left) (sE : Sp S ⟶ Sp B) (e : SiegPre g n ζ sE) (j : e.A.left ⟶ d₀.A.left), IsPullback ψ d₀.A.hom u.A.hom h₀ → IsGrpPullback e.A d₀.A (spMap R₀.subtype) j → IsGrpPullback e.A u.A (spMap R₀.subtype ≫ h₀) (j ≫ ψ) → ∃ F : Finset S, ∀ (R₁ : Subring S) (hle : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (A₁ : Over (Sp R₁)) [GrpObj A₁] (φ₁ : A₁.left ⟶ d₀.A.left), IsGrpPullback A₁ d₀.A (spMap (Subring.inclusion hle)) φ₁ → IsGrpPullback A₁ u.A (spMap (Subring.inclusion hle) ≫ h₀) (φ₁ ≫ ψ) := by
  first | exact @GlobalTheory.GrpMulSpread.isGrpPullback_comp_spread_to_subring | exact GlobalTheory.GrpMulSpread.isGrpPullback_comp_spread_to_subring | (intros; apply GlobalTheory.GrpMulSpread.isGrpPullback_comp_spread_to_subring; all_goals assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeIsoSpreadsToSubring
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeIsoSpreadsToSubring
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.IsoSpread

theorem spMap_inclusion_comp {S : Type} [CommRing S] {A B C : Subring S} (h₁ : A ≤ B)
    (h₂ : B ≤ C) :
    spMap (Subring.inclusion h₂) ≫ spMap (Subring.inclusion h₁) =
      spMap (Subring.inclusion (h₁.trans h₂)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem spMap_subtype_comp {S : Type} [CommRing S] {A B : Subring S} (h : A ≤ B) :
    spMap B.subtype ≫ spMap (Subring.inclusion h) = spMap A.subtype := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem exists_isPullback_lift {X₀ X₁ T₀ T₁ T₂ : Scheme.{0}} {f₀ : X₀ ⟶ T₀} {f₁ : X₁ ⟶ T₁}
    {π₁ : X₁ ⟶ X₀} {u : T₁ ⟶ T₂} {v : T₂ ⟶ T₀} {w : T₁ ⟶ T₀} (huv : u ≫ v = w)
    (hp : IsPullback π₁ f₁ f₀ w) :
    ∃ m : X₁ ⟶ pullback f₀ v, m ≫ pullback.fst _ _ = π₁ ∧ m ≫ pullback.snd _ _ = f₁ ≫ u ∧
      IsPullback m f₁ (pullback.snd f₀ v) u := by
  subst huv
  refine ⟨pullback.lift π₁ (f₁ ≫ u) (by rw [Category.assoc, hp.w]), pullback.lift_fst _ _ _,
    pullback.lift_snd _ _ _, ?_⟩
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  rw [pullback.lift_fst]
  exact hp

end GlobalTheory.IsoSpread

namespace GlobalTheory


open GlobalTheory.IsoSpread in
theorem iso_spreads_to_subring :
    ∀ (S : Type) [CommRing S] (R₀ : Subring S) (X X₀ Z : Scheme.{0}) (f : X ⟶ Sp S) (f₀ : X₀ ⟶ Sp R₀) (q : Z ⟶ Sp R₀) (π : X ⟶ X₀) [QuasiCompact f₀] [QuasiSeparated f₀] [LocallyOfFinitePresentation f₀] [QuasiCompact q] [QuasiSeparated q] [LocallyOfFinitePresentation q] (φ : X ⟶ Z), IsPullback π f f₀ (spMap R₀.subtype) → IsPullback φ f q (spMap R₀.subtype) → ∃ F : Finset S, ∀ (R₁ : Subring S) (hle : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R₁) (π₁ : X₁ ⟶ X₀) (j : X ⟶ X₁), IsPullback π₁ f₁ f₀ (spMap (Subring.inclusion hle)) → j ≫ π₁ = π → j ≫ f₁ = f ≫ spMap R₁.subtype → ∃ ψ : X₁ ⟶ Z, j ≫ ψ = φ ∧ IsPullback ψ f₁ q (spMap (Subring.inclusion hle)) := by
  classical
  intro S _ R₀ X X₀ Z f f₀ q π _ _ _ _ _ _ φ hπ hφ

  obtain ⟨Fa, ha⟩ := morphism_descends_to_subring S R₀ X X₀ Z f f₀ q π φ hπ
    (hφ.w.trans hπ.w.symm)
  obtain ⟨Fb, hb⟩ := morphism_descends_to_subring S R₀ X Z X₀ f q f₀ φ π hφ
    (hπ.w.trans hφ.w.symm)

  let R₂ : Subring S := Subring.closure ((R₀ : Set S) ∪ (Fa : Set S) ∪ (Fb : Set S))
  have h₀₂ : R₀ ≤ R₂ := fun x hx ↦ Subring.subset_closure (Or.inl (Or.inl hx))
  have hFa : (Fa : Set S) ⊆ R₂ := fun x hx ↦ Subring.subset_closure (Or.inl (Or.inr hx))
  have hFb : (Fb : Set S) ⊆ R₂ := fun x hx ↦ Subring.subset_closure (Or.inr hx)
  obtain ⟨j₂, hj₂f, hj₂s, hj₂⟩ := exists_isPullback_lift (spMap_subtype_comp h₀₂) hπ
  obtain ⟨k₂, hk₂f, hk₂s, hk₂⟩ := exists_isPullback_lift (spMap_subtype_comp h₀₂) hφ
  obtain ⟨ψ₂, hψ₂, hψ₂q⟩ := ha R₂ h₀₂ hFa _ _ _ j₂ (IsPullback.of_hasPullback _ _) hj₂f hj₂s
  obtain ⟨χ₂, hχ₂, hχ₂q⟩ := hb R₂ h₀₂ hFb _ _ _ k₂ (IsPullback.of_hasPullback _ _) hk₂f hk₂s
  let α₂ := pullback.lift ψ₂ (pullback.snd f₀ (spMap (Subring.inclusion h₀₂)))
    (by rw [hψ₂q, pullback.condition])
  let β₂ := pullback.lift χ₂ (pullback.snd q (spMap (Subring.inclusion h₀₂)))
    (by rw [hχ₂q, pullback.condition])
  have hα₂f : α₂ ≫ pullback.fst _ _ = ψ₂ := pullback.lift_fst _ _ _
  have hα₂s : α₂ ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have hβ₂f : β₂ ≫ pullback.fst _ _ = χ₂ := pullback.lift_fst _ _ _
  have hβ₂s : β₂ ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have hjα : j₂ ≫ α₂ = k₂ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hα₂f, hψ₂, hk₂f]
    · rw [Category.assoc, hα₂s, hj₂s, hk₂s]
  have hkβ : k₂ ≫ β₂ = j₂ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hβ₂f, hχ₂, hj₂f]
    · rw [Category.assoc, hβ₂s, hj₂s, hk₂s]

  obtain ⟨Fc, hc⟩ := morphisms_eq_spread_to_subring S R₂ X _ _ f _ _ j₂ (α₂ ≫ β₂) (𝟙 _) hj₂
    (by rw [Category.assoc, hβ₂s, hα₂s]) (Category.id_comp _)
    (by rw [reassoc_of% hjα, hkβ, Category.comp_id])
  obtain ⟨Fd, hd⟩ := morphisms_eq_spread_to_subring S R₂ X _ _ f _ _ k₂ (β₂ ≫ α₂) (𝟙 _) hk₂
    (by rw [Category.assoc, hα₂s, hβ₂s]) (Category.id_comp _)
    (by rw [reassoc_of% hkβ, hjα, Category.comp_id])
  refine ⟨Fa ∪ Fb ∪ Fc ∪ Fd, fun R₁ hle hF X₁ f₁ π₁ j hp₁ hj₁ hjf ↦ ?_⟩
  simp only [Finset.coe_union, Set.union_subset_iff] at hF
  obtain ⟨⟨⟨hFa₁, hFb₁⟩, hFc₁⟩, hFd₁⟩ := hF
  have h₂₁ : R₂ ≤ R₁ := Subring.closure_le.mpr
    (Set.union_subset (Set.union_subset (fun x hx ↦ hle hx) hFa₁) hFb₁)
  obtain ⟨m, hmf, hms, hm⟩ := exists_isPullback_lift (w := spMap (Subring.inclusion hle))
    (spMap_inclusion_comp h₀₂ h₂₁) hp₁
  obtain ⟨n, hnf, hns, hn⟩ := exists_isPullback_lift (w := spMap (Subring.inclusion hle))
    (spMap_inclusion_comp h₀₂ h₂₁) (IsPullback.of_hasPullback q (spMap (Subring.inclusion hle)))
  have hmc : m ≫ α₂ ≫ β₂ = m := (hc R₁ h₂₁ hFc₁ X₁ f₁ m hm).trans (Category.comp_id _)
  have hnd : n ≫ β₂ ≫ α₂ = n := (hd R₁ h₂₁ hFd₁ _ _ n hn).trans (Category.comp_id _)
  have hjm : j ≫ m = j₂ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hmf, hj₁, hj₂f]
    · rw [Category.assoc, hms, reassoc_of% hjf, spMap_subtype_comp, hj₂s]
  have hw : (m ≫ ψ₂) ≫ q = f₁ ≫ spMap (Subring.inclusion hle) := by
    rw [Category.assoc, hψ₂q, reassoc_of% hmf, hp₁.w]
  let α : X₁ ⟶ pullback q (spMap (Subring.inclusion hle)) := pullback.lift (m ≫ ψ₂) f₁ hw
  let β : pullback q (spMap (Subring.inclusion hle)) ⟶ X₁ :=
    hp₁.lift (n ≫ χ₂) (pullback.snd _ _) (by rw [Category.assoc, hχ₂q, reassoc_of% hnf,
      pullback.condition])
  have hαf : α ≫ pullback.fst _ _ = m ≫ ψ₂ := pullback.lift_fst _ _ _
  have hαs : α ≫ pullback.snd _ _ = f₁ := pullback.lift_snd _ _ _
  have hβf : β ≫ π₁ = n ≫ χ₂ := hp₁.lift_fst _ _ _
  have hβs : β ≫ f₁ = pullback.snd _ _ := hp₁.lift_snd _ _ _
  have hαn : α ≫ n = m ≫ α₂ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hnf, hαf, Category.assoc, hα₂f]
    · rw [Category.assoc, hns, reassoc_of% hαs, Category.assoc, hα₂s, hms]
  have hβm : β ≫ m = n ≫ β₂ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hmf, hβf, Category.assoc, hβ₂f]
    · rw [Category.assoc, hms, reassoc_of% hβs, Category.assoc, hβ₂s, hns]
  have h₁ : α ≫ β = 𝟙 X₁ := by
    apply hp₁.hom_ext
    · rw [Category.assoc, hβf, reassoc_of% hαn, Category.id_comp, ← hβ₂f, ← Category.assoc m,
        ← Category.assoc, Category.assoc m, hmc, hmf]
    · rw [Category.assoc, hβs, hαs, Category.id_comp]
  have h₂ : β ≫ α = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hαf, reassoc_of% hβm, Category.id_comp, ← hα₂f, ← Category.assoc n,
        ← Category.assoc, Category.assoc n, hnd, hnf]
    · rw [Category.assoc, hαs, hβs, Category.id_comp]
  exact ⟨m ≫ ψ₂, by rw [reassoc_of% hjm, hψ₂],
    IsPullback.of_iso_pullback ⟨hw⟩ ⟨α, β, h₁, h₂⟩ hαf hαs⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeIsoSpreadsToSubringStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseChange_iso_spreads_to_subring : ∀ (S : Type) [CommRing S] (R₀ : Subring S) (X X₀ Z : Scheme.{0}) (f : X ⟶ Sp S) (f₀ : X₀ ⟶ Sp R₀) (q : Z ⟶ Sp R₀) (π : X ⟶ X₀) [QuasiCompact f₀] [QuasiSeparated f₀] [LocallyOfFinitePresentation f₀] [QuasiCompact q] [QuasiSeparated q] [LocallyOfFinitePresentation q] (φ : X ⟶ Z), IsPullback π f f₀ (spMap R₀.subtype) → IsPullback φ f q (spMap R₀.subtype) → ∃ F : Finset S, ∀ (R₁ : Subring S) (hle : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R₁) (π₁ : X₁ ⟶ X₀) (j : X ⟶ X₁), IsPullback π₁ f₁ f₀ (spMap (Subring.inclusion hle)) → j ≫ π₁ = π → j ≫ f₁ = f ≫ spMap R₁.subtype → ∃ ψ : X₁ ⟶ Z, j ≫ ψ = φ ∧ IsPullback ψ f₁ q (spMap (Subring.inclusion hle)) := by
  first | exact @GlobalTheory.iso_spreads_to_subring | exact GlobalTheory.iso_spreads_to_subring | (intros; apply GlobalTheory.iso_spreads_to_subring <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelLevelSectionsSpreadToSubring
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelLevelSectionsSpreadToSubring
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem siegel_levels_spread_to_subring : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Type) [CommRing S] (R₀ : Subring S) (s₀ : Sp R₀ ⟶ Sp B) (d₀ : SiegPre g n ζ s₀) (Y : Scheme.{0}) (sY : Y ⟶ Sp B) (u : SiegPre g n ζ sY) (h₀ : Sp R₀ ⟶ Y) (ψ : d₀.A.left ⟶ u.A.left) (sE : Sp S ⟶ Sp B) (e : SiegPre g n ζ sE) (j : e.A.left ⟶ d₀.A.left), IsPullback ψ d₀.A.hom u.A.hom h₀ → (∀ a, (e.lev a).left ≫ j = spMap R₀.subtype ≫ (d₀.lev a).left) → (∀ a, (e.lev a).left ≫ (j ≫ ψ) = (spMap R₀.subtype ≫ h₀) ≫ (u.lev a).left) → ∃ F : Finset S, ∀ (R₁ : Subring S) (hle : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (s₁ : Sp R₁ ⟶ Sp B) (d₁ : SiegPre g n ζ s₁) (φ₁ : d₁.A.left ⟶ d₀.A.left), IsGrpPullback d₁.A u.A (spMap (Subring.inclusion hle) ≫ h₀) (φ₁ ≫ ψ) → (∀ a, (d₁.lev a).left ≫ φ₁ = spMap (Subring.inclusion hle) ≫ (d₀.lev a).left) → ∀ a, (d₁.lev a).left ≫ (φ₁ ≫ ψ) = (spMap (Subring.inclusion hle) ≫ h₀) ≫ (u.lev a).left := by
  intro g n B _ ζ S _ R₀ s₀ d₀ Y sY u h₀ ψ sE e j hψ hj hjψ
  classical
  haveI : Smooth u.A.hom := u.ab.smooth
  have hsec₀ : ∀ a, (d₀.lev a).left ≫ d₀.A.hom = 𝟙 (Sp R₀) := fun a => Over.w (d₀.lev a)
  have hsecu : ∀ a, (u.lev a).left ≫ u.A.hom = 𝟙 Y := fun a => Over.w (u.lev a)
  have key : ∀ i : Fin g ⊕ Fin g, ∃ F : Finset S, ∀ (R₁ : Subring S) (hle : R₀ ≤ R₁), (F : Set S) ⊆ R₁ →
      spMap (Subring.inclusion hle) ≫ (d₀.lev (Pi.single i 1)).left ≫ ψ =
        spMap (Subring.inclusion hle) ≫ h₀ ≫ (u.lev (Pi.single i 1)).left := by
    intro i
    let x : Sp R₀ ⟶ pullback u.A.hom h₀ := pullback.lift ((d₀.lev (Pi.single i 1)).left ≫ ψ) (𝟙 _) (by
      rw [Category.assoc, hψ.w, ← Category.assoc, hsec₀, Category.id_comp])
    let y : Sp R₀ ⟶ pullback u.A.hom h₀ := pullback.lift (h₀ ≫ (u.lev (Pi.single i 1)).left) (𝟙 _) (by
      rw [Category.assoc, hsecu, Category.comp_id, Category.id_comp])
    have hx : x ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
    have hy : y ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
    have hxy : spMap R₀.subtype ≫ x = spMap R₀.subtype ≫ y := by
      apply pullback.hom_ext
      · simp only [x, y, Category.assoc, pullback.lift_fst]
        rw [← Category.assoc, ← hj, Category.assoc, hjψ, Category.assoc]
      · simp only [x, y, Category.assoc, pullback.lift_snd]
    obtain ⟨F, hF⟩ := morphisms_eq_spread_to_subring S R₀ (Sp S) (Sp R₀) (pullback u.A.hom h₀) (𝟙 _) (𝟙 _)
      (pullback.snd _ _) (spMap R₀.subtype) x y (IsPullback.id_vert _) hx hy hxy
    refine ⟨F, fun R₁ hle hF₁ => ?_⟩
    have := congrArg (· ≫ pullback.fst u.A.hom h₀)
      (hF R₁ hle hF₁ (Sp R₁) (𝟙 _) (spMap (Subring.inclusion hle)) (IsPullback.id_vert _))
    simpa only [x, y, Category.assoc, pullback.lift_fst] using this
  choose F hF using key
  refine ⟨Finset.univ.biUnion F, fun R₁ hle hsub s₁ d₁ φ₁ hgp hlev₁ a => ?_⟩
  have hbasis : ∀ i : Fin g ⊕ Fin g, (d₁.lev (Pi.single i 1)).left ≫ (φ₁ ≫ ψ) =
      (spMap (Subring.inclusion hle) ≫ h₀) ≫ (u.lev (Pi.single i 1)).left := by
    intro i
    have hFi : (F i : Set S) ⊆ R₁ := fun x hx => hsub (by
      simp only [Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true, Set.mem_iUnion]
      exact ⟨i, hx⟩)
    rw [← Category.assoc, hlev₁, Category.assoc, hF i R₁ hle hFi, Category.assoc]
  let f : Sp R₁ ⟶ Y := spMap (Subring.inclusion hle) ≫ h₀
  let M : Over Y := Over.mk ((𝟙_ (Over (Sp R₁))).hom ≫ f)
  have hunit : (toUnit M).left = f := by
    have := Over.w (toUnit M)
    exact (Category.comp_id _).symm.trans (this.trans (Category.id_comp _))
  have w : ∀ a, ((d₁.lev a).left ≫ (φ₁ ≫ ψ)) ≫ u.A.hom = M.hom := by
    intro a
    rw [Category.assoc, hgp.1.w, ← Category.assoc, Over.w (d₁.lev a)]
    rfl
  let Ψ₁ : (Fin g ⊕ Fin g → ℤ) →+ Additive (M ⟶ u.A) :=
    AddMonoidHom.mk' (fun a => Additive.ofMul (toUnit M ≫ u.lev a)) (by
      intro a b
      rw [u.lev_add, comp_mul]
      rfl)
  let Ψ₂ : (Fin g ⊕ Fin g → ℤ) →+ Additive (M ⟶ u.A) :=
    AddMonoidHom.mk' (fun a => Additive.ofMul (Over.homMk ((d₁.lev a).left ≫ (φ₁ ≫ ψ)) (w a) : M ⟶ u.A)) (by
      intro a b
      show Additive.ofMul _ = Additive.ofMul (_ * _)
      congr 1
      apply Over.OverMorphism.ext
      rw [hgp.2 (𝟙_ _) (d₁.lev a) (d₁.lev b) _ _ rfl rfl, ← d₁.lev_add]
      rfl)
  have hΨ : Ψ₁ = Ψ₂ := by
    refine AddMonoidHom.functions_ext' _ _ _ (fun i => AddMonoidHom.ext_int ?_)
    show Additive.ofMul (toUnit M ≫ u.lev (Pi.single i 1)) =
      Additive.ofMul (Over.homMk ((d₁.lev (Pi.single i 1)).left ≫ (φ₁ ≫ ψ)) (w (Pi.single i 1)) : M ⟶ u.A)
    refine congrArg Additive.ofMul (Over.OverMorphism.ext ?_)
    rw [Over.comp_left, hunit]
    exact (hbasis i).symm
  have := congrArg (fun φ => (Additive.toMul (φ a)).left) hΨ
  simp only [Ψ₁, Ψ₂, AddMonoidHom.mk'_apply, toMul_ofMul, Over.comp_left, Over.homMk_left] at this
  rw [← this, hunit]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelLevelSectionsSpreadToSubringStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_level_sections_spread_to_subring : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Type) [CommRing S] (R₀ : Subring S) (s₀ : Sp R₀ ⟶ Sp B) (d₀ : SiegPre g n ζ s₀) (Y : Scheme.{0}) (sY : Y ⟶ Sp B) (u : SiegPre g n ζ sY) (h₀ : Sp R₀ ⟶ Y) (ψ : d₀.A.left ⟶ u.A.left) (sE : Sp S ⟶ Sp B) (e : SiegPre g n ζ sE) (j : e.A.left ⟶ d₀.A.left), IsPullback ψ d₀.A.hom u.A.hom h₀ → (∀ a, (e.lev a).left ≫ j = spMap R₀.subtype ≫ (d₀.lev a).left) → (∀ a, (e.lev a).left ≫ (j ≫ ψ) = (spMap R₀.subtype ≫ h₀) ≫ (u.lev a).left) → ∃ F : Finset S, ∀ (R₁ : Subring S) (hle : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (s₁ : Sp R₁ ⟶ Sp B) (d₁ : SiegPre g n ζ s₁) (φ₁ : d₁.A.left ⟶ d₀.A.left), IsGrpPullback d₁.A u.A (spMap (Subring.inclusion hle) ≫ h₀) (φ₁ ≫ ψ) → (∀ a, (d₁.lev a).left ≫ φ₁ = spMap (Subring.inclusion hle) ≫ (d₀.lev a).left) → ∀ a, (d₁.lev a).left ≫ (φ₁ ≫ ψ) = (spMap (Subring.inclusion hle) ≫ h₀) ≫ (u.lev a).left := by
  first | exact @GlobalTheory.siegel_levels_spread_to_subring | exact GlobalTheory.siegel_levels_spread_to_subring | (intros; apply GlobalTheory.siegel_levels_spread_to_subring; all_goals assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPullbackSpreadsToIntermediateSubring
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegSpreadCore

theorem spMap_subtype_eq {S : Type} [CommRing S] {R₀ R₁ : Subring S} (h : R₀ ≤ R₁) :
    spMap R₀.subtype = spMap R₁.subtype ≫ spMap (Subring.inclusion h) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl

theorem spMap_inclusion_eq {S : Type} [CommRing S] {R₀ R₁ R₂ : Subring S} (h₁ : R₀ ≤ R₁) (h₂ : R₁ ≤ R₂) (h : R₀ ≤ R₂) :
    spMap (Subring.inclusion h) = spMap (Subring.inclusion h₂) ≫ spMap (Subring.inclusion h₁) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl

theorem siegPB_spread_subring : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Type) [CommRing S] (R₀ : Subring S) (s₀ : Sp R₀ ⟶ Sp B) (d₀ : SiegPre g n ζ s₀) (Y : Scheme.{0}) (sY : Y ⟶ Sp B) (u : SiegPre g n ζ sY) (h₀ : Sp R₀ ⟶ Y) (sE : Sp S ⟶ Sp B) (e : SiegPre g n ζ sE), SiegPB e d₀ (spMap R₀.subtype) → SiegPB e u (spMap R₀.subtype ≫ h₀) → ∃ F : Finset S, ∀ (R₁ : Subring S) (hle : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (s₁ : Sp R₁ ⟶ Sp B) (d₁ : SiegPre g n ζ s₁), SiegPB d₁ d₀ (spMap (Subring.inclusion hle)) → SiegPB d₁ u (spMap (Subring.inclusion hle) ≫ h₀) := by
  intro g n B _ ζ S _ R₀ s₀ d₀ Y sY u h₀ sE e hd hu
  classical
  obtain ⟨φd, φd₂, hφd, hsd, hwd, hld⟩ := hd
  obtain ⟨φu, φu₂, hφu, hsu, hwu, hlu⟩ := hu
  haveI := d₀.ab.smooth; haveI := d₀.ab.proper; haveI := u.ab.smooth; haveI := u.ab.proper
  have hZ : IsPullback (pullback.lift φu (e.A.hom ≫ spMap R₀.subtype) (by rw [hφu.1.w, Category.assoc]))
      e.A.hom (pullback.snd u.A.hom h₀) (spMap R₀.subtype) := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback u.A.hom h₀)
    rw [pullback.lift_fst]; exact hφu.1
  obtain ⟨F₁, hF₁⟩ := GlobalTheory.T.baseChange_iso_spreads_to_subring S R₀ e.A.left d₀.A.left (pullback u.A.hom h₀) e.A.hom d₀.A.hom
    (pullback.snd u.A.hom h₀) φd _ hφd.1 hZ
  let R' : Subring S := Subring.closure ((R₀ : Set S) ∪ (F₁ : Set S))
  have hR0 : R₀ ≤ R' := fun x hx => Subring.subset_closure (Or.inl hx)
  have hF1 : (F₁ : Set S) ⊆ R' := fun x hx => Subring.subset_closure (Or.inr hx)
  obtain ⟨⟨d', hd'⟩, -⟩ := GlobalTheory.siegPre_pullback g n B ζ (Sp R₀) (Sp R') s₀
    (spMap (Subring.inclusion hR0) ≫ s₀) (spMap (Subring.inclusion hR0)) d₀ rfl
  have hd'c := hd'
  obtain ⟨φ', φ'₂, hφ', hs', hw', hl'⟩ := hd'
  have eR' := spMap_subtype_eq hR0
  let j : e.A.left ⟶ d'.A.left := hφ'.1.lift φd (e.A.hom ≫ spMap R'.subtype)
    (by rw [hφd.1.w, eR', Category.assoc])
  have hj1 : j ≫ φ' = φd := hφ'.1.lift_fst _ _ _
  have hj2 : j ≫ d'.A.hom = e.A.hom ≫ spMap R'.subtype := hφ'.1.lift_snd _ _ _
  obtain ⟨ψZ, hψZ1, hψZ2⟩ := hF₁ R' hR0 hF1 d'.A.left d'.A.hom φ' j hφ'.1 hj1 hj2
  let ψ := ψZ ≫ pullback.fst u.A.hom h₀
  have hψ : IsPullback ψ d'.A.hom u.A.hom (spMap (Subring.inclusion hR0) ≫ h₀) :=
    hψZ2.paste_horiz (IsPullback.of_hasPullback _ _)
  have hjψ : j ≫ ψ = φu := by
    show j ≫ ψZ ≫ pullback.fst u.A.hom h₀ = φu
    rw [reassoc_of% hψZ1, pullback.lift_fst]
  have eh : spMap R'.subtype ≫ spMap (Subring.inclusion hR0) ≫ h₀ = spMap R₀.subtype ≫ h₀ := by
    rw [← Category.assoc, ← eR']
  have gj : IsGrpPullback e.A d'.A (spMap R'.subtype) j :=
    IsGrpPullback.cancel hφ' (by rw [hj1, ← eR']; exact hφd) hj2
  obtain ⟨j₂, hsj⟩ := GlobalTheory.SiegDesc.exists_isSquare hj2
  have hj₂ : j₂ ≫ φ'₂ = φd₂ := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst d₀.A d₀.A).left = _ ≫ (fst d₀.A d₀.A).left
      rw [Category.assoc, hs'.1, ← Category.assoc, hsj.1, Category.assoc, hj1, hsd.1]
    · show (_ ≫ _) ≫ (snd d₀.A d₀.A).left = _ ≫ (snd d₀.A d₀.A).left
      rw [Category.assoc, hs'.2, ← Category.assoc, hsj.2, Category.assoc, hj1, hsd.2]
  have hwj : LBIso e.P (d'.P.pull j₂) := by
    rw [← hj₂] at hwd
    exact (hwd.trans e.isLB (pull_isLB d₀.isLB _) (pull_isLB (pull_isLB d₀.isLB _) _)
      (GlobalTheory.SiegelPullComp.iso_pull_pull d₀.isLB φ'₂ j₂).symm).trans e.isLB
      (pull_isLB (pull_isLB d₀.isLB _) _) (pull_isLB d'.isLB _) (GlobalTheory.SiegelPullComp.iso_pull j₂ hw').symm
  have hlj : ∀ a, (e.lev a).left ≫ j = spMap R'.subtype ≫ (d'.lev a).left := by
    intro a
    apply hφ'.1.hom_ext
    · rw [Category.assoc, hj1, hld a, Category.assoc, hl' a, ← Category.assoc, ← eR']
    · have a₁ : (e.lev a).left ≫ e.A.hom = 𝟙 _ := Over.w (e.lev a)
      have a₂ : (d'.lev a).left ≫ d'.A.hom = 𝟙 _ := Over.w (d'.lev a)
      rw [Category.assoc, hj2, reassoc_of% a₁, Category.assoc, a₂]
      simp
  obtain ⟨F₂, hF₂⟩ := GlobalTheory.T.exists_finset_isGrpPullback_comp_of_subring_le g n B ζ S R' _ d' Y sY u _ ψ sE e j hψ gj (by rw [eh, hjψ]; exact hφu)
  obtain ⟨F₃, hF₃⟩ := GlobalTheory.T.lbIso_spread_alt g n B ζ S R' _ d' Y sY u _ ψ sE e j hψ j₂ φu₂ gj.1 hsj hwj
    (by rw [hjψ]; exact hsu) hwu
  obtain ⟨F₄, hF₄⟩ := GlobalTheory.T.siegel_level_sections_spread_to_subring g n B ζ S R' _ d' Y sY u _ ψ sE e j hψ hlj
    (fun a => by rw [eh, hjψ]; exact hlu a)
  refine ⟨F₁ ∪ F₂ ∪ F₃ ∪ F₄, fun R₁ hle hF s₁ d₁ hd₁ => ?_⟩
  have hsub : ∀ G : Finset S, G ⊆ F₁ ∪ F₂ ∪ F₃ ∪ F₄ → (G : Set S) ⊆ R₁ :=
    fun G h => (Finset.coe_subset.2 h).trans hF
  have hR'1 : R' ≤ R₁ := Subring.closure_le.2 (Set.union_subset hle
    (hsub F₁ (by intro x; simp only [Finset.mem_union]; tauto)))
  have eR1 := spMap_inclusion_eq hR0 hR'1 hle
  have hd₁' : SiegPB d₁ d' (spMap (Subring.inclusion hR'1)) :=
    GlobalTheory.SiegelPullComp.pb_cancel hd'c (by rw [← eR1]; exact hd₁)
  obtain ⟨φ₁, φ₁₂, hφ₁, hs₁, hw₁, hl₁⟩ := hd₁'
  have gm := hF₂ R₁ hR'1 (hsub F₂ (by intro x; simp only [Finset.mem_union]; tauto)) d₁.A φ₁ hφ₁
  have e2 : spMap (Subring.inclusion hR'1) ≫ spMap (Subring.inclusion hR0) ≫ h₀ =
      spMap (Subring.inclusion hle) ≫ h₀ := by rw [eR1, Category.assoc]
  rw [e2] at gm
  obtain ⟨χ₂, hχ⟩ := GlobalTheory.SiegDesc.exists_isSquare gm.1.w
  refine ⟨φ₁ ≫ ψ, χ₂, gm, hχ, hF₃ R₁ hR'1 (hsub F₃ (by intro x; simp only [Finset.mem_union]; tauto))
    s₁ d₁ φ₁ φ₁₂ χ₂ hφ₁.1 hs₁ hw₁ hχ, fun a => ?_⟩
  have := hF₄ R₁ hR'1 (hsub F₄ (by intro x; simp only [Finset.mem_union]; tauto)) s₁ d₁ φ₁
    (by rw [e2]; exact gm) hl₁ a
  rw [e2] at this
  exact this

end GlobalTheory.SiegSpreadCore
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPullbackSpreadsToIntermediateSubringStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelPullback_spreads_to_intermediate_subring : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Type) [CommRing S] (R₀ : Subring S) (s₀ : Sp R₀ ⟶ Sp B) (d₀ : SiegPre g n ζ s₀) (Y : Scheme.{0}) (sY : Y ⟶ Sp B) (u : SiegPre g n ζ sY) (h₀ : Sp R₀ ⟶ Y) (sE : Sp S ⟶ Sp B) (e : SiegPre g n ζ sE), SiegPB e d₀ (spMap R₀.subtype) → SiegPB e u (spMap R₀.subtype ≫ h₀) → ∃ F : Finset S, ∀ (R₁ : Subring S) (hle : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (s₁ : Sp R₁ ⟶ Sp B) (d₁ : SiegPre g n ζ s₁), SiegPB d₁ d₀ (spMap (Subring.inclusion hle)) → SiegPB d₁ u (spMap (Subring.inclusion hle) ≫ h₀) := by
  first | exact @GlobalTheory.SiegSpreadCore.siegPB_spread_subring | exact GlobalTheory.SiegSpreadCore.siegPB_spread_subring | (intros; apply GlobalTheory.SiegSpreadCore.siegPB_spread_subring <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationAwayInjectiveAtPrimeOfDvd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationAwayInjectiveAtPrimeOfDvd
namespace GlobalTheory

theorem localization_away_injective_of_dvd (R : Type) [CommRing R] [IsNoetherianRing R] (𝔭 : Ideal R) [𝔭.IsPrime] :
    ∃ t ∉ 𝔭, ∀ (c : R), t ∣ c → ∀ κ : Localization.Away c →+* Localization.AtPrime 𝔭,
      κ.comp (algebraMap R (Localization.Away c)) = algebraMap R (Localization.AtPrime 𝔭) →
      Function.Injective κ := by
  classical
  set I : Ideal R := RingHom.ker (algebraMap R (Localization.AtPrime 𝔭)) with hI
  obtain ⟨s, hs⟩ : I.FG := IsNoetherian.noetherian I
  have key : ∀ s : Finset R, (∀ x ∈ s, algebraMap R (Localization.AtPrime 𝔭) x = 0) →
      ∃ t ∉ 𝔭, ∀ x ∈ s, t * x = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨1, fun h => ‹𝔭.IsPrime›.ne_top ((Ideal.eq_top_iff_one _).mpr h), by simp⟩
    | insert a s ha ih =>
      intro h
      obtain ⟨t, ht, hts⟩ := ih (fun x hx => h x (Finset.mem_insert_of_mem hx))
      obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff 𝔭.primeCompl (Localization.AtPrime 𝔭) a).mp
        (h a (Finset.mem_insert_self a s))
      refine ⟨(m : R) * t, 𝔭.primeCompl.mul_mem m.2 ht, ?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · rw [mul_comm (m : R) t, mul_assoc, hm, mul_zero]
      · rw [mul_assoc, hts x hx, mul_zero]
  obtain ⟨t, ht, hts⟩ := key s (fun x hx => by
    have : x ∈ I := hs ▸ Submodule.subset_span hx
    simpa [hI] using this)
  have hker : ∀ x ∈ I, t * x = 0 := by
    have hle : I ≤ LinearMap.ker (LinearMap.mulLeft R t) := by
      rw [← hs, Submodule.span_le]
      intro x hx
      simp [hts x hx]
    intro x hx
    simpa using hle hx
  refine ⟨t, ht, ?_⟩
  intro c ⟨d, hd⟩ κ hκ
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨⟨a, m⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers c) x
  have hspec := IsLocalization.mk'_spec (Localization.Away c) a m
  have h1 : algebraMap R (Localization.AtPrime 𝔭) a = 0 := by
    have := congrArg κ hspec
    rw [map_mul, hx, zero_mul] at this
    rw [← hκ, RingHom.comp_apply, ← this]
  have hta : t * a = 0 := hker a (by simpa [hI] using h1)
  have hu : IsUnit (algebraMap R (Localization.Away c) t) := by
    have hc := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away c) c
    have hc' : IsUnit (algebraMap R (Localization.Away c) t * algebraMap R (Localization.Away c) d) := by
      rw [← map_mul, ← hd]; exact hc
    exact isUnit_of_mul_isUnit_left hc'
  have ha : algebraMap R (Localization.Away c) a = 0 := by
    have : algebraMap R (Localization.Away c) t * algebraMap R (Localization.Away c) a = 0 := by
      rw [← map_mul, hta, map_zero]
    exact (hu.mul_right_eq_zero).mp this
  show IsLocalization.mk' (Localization.Away c) a m = 0
  rw [IsLocalization.mk'_eq_mul_mk'_one, ha, zero_mul]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationAwayInjectiveAtPrimeOfDvdStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localization_away_injective_atPrime_of_dvd : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (𝔭 : Ideal R) [𝔭.IsPrime], ∃ t ∉ 𝔭, ∀ (c : R), t ∣ c → ∀ κ : Localization.Away c →+* Localization.AtPrime 𝔭, κ.comp (algebraMap R (Localization.Away c)) = algebraMap R (Localization.AtPrime 𝔭) → Function.Injective κ := by
  first | exact @GlobalTheory.localization_away_injective_of_dvd | exact GlobalTheory.localization_away_injective_of_dvd | (intros; apply GlobalTheory.localization_away_injective_of_dvd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationAwayRangeLeOfDvdOfComp
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationAwayRangeLeOfDvdOfComp
namespace GlobalTheory

theorem away_range_le_of_dvd (R : Type) [CommRing R] (P : Type) [CommRing P] (g : R →+* P) (c c' : R)
    (hcc : c ∣ c') (κ : Localization.Away c →+* P) (κ' : Localization.Away c' →+* P)
    (hκ : κ.comp (algebraMap R (Localization.Away c)) = g)
    (hκ' : κ'.comp (algebraMap R (Localization.Away c')) = g) : κ.range ≤ κ'.range := by
  have hu : IsUnit (algebraMap R (Localization.Away c') c) :=
    isUnit_of_dvd_unit (map_dvd _ hcc) (IsLocalization.Away.algebraMap_isUnit c')
  let φ : Localization.Away c →+* Localization.Away c' := IsLocalization.Away.lift c hu
  have hφ : (κ'.comp φ) = κ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers c)
    rw [hκ, RingHom.comp_assoc]
    have : φ.comp (algebraMap R (Localization.Away c)) = algebraMap R (Localization.Away c') :=
      IsLocalization.Away.lift_comp c hu
    rw [this, hκ']
  rintro y ⟨x, rfl⟩
  exact ⟨φ x, by rw [← hφ]; rfl⟩

theorem away_range_le_of_dvd' : ∀ (R : Type) [CommRing R] (P : Type) [CommRing P] (g : R →+* P) (c c' : R), c ∣ c' → ∀ (κ : Localization.Away c →+* P) (κ' : Localization.Away c' →+* P), κ.comp (algebraMap R (Localization.Away c)) = g → κ'.comp (algebraMap R (Localization.Away c')) = g → κ.range ≤ κ'.range :=
  fun R _ P _ g c c' h κ κ' hκ hκ' => away_range_le_of_dvd R P g c c' h κ κ' hκ hκ'

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationAwayRangeLeOfDvdOfCompStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localization_away_range_le_of_dvd_of_comp : ∀ (R : Type) [CommRing R] (P : Type) [CommRing P] (g : R →+* P) (c c' : R), c ∣ c' → ∀ (κ : Localization.Away c →+* P) (κ' : Localization.Away c' →+* P), κ.comp (algebraMap R (Localization.Away c)) = g → κ'.comp (algebraMap R (Localization.Away c')) = g → κ.range ≤ κ'.range := by
  first | exact @GlobalTheory.away_range_le_of_dvd' | exact GlobalTheory.away_range_le_of_dvd' | (intros; apply GlobalTheory.away_range_le_of_dvd' <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsetMemRangeLocalizationAwayOfDvd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsetMemRangeLocalizationAwayOfDvd
namespace GlobalTheory

theorem finset_mem_range_of_away_dvd (R : Type) [CommRing R] (𝔭 : Ideal R) [𝔭.IsPrime]
    (F : Finset (Localization.AtPrime 𝔭)) :
    ∃ s ∉ 𝔭, ∀ (c : R), s ∣ c → ∀ κ : Localization.Away c →+* Localization.AtPrime 𝔭,
      κ.comp (algebraMap R (Localization.Away c)) = algebraMap R (Localization.AtPrime 𝔭) →
        ∀ x ∈ F, x ∈ κ.range := by
  classical
  choose p hp using fun x : Localization.AtPrime 𝔭 =>
    IsLocalization.mk'_surjective 𝔭.primeCompl x
  let sx : Localization.AtPrime 𝔭 → 𝔭.primeCompl := fun x => (p x).2
  refine ⟨((∏ x ∈ F, sx x : 𝔭.primeCompl) : R), (∏ x ∈ F, sx x).2, ?_⟩
  intro c hc κ hκ x hx
  have hdvd : ((sx x : 𝔭.primeCompl) : R) ∣ c := by
    refine dvd_trans ?_ hc
    rw [Submonoid.coe_finsetProd]
    exact Finset.dvd_prod_of_mem (fun y => ((sx y : 𝔭.primeCompl) : R)) hx
  obtain ⟨m, hm⟩ := hdvd
  have hκa : ∀ r : R, κ (algebraMap R (Localization.Away c) r) =
      algebraMap R (Localization.AtPrime 𝔭) r := fun r => by
    rw [← RingHom.comp_apply, hκ]
  refine ⟨algebraMap R _ (p x).1 * algebraMap R _ m * IsLocalization.Away.invSelf c, ?_⟩
  have hinv : algebraMap R (Localization.AtPrime 𝔭) c *
      κ (IsLocalization.Away.invSelf (S := Localization.Away c) c) = 1 := by
    rw [← hκa, ← map_mul, IsLocalization.Away.mul_invSelf, map_one]
  refine (?_ : _ = IsLocalization.mk' (Localization.AtPrime 𝔭) (p x).1 (p x).2).trans (hp x)
  rw [IsLocalization.eq_mk'_iff_mul_eq, map_mul, map_mul, hκa, hκa]
  calc algebraMap R (Localization.AtPrime 𝔭) (p x).1 * algebraMap R _ m *
        κ (IsLocalization.Away.invSelf c) * algebraMap R _ ((p x).2 : R)
      = algebraMap R (Localization.AtPrime 𝔭) (p x).1 *
        (algebraMap R _ (((p x).2 : R) * m) * κ (IsLocalization.Away.invSelf c)) := by
        rw [map_mul]; ring
    _ = algebraMap R (Localization.AtPrime 𝔭) (p x).1 := by
        rw [← hm, hinv, mul_one]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsetMemRangeLocalizationAwayOfDvdStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finset_mem_range_localization_away_of_dvd : ∀ (R : Type) [CommRing R] (𝔭 : Ideal R) [𝔭.IsPrime] (F : Finset (Localization.AtPrime 𝔭)), ∃ s ∉ 𝔭, ∀ (c : R), s ∣ c → ∀ κ : Localization.Away c →+* Localization.AtPrime 𝔭, κ.comp (algebraMap R (Localization.Away c)) = algebraMap R (Localization.AtPrime 𝔭) → ∀ x ∈ F, x ∈ κ.range := by
  first | exact @GlobalTheory.finset_mem_range_of_away_dvd | exact GlobalTheory.finset_mem_range_of_away_dvd | (intros; apply GlobalTheory.finset_mem_range_of_away_dvd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpreadOfPullbacks
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegelSpreadLocal

theorem exists_spread_of_pullbacks : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (R : Type) [CommRing R] [IsNoetherianRing R] (β : B →+* R) (𝔭 : Ideal R) [𝔭.IsPrime] (d : SiegPre g n ζ (spMap β)) (Y : Scheme.{0}) (sY : Y ⟶ Sp B) [LocallyOfFinitePresentation sY] (u : SiegPre g n ζ sY) (r₀ : R) (ι₀ : Localization.Away r₀ →+* Localization.AtPrime 𝔭) (h : Sp (Localization.Away r₀) ⟶ Y) (e : SiegPre g n ζ (spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β))), r₀ ∉ 𝔭 → ι₀.comp (algebraMap R (Localization.Away r₀)) = algebraMap R (Localization.AtPrime 𝔭) → h ≫ sY = spMap ((algebraMap R (Localization.Away r₀)).comp β) → SiegPB e d (spMap (algebraMap R (Localization.AtPrime 𝔭))) → SiegPB e u (spMap ι₀ ≫ h) → ∃ r ∉ 𝔭, ∃ (κ : Localization.Away r₀ →+* Localization.Away r) (d' : SiegPre g n ζ (spMap ((algebraMap R (Localization.Away r)).comp β))), κ.comp (algebraMap R (Localization.Away r₀)) = algebraMap R (Localization.Away r) ∧ SiegPB d' d (spMap (algebraMap R (Localization.Away r))) ∧ SiegPB d' u (spMap κ ≫ h) := by
  intro g n B _ ζ R _ _ β 𝔭 _ d Y sY _ u r₀ ι₀ h e hr₀ hι₀ hh hed heu
  obtain ⟨t₁, ht₁, hinj⟩ := GlobalTheory.T.localization_away_injective_atPrime_of_dvd R 𝔭
  have hrange := GlobalTheory.T.finset_mem_range_localization_away_of_dvd R 𝔭
  have hmono := GlobalTheory.T.localization_away_range_le_of_dvd_of_comp R (Localization.AtPrime 𝔭) (algebraMap R (Localization.AtPrime 𝔭))
  have spc : ∀ {A₁ A₂ A₃ : Type} [CommRing A₁] [CommRing A₂] [CommRing A₃] (a : A₁ →+* A₂) (b : A₂ →+* A₃),
      spMap (b.comp a) = spMap b ≫ spMap a := by
    intro A₁ A₂ A₃ _ _ _ a b
    simp only [spMap, ← Spec.map_comp]
    rfl
  have unit : ∀ x : R, x ∉ 𝔭 → IsUnit (algebraMap R (Localization.AtPrime 𝔭) x) := fun x hx =>
    IsLocalization.map_units (M := 𝔭.primeCompl) (Localization.AtPrime 𝔭) ⟨x, hx⟩
  have nmul : ∀ x y : R, x ∉ 𝔭 → y ∉ 𝔭 → x * y ∉ 𝔭 := fun x y hx hy hm =>
    ((inferInstance : 𝔭.IsPrime).mem_or_mem hm).elim hx hy
  let lam : ∀ c : R, c ∉ 𝔭 → Localization.Away c →+* Localization.AtPrime 𝔭 := fun c hc =>
    IsLocalization.Away.lift c (unit c hc)
  have lamc : ∀ (c : R) (hc : c ∉ 𝔭), (lam c hc).comp (algebraMap R (Localization.Away c)) =
      algebraMap R (Localization.AtPrime 𝔭) := fun c hc => IsLocalization.Away.lift_comp _ _

  have ht : r₀ * t₁ ∉ 𝔭 := nmul _ _ hr₀ ht₁
  let R₀ : Subring (Localization.AtPrime 𝔭) := (lam _ ht).range
  have memR₀ : ∀ x : R, algebraMap R (Localization.AtPrime 𝔭) x ∈ R₀ := fun x =>
    ⟨algebraMap R _ x, by rw [← RingHom.comp_apply, lamc _ ht]⟩
  let a₀ : R →+* R₀ := (algebraMap R (Localization.AtPrime 𝔭)).codRestrict R₀ memR₀
  obtain ⟨⟨d₀, hd₀⟩, -⟩ := GlobalTheory.siegPre_pullback g n B ζ (Sp R) (Sp R₀) (spMap β) (spMap a₀ ≫ spMap β)
    (spMap a₀) d rfl
  have hsub : R₀.subtype.comp a₀ = algebraMap R (Localization.AtPrime 𝔭) := RingHom.ext fun _ => rfl
  have hed₀ : SiegPB e d₀ (spMap R₀.subtype) :=
    GlobalTheory.SiegelPullComp.pb_cancel hd₀ (by rw [← spc, hsub]; exact hed)
  have memι₀ : ∀ x, ι₀ x ∈ R₀ := fun x =>
    hmono r₀ (r₀ * t₁) (dvd_mul_right _ _) ι₀ (lam _ ht) hι₀ (lamc _ ht) ⟨x, rfl⟩
  let j₀ : Localization.Away r₀ →+* R₀ := ι₀.codRestrict R₀ memι₀
  have hj₀ : R₀.subtype.comp j₀ = ι₀ := RingHom.ext fun _ => rfl
  have heu₀ : SiegPB e u (spMap R₀.subtype ≫ (spMap j₀ ≫ h)) := by
    rw [← Category.assoc, ← spc, hj₀]; exact heu
  obtain ⟨F, hF⟩ := GlobalTheory.T.siegelPullback_spreads_to_intermediate_subring g n B ζ (Localization.AtPrime 𝔭) R₀ _ d₀ Y sY u (spMap j₀ ≫ h) _ e hed₀ heu₀
  obtain ⟨s, hs, hsF⟩ := hrange F

  have hr : r₀ * t₁ * s ∉ 𝔭 := nmul _ _ ht hs
  let lr := lam _ hr
  let R₁ : Subring (Localization.AtPrime 𝔭) := lr.range
  have hle : R₀ ≤ R₁ := hmono _ _ (dvd_mul_right _ _) _ _ (lamc _ ht) (lamc _ hr)
  have hFR : (F : Set (Localization.AtPrime 𝔭)) ⊆ R₁ := fun x hx =>
    hsF _ (dvd_mul_left _ _) lr (lamc _ hr) x hx
  have hlinj : Function.Injective lr :=
    hinj _ ⟨r₀ * s, by ring⟩ lr (lamc _ hr)
  let er : Localization.Away (r₀ * t₁ * s) ≃+* R₁ :=
    RingEquiv.ofBijective lr.rangeRestrict ⟨fun x y hxy => hlinj (congrArg Subtype.val hxy), lr.rangeRestrict_surjective⟩
  have erv : ∀ x, (er x : Localization.AtPrime 𝔭) = lr x := fun _ => rfl
  obtain ⟨⟨d', hd'⟩, -⟩ := GlobalTheory.siegPre_pullback g n B ζ (Sp R) (Sp (Localization.Away (r₀ * t₁ * s)))
    (spMap β) (spMap ((algebraMap R (Localization.Away (r₀ * t₁ * s))).comp β))
    (spMap (algebraMap R (Localization.Away (r₀ * t₁ * s)))) d (spc _ _).symm
  obtain ⟨⟨d₁, hd₁⟩, -⟩ := GlobalTheory.siegPre_pullback g n B ζ _ (Sp R₁) _ _ (spMap er.toRingHom) d' rfl
  have hd₁₀ : SiegPB d₁ d₀ (spMap (Subring.inclusion hle)) := by
    refine GlobalTheory.SiegelPullComp.pb_cancel hd₀ ?_
    have e₁ : spMap (Subring.inclusion hle) ≫ spMap a₀ = spMap er.toRingHom ≫ spMap (algebraMap R (Localization.Away (r₀ * t₁ * s))) := by
      rw [← spc, ← spc]
      congr 1
      refine RingHom.ext fun x => Subtype.ext ?_
      show algebraMap R (Localization.AtPrime 𝔭) x = lr (algebraMap R _ x)
      rw [← RingHom.comp_apply, lamc _ hr]
    rw [e₁]
    exact GlobalTheory.SiegelPullComp.pb_comp hd' hd₁
  have hd₁u := hF R₁ hle hFR _ d₁ hd₁₀
  have hd'd₁ : SiegPB d' d₁ (spMap er.symm.toRingHom) := by
    refine GlobalTheory.SiegelPullComp.pb_cancel hd₁ ?_
    have e₂ : spMap er.symm.toRingHom ≫ spMap er.toRingHom = 𝟙 _ := by
      rw [← spc]
      have : er.symm.toRingHom.comp er.toRingHom = RingHom.id _ := RingHom.ext fun x => er.symm_apply_apply x
      rw [this]
      simp [spMap]
    rw [e₂]
    exact GlobalTheory.SiegelPullComp.pb_id d'
  let κ : Localization.Away r₀ →+* Localization.Away (r₀ * t₁ * s) :=
    er.symm.toRingHom.comp ((Subring.inclusion hle).comp j₀)
  refine ⟨r₀ * t₁ * s, hr, κ, d', ?_, hd', ?_⟩
  · refine RingHom.ext fun x => hlinj ?_
    rw [RingHom.comp_apply, RingHom.comp_apply]
    have hk : er (κ (algebraMap R _ x)) = (Subring.inclusion hle) (j₀ (algebraMap R _ x)) := er.apply_symm_apply _
    calc lr (κ (algebraMap R _ x)) = (er (κ (algebraMap R _ x)) : Localization.AtPrime 𝔭) := rfl
      _ = ((Subring.inclusion hle) (j₀ (algebraMap R _ x)) : Localization.AtPrime 𝔭) := congrArg Subtype.val hk
      _ = ι₀ (algebraMap R _ x) := rfl
      _ = algebraMap R (Localization.AtPrime 𝔭) x := by rw [← RingHom.comp_apply, hι₀]
      _ = lr (algebraMap R _ x) := by rw [← RingHom.comp_apply, lamc _ hr]
  · have e₃ : spMap κ ≫ h = spMap er.symm.toRingHom ≫ (spMap (Subring.inclusion hle) ≫ (spMap j₀ ≫ h)) := by
      simp only [κ, spc, Category.assoc]
    rw [e₃]
    exact GlobalTheory.SiegelPullComp.pb_comp hd₁u hd'd₁

end GlobalTheory.SiegelSpreadLocal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpreadOfPullbacksStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_spread_of_pullbacks_alt : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (R : Type) [CommRing R] [IsNoetherianRing R] (β : B →+* R) (𝔭 : Ideal R) [𝔭.IsPrime] (d : SiegPre g n ζ (spMap β)) (Y : Scheme.{0}) (sY : Y ⟶ Sp B) [LocallyOfFinitePresentation sY] (u : SiegPre g n ζ sY) (r₀ : R) (ι₀ : Localization.Away r₀ →+* Localization.AtPrime 𝔭) (h : Sp (Localization.Away r₀) ⟶ Y) (e : SiegPre g n ζ (spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β))), r₀ ∉ 𝔭 → ι₀.comp (algebraMap R (Localization.Away r₀)) = algebraMap R (Localization.AtPrime 𝔭) → h ≫ sY = spMap ((algebraMap R (Localization.Away r₀)).comp β) → SiegPB e d (spMap (algebraMap R (Localization.AtPrime 𝔭))) → SiegPB e u (spMap ι₀ ≫ h) → ∃ r ∉ 𝔭, ∃ (κ : Localization.Away r₀ →+* Localization.Away r) (d' : SiegPre g n ζ (spMap ((algebraMap R (Localization.Away r)).comp β))), κ.comp (algebraMap R (Localization.Away r₀)) = algebraMap R (Localization.Away r) ∧ SiegPB d' d (spMap (algebraMap R (Localization.Away r))) ∧ SiegPB d' u (spMap κ ≫ h) := by
  first | exact @GlobalTheory.SiegelSpreadLocal.exists_spread_of_pullbacks | exact GlobalTheory.SiegelSpreadLocal.exists_spread_of_pullbacks | (intros; apply GlobalTheory.SiegelSpreadLocal.exists_spread_of_pullbacks <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelClassifiedAtPrimeSpreadsBasicOpen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegSpread

theorem spread_point : ∀ (B : Type) [CommRing B] (X : Scheme.{0}) (q : X ⟶ Sp B) [LocallyOfFinitePresentation q] (R : Type) [CommRing R] (β : B →+* R) (𝔭 : Ideal R) [𝔭.IsPrime] (f₀ : Sp (Localization.AtPrime 𝔭) ⟶ X), f₀ ≫ q = spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β) → ∃ r ∉ 𝔭, ∃ (j : Localization.Away r →+* Localization.AtPrime 𝔭) (f : Sp (Localization.Away r) ⟶ X), j.comp (algebraMap R (Localization.Away r)) = algebraMap R (Localization.AtPrime 𝔭) ∧ f ≫ q = spMap ((algebraMap R (Localization.Away r)).comp β) ∧ spMap j ≫ f = f₀ := GlobalTheory.T.exists_away_spread_point_localization_atPrime

theorem spread_iso : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (R : Type) [CommRing R] [IsNoetherianRing R] (β : B →+* R) (𝔭 : Ideal R) [𝔭.IsPrime] (d : SiegPre g n ζ (spMap β)) (Y : Scheme.{0}) (sY : Y ⟶ Sp B) [LocallyOfFinitePresentation sY] (u : SiegPre g n ζ sY) (r₀ : R) (ι₀ : Localization.Away r₀ →+* Localization.AtPrime 𝔭) (h : Sp (Localization.Away r₀) ⟶ Y) (e : SiegPre g n ζ (spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β))), r₀ ∉ 𝔭 → ι₀.comp (algebraMap R (Localization.Away r₀)) = algebraMap R (Localization.AtPrime 𝔭) → h ≫ sY = spMap ((algebraMap R (Localization.Away r₀)).comp β) → SiegPB e d (spMap (algebraMap R (Localization.AtPrime 𝔭))) → SiegPB e u (spMap ι₀ ≫ h) → ∃ r ∉ 𝔭, ∃ (κ : Localization.Away r₀ →+* Localization.Away r) (d' : SiegPre g n ζ (spMap ((algebraMap R (Localization.Away r)).comp β))), κ.comp (algebraMap R (Localization.Away r₀)) = algebraMap R (Localization.Away r) ∧ SiegPB d' d (spMap (algebraMap R (Localization.Away r))) ∧ SiegPB d' u (spMap κ ≫ h) := GlobalTheory.T.exists_spread_of_pullbacks_alt

theorem spMap_comp_eq {A C D : Type} [CommRing A] [CommRing C] [CommRing D] (a : A →+* C) (b : C →+* D) :
    spMap b ≫ spMap a = spMap (b.comp a) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem classified_basicOpen : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (β : cycAway n →+* R) (c : SiegPre g n (zetaAway n) (spMap β)) (𝔭 : Ideal R) [𝔭.IsPrime], c.Principal → (∀ c' : SiegPre g n (zetaAway n) (spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β)), SiegPB c' c (spMap (algebraMap R (Localization.AtPrime 𝔭))) → ∃ f : Sp (Localization.AtPrime 𝔭) ⟶ F.X, f ≫ F.s = spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β) ∧ SiegPB c' F.univ f) → ∃ r ∉ 𝔭, ∀ c' : SiegPre g n (zetaAway n) (spMap ((algebraMap R (Localization.Away r)).comp β)), SiegPB c' c (spMap (algebraMap R (Localization.Away r))) → ∃ f : Sp (Localization.Away r) ⟶ F.X, f ≫ F.s = spMap ((algebraMap R (Localization.Away r)).comp β) ∧ SiegPB c' F.univ f := by
  intro g n hg hn hodd F R _ _ β c 𝔭 _ hc H
  obtain ⟨c₀, hc₀⟩ := (GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n (cycAway n) (cycAway n) (zetaAway n) (zetaAway n) (RingHom.id _)
    (Sp R) (Sp (Localization.AtPrime 𝔭)) (spMap β) (spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β))
    (spMap (algebraMap R (Localization.AtPrime 𝔭))) rfl (by rw [spMap_comp_eq, spMap_comp_eq, RingHom.comp_id])).1 c
  obtain ⟨f₀, hf₀s, hf₀⟩ := H c₀ hc₀
  haveI := F.smooth
  haveI : Smooth F.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s
  haveI : LocallyOfFinitePresentation F.s := inferInstance
  obtain ⟨r₀, hr₀, ι₀, f₁, hι₀, hf₁s, hf₁⟩ := spread_point (cycAway n) F.X F.s R β 𝔭 f₀ hf₀s
  obtain ⟨r, hr, κ, d', hκ, hd'c, hd'u⟩ := spread_iso g n (cycAway n) (zetaAway n) R β 𝔭 c F.X F.s F.univ r₀ ι₀ f₁ c₀
    hr₀ hι₀ hf₁s hc₀ (hf₁ ▸ hf₀)
  refine ⟨r, hr, fun c' hc' => ⟨spMap κ ≫ f₁, ?_, ?_⟩⟩
  · rw [Category.assoc, hf₁s, spMap_comp_eq, ← RingHom.comp_assoc, hκ]
  · have h₁ : SiegPB c' c (𝟙 _ ≫ spMap (algebraMap R (Localization.Away r))) := by rwa [Category.id_comp]
    have h₂ := GlobalTheory.SiegelPullComp.pb_cancel hd'c h₁
    have h₃ := GlobalTheory.SiegelPullComp.pb_comp hd'u h₂
    rwa [Category.id_comp] at h₃

end GlobalTheory.SiegSpread
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelClassifiedAtPrimeSpreadsBasicOpenStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelClassified_at_prime_spreads_basicOpen : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (β : cycAway n →+* R) (c : SiegPre g n (zetaAway n) (spMap β)) (𝔭 : Ideal R) [𝔭.IsPrime], c.Principal → (∀ c' : SiegPre g n (zetaAway n) (spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β)), SiegPB c' c (spMap (algebraMap R (Localization.AtPrime 𝔭))) → ∃ f : Sp (Localization.AtPrime 𝔭) ⟶ F.X, f ≫ F.s = spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β) ∧ SiegPB c' F.univ f) → ∃ r ∉ 𝔭, ∀ c' : SiegPre g n (zetaAway n) (spMap ((algebraMap R (Localization.Away r)).comp β)), SiegPB c' c (spMap (algebraMap R (Localization.Away r))) → ∃ f : Sp (Localization.Away r) ⟶ F.X, f ≫ F.s = spMap ((algebraMap R (Localization.Away r)).comp β) ∧ SiegPB c' F.univ f := by
  first | exact @GlobalTheory.SiegSpread.classified_basicOpen | exact GlobalTheory.SiegSpread.classified_basicOpen | (intros; apply GlobalTheory.SiegSpread.classified_basicOpen <;> assumption)
end

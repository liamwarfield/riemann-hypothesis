module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSystemMovedToAffineOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorialMulRankLeDegreeOfIndepSmallSections
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SameGenericFibreChainRescaledDeeperRealisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingConditionLocusIsClopen

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupRescaleIntoLocalRingClassicalTrait
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupRescaleIntoLocalRingClassicalTrait
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.GLiftRechart

theorem main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X.M.s → ∀ (ε : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)), IsDiagEnd F W X.ρ.P X.u ε → ∀ (p : ℕ) [Fact p.Prime] (z : X.M.Z) (c : CTrait X p z), ∃ (c₀ : X.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X.o₁ X.Ω₁) (fg : R'.FG) (frac : ∀ x : X.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X.S.th x ∈ R') (hev : ∀ x k, c₀ * X.S.ev x k ∈ R') (ρ' : (X.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)), Same X.ρ ε ρ' ε' (fun x => x) (RingHom.id _) ∧ ρ'.i₀ = X.ρ.i₀ ∧ R' ≤ X.M.O ((gPt p ≫ c.y) (closedPoint (PadicAlgCl p))) ∧ ∃ y₀ : R' →+* PadicAlgCl p, (∀ a : R', y₀ a = X.M.val (gPt p ≫ c.y) a) ∧ ∀ a : X.o₁, ‖y₀ (algebraMap X.o₁ R' a)‖ ≤ 1 := by
  intro g n F W Z i X hg hn ho himm he8 hth hproj ε hε p _ z c
  set w : X.M.Z := (gPt p ≫ c.y) (IsLocalRing.closedPoint (PadicAlgCl p)) with hw
  have hwr : X.π w ∈ Set.range i := by
    refine ⟨(spMap c.ι ≫ c.T.y) (IsLocalRing.closedPoint (PadicAlgCl p)), ?_⟩
    have h := congrArg (fun f => f (IsLocalRing.closedPoint (PadicAlgCl p))) c.comm
    rw [hw]
    exact h.symm
  obtain ⟨U, c₀, hc, fg, frac, hth', hev, ρ', ε', u', hUa, hwU, hUi, hSame, hi₀, hdiag, hcomp⟩ :=
    GlobalTheory.T.exists_thetaSystem_moved_to_affineOpen g n F W Z i X hg hn ho himm he8 hth hproj ε hε w hwr
  have hle : X.M.ringOn (U : Set X.M.Z) ≤ X.M.O w := RatModel.ringOn_le_O hwU
  refine ⟨c₀, hc, X.M.ringOn (U : Set X.M.Z), fg, frac, hth', hev, ρ', ε', hSame, hi₀, hle, ?_⟩
  refine ⟨(X.M.valHom (gPt p ≫ c.y) w (RatModel.range_eq_singleton _ _)).comp
    (Subalgebra.inclusion hle).toRingHom, fun a => rfl, fun a => ?_⟩
  have hmem : algebraMap X.o₁ X.Ω₁ a ∈ X.M.O z := Subalgebra.algebraMap_mem _ a
  have h1 := c.norm_val_le ((X.M.stalkEquiv z).symm ⟨_, hmem⟩)
  simp only [CTrait.val] at h1
  rw [← RatModel.coe_stalkEquiv, RingEquiv.apply_symm_apply] at h1
  simpa using h1

end GlobalTheory.Poinc.GLiftRechart
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupRescaleIntoLocalRingClassicalTraitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSetup_rescale_into_localRing_classicalTrait : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X.M.s → ∀ (ε : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)), IsDiagEnd F W X.ρ.P X.u ε → ∀ (p : ℕ) [Fact p.Prime] (z : X.M.Z) (c : CTrait X p z), ∃ (c₀ : X.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X.o₁ X.Ω₁) (fg : R'.FG) (frac : ∀ x : X.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X.S.th x ∈ R') (hev : ∀ x k, c₀ * X.S.ev x k ∈ R') (ρ' : (X.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)), Same X.ρ ε ρ' ε' (fun x => x) (RingHom.id _) ∧ ρ'.i₀ = X.ρ.i₀ ∧ R' ≤ X.M.O ((gPt p ≫ c.y) (closedPoint (PadicAlgCl p))) ∧ ∃ y₀ : R' →+* PadicAlgCl p, (∀ a : R', y₀ a = X.M.val (gPt p ≫ c.y) a) ∧ ∀ a : X.o₁, ‖y₀ (algebraMap X.o₁ R' a)‖ ≤ 1 := by
  first | exact @GlobalTheory.Poinc.GLiftRechart.main | exact GlobalTheory.Poinc.GLiftRechart.main | (intros; apply GlobalTheory.Poinc.GLiftRechart.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedModelTransportDeeperThetaSetup
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisationsSameGenericFibreAgreeAtPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisationsSameGenericFibreAgreeAtPoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Points
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Special

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

section Model

variable {o Ω o' Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [CommRing o'] [Field Ω'] [Algebra o' Ω']
  [Algebra Ω Ω'] {M : RatModel o Ω} {M' : RatModel o' Ω'} {f : M'.Z ⟶ M.Z}

theorem valF_app_of (hf : M'.pt ≫ f = spMap (algebraMap Ω Ω') ≫ M.pt) {U : M.Z.Opens}
    (hU : (U : Set M.Z).Nonempty) (a : Γ(M.Z, U)) :
    valF M'.pt (f ⁻¹ᵁ U) (f.app U a) = algebraMap Ω Ω' (valF M.pt U a) := by
  refine (valR_comp M'.pt f U a).symm.trans ?_
  rw [hf]
  exact valR_spMap_comp _ M.pt U (M.top_le_preimage_pt hU) a

theorem map_mem_O_of (hf : M'.pt ≫ f = spMap (algebraMap Ω Ω') ≫ M.pt) {z : M'.Z} {x : Ω}
    (hx : x ∈ M.O (f z)) : algebraMap Ω Ω' x ∈ M'.O z := by
  obtain ⟨U, a, hz, rfl⟩ := hx
  exact ⟨f ⁻¹ᵁ U, f.app U a, hz, valF_app_of hf ⟨_, hz⟩ a⟩

theorem val_comp_of (hf : M'.pt ≫ f = spMap (algebraMap Ω Ω') ≫ M.pt) {K : Type} [Field K] (y : Sp K ⟶ M'.Z)
    (w : Sp K) {x : Ω} (hx : x ∈ M.O (f (y w))) : M.val (y ≫ f) x = M'.val y (algebraMap Ω Ω' x) := by
  obtain ⟨U, a, hz, rfl⟩ := hx
  have h1 : Set.range y ⊆ (f ⁻¹ᵁ U : M'.Z.Opens) := by
    rw [RatModel.range_eq_singleton y w, Set.singleton_subset_iff]
    exact hz
  rw [RatModel.val_eq h1 (valF_app_of hf ⟨_, hz⟩ a), RatModel.val_valF (U := U) (by rintro _ ⟨w', rfl⟩; exact h1 ⟨w', rfl⟩)]
  exact valR_comp y f U a

end Model

section Pts

variable {K C : Type} [CommRing K] [CommRing C] {A : Over (Sp K)}

theorem pt_iff_eq {R : Type} [CommRing R] {G : Over (Sp R)} {h : R →+* K} {a : A.left ⟶ G.left}
    (c : IsPullback a A.hom G.hom (spMap h)) (j : K →+* C) {s : Sp R ⟶ G.left} {w : Sp K ⟶ A.left}
    (hw : w ≫ A.hom = 𝟙 _) (hs : w ≫ a = spMap h ≫ s) (x : Sp C ⟶ A.left) (hx : x ≫ A.hom = spMap j) :
    x ≫ a = spMap (j.comp h) ≫ s ↔ x = spMap j ≫ w := by
  rw [spMap_comp', Category.assoc, ← hs]
  constructor
  · intro e
    exact c.hom_ext (by rw [e, Category.assoc]) (by rw [hx, Category.assoc, hw, Category.comp_id])
  · intro e
    rw [e, Category.assoc]

theorem end_iff_eq {S : Scheme.{0}} {G : Over S} {f : Sp K ⟶ S} {a : A.left ⟶ G.left}
    (c : IsPullback a A.hom G.hom f) {ε : G.left ⟶ G.left} {e : A.left ⟶ A.left} (he : e ≫ A.hom = A.hom)
    (he' : e ≫ a = a ≫ ε) {T : Scheme.{0}} (x x' : T ⟶ A.left) (hx : x' ≫ A.hom = x ≫ A.hom) :
    x' ≫ a = x ≫ a ≫ ε ↔ x' = x ≫ e := by
  rw [← he', ← Category.assoc]
  constructor
  · intro k
    exact c.hom_ext k (by rw [Category.assoc, he, hx])
  · intro k
    rw [k]

end Pts

end GlobalTheory.Poinc.Special

theorem GlobalTheory.Poinc.Special.specialise_sameAt : ∀ (R₁ R₂ B K M Γ : Type) [CommRing R₁] [CommRing R₂] [CommRing B] [CommRing K] (P₁ : PolAV (Sp R₁)) (P₂ : PolAV (Sp R₂)) (f₁ : R₁ →+* B) (f₂ : R₂ →+* B) (e₁ : M → (P₁.A ⟶ P₁.A)) (e₂ : M → (P₂.A ⟶ P₂.A)) (t₁ : Γ → (baseOver (Sp R₁) ⟶ P₁.A)) (t₂ : Γ → (baseOver (Sp R₂) ⟶ P₂.A)), SameAt P₁ P₂ f₁ f₂ e₁ e₂ t₁ t₂ → (∀ τ : B →+* B, τ.comp f₂ = f₂ → τ = RingHom.id B) → ∀ (v : B →+* K) (A₁ : PolAV (Sp K)) (a₁ : A₁.A.left ⟶ P₁.A.left), IsGrpPullback A₁.A P₁.A (spMap (v.comp f₁)) a₁ → LBIso A₁.L (P₁.L.pull a₁) → ∃ φ₂ : A₁.A.left ⟶ P₂.A.left, IsGrpPullback A₁.A P₂.A (spMap (v.comp f₂)) φ₂ ∧ LBIso A₁.L (P₂.L.pull φ₂) ∧ (∀ E, ∃ e : A₁.A.left ⟶ A₁.A.left, e ≫ A₁.A.hom = A₁.A.hom ∧ e ≫ a₁ = a₁ ≫ (e₁ E).left ∧ e ≫ φ₂ = φ₂ ≫ (e₂ E).left) ∧ ∀ x, ∃ w : Sp K ⟶ A₁.A.left, w ≫ A₁.A.hom = 𝟙 _ ∧ w ≫ a₁ = spMap (v.comp f₁) ≫ (t₁ x).left ∧ w ≫ φ₂ = spMap (v.comp f₂) ≫ (t₂ x).left := by
  intro R₁ R₂ B K M Γ _ _ _ _ P₁ P₂ f₁ f₂ e₁ e₂ t₁ t₂ hS hrig v A₁ a₁ ha₁ hL₁
  obtain ⟨P, b₁, b₂, hb₁, hb₂, hLb₁, hLb₂, hε, ht⟩ := hS
  have hv₁ : spMap (v.comp f₁) = spMap v ≫ spMap f₁ := GlobalTheory.Poinc.Special.spMap_comp' f₁ v
  have hv₂ : spMap (v.comp f₂) = spMap v ≫ spMap f₂ := GlobalTheory.Poinc.Special.spMap_comp' f₂ v
  have sq : a₁ ≫ P₁.A.hom = (A₁.A.hom ≫ spMap v) ≫ spMap f₁ := by
    rw [ha₁.1.w, hv₁, Category.assoc]
  let b : A₁.A.left ⟶ P.A.left := hb₁.1.lift a₁ (A₁.A.hom ≫ spMap v) sq
  have hb_a : b ≫ b₁ = a₁ := hb₁.1.lift_fst _ _ _
  have hb_s : b ≫ P.A.hom = A₁.A.hom ≫ spMap v := hb₁.1.lift_snd _ _ _
  have hbP : IsGrpPullback A₁.A P.A (spMap v) b :=
    IsGrpPullback.cancel hb₁ (ha₁.congr hv₁ hb_a.symm) hb_s
  refine ⟨b ≫ b₂, (hbP.comp hb₂).congr hv₂.symm rfl, ?_, fun E => ?_, fun x => ?_⟩
  · have i1 : LBIso (P.L.pull b) (P₁.L.pull a₁) := GlobalTheory.PolDeg.lbIso_pull_comp hLb₁ b hb_a.symm
    have i2 : LBIso (P.L.pull b) (P₂.L.pull (b ≫ b₂)) := GlobalTheory.PolDeg.lbIso_pull_comp hLb₂ b rfl
    exact (hL₁.trans A₁.isLB (pull_isLB P₁.isLB _) (pull_isLB P.isLB _) i1.symm).trans A₁.isLB
      (pull_isLB P.isLB _) (pull_isLB P₂.isLB _) i2
  · obtain ⟨eP, heP₁, heP₂⟩ := hε E
    have sqe : (a₁ ≫ (e₁ E).left) ≫ P₁.A.hom = A₁.A.hom ≫ spMap (v.comp f₁) := by
      rw [Category.assoc, Over.w (e₁ E), ha₁.1.w]
    let e : A₁.A.left ⟶ A₁.A.left := ha₁.1.lift (a₁ ≫ (e₁ E).left) A₁.A.hom sqe
    have he₁ : e ≫ a₁ = a₁ ≫ (e₁ E).left := ha₁.1.lift_fst _ _ _
    have he : e ≫ A₁.A.hom = A₁.A.hom := ha₁.1.lift_snd _ _ _
    have heb : e ≫ b = b ≫ eP.left := hb₁.1.hom_ext
      (by rw [Category.assoc, hb_a, he₁, Category.assoc, heP₁, ← Category.assoc, hb_a])
      (by rw [Category.assoc, hb_s, ← Category.assoc, he, Category.assoc, Over.w eP, hb_s])
    exact ⟨e, he, he₁, by rw [← Category.assoc, heb, Category.assoc, heP₂, Category.assoc]⟩
  · obtain ⟨w, hw₁, hw₂⟩ := ht x
    have hσ : spMap ((Spec.preimage (w ≫ P.A.hom)).hom) = w ≫ P.A.hom := by
      rw [spMap, CommRingCat.ofHom_hom, Spec.map_preimage]
    have hσ₂ : (w ≫ P.A.hom) ≫ spMap f₂ = spMap f₂ := by
      rw [Category.assoc, ← hb₂.1.w, ← Category.assoc, hw₂, Category.assoc, Over.w (t₂ x)]
      exact Category.comp_id _
    have hτ : (Spec.preimage (w ≫ P.A.hom)).hom.comp f₂ = f₂ := by
      have h1 : spMap ((Spec.preimage (w ≫ P.A.hom)).hom.comp f₂) = spMap f₂ := by
        rw [GlobalTheory.Poinc.Special.spMap_comp', hσ, hσ₂]
      exact congrArg CommRingCat.Hom.hom (Spec.map_inj.1 h1)
    have hwP : w ≫ P.A.hom = 𝟙 _ := by
      rw [← hσ, hrig _ hτ]
      exact Spec.map_id _
    have sqt : (spMap (v.comp f₁) ≫ (t₁ x).left) ≫ P₁.A.hom = 𝟙 _ ≫ spMap (v.comp f₁) := by
      rw [Category.assoc, Over.w (t₁ x), Category.id_comp]
      exact Category.comp_id _
    let w' : Sp K ⟶ A₁.A.left := ha₁.1.lift (spMap (v.comp f₁) ≫ (t₁ x).left) (𝟙 _) sqt
    have hw'₁ : w' ≫ a₁ = spMap (v.comp f₁) ≫ (t₁ x).left := ha₁.1.lift_fst _ _ _
    have hw' : w' ≫ A₁.A.hom = 𝟙 _ := ha₁.1.lift_snd _ _ _
    have hw'b : w' ≫ b = spMap v ≫ w := hb₁.1.hom_ext
      (by rw [Category.assoc, hb_a, hw'₁, hv₁, Category.assoc, Category.assoc, hw₁])
      (by rw [Category.assoc, hb_s, ← Category.assoc, hw', Category.id_comp, Category.assoc, hwP,
        Category.comp_id])
    exact ⟨w', hw', hw'₁, by rw [← Category.assoc, hw'b, Category.assoc, hw₂, hv₂, Category.assoc]⟩


open GlobalTheory.Poinc.Special in
theorem GlobalTheory.Poinc.special_transport : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y)
  (c₀ : X₁.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X₁.o₁ X₁.Ω₁) (fg : R'.FG) (frac : ∀ x : X₁.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X₁.S.th x ∈ R') (hev : ∀ x k, c₀ * X₁.S.ev x k ∈ R') (ρ' : (X₁.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)), R' ≤ X₁.M.O ((gPt p ≫ c.y) (closedPoint (PadicAlgCl p))) → ∀ (y₀ : R' →+* PadicAlgCl p), (∀ a : R', y₀ a = X₁.M.val (gPt p ≫ c.y) a) →
  ∀ (c₂ : D.X.Ω₁) (hc₂ : c₂ ≠ 0) (R₂ : Subalgebra D.X.o₁ D.X.Ω₁) (fg₂ : R₂.FG) (frac₂ : ∀ x : D.X.Ω₁, ∃ a ∈ R₂, ∃ b ∈ R₂, x = a / b) (hth₂ : ∀ x, c₂ * D.X.S.th x ∈ R₂) (hev₂ : ∀ x k, c₂ * D.X.S.ev x k ∈ R₂) (ρ₂ : (D.X.S.rechart c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂).Real) (ε₂ : Matrix (Fin 8) (Fin 8) ℤ → (ρ₂.P.A ⟶ ρ₂.P.A)), Same ρ' ε' ρ₂ ε₂ (fun a => D.lab a) (algebraMap X₁.Ω₁ D.X.Ω₁) → R₂ ≤ D.X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))) → ∀ (y₂ : R₂ →+* PadicAlgCl p), (∀ a : R₂, y₂ a = D.X.M.val (gPt p ≫ y) a) →
  ∀ (K : Type) [Field K] (j : K →+* PadicAlgCl p) (f' : R' →+* K), j.comp f' = y₀ → (∀ a ∈ D.X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))), D.X.M.val (gPt p ≫ y) a ∈ j.range) →
  ∀ (A₁ : PolAV (Sp K)) (a₁ : A₁.A.left ⟶ ρ'.P.A.left), IsGrpPullback A₁.A ρ'.P.A (spMap f') a₁ → LBIso A₁.L (ρ'.P.L.pull a₁) →
  ∃ (f₂ : R₂ →+* K) (φ₂ : A₁.A.left ⟶ ρ₂.P.A.left), j.comp f₂ = y₂ ∧ IsGrpPullback A₁.A ρ₂.P.A (spMap f₂) φ₂ ∧ LBIso A₁.L (ρ₂.P.L.pull φ₂) ∧
    (∀ (x : Sp (PadicAlgCl p) ⟶ A₁.A.left) (a : X₁.S.Gam), x ≫ A₁.A.hom = spMap j → (x ≫ φ₂ = spMap y₂ ≫ (ρ₂.pt (D.lab a)).left ↔ x ≫ a₁ = spMap y₀ ≫ (ρ'.pt a).left)) ∧
    (∀ (x x' : Sp (PadicAlgCl p) ⟶ A₁.A.left) (E : Matrix (Fin 8) (Fin 8) ℤ), x ≫ A₁.A.hom = spMap j → x' ≫ A₁.A.hom = spMap j → (x' ≫ φ₂ = x ≫ φ₂ ≫ (ε₂ E).left ↔ x' ≫ a₁ = x ≫ a₁ ≫ (ε' E).left)) := by
  intro g n F W Z i X₁ _ _ _ _ _ _ _ ε₁ _ D p _ z₁ c y h c₀ hc R' fg frac hth hev ρ' ε' hR' y₀ hy₀ c₂ hc₂ R₂ fg₂ frac₂
    hth₂ hev₂ ρ₂ ε₂ hsame hR₂ y₂ hy₂ K _ j f' hf' hval A₁ a₁ ha₁ hL₁

  set x₂ := (gPt p ≫ y) (closedPoint (PadicAlgCl p)) with hx₂
  have hx₁ : (gPt p ≫ c.y) (closedPoint (PadicAlgCl p)) = D.q x₂ := by
    rw [← h, ← Category.assoc]; rfl
  haveI : IsDedekindDomain D.X.o₁ := ArithBase.ded (Ω := D.X.Ω₁)
  haveI : IsNoetherianRing (D.X.M.O x₂) := D.X.M.isNoetherianRing_O x₂
  haveI : IsIntegrallyClosed (D.X.M.O x₂) := haveI := D.X.normal; RatModel.isIntegrallyClosed_O (GlobalTheory.IsNormalScheme.pred _) x₂
  have hmem : ∀ a : R', algebraMap X₁.Ω₁ D.X.Ω₁ a ∈ D.X.M.O x₂ := fun a =>
    map_mem_O_of D.gen (hx₁ ▸ hR' a.2)
  let g₁ : R' →+* D.X.M.O x₂ := ((algebraMap X₁.Ω₁ D.X.Ω₁).comp R'.val.toRingHom).codRestrict _ hmem
  let g₂ : R₂ →+* D.X.M.O x₂ := (Subalgebra.inclusion hR₂).toRingHom
  have e₁ : (algebraMap (D.X.M.O x₂) D.X.Ω₁).comp g₁ = (algebraMap X₁.Ω₁ D.X.Ω₁).comp R'.val.toRingHom :=
    RingHom.ext fun _ => rfl
  have e₂ : (algebraMap (D.X.M.O x₂) D.X.Ω₁).comp g₂ = R₂.val.toRingHom := RingHom.ext fun _ => rfl

  have hS₀ : SameAt ρ'.P ρ₂.P ((algebraMap (D.X.M.O x₂) D.X.Ω₁).comp g₁) ((algebraMap (D.X.M.O x₂) D.X.Ω₁).comp g₂)
      ε' ε₂ ρ'.pt (fun a => ρ₂.pt (D.lab a)) := by
    rw [e₁, e₂]
    obtain ⟨P₀, a, a', ε₀, h1, h2, h3, h4, h5, h6⟩ := hsame
    exact ⟨P₀, a, a', h1, h2, h3, h4, fun E => ⟨ε₀ E, (h5 E).1, (h5 E).2⟩, h6⟩
  have hSO := GlobalTheory.Poinc.sameAt_of_generic _ _ _ _ _ _ ρ'.P ρ₂.P g₁ g₂ ε' ε₂ _ _ hS₀

  let vO : D.X.M.O x₂ →+* PadicAlgCl p :=
    D.X.M.valHom (gPt p ≫ y) x₂ (RatModel.range_eq_singleton _ _)
  have hvr : ∀ a, vO a ∈ j.range := fun a => hval a a.2
  let jE : K ≃+* j.range := RingEquiv.ofBijective j.rangeRestrict ⟨fun a b hab => j.injective
    (congrArg Subtype.val hab), j.rangeRestrict_surjective⟩
  let v : D.X.M.O x₂ →+* K := jE.symm.toRingHom.comp (vO.codRestrict j.range hvr)
  have hjv : ∀ a, j (v a) = vO a := fun a => congrArg Subtype.val (jE.apply_symm_apply (vO.codRestrict j.range hvr a))
  have hf₂ : j.comp (v.comp g₂) = y₂ := RingHom.ext fun a => (hjv _).trans (hy₂ a).symm
  have hf'v : f' = v.comp g₁ := RingHom.ext fun a => j.injective <| by
    rw [← RingHom.comp_apply j f', hf', hy₀ a, RingHom.comp_apply, hjv]
    show X₁.M.val (gPt p ≫ c.y) a = D.X.M.val (gPt p ≫ y) (algebraMap X₁.Ω₁ D.X.Ω₁ a)
    rw [← h, ← Category.assoc]
    have hm : (a : X₁.Ω₁) ∈ X₁.M.O (D.q ((gPt p ≫ y) (closedPoint (PadicAlgCl p)))) := hx₁ ▸ hR' a.2
    exact val_comp_of D.gen (gPt p ≫ y) (closedPoint (PadicAlgCl p)) hm
  subst hf'v
  have hrig : ∀ τ : D.X.M.O x₂ →+* D.X.M.O x₂, τ.comp g₂ = g₂ → τ = RingHom.id _ := by
    intro τ hτ
    refine RingHom.ext fun x => ?_
    show τ x = x
    obtain ⟨a, ha, b, hb, hab⟩ := frac₂ x
    have hτa : ∀ r : R₂, τ (g₂ r) = g₂ r := fun r => RingHom.congr_fun hτ r
    by_cases hb0 : b = 0
    · have hx0 : x = 0 := Subtype.ext (by rw [hab, hb0, div_zero]; rfl)
      rw [hx0, map_zero]
    · have key : g₂ ⟨b, hb⟩ * x = g₂ ⟨a, ha⟩ := Subtype.ext (by
        show b * (x : D.X.Ω₁) = a
        rw [hab, mul_div_cancel₀ _ hb0])
      have h0 : g₂ ⟨b, hb⟩ ≠ 0 := fun h0 => hb0 (congrArg Subtype.val h0)
      have key' := congrArg τ key
      rw [map_mul, hτa, hτa, ← key] at key'
      exact mul_left_cancel₀ h0 key'
  obtain ⟨φ₂, hφ₂, hL₂, hε, ht⟩ := (GlobalTheory.Poinc.Special.specialise_sameAt) _ _ _ _ _ _ ρ'.P ρ₂.P g₁ g₂ ε' ε₂ _ _ hSO hrig v A₁ a₁ ha₁ hL₁
  refine ⟨v.comp g₂, φ₂, hf₂, hφ₂, hL₂, fun x a hx => ?_, fun x x' E hx hx' => ?_⟩
  · obtain ⟨w, hw, hw₁, hw₂⟩ := ht a
    rw [← hf₂, ← hf', pt_iff_eq hφ₂.1 j hw hw₂ x hx, pt_iff_eq ha₁.1 j hw hw₁ x hx]
  · obtain ⟨e, he, he₁, he₂⟩ := hε E
    rw [end_iff_eq hφ₂.1 he he₂ x x' (hx'.trans hx.symm), end_iff_eq ha₁.1 he he₁ x x' (hx'.trans hx.symm)]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisationsSameGenericFibreAgreeAtPointsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realisations_same_genericFibre_agree_at_points : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y)
  (c₀ : X₁.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X₁.o₁ X₁.Ω₁) (fg : R'.FG) (frac : ∀ x : X₁.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X₁.S.th x ∈ R') (hev : ∀ x k, c₀ * X₁.S.ev x k ∈ R') (ρ' : (X₁.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)), R' ≤ X₁.M.O ((gPt p ≫ c.y) (closedPoint (PadicAlgCl p))) → ∀ (y₀ : R' →+* PadicAlgCl p), (∀ a : R', y₀ a = X₁.M.val (gPt p ≫ c.y) a) →
  ∀ (c₂ : D.X.Ω₁) (hc₂ : c₂ ≠ 0) (R₂ : Subalgebra D.X.o₁ D.X.Ω₁) (fg₂ : R₂.FG) (frac₂ : ∀ x : D.X.Ω₁, ∃ a ∈ R₂, ∃ b ∈ R₂, x = a / b) (hth₂ : ∀ x, c₂ * D.X.S.th x ∈ R₂) (hev₂ : ∀ x k, c₂ * D.X.S.ev x k ∈ R₂) (ρ₂ : (D.X.S.rechart c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂).Real) (ε₂ : Matrix (Fin 8) (Fin 8) ℤ → (ρ₂.P.A ⟶ ρ₂.P.A)), Same ρ' ε' ρ₂ ε₂ (fun a => D.lab a) (algebraMap X₁.Ω₁ D.X.Ω₁) → R₂ ≤ D.X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))) → ∀ (y₂ : R₂ →+* PadicAlgCl p), (∀ a : R₂, y₂ a = D.X.M.val (gPt p ≫ y) a) →
  ∀ (K : Type) [Field K] (j : K →+* PadicAlgCl p) (f' : R' →+* K), j.comp f' = y₀ → (∀ a ∈ D.X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))), D.X.M.val (gPt p ≫ y) a ∈ j.range) →
  ∀ (A₁ : PolAV (Sp K)) (a₁ : A₁.A.left ⟶ ρ'.P.A.left), IsGrpPullback A₁.A ρ'.P.A (spMap f') a₁ → LBIso A₁.L (ρ'.P.L.pull a₁) →
  ∃ (f₂ : R₂ →+* K) (φ₂ : A₁.A.left ⟶ ρ₂.P.A.left), j.comp f₂ = y₂ ∧ IsGrpPullback A₁.A ρ₂.P.A (spMap f₂) φ₂ ∧ LBIso A₁.L (ρ₂.P.L.pull φ₂) ∧
    (∀ (x : Sp (PadicAlgCl p) ⟶ A₁.A.left) (a : X₁.S.Gam), x ≫ A₁.A.hom = spMap j → (x ≫ φ₂ = spMap y₂ ≫ (ρ₂.pt (D.lab a)).left ↔ x ≫ a₁ = spMap y₀ ≫ (ρ'.pt a).left)) ∧
    (∀ (x x' : Sp (PadicAlgCl p) ⟶ A₁.A.left) (E : Matrix (Fin 8) (Fin 8) ℤ), x ≫ A₁.A.hom = spMap j → x' ≫ A₁.A.hom = spMap j → (x' ≫ φ₂ = x ≫ φ₂ ≫ (ε₂ E).left ↔ x' ≫ a₁ = x ≫ a₁ ≫ (ε' E).left)) := by
  first | exact @GlobalTheory.Poinc.special_transport | exact GlobalTheory.Poinc.special_transport | (intros; apply GlobalTheory.Poinc.special_transport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedModelTransportDeeperThetaSetup
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.GLift

theorem transport : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y)
  (c₀ : X₁.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X₁.o₁ X₁.Ω₁) (fg : R'.FG) (frac : ∀ x : X₁.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X₁.S.th x ∈ R') (hev : ∀ x k, c₀ * X₁.S.ev x k ∈ R') (ρ' : (X₁.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)), Same X₁.ρ ε₁ ρ' ε' (fun x => x) (RingHom.id _) → ρ'.i₀ = X₁.ρ.i₀ → R' ≤ X₁.M.O ((gPt p ≫ c.y) (closedPoint (PadicAlgCl p))) → ∀ (y₀ : R' →+* PadicAlgCl p), (∀ a : R', y₀ a = X₁.M.val (gPt p ≫ c.y) a) → ∀ (u : ρ'.UTest p y₀)
  (c₂ : D.X.Ω₁) (hc₂ : c₂ ≠ 0) (R₂ : Subalgebra D.X.o₁ D.X.Ω₁) (fg₂ : R₂.FG) (frac₂ : ∀ x : D.X.Ω₁, ∃ a ∈ R₂, ∃ b ∈ R₂, x = a / b) (hth₂ : ∀ x, c₂ * D.X.S.th x ∈ R₂) (hev₂ : ∀ x k, c₂ * D.X.S.ev x k ∈ R₂) (ρ₂ : (D.X.S.rechart c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂).Real) (ε₂ : Matrix (Fin 8) (Fin 8) ℤ → (ρ₂.P.A ⟶ ρ₂.P.A)), Same D.X.ρ D.ε ρ₂ ε₂ (fun x => x) (RingHom.id _) → ρ₂.i₀ = D.X.ρ.i₀ → R₂ ≤ D.X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))) → ∀ (y₂ : R₂ →+* PadicAlgCl p), (∀ a : R₂, y₂ a = D.X.M.val (gPt p ≫ y) a) →
  ∃ (u₂ : ρ₂.UTest p y₂) (e : u₂.D.toPre.X ≃+ u.D.toPre.X) (T : (TFK (R := u₂.V) (PadicAlgCl p) ⟶ u₂.A.A) ≃ (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)),
    (∀ χ r, u.PsiNorm (e χ) r → u₂.PsiNorm χ r) ∧
    (∀ x₂ a, x₂.left ≫ u₂.φ = spMap y₂ ≫ (ρ₂.pt (D.lab a)).left ↔ (T x₂).left ≫ u.φ = spMap y₀ ≫ (ρ'.pt a).left) ∧
    (∀ x₂ x₂' E, x₂'.left ≫ u₂.φ = x₂.left ≫ u₂.φ ≫ (ε₂ E).left → (T x₂').left ≫ u.φ = (T x₂).left ≫ u.φ ≫ (ε' E).left) ∧
    (∀ (m : ℕ) (pk₂ : QkPt u₂.D.toPre (PadicAlgCl p) m) x₂, 1 ≤ m → QkToAkU u₂.U.toUnifPre (PadicAlgCl p) m pk₂ x₂ → ∃ pk : QkPt u.D.toPre (PadicAlgCl p) m, pk.y = e pk₂.y ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk (T x₂)) ∧
    (∀ (m : ℕ) (pk : QkPt u.D.toPre (PadicAlgCl p) m) x, 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → ∃ pk₂ : QkPt u₂.D.toPre (PadicAlgCl p) m, e pk₂.y = pk.y ∧ QkToAkU u₂.U.toUnifPre (PadicAlgCl p) m pk₂ (T.symm x)) := by
  intro g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag D p _ z₁ c y h c₀ hc R' fg frac hth' hev ρ' ε' hS hi hR y₀ hy₀ u c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂ ρ₂ ε₂ hS₂ hi₂ hR₂ y₂ hy₂
  obtain ⟨V₂, _, _, _, _, hV₂c, hV₂n, σ, hσ, hval⟩ := GlobalTheory.T.exists_complete_dvr_field_values_deeper_point g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag D p z₁ c y h u.V u.complete u.norm_le
  obtain ⟨u', τ, e, T, hτ, hpsi, hT, hfw, hbw⟩ := GlobalTheory.T.uniformisedModel_baseChange_complete_dvr_extension _ _ _ ρ' p y₀ u V₂ hV₂c hV₂n σ hσ
  have hval' : ∀ a ∈ D.X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))),
      D.X.M.val (gPt p ≫ y) a ∈ (algebraMap (FractionRing u'.V) (PadicAlgCl p)).range := by
    intro a ha
    obtain ⟨b, hb⟩ := hval a ha
    exact ⟨τ b, by rw [← hb, ← hτ]; rfl⟩
  have hSS := GlobalTheory.T.sameGenericFibre_chain_rescaled_deeper_realisation g n F W Z i X₁ ε₁ D c₀ hc R' fg frac hth' hev ρ' ε' c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂ ρ₂ ε₂ hS hS₂
  obtain ⟨f₂, φ₂, hf₂, hcart, hlb, htor, heps⟩ := GlobalTheory.T.realisations_same_genericFibre_agree_at_points g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag D p z₁ c y h
    c₀ hc R' fg frac hth' hev ρ' ε' hR y₀ hy₀ c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂ ρ₂ ε₂ hSS hR₂ y₂ hy₂
    (FractionRing u'.V) (algebraMap _ _) u'.yK u'.fac hval' u'.A u'.φ u'.cart u'.lb
  let u₂ : ρ₂.UTest p y₂ :=
    { V := u'.V, complete := u'.complete, norm_le := u'.norm_le, yK := f₂, fac := hf₂, A := u'.A, φ := φ₂,
      cart := hcart, lb := hlb, G := u'.G, semi := u'.semi, D := u'.D, U := u'.U }
  refine ⟨u₂, e, T, hpsi, ?_, ?_, hfw, hbw⟩
  · intro x₂ a
    rw [hT]
    exact htor x₂.left a (Over.w x₂)
  · intro x₂ x₂' E hxx
    rw [hT, ← Category.assoc, hT, Category.assoc]
    exact (heps x₂.left x₂'.left E (Over.w x₂) (Over.w x₂')).1 hxx

end GlobalTheory.Poinc.GLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedModelTransportDeeperThetaSetupStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedModel_transport_deeperThetaSetup : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y)
  (c₀ : X₁.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X₁.o₁ X₁.Ω₁) (fg : R'.FG) (frac : ∀ x : X₁.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X₁.S.th x ∈ R') (hev : ∀ x k, c₀ * X₁.S.ev x k ∈ R') (ρ' : (X₁.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)), Same X₁.ρ ε₁ ρ' ε' (fun x => x) (RingHom.id _) → ρ'.i₀ = X₁.ρ.i₀ → R' ≤ X₁.M.O ((gPt p ≫ c.y) (closedPoint (PadicAlgCl p))) → ∀ (y₀ : R' →+* PadicAlgCl p), (∀ a : R', y₀ a = X₁.M.val (gPt p ≫ c.y) a) → ∀ (u : ρ'.UTest p y₀)
  (c₂ : D.X.Ω₁) (hc₂ : c₂ ≠ 0) (R₂ : Subalgebra D.X.o₁ D.X.Ω₁) (fg₂ : R₂.FG) (frac₂ : ∀ x : D.X.Ω₁, ∃ a ∈ R₂, ∃ b ∈ R₂, x = a / b) (hth₂ : ∀ x, c₂ * D.X.S.th x ∈ R₂) (hev₂ : ∀ x k, c₂ * D.X.S.ev x k ∈ R₂) (ρ₂ : (D.X.S.rechart c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂).Real) (ε₂ : Matrix (Fin 8) (Fin 8) ℤ → (ρ₂.P.A ⟶ ρ₂.P.A)), Same D.X.ρ D.ε ρ₂ ε₂ (fun x => x) (RingHom.id _) → ρ₂.i₀ = D.X.ρ.i₀ → R₂ ≤ D.X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))) → ∀ (y₂ : R₂ →+* PadicAlgCl p), (∀ a : R₂, y₂ a = D.X.M.val (gPt p ≫ y) a) →
  ∃ (u₂ : ρ₂.UTest p y₂) (e : u₂.D.toPre.X ≃+ u.D.toPre.X) (T : (TFK (R := u₂.V) (PadicAlgCl p) ⟶ u₂.A.A) ≃ (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)),
    (∀ χ r, u.PsiNorm (e χ) r → u₂.PsiNorm χ r) ∧
    (∀ x₂ a, x₂.left ≫ u₂.φ = spMap y₂ ≫ (ρ₂.pt (D.lab a)).left ↔ (T x₂).left ≫ u.φ = spMap y₀ ≫ (ρ'.pt a).left) ∧
    (∀ x₂ x₂' E, x₂'.left ≫ u₂.φ = x₂.left ≫ u₂.φ ≫ (ε₂ E).left → (T x₂').left ≫ u.φ = (T x₂).left ≫ u.φ ≫ (ε' E).left) ∧
    (∀ (m : ℕ) (pk₂ : QkPt u₂.D.toPre (PadicAlgCl p) m) x₂, 1 ≤ m → QkToAkU u₂.U.toUnifPre (PadicAlgCl p) m pk₂ x₂ → ∃ pk : QkPt u.D.toPre (PadicAlgCl p) m, pk.y = e pk₂.y ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk (T x₂)) ∧
    (∀ (m : ℕ) (pk : QkPt u.D.toPre (PadicAlgCl p) m) x, 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → ∃ pk₂ : QkPt u₂.D.toPre (PadicAlgCl p) m, e pk₂.y = pk.y ∧ QkToAkU u₂.U.toUnifPre (PadicAlgCl p) m pk₂ (T.symm x)) := by
  first | exact @GlobalTheory.Poinc.GLift.transport | exact GlobalTheory.Poinc.GLift.transport | (intros; apply GlobalTheory.Poinc.GLift.transport <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.GLift

theorem psiQ : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (q : u.D.toPre.X → ℝ), (∀ χ, u.PsiNorm χ (Real.exp (-q χ))) → ∀ χ, l.q χ = q χ := by
  intro o Ω _ _ _ S ρ p _ y₀ u l q hq χ
  have := GlobalTheory.ZH.RealCase.psiNorm_unique u χ (l.q_eq χ) (hq χ)
  exact neg_injective (Real.exp_injective this)

theorem labels_lift : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁), ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X₁ ε₁ c yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y), ∃ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y h) yy ∧ D.Compat yy₁ yy := by
  intro g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag D p _ z₁ c yy₁ hLab y h
  obtain ⟨c₀, hc, R', fg, frac, hth', hev, ρ', ε', hS, hi, hR, y₀, hy₀, u, l, j, hq, hyy, hmat⟩ := hLab
  obtain ⟨c₂, hc₂, R₂, fg₂, frac₂, hth₂, hev₂, ρ₂, ε₂, hS₂, hi₂, hR₂, y₂, hy₂, hint₂⟩ :=
    GlobalTheory.T.thetaSetup_rescale_into_localRing_classicalTrait g n F W Z i D.X hg hn hodd himm he8 hth D.proj D.ε D.diag p (y (cPt p)) (D.lift c y h)
  obtain ⟨u₂, e, T, hpsi, htor, heps, hfw, hbw⟩ := GlobalTheory.T.uniformisedModel_transport_deeperThetaSetup g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag D p z₁ c y h
    c₀ hc R' fg frac hth' hev ρ' ε' hS hi hR y₀ hy₀ u c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂ ρ₂ ε₂ hS₂ hi₂ hR₂ y₂ hy₂
  obtain ⟨l₂⟩ := GlobalTheory.ZH.labels_exist GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 GlobalTheory.ZH.uTors_closed _ _ _ ρ₂ p y₂ u₂ hint₂
  set L₂ : ℕ := D.X.S.r * D.X.S.N with hL₂
  set L₁ : ℕ := X₁.S.r * X₁.S.N with hL₁
  let jj : u₂.D.toPre.X ≃+ (Fin 8 → c.T.D.toPre.X) := e.trans j
  have hrange : (nsmulAddMonoidHom L₂ : u₂.D.toPre.X →+ u₂.D.toPre.X).range ≤
      ((nsmulAddMonoidHom L₂ : (Fin 8 → c.T.D.toPre.X) →+ (Fin 8 → c.T.D.toPre.X)).range).comap jj.toAddMonoidHom := by
    rintro _ ⟨z, rfl⟩
    exact ⟨jj z, by simp⟩
  let f := QuotientAddGroup.map _ _ jj.toAddMonoidHom hrange
  have hf : ∀ χ, f (QuotientAddGroup.mk χ) = QuotientAddGroup.mk (jj χ) := fun χ => rfl
  refine ⟨f.comp l₂.yy, ⟨c₂, hc₂, R₂, fg₂, frac₂, hth₂, hev₂, ρ₂, ε₂, hS₂, hi₂, hR₂, y₂, hy₂, u₂, l₂, jj, ?_, ?_, ?_⟩, ?_⟩
  · intro χ
    rw [GlobalTheory.Poinc.GLift.psiQ _ _ _ ρ₂ p y₂ u₂ l₂ (fun χ => l.q (e χ)) (fun χ => hpsi χ _ (l.q_eq (e χ))) χ]
    exact hq (e χ)
  · intro a χ ha
    simp only [AddMonoidHom.comp_apply, ha]
    rfl
  · intro m pk pk' x x' E hm hx hx' hxx
    obtain ⟨q₁, hq₁y, hq₁⟩ := hfw m pk x hm hx
    obtain ⟨q₁', hq₁y', hq₁'⟩ := hfw m pk' x' hm hx'
    have := hmat m q₁ q₁' (T x) (T x') E hm hq₁ hq₁' (heps x x' E hxx)
    rw [hq₁y, hq₁y'] at this
    exact this
  · intro a μ hμ
    obtain ⟨pk, x, hx, hxa⟩ := GlobalTheory.T.exists_thetaTorsion_preimage_uniformised_model _ _ _ ρ' p y₀ u a
    have h1 := l.yy_eq a pk x hx hxa
    have h2 := hyy a pk.y h1
    have hL₁pos : 1 ≤ L₁ := by
      obtain ⟨jr, hjr, hr⟩ := X₁.ρ.r_eq
      have h1' : 0 < X₁.S.r := by rw [hr]; exact pow_pos X₁.ρ.n_prime.pos _
      have h2' : 0 < X₁.S.N := by rw [X₁.ρ.N_eq]; exact pow_pos (pow_pos X₁.ρ.n_prime.pos _) _
      exact Nat.mul_pos h1' h2'
    have hdvd : L₁ ∣ L₂ := by
      obtain ⟨t, ht⟩ := D.dvd
      refine ⟨t * (D.m * D.X.S.r), ?_⟩
      rw [hL₂, D.sq, ht]; ring
    have hL₂pos : 1 ≤ L₂ := by
      obtain ⟨jr, hjr, hr⟩ := D.X.ρ.r_eq
      have h1' : 0 < D.X.S.r := by rw [hr]; exact pow_pos D.X.ρ.n_prime.pos _
      have h2' : 0 < D.X.S.N := by rw [D.X.ρ.N_eq]; exact pow_pos (pow_pos D.X.ρ.n_prime.pos _) _
      exact Nat.mul_pos h1' h2'
    have hdpos : 1 ≤ L₂ / L₁ := by
      rw [Nat.one_le_div_iff (by omega)]
      exact Nat.le_of_dvd (by omega) hdvd
    obtain ⟨pk', hpk'y, hpk'⟩ := GlobalTheory.T.exists_levelPoint_rescale_same_torsionPoint _ _ _ ρ' p y₀ u L₁ L₂ (L₂ / L₁) pk x hL₁pos hdpos
      (Nat.div_mul_cancel hdvd).symm hx
    obtain ⟨pk₂, hpk₂y, hpk₂⟩ := hbw L₂ pk' x hL₂pos hpk'
    have h3 := (htor (T.symm x) a).2 (by simpa using hxa)
    have h4 := l₂.yy_eq (D.lab a) pk₂ (T.symm x) hpk₂ h3
    show f (l₂.yy (D.lab a)) = _
    rw [h4, hf]
    have h5 : jj pk₂.y = (L₂ / L₁) • j pk.y := by
      show j (e pk₂.y) = _
      rw [hpk₂y, hpk'y, map_nsmul]
    rw [h5]
    rw [hμ] at h2
    obtain ⟨z, hz⟩ := (QuotientAddGroup.eq).1 h2.symm
    apply (QuotientAddGroup.eq).2
    refine ⟨z, ?_⟩
    simp only [nsmulAddMonoidHom_apply] at hz ⊢
    rw [← smul_neg, ← smul_add, ← hz, smul_smul, Nat.div_mul_cancel hdvd]

end GlobalTheory.Poinc.GLift

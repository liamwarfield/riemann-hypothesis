module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendCompletion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFlatFinrank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelsConstantCompletedLocalRingClosedPoi

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompleteLocalBaseAtClosedPointGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedTestModelBaseChangeCompletedLoc
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfPullbackChainThroughSection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfPullbackChainThroughSection
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section
namespace GlobalTheory.LbChain

theorem lbIso_chain : ∀ {A₀ X₁ G₁ G₂ Z P Q : Scheme.{0}} (LA : LB A₀) (L₁ : LB G₁) (L₂ : LB G₂) (LZ : LB Z) (LQ : LB Q) (a : X₁ ⟶ A₀) (a' : A₀ ⟶ X₁) (f₁ : X₁ ⟶ G₁) (f₂ : G₁ ⟶ G₂) (f₃ : G₂ ⟶ Z) (ψ : P ⟶ Z) (π : P ⟶ Q) (t : A₀ ⟶ P), LA.IsLB → L₁.IsLB → L₂.IsLB → LZ.IsLB → LQ.IsLB → a' ≫ a = 𝟙 A₀ → LBIso (LA.pull a) (L₁.pull f₁) → LBIso L₁ (L₂.pull f₂) → LBIso L₂ (LZ.pull f₃) → LBIso (LZ.pull ψ) (LQ.pull π) → t ≫ ψ = a' ≫ f₁ ≫ f₂ ≫ f₃ → LBIso LA (LQ.pull (t ≫ π)) := by
  intro A₀ X₁ G₁ G₂ Z P Q LA L₁ L₂ LZ LQ a a' f₁ f₂ f₃ ψ π t hA h₁ h₂ hZ hQ hs e₁ e₂ e₃ e₄ ht
  have E0 : LBIso LA (LA.pull (a' ≫ a)) :=
    LBIso.chartPull (chartPullUnpull LA (a' ≫ a) hs) (chartPullId _) (PolBaseChange.lbIso_refl (pull_isLB hA _))
  have E1 : LBIso (LA.pull (a' ≫ a)) (L₁.pull (a' ≫ f₁)) := GlobalTheory.GenSpread.lbIso_pull_comp a' rfl rfl e₁
  have E2 : LBIso (L₁.pull (a' ≫ f₁)) (L₂.pull (a' ≫ f₁ ≫ f₂)) :=
    GlobalTheory.GenSpread.lbIso_pull_of_lbIso e₂ (a' ≫ f₁) (by simp)
  have E3 : LBIso (L₂.pull (a' ≫ f₁ ≫ f₂)) (LZ.pull (t ≫ ψ)) :=
    GlobalTheory.GenSpread.lbIso_pull_of_lbIso e₃ (a' ≫ f₁ ≫ f₂) (by rw [ht]; simp)
  have E4 : LBIso (LZ.pull (t ≫ ψ)) (LQ.pull (t ≫ π)) := GlobalTheory.GenSpread.lbIso_pull_comp t rfl rfl e₄
  exact LBIso.trans hA (pull_isLB hA _) (pull_isLB hQ _) E0
    (LBIso.trans (pull_isLB hA _) (pull_isLB h₁ _) (pull_isLB hQ _) E1
      (LBIso.trans (pull_isLB h₁ _) (pull_isLB h₂ _) (pull_isLB hQ _) E2
        (LBIso.trans (pull_isLB h₂ _) (pull_isLB hZ _) (pull_isLB hQ _) E3 E4)))

end GlobalTheory.LbChain
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfPullbackChainThroughSectionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleIso_of_pullback_chain_through_section : ∀ {A₀ X₁ G₁ G₂ Z P Q : Scheme.{0}} (LA : LB A₀) (L₁ : LB G₁) (L₂ : LB G₂) (LZ : LB Z) (LQ : LB Q) (a : X₁ ⟶ A₀) (a' : A₀ ⟶ X₁) (f₁ : X₁ ⟶ G₁) (f₂ : G₁ ⟶ G₂) (f₃ : G₂ ⟶ Z) (ψ : P ⟶ Z) (π : P ⟶ Q) (t : A₀ ⟶ P), LA.IsLB → L₁.IsLB → L₂.IsLB → LZ.IsLB → LQ.IsLB → a' ≫ a = 𝟙 A₀ → LBIso (LA.pull a) (L₁.pull f₁) → LBIso L₁ (L₂.pull f₂) → LBIso L₂ (LZ.pull f₃) → LBIso (LZ.pull ψ) (LQ.pull π) → t ≫ ψ = a' ≫ f₁ ≫ f₂ ≫ f₃ → LBIso LA (LQ.pull (t ≫ π)) := by
  first | exact @GlobalTheory.LbChain.lbIso_chain | exact GlobalTheory.LbChain.lbIso_chain | (intros; apply GlobalTheory.LbChain.lbIso_chain <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianExtensionAbelianOverOpenPart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianExtensionAbelianOverOpenPart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
namespace GlobalTheory.ZH

theorem abLocus_of_over₀ : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → (U₀ : Set M.Z) ⊆ abLocus FinalForm.G := by
  intro o Ω _ _ _ S ρ M U₀ EE FinalForm hO z hz
  rw [FinalForm.ab]
  show S.TT M z = ⊥
  have hle : M.ringOn U₀ ≤ M.O z := RatModel.ringOn_le_O hz
  have hsub : {x | S.th x ≠ 0} ⊆ S.supI M z := by
    intro x hx
    refine ⟨hx, fun y => ?_⟩
    rw [div_eq_mul_inv]
    exact mul_mem (hle (hO.le (S.th_mem y))) (hle (hO.th_unit x hx))
  have hHH : S.HH M z = ⊤ := by
    rw [eq_top_iff, ← S.supp]
    exact AddSubgroup.closure_mono hsub
  rw [ThetaSys.TT, hHH, eq_bot_iff]
  intro a ha
  rw [AddSubgroup.mem_bot]
  have h := fun b => ha b (AddSubgroup.mem_top b)
  funext j
  rcases j with i | i
  · have := h (Pi.single (Sum.inr i) 1)
    simpa [eStd, Pi.single_apply] using this
  · have := h (Pi.single (Sum.inl i) 1)
    simpa [eStd, Pi.single_apply] using this

end GlobalTheory.ZH
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianExtensionAbelianOverOpenPartStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiAbelianExtension_abelian_over_open_part : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → (U₀ : Set M.Z) ⊆ abLocus FinalForm.G := by
  first | exact @GlobalTheory.ZH.abLocus_of_over₀ | exact GlobalTheory.ZH.abLocus_of_over₀ | (intros; apply GlobalTheory.ZH.abLocus_of_over₀ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelValueAtPointOfOpenViaSpecSubalgebra
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelValueAtPointOfOpenViaSpecSubalgebra
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section
namespace GlobalTheory.Poinc.TestAtPt

theorem val_eq_of_spMap : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U₀ : M.Z.Opens) (Rs : Subalgebra o Ω) (u₀ : U₀.toScheme ⟶ Sp Rs), (U₀ : Set M.Z).Nonempty → (∀ x : Sp Ω ⟶ U₀.toScheme, x ≫ U₀.ι = M.pt → x ≫ u₀ = spMap Rs.val.toRingHom) → ∀ (K : Type) [Field K] (q : Sp K ⟶ U₀.toScheme) (f : Rs →+* K), spMap f = q ≫ u₀ → ∀ a : Rs, M.val (q ≫ U₀.ι) (a : Ω) = f a := by
  intro o Ω _ _ _ M U₀ Rs u₀ hne hpt K _ q f hf a
  set s : Γ(U₀.toScheme, ⊤) :=
    (u₀.appLE ⊤ ⊤ (fun _ _ => trivial)).hom ((Scheme.ΓSpecIso (CommRingCat.of Rs)).inv.hom a) with hs
  set t : Γ(M.Z, U₀.ι ''ᵁ ⊤) := (U₀.ι.appIso ⊤).inv.hom s with ht
  have key : ∀ {C : Type} [Field C] (y : Sp C ⟶ U₀.toScheme),
      valF (y ≫ U₀.ι) (U₀.ι ''ᵁ ⊤) t = valR (y ≫ u₀) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of Rs)).inv.hom a) := by
    intro C _ y
    rw [GlobalTheory.Points.valF_eq_valR, ← GlobalTheory.Points.valR_appLE y U₀.ι (U₀.ι.preimage_image_eq ⊤).ge
      (GlobalTheory.Points.le_preimage_top y), ← Scheme.Hom.appIso_hom', ht, ← CommRingCat.comp_apply, Iso.inv_hom_id,
      CommRingCat.id_apply, hs]
    exact GlobalTheory.Points.valR_appLE y u₀ _ (GlobalTheory.Points.le_preimage_top y) _
  have hW : ∀ {C : Type} [Field C] (y : Sp C ⟶ U₀.toScheme),
      Set.range (y ≫ U₀.ι) ⊆ ((U₀.ι ''ᵁ ⊤ : M.Z.Opens) : Set M.Z) := by
    intro C _ y
    rw [Scheme.Opens.ι_image_top, ← Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    exact ⟨y w, rfl⟩
  have hrange : Set.range M.pt ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    exact M.top_le_preimage_pt hne (x := w) trivial
  have hx : IsOpenImmersion.lift U₀.ι M.pt hrange ≫ U₀.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  have h1 := hpt _ hx
  have e1 : valF M.pt (U₀.ι ''ᵁ ⊤) t = (a : Ω) := by
    rw [← hx, key, h1, GlobalTheory.Points.valR_specMap]
    rfl
  rw [RatModel.val_eq (hW q) e1, key, ← hf, GlobalTheory.Points.valR_specMap]
  rfl

end GlobalTheory.Poinc.TestAtPt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelValueAtPointOfOpenViaSpecSubalgebraStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modelValue_at_point_of_open_via_spec_subalgebra : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U₀ : M.Z.Opens) (Rs : Subalgebra o Ω) (u₀ : U₀.toScheme ⟶ Sp Rs), (U₀ : Set M.Z).Nonempty → (∀ x : Sp Ω ⟶ U₀.toScheme, x ≫ U₀.ι = M.pt → x ≫ u₀ = spMap Rs.val.toRingHom) → ∀ (K : Type) [Field K] (q : Sp K ⟶ U₀.toScheme) (f : Rs →+* K), spMap f = q ≫ u₀ → ∀ a : Rs, M.val (q ≫ U₀.ι) (a : Ω) = f a := by
  first | exact @GlobalTheory.Poinc.TestAtPt.val_eq_of_spMap | exact GlobalTheory.Poinc.TestAtPt.val_eq_of_spMap | (intros; apply GlobalTheory.Poinc.TestAtPt.val_eq_of_spMap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrFractionLiftPadicAlgClosureNormLeOneIff
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrFractionLiftPadicAlgClosureNormLeOneIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem GlobalTheory.Poinc.norm_lift_le_one_iff_mem_range : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (i : V →+* OO p), IsLocalHom i → ∀ (hi : Function.Injective ((OO p).subtype.comp i)) (x : FractionRing V), ‖IsFractionRing.lift (K := FractionRing V) hi x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V)) := by
  intro p _ V _ _ _ i hloc hi x
  have hV : ValuationRing V := inferInstance
  constructor
  · intro hx
    by_contra hnot
    have hx0 : x ≠ 0 := fun h => hnot ⟨0, by simp [h]⟩
    rcases ValuationRing.isInteger_or_isInteger V x with ⟨a, ha⟩ | ⟨w, hw⟩
    · exact hnot ⟨a, ha⟩
    · have hwu : ¬ IsUnit w := by
        intro hu
        apply hnot
        refine ⟨(hu.unit⁻¹ : Vˣ), ?_⟩
        have h1 : algebraMap V (FractionRing V) (hu.unit⁻¹ : Vˣ) * algebraMap V (FractionRing V) w = 1 := by
          rw [← map_mul]; simp
        rw [hw] at h1
        exact (eq_inv_of_mul_eq_one_left h1).trans (inv_inv x)
      have hiw : ¬ IsUnit (i w) := fun h => hwu (IsLocalHom.map_nonunit w h)
      have hlt : ‖((i w : OO p) : PadicAlgCl p)‖ < 1 := (GlobalTheory.ZH.not_isUnit_OO_iff _).1 hiw
      have hlw : IsFractionRing.lift (K := FractionRing V) hi x⁻¹ = ((i w : OO p) : PadicAlgCl p) := by
        rw [← hw, IsFractionRing.lift_algebraMap]; rfl
      have hprod : ‖IsFractionRing.lift (K := FractionRing V) hi x‖ * ‖IsFractionRing.lift (K := FractionRing V) hi x⁻¹‖ = 1 := by
        rw [← norm_mul, ← map_mul, mul_inv_cancel₀ hx0, map_one, norm_one]
      rw [hlw] at hprod
      have : ‖IsFractionRing.lift (K := FractionRing V) hi x‖ * ‖((i w : OO p) : PadicAlgCl p)‖ < 1 :=
        calc _ ≤ 1 * ‖((i w : OO p) : PadicAlgCl p)‖ := mul_le_mul_of_nonneg_right hx (norm_nonneg _)
          _ < 1 := by rw [_root_.one_mul]; exact hlt
      linarith
  · rintro ⟨v, rfl⟩
    rw [IsFractionRing.lift_algebraMap]
    exact (GlobalTheory.ZH.mem_OO_iff _).1 (i v).2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrFractionLiftPadicAlgClosureNormLeOneIffStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvr_fractionLift_padicAlgClosure_norm_le_one_iff : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (i : V →+* OO p), IsLocalHom i → ∀ (hi : Function.Injective ((OO p).subtype.comp i)) (x : FractionRing V), ‖IsFractionRing.lift (K := FractionRing V) hi x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V)) := by
  first | exact @GlobalTheory.Poinc.norm_lift_le_one_iff_mem_range | exact GlobalTheory.Poinc.norm_lift_le_one_iff_mem_range | (intros; apply GlobalTheory.Poinc.norm_lift_le_one_iff_mem_range <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedTestModelBaseChangeCompletedLoc
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section
namespace GlobalTheory.Poinc.TestAtPt


set_option maxHeartbeats 1600000 in
theorem exists_uTest_isBC : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real), S.Big → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left), IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (FinalForm.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G)) → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), M.Cen U₀ x y → spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ∀ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ → ∃ (u : ρ.UTest p y₀) (ε : D.toPre.X ≃+ u.D.toPre.X), GlobalTheory.Poinc.TestAtPt.IsBC FinalForm gm U ev u ε := by
  intro o' Ω _ _ _ _ S ρ hBig M U₀ EE FinalForm hAdm hEE x hx R _ _ _ j hBase hcpl G _ _ gm hgm D A U hLB hpsi p _ y ev hCen hev y₀ hAt
  obtain ⟨V, _, _, _, ev₀, i, hVc, hev₀, hi, hiinj, -, huniq⟩ :=
    GlobalTheory.ClassicalPt.extend_completion o' Ω M x R j hcpl p y hCen.1
  have hevi : ev = i.comp ev₀ := huniq ev hev
  have hinj : Function.Injective ((OO p).subtype.comp i) := Subtype.val_injective.comp hiinj
  letI alg : Algebra (FractionRing V) (PadicAlgCl p) := (IsFractionRing.lift (K := FractionRing V) hinj).toAlgebra
  haveI := ArithBase.ded (o := o') (Ω := Ω)
  haveI := M.lft
  haveI : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  let Wab : M.Z.Opens := ⟨abLocus FinalForm.G, GlobalTheory.AbLocusOpenGlobal.isOpen_abLocus_of_locallyNoetherian FinalForm.G FinalForm.semi⟩
  let W : (Sp R).Opens := (spMap j ≫ M.Z.fromSpecStalk x) ⁻¹ᵁ Wab
  have hgenU : (spMap j ≫ M.Z.fromSpecStalk x) (spMap ev₀ (genericPoint (Sp V))) ∈ U₀ := by
    have hw := hCen.2 ⟨genericPoint (Sp (PadicAlgCl p)), rfl⟩
    have e2 : (spMap ((OO p).subtype.comp i)).base (genericPoint (Sp (PadicAlgCl p))) = genericPoint (Sp V) := by
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      apply PrimeSpectrum.ext
      show Ideal.comap ((OO p).subtype.comp i) ⊥ = ⊥
      exact Ideal.comap_bot_of_injective _ hinj
    have e3 : gPt p ≫ y = spMap ((OO p).subtype.comp i) ≫ spMap ev₀ ≫ spMap j ≫ M.Z.fromSpecStalk x := by
      rw [← hev, hevi]
      simp only [spMap, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [e3] at hw
    rw [← e2]; exact hw
  have hU₀ab : (U₀ : Set M.Z) ⊆ abLocus FinalForm.G := GlobalTheory.T.semiAbelianExtension_abelian_over_open_part o' Ω S ρ M U₀ EE FinalForm hAdm.1
  have hgenW : spMap ev₀ (genericPoint (Sp V)) ∈ W := hU₀ab hgenU
  have hsemi : IsSemiAbelian G := by
    obtain ⟨e, he, -⟩ := grpPullback_iso hgm (isGrpPullback_pullback FinalForm.G _)
    haveI := he
    exact GlobalTheory.isSemiAbelian_of_grpIso e (IsSemiAbelian.pullback _ FinalForm.G FinalForm.semi)
  have hadm : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hVc⟩
  obtain ⟨D', A', hD, U', hU'⟩ := GlobalTheory.T.uniformisation_baseChange_of_kernel_in_generating_open R hBase D A G hsemi U V hadm ev₀ hev₀ W hpsi hgenW
    ((Over.pullback (specOf ev₀)).obj G) (Iso.refl _) (show IsMonHom (𝟙 _) from ⟨by simp, by simp⟩)
  have hgenV : (jK V).base (genericPoint (Sp (FractionRing V))) = genericPoint (Sp V) := by
    rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
    apply PrimeSpectrum.ext
    show Ideal.comap (algebraMap V (FractionRing V)) ⊥ = ⊥
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective V (FractionRing V))
  have hrange : Set.range (jK V ≫ spMap ev₀ ≫ spMap j ≫ M.Z.fromSpecStalk x).base ⊆ Set.range U₀.ι.base := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hw : w = genericPoint (Sp (FractionRing V)) := Subsingleton.elim _ _
    subst hw
    show (spMap j ≫ M.Z.fromSpecStalk x).base ((spMap ev₀).base ((jK V).base _)) ∈ U₀
    rw [hgenV]; exact hgenU
  obtain ⟨m, hm⟩ : ∃ m : Sp (FractionRing V) ⟶ U₀.toScheme,
      m ≫ U₀.ι = jK V ≫ spMap ev₀ ≫ spMap j ≫ M.Z.fromSpecStalk x :=
    ⟨IsOpenImmersion.lift U₀.ι _ hrange, IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨yK, hyK⟩ : ∃ yK : S.R →+* FractionRing V, spMap yK = m ≫ FinalForm.u₀ :=
    ⟨(Spec.preimage (m ≫ FinalForm.u₀)).hom, Spec.map_preimage _⟩
  have hval : ∀ (K : Type) [Field K] (q : Sp K ⟶ U₀.toScheme) (f : S.R →+* K), spMap f = q ≫ FinalForm.u₀ →
      ∀ a : S.R, M.val (q ≫ U₀.ι) (a : Ω) = f a :=
    fun K _ q f hf a => GlobalTheory.T.modelValue_at_point_of_open_via_spec_subalgebra o' Ω M U₀ S.R FinalForm.u₀ hAdm.1.ne FinalForm.u₀_gen K q f hf a
  have hlift : ∀ v : V, algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V (FractionRing V) v) = (i v : PadicAlgCl p) :=
    fun v => IsFractionRing.lift_algebraMap (K := FractionRing V) hinj v
  have e1 : gPt p ≫ spMap (i.comp ev₀) = spMap (algebraMap (FractionRing V) (PadicAlgCl p)) ≫ jK V ≫ spMap ev₀ := by
    simp only [spMap, jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext v
    exact (hlift (ev₀ v)).symm
  have hgy : gPt p ≫ y = (spMap (algebraMap (FractionRing V) (PadicAlgCl p)) ≫ m) ≫ U₀.ι := by
    rw [Category.assoc, hm, ← hev, hevi, ← Category.assoc, e1]
    simp only [Category.assoc]
  have hfac : (algebraMap (FractionRing V) (PadicAlgCl p)).comp yK = y₀ := by
    ext a
    rw [hAt a, hgy, hval (PadicAlgCl p) _ ((algebraMap (FractionRing V) (PadicAlgCl p)).comp yK)]
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    rw [← hyK]
  have hid : IsMonHom (Iso.refl ((Over.pullback (specOf ev₀)).obj G)).hom := show IsMonHom (𝟙 _) from ⟨by simp, by simp⟩
  have hβ : (genMap U' ≫ pullback.fst G.hom (specOf ev₀) ≫ gm) ≫ FinalForm.G.hom = A'.A.hom ≫ m ≫ U₀.ι := by
    rw [hm]
    simp only [genMap, Category.assoc]
    rw [hgm.1.w, pullback.condition_assoc]
    have h1 : pullback.fst ((Over.pullback (specOf ev₀)).obj G).hom (jK V) ≫ pullback.snd G.hom (specOf ev₀) =
        pullback.snd ((Over.pullback (specOf ev₀)).obj G).hom (jK V) ≫ jK V :=
      pullback.condition
    rw [reassoc_of% h1]
    have h2 : U'.gen.inv.left ≫ pullback.snd ((Over.pullback (specOf ev₀)).obj G).hom (jK V) = A'.A.hom := Over.w U'.gen.inv
    rw [reassoc_of% h2]
  obtain ⟨t, ht₁, ht₂⟩ : ∃ t : A'.A.left ⟶ pullback ρ.P.A.hom FinalForm.u₀,
      t ≫ FinalForm.φ = genMap U' ≫ pullback.fst G.hom (specOf ev₀) ≫ gm ∧ t ≫ pullback.snd ρ.P.A.hom FinalForm.u₀ = A'.A.hom ≫ m :=
    ⟨FinalForm.cart.1.lift _ _ hβ, FinalForm.cart.1.lift_fst _ _ _, FinalForm.cart.1.lift_snd _ _ _⟩
  have hcart : IsGrpPullback A'.A ρ.P.A (spMap yK) (t ≫ pullback.fst ρ.P.A.hom FinalForm.u₀) := by
    haveI := U'.gen_hom
    haveI : IsMonHom U'.gen.symm.hom := by show IsMonHom U'.gen.inv; infer_instance
    have c1 : IsGrpPullback A'.A ((Over.pullback (jK V)).obj ((Over.pullback (specOf ev₀)).obj G)) (𝟙 _)
        U'.gen.symm.hom.left := isGrpPullback_of_iso U'.gen.symm
    have c := ((c1.comp (isGrpPullback_pullback _ (jK V))).comp (isGrpPullback_pullback G (specOf ev₀))).comp hgm
    have n : IsGrpPullback A'.A FinalForm.G (m ≫ U₀.ι) (t ≫ FinalForm.φ) := by
      refine c.congr ?_ ?_
      · rw [hm]; simp [specOf, jK, spMap]
      · rw [ht₁]; simp only [genMap, Category.assoc]; rfl
    have c4 := IsGrpPullback.cancel FinalForm.cart n ht₂
    exact (c4.comp (isGrpPullback_pullback ρ.P.A FinalForm.u₀)).congr hyK.symm rfl
  have hlb : LBIso A'.L (ρ.P.L.pull (t ≫ pullback.fst ρ.P.A.hom FinalForm.u₀)) := by
    obtain ⟨wE, hwE⟩ := U'.ext
    obtain ⟨wL, hwL, -⟩ := hU'.lg
    refine GlobalTheory.T.lineBundleIso_of_pullback_chain_through_section A'.L U'.LG.L U.LG.L FinalForm.L.L ρ.P.L U'.gen.hom.left U'.gen.inv.left
      (pullback.fst _ (jK V)) ((Iso.refl ((Over.pullback (specOf ev₀)).obj G)).hom.left ≫ pullback.fst G.hom (specOf ev₀)) gm
      FinalForm.φ (pullback.fst ρ.P.A.hom FinalForm.u₀) t A'.isLB U'.LG.isLB U.LG.isLB FinalForm.L.isLB ρ.P.isLB ?_ ⟨wE, hwE⟩ ⟨wL, hwL⟩ hLB
      ⟨FinalForm.w, FinalForm.w_gen⟩ ?_
    · rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
    · rw [ht₁]; simp only [genMap, Iso.refl_hom, Over.id_left, Category.assoc]; erw [Category.id_comp]
  refine ⟨⟨V, hVc, ?_, yK, hfac, A', t ≫ pullback.fst ρ.P.A.hom FinalForm.u₀, hcart, hlb, (Over.pullback (specOf ev₀)).obj G,
    IsSemiAbelian.pullback _ G hsemi, D', U'⟩, hD.xe.symm, ?_⟩
  · exact fun x => GlobalTheory.T.dvr_fractionLift_padicAlgClosure_norm_le_one_iff p V i hi hinj x
  · refine ⟨ev₀, hev₀, hD, Iso.refl _, hid, hU', fun χ => hD.xe.apply_symm_apply χ, fun r => ?_, t, rfl, ?_⟩
    · rw [hlift, hevi]; rfl
    · exact ht₁.trans (by simp only [Iso.refl_hom, Over.id_left]; erw [Category.id_comp])

end GlobalTheory.Poinc.TestAtPt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedTestModelBaseChangeCompletedLocStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformisedTestModel_baseChange_completedLocal : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real), S.Big → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left), IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (FinalForm.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G)) → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), M.Cen U₀ x y → spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ∀ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ → ∃ (u : ρ.UTest p y₀) (ε : D.toPre.X ≃+ u.D.toPre.X), GlobalTheory.Poinc.TestAtPt.IsBC FinalForm gm U ev u ε := by
  first | exact @GlobalTheory.Poinc.TestAtPt.exists_uTest_isBC | exact GlobalTheory.Poinc.TestAtPt.exists_uTest_isBC | (intros; apply GlobalTheory.Poinc.TestAtPt.exists_uTest_isBC <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassicalPointNormPsiCoordinateExpNegQuadratic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassicalPointNormPsiCoordinateExpNegQuadratic
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.TestAtPt

theorem norm_psi_coord : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left) (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (ev : R →+* OO p) (u : ρ.UTest p y₀) (ε : D.toPre.X ≃+ u.D.toPre.X), GlobalTheory.Poinc.TestAtPt.IsBC FinalForm gm U ev u ε → ∀ (l : u.Lab) α s, PsiCoord D.toPre α s → ‖(ev s : PadicAlgCl p)‖ = Real.exp (-l.q (ε α)) := by
  intro o' Ω _ _ _ S ρ M U₀ EE FinalForm R _ _ _ G _ _ gm D A U p _ y₀ ev u ε hBC l α s hs
  obtain ⟨ev₀, _, hD, bc, -, -, hx, hev, -⟩ := hBC
  have hs' : PsiCoord D.toPre (hD.xe (ε α)) s := by rw [hx]; exact hs
  obtain ⟨w, hw⟩ := GlobalTheory.PelCoordPull.psiCoord_pull hD (ε α) s hs'
  obtain ⟨j, hj, hv⟩ := GlobalTheory.Poinc.valF_psi_of_psiCoord u.V u.D.toPre (ε α) _ hw
  have hq := l.q_eq (ε α) j hj
  rw [hv] at hq
  have unit_norm : ∀ v : u.Vˣ, ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) (v : u.V))‖ = 1 := by
    intro v
    have h1 := (u.norm_le _).2 ⟨(v : u.V), rfl⟩
    have h2 := (u.norm_le _).2 ⟨((v⁻¹ : u.Vˣ) : u.V), rfl⟩
    have hm : algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) (v : u.V)) *
        algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) ((v⁻¹ : u.Vˣ) : u.V)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    have hn := congrArg norm hm
    rw [norm_mul, norm_one] at hn
    nlinarith [norm_nonneg (algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) (v : u.V))),
      norm_nonneg (algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) ((v⁻¹ : u.Vˣ) : u.V)))]
  rw [map_mul, map_mul, norm_mul, unit_norm w, _root_.one_mul, hev] at hq
  exact hq

end GlobalTheory.Poinc.TestAtPt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassicalPointNormPsiCoordinateExpNegQuadraticStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classicalPoint_norm_psi_coordinate_exp_neg_quadratic : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left) (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (ev : R →+* OO p) (u : ρ.UTest p y₀) (ε : D.toPre.X ≃+ u.D.toPre.X), GlobalTheory.Poinc.TestAtPt.IsBC FinalForm gm U ev u ε → ∀ (l : u.Lab) α s, PsiCoord D.toPre α s → ‖(ev s : PadicAlgCl p)‖ = Real.exp (-l.q (ε α)) := by
  first | exact @GlobalTheory.Poinc.TestAtPt.norm_psi_coord | exact GlobalTheory.Poinc.TestAtPt.norm_psi_coord | (intros; apply GlobalTheory.Poinc.TestAtPt.norm_psi_coord <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompleteLocalBaseAtClosedPointGroup
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section
namespace GlobalTheory.Poinc.TestAtPt

theorem main : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real), S.Big → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left), IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (FinalForm.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G)) → ∃ yy : S.Gam →+ D.toPre.X ⧸ (nsmulAddMonoidHom (S.r * S.N) : D.toPre.X →+ D.toPre.X).range, ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), M.Cen U₀ x y → spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ∀ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ → ∃ (τ : S.Test p y₀) (ε : D.toPre.X ≃+ τ.X), (∀ α s, PsiCoord D.toPre α s → ‖(ev s : PadicAlgCl p)‖ = Real.exp (-τ.q (ε α))) ∧ ∀ a α, yy a = QuotientAddGroup.mk α ↔ τ.yy a = QuotientAddGroup.mk (ε α) := by
  intro o' Ω _ _ _ _ S ρ hBig M U₀ EE FinalForm hAdm hEE x hx R _ _ _ j hBase hCpl G _ _ gm hpb D A U hLB hPsi
  obtain ⟨yy, hyy⟩ := GlobalTheory.T.torsionLabels_constant_completedLocalRing_closedPoint o' Ω S ρ hBig M U₀ EE FinalForm hAdm hEE x hx R j hBase hCpl G gm hpb D A U hLB hPsi
  refine ⟨yy, ?_⟩
  intro p _ y ev hCen hev y₀ hAt
  obtain ⟨u, ε₀, hbc⟩ := GlobalTheory.T.exists_uniformisedTestModel_baseChange_completedLocal o' Ω S ρ hBig M U₀ EE FinalForm hAdm hEE x hx R j hBase hCpl G gm hpb D A U hLB hPsi
    p y ev hCen hev y₀ hAt
  have hint : ∀ a : o', ‖y₀ (algebraMap o' S.R a)‖ ≤ 1 := by
    intro a
    rw [hAt]
    exact hCen.norm_val_le_one ((M.O x).algebraMap_mem a)
  have hL := GlobalTheory.firstFiveLaws.1
  have hL2 := GlobalTheory.firstFiveLaws.2.1
  have hT := GlobalTheory.ZH.uTors_closed
  obtain ⟨l⟩ := GlobalTheory.T.uniformisedModel_torsionLabels_exist hL hL2 hT o' Ω S ρ p y₀ u hint
  obtain ⟨τ, e, hq, hy⟩ := exists_test_match o' Ω S ρ p y₀ u l
    (GlobalTheory.T.thetaConstant_bounded_by_shortestVector hL hL2 hT o' Ω S ρ p y₀ u l hint) (GlobalTheory.T.unitThetaConstants_generate_integralTorsion hL hL2 hT o' Ω S ρ p y₀ u l hint)
    (GlobalTheory.T.weightSpace_values_integralTorsion_bound_shortestVector hL hL2 hT o' Ω S ρ p y₀ u l hint) (GlobalTheory.T.exists_norm_torsionSum_shortestVector_eq hL hL2 hT o' Ω S ρ p y₀ u l hint)
    (GlobalTheory.T.exists_weightZeroSection_unit_integralTorsionPoint hL hL2 hT o' Ω S ρ p y₀ u l hint)
  refine ⟨τ, ε₀.trans e.symm, ?_, ?_⟩
  · intro α s hs
    rw [GlobalTheory.T.classicalPoint_norm_psi_coordinate_exp_neg_quadratic o' Ω S ρ M U₀ EE FinalForm R G gm D A U p y₀ ev u ε₀ hbc l α s hs, AddEquiv.trans_apply, hq,
      AddEquiv.apply_symm_apply]
  · intro a α
    rw [hyy p y ev hCen hev y₀ hAt u ε₀ hbc l a α, AddEquiv.trans_apply, hy, AddEquiv.apply_symm_apply]

end GlobalTheory.Poinc.TestAtPt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompleteLocalBaseAtClosedPointGroupStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complete_local_base_at_closed_point_group : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real), S.Big → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left), IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (FinalForm.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G)) → ∃ yy : S.Gam →+ D.toPre.X ⧸ (nsmulAddMonoidHom (S.r * S.N) : D.toPre.X →+ D.toPre.X).range, ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), M.Cen U₀ x y → spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ∀ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ → ∃ (τ : S.Test p y₀) (ε : D.toPre.X ≃+ τ.X), (∀ α s, PsiCoord D.toPre α s → ‖(ev s : PadicAlgCl p)‖ = Real.exp (-τ.q (ε α))) ∧ ∀ a α, yy a = QuotientAddGroup.mk α ↔ τ.yy a = QuotientAddGroup.mk (ε α) := by
  first | exact @GlobalTheory.Poinc.TestAtPt.main | exact GlobalTheory.Poinc.TestAtPt.main | (intros; apply GlobalTheory.Poinc.TestAtPt.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantFourierPartsBoundedClassMinima
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.CNorm

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem transport (S : ThetaSys o Ω) {T T' : AddSubgroup S.Gam} (h : T = T') (c : T →+ ZMod S.N)
    (c' : T' →+ ZMod S.N) (hc : ∀ t (h1 : t ∈ T) (h2 : t ∈ T'), c ⟨t, h1⟩ = c' ⟨t, h2⟩) :
    S.proj T c = S.proj T' c' ∧ ∀ k', ∃ k, S.FF T c k = S.FF T' c' k' := by
  subst h
  obtain rfl : c = c' := AddMonoidHom.ext fun t => hc t t.2 t.2
  exact ⟨rfl, fun k' => ⟨k', rfl⟩⟩

theorem mem_supI_iff_norm {S : ThetaSys o Ω} {M : RatModel o Ω} {U₀ : M.Z.Opens} (hO : S.Over₀ M U₀) {x : M.Z}
    {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} (hc : M.Cen U₀ x y) {y₀ : S.R →+* PadicAlgCl p}
    (hat : S.At M y y₀) (τ : S.Test p y₀) (a : S.Gam) :
    a ∈ S.supI M x ↔ ‖y₀ ⟨S.th a, S.th_mem a⟩‖ = τ.δ := by
  set w : Sp (PadicAlgCl p) := IsLocalRing.closedPoint _
  have hsp : ∀ w', (gPt p ≫ y) w' ⤳ (gPt p ≫ y) w :=
    RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ w)
  have hR : ∀ b ∈ S.R, b ∈ M.O ((gPt p ≫ y) w) := fun b hb =>
    RatModel.mem_ringOn.1 (hO.le hb) _ (hc.2 ⟨w, rfl⟩)
  have hOx : ∀ b ∈ M.O x, b ∈ M.O ((gPt p ≫ y) w) := fun b hb =>
    RatModel.O_le_of_specializes (RatModel.gPt_specializes hc.1 w) hb
  have hval : ∀ b (hb : b ∈ S.R), y₀ ⟨b, hb⟩ = M.val (gPt p ≫ y) b := fun b hb => hat ⟨b, hb⟩
  have key : ∀ a₁ ∈ S.supI M x, ∀ a', ‖y₀ ⟨S.th a', S.th_mem a'⟩‖ =
      ‖M.val (gPt p ≫ y) (S.th a' / S.th a₁)‖ * ‖y₀ ⟨S.th a₁, S.th_mem a₁⟩‖ := by
    intro a₁ h₁ a'
    rw [hval, hval, ← norm_mul, ← RatModel.val_mul hsp (hOx _ (h₁.2 a')) (hR _ (S.th_mem a₁)),
      div_mul_cancel₀ _ h₁.1]
  have hmax : ∀ a₁ ∈ S.supI M x, ‖y₀ ⟨S.th a₁, S.th_mem a₁⟩‖ = τ.δ := by
    intro a₁ h₁
    refine IsGreatest.unique (s := Set.range fun x => ‖y₀ ⟨S.th x, S.th_mem x⟩‖) ⟨⟨a₁, rfl⟩, ?_⟩ τ.δ_max
    rintro _ ⟨a', rfl⟩
    show ‖y₀ ⟨S.th a', S.th_mem a'⟩‖ ≤ _
    rw [key a₁ h₁ a']
    exact mul_le_of_le_one_left (norm_nonneg _) (hc.norm_val_le_one (h₁.2 a'))
  refine ⟨hmax a, fun h => ?_⟩
  obtain ⟨a₁, h₁⟩ := hO.div x
  have e := key a₁ h₁ a
  rw [h, hmax a₁ h₁] at e
  have h1 : ‖M.val (gPt p ≫ y) (S.th a / S.th a₁)‖ = 1 :=
    mul_right_cancel₀ τ.δ_pos.ne' (e.symm.trans (_root_.one_mul _).symm)
  exact (RatModel.Div.div_iff_isUnit h₁ a).2 ((RatModel.norm_val_eq_one_iff hc.1 (h₁.2 a)).1 h1)

theorem HH_eq {S : ThetaSys o Ω} {M : RatModel o Ω} {U₀ : M.Z.Opens} (hO : S.Over₀ M U₀) {x : M.Z}
    {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} (hc : M.Cen U₀ x y) {y₀ : S.R →+* PadicAlgCl p}
    (hat : S.At M y y₀) (τ : S.Test p y₀) : S.HH M x = τ.yy.ker := by
  rw [← τ.supp, ThetaSys.HH]
  congr 1
  ext a
  exact mem_supI_iff_norm hO hc hat τ a

theorem norm_val_div {S : ThetaSys o Ω} {M : RatModel o Ω} {U₀ : M.Z.Opens} (hO : S.Over₀ M U₀) {x : M.Z}
    {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} (hc : M.Cen U₀ x y) {y₀ : S.R →+* PadicAlgCl p}
    (hat : S.At M y y₀) {F : Ω} (hF : F ∈ S.R) {a : S.Gam} (ha : S.th a ≠ 0) :
    ‖M.val (gPt p ≫ y) (F / S.th a)‖ = ‖y₀ ⟨F, hF⟩‖ / ‖y₀ ⟨S.th a, S.th_mem a⟩‖ := by
  set w : Sp (PadicAlgCl p) := IsLocalRing.closedPoint _
  have hsp : ∀ w', (gPt p ≫ y) w' ⤳ (gPt p ≫ y) w :=
    RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ w)
  have hU : ∀ b ∈ M.ringOn U₀, b ∈ M.O ((gPt p ≫ y) w) := fun b hb =>
    RatModel.mem_ringOn.1 hb _ (hc.2 ⟨w, rfl⟩)
  have hth := hU _ (hO.le (S.th_mem a))
  have hinv := hU _ (hO.th_unit a ha)
  have hval : ∀ b (hb : b ∈ S.R), y₀ ⟨b, hb⟩ = M.val (gPt p ≫ y) b := fun b hb => hat ⟨b, hb⟩
  have e1 : M.val (gPt p ≫ y) (S.th a) * M.val (gPt p ≫ y) (S.th a)⁻¹ = 1 := by
    rw [← RatModel.val_mul hsp hth hinv, mul_inv_cancel₀ ha, RatModel.val_one]
  rw [div_eq_mul_inv, RatModel.val_mul hsp (hU _ (hO.le hF)) hinv, hval, hval, norm_mul, div_eq_mul_inv,
    eq_inv_of_mul_eq_one_right e1, norm_inv]

theorem norm_FF_le {S : ThetaSys o Ω} {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (τ : S.Test p y₀)
    {β : τ.X} (hβ : ∀ v0, τ.q β ≤ τ.q (β + S.N • v0)) {T : AddSubgroup S.Gam} (hT : T = S.perp τ.yy.ker)
    (c : T →+ ZMod S.N) (hc : ∀ t (h1 : t ∈ T) (h2 : t ∈ S.perp τ.yy.ker), c ⟨t, h1⟩ = τ.wt β ⟨t, h2⟩)
    (κ : S.J × (T → ZMod ((S.r * S.N) ^ 2))) :
    ‖y₀ ⟨S.FF T c κ, S.FF_mem T c κ⟩‖ ≤ τ.δ * Real.exp (-(τ.q β / S.N)) := by
  have hproj := (transport S hT c (τ.wt β) hc).1
  have := Fintype.ofFinite T
  rw [S.map_FF y₀ T c κ]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_pos τ.δ_pos (Real.exp_pos _)).le
    fun t _ => ?_
  rw [norm_mul, norm_pow, S.norm_ζ, one_pow, _root_.one_mul, hproj]
  exact τ.le β hβ t (τ.perp_ker_le_ker (hT ▸ t.2)) κ.1

theorem main : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real), S.Big → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left), IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (FinalForm.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G)) → S.IsoFree (S.TT M x) ∧ ∀ α₀ : D.toPre.X, ∃ c' : S.TT M x →+ ZMod S.N, ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), M.Cen U₀ x y → spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ∀ x₀ ∈ S.supI M x, (∀ κ, ∃ α s, CongMod S.N α α₀ ∧ PsiCoord D.toPre α s ∧ ‖M.val (gPt p ≫ y) (S.FF (S.TT M x) c' κ / S.th x₀)‖ ^ S.N ≤ ‖(ev s : PadicAlgCl p)‖) ∧ ∃ κ, ∀ α s, CongMod S.N α α₀ → PsiCoord D.toPre α s → ‖(ev s : PadicAlgCl p)‖ ≤ ‖M.val (gPt p ≫ y) (S.FF (S.TT M x) c' κ / S.th x₀)‖ ^ S.N := by
  intro o' Ω _ _ _ _ S ρ hBig M U₀ EE FinalForm hAdm hEE x hx R _ _ _ j hBase hCpl G _ _ gm hpb D A U hLB hPsi
  obtain ⟨yy, H⟩ := GlobalTheory.T.complete_local_base_at_closed_point_group o' Ω S ρ hBig M U₀ EE FinalForm hAdm hEE x hx R j hBase hCpl G gm hpb D A U hLB hPsi
  have hO := hAdm.1
  obtain ⟨p₁, hp₁, y₁, hc₁⟩ := GlobalTheory.Poinc.exists_cen_main o' Ω M x hx U₀ hO.ne
  obtain ⟨V, _, _, _, ev₀, i, -, -, -, -, hcomp₁, -⟩ :=
    GlobalTheory.ClassicalPt.extend_completion o' Ω M x R j hCpl p₁ y₁ hc₁.1
  obtain ⟨y₀₁, hat₁, -⟩ := S.exists_at_of_cen M hO.le hc₁
  obtain ⟨τ₁, ε₁, -, hlab₁⟩ := H p₁ y₁ (i.comp ev₀) hc₁ hcomp₁ y₀₁ hat₁
  have hTT₁ : S.TT M x = S.perp τ₁.yy.ker := by rw [ThetaSys.TT, HH_eq hO hc₁ hat₁ τ₁]
  refine ⟨by rw [hTT₁]; exact τ₁.isoFree, fun α₀ => ?_⟩
  obtain ⟨a₀, ha₀⟩ := τ₁.yy_onto (QuotientAddGroup.mk (ε₁ α₀))
  have hya₀ : yy a₀ = QuotientAddGroup.mk α₀ := (hlab₁ a₀ α₀).2 ha₀
  let c' : S.TT M x →+ ZMod S.N :=
    { toFun := fun t => ZMod.castHom (dvd_mul_left S.N S.r) (ZMod S.N) (eStd S.g _ (t : S.Gam) a₀)
      map_zero' := by simp
      map_add' := fun t t' => by simp [eStd_add_left] }
  refine ⟨c', ?_⟩
  intro p _ y ev hc hcomp x₀ hx₀
  obtain ⟨y₀, hat, -⟩ := S.exists_at_of_cen M hO.le hc
  obtain ⟨τ, ε, hnorm, hlab⟩ := H p y ev hc hcomp y₀ hat
  have hTT : S.TT M x = S.perp τ.yy.ker := by rw [ThetaSys.TT, HH_eq hO hc hat τ]
  obtain ⟨v, hv⟩ := τ.exists_shortest (ε α₀)
  have hwt : ∀ t (h1 : t ∈ S.TT M x) (h2 : t ∈ S.perp τ.yy.ker),
      c' ⟨t, h1⟩ = τ.wt (ε α₀ + S.N • v) ⟨t, h2⟩ := by
    intro t h1 h2
    have hτa : τ.yy a₀ = QuotientAddGroup.mk (ε α₀) := (hlab a₀ α₀).1 hya₀
    rw [map_add (f := _), τ.wt_nsmul, add_zero, τ.wt_eq a₀ (ε α₀) hτa]
    rfl
  have hqβ : ∀ α', CongMod S.N α' α₀ → τ.q (ε α₀ + S.N • v) ≤ τ.q (ε α') := by
    rintro α' ⟨w', rfl⟩
    have e : ε (α₀ + S.N • w') = ε α₀ + S.N • v + S.N • (ε w' - v) := by
      rw [map_add (f := _), map_nsmul, smul_sub]
      abel
    rw [e]
    exact hv _
  have hα : CongMod S.N (ε.symm (ε α₀ + S.N • v)) α₀ :=
    ⟨ε.symm v, by rw [map_add (f := _), map_nsmul, AddEquiv.symm_apply_apply]⟩
  obtain ⟨s, hs⟩ := (GlobalTheory.PeriodFormCompare.exists_psiCoord_iff D.toPre (ε.symm (ε α₀ + S.N • v))).2
    (GlobalTheory.PeriodFormCompare.psiIn_top D _)
  have hsn : ‖(ev s : PadicAlgCl p)‖ = Real.exp (-τ.q (ε α₀ + S.N • v)) := by
    rw [hnorm _ s hs, AddEquiv.apply_symm_apply]
  have hN : (S.N : ℝ) ≠ 0 := by have := S.N_ge; positivity
  have hexp : Real.exp (-(τ.q (ε α₀ + S.N • v) / S.N)) ^ S.N = Real.exp (-τ.q (ε α₀ + S.N • v)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  have hδ : ‖y₀ ⟨S.th x₀, S.th_mem x₀⟩‖ = τ.δ := (mem_supI_iff_norm hO hc hat τ x₀).1 hx₀
  refine ⟨fun κ => ⟨_, s, hα, hs, ?_⟩, ?_⟩
  · rw [norm_val_div hO hc hat (S.FF_mem _ c' κ) hx₀.1, hδ, hsn, ← hexp]
    refine pow_le_pow_left₀ (div_nonneg (norm_nonneg _) τ.δ_pos.le) ?_ _
    rw [div_le_iff₀ τ.δ_pos, mul_comm]
    exact norm_FF_le τ hv hTT c' hwt κ
  · obtain ⟨k, hk, hkeq⟩ := τ.eq _ hv
    obtain ⟨κ, hκ⟩ := (transport S hTT c' _ hwt).2 k
    refine ⟨κ, fun α' s' hα' hs' => ?_⟩
    have e : ‖M.val (gPt p ≫ y) (S.FF (S.TT M x) c' κ / S.th x₀)‖ ^ S.N =
        Real.exp (-τ.q (ε α₀ + S.N • v)) := by
      rw [norm_val_div hO hc hat (S.FF_mem _ c' κ) hx₀.1, hδ,
        show (⟨S.FF (S.TT M x) c' κ, S.FF_mem _ c' κ⟩ : S.R) = ⟨_, hk⟩ from Subtype.ext hκ, hkeq,
        mul_div_cancel_left₀ _ τ.δ_pos.ne', hexp]
    rw [e, hnorm α' s' hs']
    exact Real.exp_le_exp.2 (neg_le_neg (hqβ α' hα'))

end GlobalTheory.Poinc.CNorm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantFourierPartsBoundedClassMinimaStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaConstant_fourierParts_bounded_classMinima : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real), S.Big → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left), IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (FinalForm.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G)) → S.IsoFree (S.TT M x) ∧ ∀ α₀ : D.toPre.X, ∃ c' : S.TT M x →+ ZMod S.N, ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), M.Cen U₀ x y → spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ∀ x₀ ∈ S.supI M x, (∀ κ, ∃ α s, CongMod S.N α α₀ ∧ PsiCoord D.toPre α s ∧ ‖M.val (gPt p ≫ y) (S.FF (S.TT M x) c' κ / S.th x₀)‖ ^ S.N ≤ ‖(ev s : PadicAlgCl p)‖) ∧ ∃ κ, ∀ α s, CongMod S.N α α₀ → PsiCoord D.toPre α s → ‖(ev s : PadicAlgCl p)‖ ≤ ‖M.val (gPt p ≫ y) (S.FF (S.TT M x) c' κ / S.th x₀)‖ ^ S.N := by
  first | exact @GlobalTheory.Poinc.CNorm.main | exact GlobalTheory.Poinc.CNorm.main | (intros; apply GlobalTheory.Poinc.CNorm.main <;> assumption)
end

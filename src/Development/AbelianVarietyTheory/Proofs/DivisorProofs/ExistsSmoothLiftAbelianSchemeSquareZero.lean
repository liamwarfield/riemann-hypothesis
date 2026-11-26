module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchemePresentingSquareZeroSmoothLiftSystem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptySmoothLiftPresystemSquareZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLiftsSqZeroClassifiedByDifferentials
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppTopBijectiveAndSurjectiveNormalDomain
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefOverOfFiniteOrbit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKernelDiagonalRestrictionOfSymmetricTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerChangeOfTangentFrame

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctorialLiftsOfObstructionTwoZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDefectCoboundaryOfObstructionClassZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDefectCoboundaryOfObstructionClassZero
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ObsCob

theorem exists_cob : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (w : Glob1 F) (θ : ∀ (T T' T'' : C) (_ : T ⟶ T') (_ : T' ⟶ T''), Ω[F.obj T⁄R₀] →+ L.B T''), L.IsObs θ → L.IsOb2 α w 0 → ∃ g : ∀ (T T' : C) (_ : T ⟶ T'), L.B T', (∀ T T' a, g T T' a ∈ I.map (algebraMap R (L.B T'))) ∧ ∀ T T' T'' a b, θ T T' T'' a b (w.1 T) = L.ρ b (g T T' a) - g T T'' (a ≫ b) + g T' T'' b := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F L w θ hθ h0
  obtain ⟨θ', σ, z, hθ', hσ, hz, hzv⟩ := h0
  obtain ⟨f, hf⟩ := (H2.mk_eq_zero (F := ext R₁ F)).1 hz.symm
  refine ⟨fun T T' a ↦ σ T' (f T T' a), fun T T' a ↦ ?_, fun T T' T'' a b ↦ ?_⟩
  · exact (GlobalTheory.T.augmentation_sigma_map_basic_properties R R₀ I hI π hπ hk R₁ α (L.B T') (F.obj T') (L.p T') (L.semi T') (L.surj T')
      (L.ker T') (σ T') (hσ T')).1 _
  · have huniq := ((GlobalTheory.T.isDifferenceDerivationOfLifts_add_swap_unique R R₀ I hI π hπ hk (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T)
      (L.ker T) (L.B T'') _ _ (L.ρ (a ≫ b)) _ _ (hθ T T' T'' a b)).2.2.1 (hθ' T T' T'' a b))
    rw [huniq, ← (hzv T T' T'' a b).2]
    have hnat := (GlobalTheory.T.augmentation_sigma_map_natural R R₀ I hI π hπ hk R₁ α (L.B T') (F.obj T') (L.p T') (L.semi T') (L.surj T')
      (L.ker T') (L.B T'') (F.obj T'') (L.p T'') (L.semi T'') (L.surj T'') (L.ker T'') (L.ρ b) (mp F b)
      (L.nat b) (σ T') (σ T'') (hσ T') (hσ T'')).1 (f T T' a)
    have e := congrFun (congrFun (congrFun (congrFun (congrFun hf T) T') T'') a) b
    rw [← e, d1_apply, map_add (f := _), map_sub, hnat]
    rfl

end GlobalTheory.ObsCob
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDefectCoboundaryOfObstructionClassZeroStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_defect_coboundary_of_obstructionClass_zero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (w : Glob1 F) (θ : ∀ (T T' T'' : C) (_ : T ⟶ T') (_ : T' ⟶ T''), Ω[F.obj T⁄R₀] →+ L.B T''), L.IsObs θ → L.IsOb2 α w 0 → ∃ g : ∀ (T T' : C) (_ : T ⟶ T'), L.B T', (∀ T T' a, g T T' a ∈ I.map (algebraMap R (L.B T'))) ∧ ∀ T T' T'' a b, θ T T' T'' a b (w.1 T) = L.ρ b (g T T' a) - g T T'' (a ≫ b) + g T' T'' b := by
  first | exact @GlobalTheory.ObsCob.exists_cob | exact GlobalTheory.ObsCob.exists_cob | (intros; apply GlobalTheory.ObsCob.exists_cob <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctorialLiftsOfObstructionTwoZero
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.Obs

theorem exists_isFun_of_isOb2_zero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Par s₀ → Module.Projective R₀ (GlobForm s₀) → ∀ L : Pre I π (OAff s₀), (∀ w, L.IsOb2 α w 0) → ∃ L' : Pre I π (OAff s₀), L'.IsFun := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α X₀ s₀ hpar hproj L hob

  obtain ⟨θ, -, -, hθ, -⟩ := hob 0

  let Wm : Submodule R (∀ (T T' : AffOp X₀) (_ : T ⟶ T'), L.B T') :=
    { carrier := {g | ∀ T T' a, g T T' a ∈ I.map (algebraMap R (L.B T'))}
      add_mem' := fun hx hy T T' a ↦ Ideal.add_mem _ (hx T T' a) (hy T T' a)
      zero_mem' := fun T T' a ↦ Ideal.zero_mem _
      smul_mem' := fun r g hg T T' a ↦ by
        show r • g T T' a ∈ _
        rw [Algebra.smul_def]; exact Ideal.mul_mem_left _ _ (hg T T' a) }
  let q : (∀ (T T' : AffOp X₀) (_ : T ⟶ T'), L.B T') →ₗ[R]
      (∀ (T T' T'' : AffOp X₀) (_ : T ⟶ T') (_ : T' ⟶ T''), L.B T'') :=
    { toFun := fun g T T' T'' a b ↦ L.ρ b (g T T' a) - g T T'' (a ≫ b) + g T' T'' b
      map_add' := fun g g' ↦ by
        funext T T' T'' a b
        simp only [Pi.add_apply, map_add (f := _)]; abel
      map_smul' := fun r g ↦ by
        funext T T' T'' a b
        simp only [Pi.smul_apply, map_smul, RingHom.id_apply, smul_sub, smul_add] }
  let v : GlobForm s₀ →+ (∀ (T T' T'' : AffOp X₀) (_ : T ⟶ T') (_ : T' ⟶ T''), L.B T'') :=
    { toFun := fun w T T' T'' a b ↦ θ T T' T'' a b (w.1 T)
      map_zero' := by funext T T' T'' a b; simp
      map_add' := fun w w' ↦ by funext T T' T'' a b; simp }
  have hv : ∀ (r : R) (w : GlobForm s₀), v (π r • w) = r • v w := by
    intro r w
    funext T T' T'' a b
    show θ T T' T'' a b (π r • w.1 T) = r • θ T T' T'' a b (w.1 T)
    have e : π r • w.1 T = L.p T (algebraMap R (L.B T) r) • w.1 T := by
      rw [SemiHom.map_algebraMap (L.semi T), algebraMap_smul]
    rw [e, (hθ T T' T'' a b).smul, AlgHom.commutes, ← Algebra.smul_def]
  have hW : ∀ (r : R), π r = 0 → ∀ m ∈ Wm, r • m = 0 := by
    intro r hr m hm
    have hrI : r ∈ I := hk ▸ RingHom.mem_ker.2 hr
    funext T T' a
    show r • m T T' a = 0
    rw [Algebra.smul_def]
    exact mul_eq_zero_of_mem_map hI (Ideal.mem_map_of_mem _ hrI) (hm T T' a)
  have hex : ∀ w : GlobForm s₀, ∃ m ∈ Wm, q m = v w := by
    intro w
    obtain ⟨g, hg, hgθ⟩ := GlobalTheory.T.exists_defect_coboundary_of_obstructionClass_zero R R₀ I hI π hπ hk R₁ α _ (OAff s₀) L w θ hθ (hob w)
    refine ⟨g, hg, ?_⟩
    funext T T' T'' a b
    exact (hgθ T T' T'' a b).symm
  obtain ⟨u, hus, huW, huq⟩ := exists_semilinear_lift_of_projective R R₀ π hπ (GlobForm s₀) hproj _ _ Wm hW q v hv hex

  have hext : ∀ (T T' : AffOp X₀) (a : T ⟶ T'), ∃! ξ : Ω[Sec s₀ T.unop.1⁄R₀] →+ L.B T',
      (∀ b w, ξ (L.p T b • w) = L.ρ a b * ξ w) ∧ (∀ w, ξ w ∈ I.map (algebraMap R (L.B T'))) ∧
        ∀ w : GlobForm s₀, ξ (w.1 T) = u w T T' a := fun T T' a ↦
    exists_unique_formExt R R₀ I hI π hπ hk X₀ s₀ hpar T _ _ (L.p T) (L.semi T) (L.surj T) (L.ker T) (L.ρ a)
      ((Pi.evalAddMonoidHom (fun _ ↦ L.B T') a).comp ((Pi.evalAddMonoidHom _ T').comp ((Pi.evalAddMonoidHom _ T).comp u)))
      (fun r w ↦ by
        show u (π r • w) T T' a = r • u w T T' a
        rw [hus]; rfl) (fun w ↦ huW w T T' a)
  choose ξ hξ huniq using hext
  have hβ : ∀ (T T' : AffOp X₀) (a : T ⟶ T'), ∃ β : L.B T →ₐ[R] L.B T', IsTheta I (L.p T) (L.ρ a) β (ξ T T' a) :=
    fun T T' a ↦ (theta_classify R R₀ _ _ _ I hI π hπ (L.p T) (L.semi T) (L.surj T) (L.ker T) (L.ρ a)).2
      (ξ T T' a) (hξ T T' a).1 (hξ T T' a).2.1
  choose ρ' hρ' using hβ
  have hρ'e : ∀ (T T' : AffOp X₀) (a : T ⟶ T') x, ρ' T T' a x = L.ρ a x - ξ T T' a (D R₀ _ (L.p T x)) := by
    intro T T' a x
    rw [(hρ' T T' a).der]; abel
  have hp0 : ∀ (T T' : AffOp X₀) (a : T ⟶ T') y, L.p T' (ξ T T' a y) = 0 :=
    fun T T' a y ↦ (L.ker T' _).2 ((hξ T T' a).2.1 y)
  have hnat : ∀ (T T' : AffOp X₀) (a : T ⟶ T') x, L.p T' (ρ' T T' a x) = mp (OAff s₀) a (L.p T x) := by
    intro T T' a x
    rw [hρ'e, map_sub, hp0, sub_zero, L.nat]
  let L' : Pre I π (OAff s₀) :=
    { B := L.B, p := L.p, semi := L.semi, surj := L.surj, ker := L.ker, smooth := L.smooth
      ρ := fun {T T'} a ↦ ρ' T T' a
      nat := fun {T T'} a x ↦ hnat T T' a x }
  refine ⟨L', ?_⟩

  have hcomp : ∀ (T T' T'' : AffOp X₀) (a : T ⟶ T') (b : T' ⟶ T'') (y : Ω[Sec s₀ T.unop.1⁄R₀]),
      ξ T T'' (a ≫ b) y = L.ρ b (ξ T T' a y) + ξ T' T'' b (p1 (OAff s₀) a y) - θ T T' T'' a b y := by
    intro T T' T'' a b
    let ψ : Ω[Sec s₀ T.unop.1⁄R₀] →+ L.B T'' :=
      AddMonoidHom.mk' (fun y ↦ L.ρ b (ξ T T' a y) + ξ T' T'' b (p1 (OAff s₀) a y) - θ T T' T'' a b y)
        (fun y z ↦ by simp only [map_add (f := _)]; abel)
    have hψm : ∀ y, ψ y ∈ I.map (algebraMap R (L.B T'')) := fun y ↦
      Ideal.sub_mem _ (Ideal.add_mem _ (algHom_mem_map I (L.ρ b) ((hξ T T' a).2.1 y)) ((hξ T' T'' b).2.1 _))
        ((hθ T T' T'' a b).mem y)
    have e : ψ = ξ T T'' (a ≫ b) := by
      refine huniq T T'' (a ≫ b) ψ ⟨fun c y ↦ ?_, hψm, fun w ↦ ?_⟩
      · have h1 : ψ (L.p T c • y) = L.ρ b (L.ρ a c) * ψ y := by
          show L.ρ b (ξ T T' a (L.p T c • y)) + ξ T' T'' b (p1 (OAff s₀) a (L.p T c • y)) -
              θ T T' T'' a b (L.p T c • y) = L.ρ b (L.ρ a c) * (L.ρ b (ξ T T' a y) + ξ T' T'' b (p1 (OAff s₀) a y) - θ T T' T'' a b y)
          rw [(hξ T T' a).1, oneFormsMapOfFunctorMorphism_smul, ← L.nat, (hξ T' T'' b).1, (hθ T T' T'' a b).smul, map_mul]
          simp only [AlgHom.comp_apply]; ring
        have h2 : L.ρ b (L.ρ a c) = L.ρ (a ≫ b) c + θ T T' T'' a b (D R₀ _ (L.p T c)) := by
          rw [(hθ T T' T'' a b).der]; simp
        rw [h1, h2, add_mul, mul_eq_zero_of_mem_map hI ((hθ T T' T'' a b).mem _) (hψm y), add_zero]
      · show L.ρ b (ξ T T' a (w.1 T)) + ξ T' T'' b (p1 (OAff s₀) a (w.1 T)) - θ T T' T'' a b (w.1 T) = u w T T'' (a ≫ b)
        rw [← w.2 a, (hξ T T' a).2.2, (hξ T' T'' b).2.2]
        have := congrFun (congrFun (congrFun (congrFun (congrFun (huq w) T) T') T'') a) b
        change L.ρ b (u w T T' a) - u w T T'' (a ≫ b) + u w T' T'' b = θ T T' T'' a b (w.1 T) at this
        rw [← this]; abel
    intro y
    rw [← e]; rfl
  intro T T' T'' a b x
  change ρ' T T'' (a ≫ b) x = ρ' T' T'' b (ρ' T T' a x)
  have hD : D R₀ _ (L.p T' (ρ' T T' a x)) = p1 (OAff s₀) a (D R₀ _ (L.p T x)) := by
    rw [hnat, p1_D]
  rw [hρ'e T' T'' b, hD, hρ'e T T' a, map_sub, hρ'e, hcomp]
  have h2 : L.ρ b (L.ρ a x) = L.ρ (a ≫ b) x + θ T T' T'' a b (D R₀ _ (L.p T x)) := by
    rw [(hθ T T' T'' a b).der]; simp
  rw [h2]; abel

end GlobalTheory.Obs
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctorialLiftsOfObstructionTwoZeroStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_functorial_lifts_of_obstructionTwo_zero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Par s₀ → Module.Projective R₀ (GlobForm s₀) → ∀ L : Pre I π (OAff s₀), (∀ w, L.IsOb2 α w 0) → ∃ L' : Pre I π (OAff s₀), L'.IsFun := by
  first | exact @GlobalTheory.Obs.exists_isFun_of_isOb2_zero | exact GlobalTheory.Obs.exists_isFun_of_isOb2_zero | (intros; apply GlobalTheory.Obs.exists_isFun_of_isOb2_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeTwoObstructionClassNatural
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeTwoObstructionClassNatural
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs

theorem extHom_coefHom_restrict {R₀ : Type} [CommRing R₀] (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁]
    {C₂ C' : Type} [Category.{0} C₂] [Category.{0} C'] (F₂ : C₂ ⥤ CommAlgCat.{0} R₀) (G : C' ⥤ C₂) (T : C')
    (y : R₁ ⊗[R₀] F₂.obj ((CoefMap.restrict F₂ G).G.obj T)) :
    extHom R₁ (coefHom (CoefMap.restrict F₂ G) T) y = y := by
  change Algebra.TensorProduct.map (AlgHom.id R₁ R₁) (AlgHom.id R₀ _) y = y
  rw [Algebra.TensorProduct.map_id]; rfl

theorem isOb2_natural : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (C₂ : Type) [Category.{0} C₂] (F₂ : C₂ ⥤ CommAlgCat.{0} R₀) (C' : Type) [Category.{0} C'] (G : C' ⥤ C₂) (n : CoefMap (RingHom.id R₀) F (G ⋙ F₂)) (L : Pre I π F) (L₂ : Pre I π F₂) (w : Glob1 F) (w₂ : Glob1 F₂) (c : GlobalTheory.CatCoh.H2 (ext R₁ F)) (c₂ : GlobalTheory.CatCoh.H2 (ext R₁ F₂)), (∀ T, q1 n T (w.1 _) = w₂.1 (G.obj T)) → L.IsOb2 α w c → L₂.IsOb2 α w₂ c₂ → (extMap R₁ n).pull2 c = (extMap R₁ (CoefMap.restrict F₂ G)).pull2 c₂ := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F C₂ _ F₂ C' _ G n L L₂ w w₂ c c₂ hw h1 h2
  obtain ⟨θ, σ, z, hθ, hσ, rfl, hz⟩ := h1
  obtain ⟨θ₂, σ₂, z₂, hθ₂, hσ₂, rfl, hz₂⟩ := h2
  have hl0 : ∀ T : C', ∃ l : L.B (n.G.obj T) →ₐ[R] L₂.B (G.obj T),
      ∀ b, L₂.p (G.obj T) (l b) = coefHom n T (L.p _ b) := by
    intro T
    haveI := L.smooth (n.G.obj T)
    exact homLift R R₀ I hI π hπ hk _ _ (L.p _) (L.semi _) (L.surj _) (L.ker _) _ _ (L₂.p (G.obj T))
      (L₂.semi _) (L₂.surj _) (L₂.ker _) (coefHom n T)
  choose l hl using hl0
  have hd : ∀ (T T' : C') (a : T ⟶ T') (b : L.B (n.G.obj T)),
      ((L₂.ρ (G.map a)).comp (l T)) b - ((l T').comp (L.ρ (n.G.map a))) b ∈
        I.map (algebraMap R (L₂.B (G.obj T'))) := by
    intro T T' a b
    refine (L₂.ker _ _).1 ?_
    rw [map_sub, sub_eq_zero]
    simp only [AlgHom.comp_apply]
    rw [L₂.nat, hl, hl, L.nat]
    exact (n.naturality a (L.p _ b)).symm
  choose κ hκ using fun (T T' : C') (a : T ⟶ T') ↦ ((theta_classify R R₀ (L.B (n.G.obj T)) (F.obj (n.G.obj T))
    (L₂.B (G.obj T')) I hI π hπ (L.p _) (L.semi _) (L.surj _) (L.ker _)
    ((L₂.ρ (G.map a)).comp (l T))).1 _ (hd T T' a)).exists
  have key : ∀ (T T' T'' : C') (a : T ⟶ T') (b : T' ⟶ T'') (ω : Ω[F.obj (n.G.obj T)⁄R₀]),
      θ₂ _ _ _ (G.map a) (G.map b) (q1 n T ω) + κ T T'' (a ≫ b) ω =
        L₂.ρ (G.map b) (κ T T' a ω) + κ T' T'' b (p1 F (n.G.map a) ω) +
          l T'' (θ _ _ _ (n.G.map a) (n.G.map b) ω) := by
    intro T T' T'' a b ω
    have e1 := (GlobalTheory.T.isDifferenceDerivationOfLifts_comp R R₀ I hI π hπ hk _ _ (L₂.p (G.obj T)) (L₂.semi _) (L₂.surj _) (L₂.ker _) _ _
      (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) (L₂.B (G.obj T'')) (L₂.B (G.obj T'')) _ _ _ (hθ₂ _ _ _ (G.map a) (G.map b))).2
      (l T) (coefHom n T) (hl T)
    have e2 := hκ T T'' (a ≫ b)
    rw [Functor.map_comp, Functor.map_comp] at e2
    have s1 := (isTheta_add R R₀ I hI π hπ hk _ _ (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) _ _ _ _ _ _
      e1).2.1 e2
    have f1 := (GlobalTheory.T.isDifferenceDerivationOfLifts_comp R R₀ I hI π hπ hk _ _ (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) _ _
      (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) (L₂.B (G.obj T')) (L₂.B (G.obj T'')) _ _ _ (hκ T T' a)).1 (L₂.ρ (G.map b))
    have f2 := (GlobalTheory.T.isDifferenceDerivationOfLifts_comp R R₀ I hI π hπ hk _ _ (L.p (n.G.obj T')) (L.semi _) (L.surj _) (L.ker _) _ _
      (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) (L₂.B (G.obj T'')) (L₂.B (G.obj T'')) _ _ _ (hκ T' T'' b)).2
      (L.ρ (n.G.map a)) (mp F (n.G.map a)) (L.nat (n.G.map a))
    have f3 := (GlobalTheory.T.isDifferenceDerivationOfLifts_comp R R₀ I hI π hπ hk _ _ (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) _ _
      (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) (L.B (n.G.obj T'')) (L₂.B (G.obj T'')) _ _ _ (hθ _ _ _ (n.G.map a) (n.G.map b))).1 (l T'')
    have s2 := (isTheta_add R R₀ I hI π hπ hk _ _ (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) _ _ _ _ _ _
      ((isTheta_add R R₀ I hI π hπ hk _ _ (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) _ _ _ _ _ _
        f1).2.1 f2)).2.1 f3
    have e := congrArg (fun t : Ω[F.obj (n.G.obj T)⁄R₀] →+ L₂.B (G.obj T'') ↦ t ω)
      ((isTheta_add R R₀ I hI π hπ hk _ _ (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) _ _ _ (l T'' |>.comp (L.ρ (n.G.map (a ≫ b)))) _ _
        s1).2.2.1 s2)
    exact e
  choose g hgK hg using fun (T T' : C') (a : T ⟶ T') ↦ (sig_basic R R₀ I hI π hπ hk R₁ α _ _
    (L₂.p (G.obj T')) (L₂.semi _) (L₂.surj _) (L₂.ker _) (σ₂ _) (hσ₂ _)).2.2.2 (κ T T' a (w.1 _))
    ((hκ T T' a).mem _)
  have kadd : ∀ {X : C₂} (y y' : R₁ ⊗[R₀] F₂.obj X), α.KerQ y → α.KerQ y' → α.KerQ (y + y') :=
    fun y y' h h' ↦ by unfold Aug.KerQ at *; rw [map_add (f := _), h, h', add_zero]
  have kneg : ∀ {X : C₂} (y : R₁ ⊗[R₀] F₂.obj X), α.KerQ y → α.KerQ (-y) :=
    fun y h ↦ by unfold Aug.KerQ at *; rw [map_neg, h, neg_zero]
  have ksub : ∀ {X : C₂} (y y' : R₁ ⊗[R₀] F₂.obj X), α.KerQ y → α.KerQ y' → α.KerQ (y - y') :=
    fun y y' h h' ↦ by rw [sub_eq_add_neg]; exact kadd _ _ h (kneg _ h')
  rw [CoefMap.pullCohomologyTwo_class, CoefMap.pullCohomologyTwo_class, H2.mk_eq_mk]
  refine ⟨fun T T' a ↦ -g T T' a, ?_⟩
  funext T T' T'' a b
  haveI := L₂.smooth (G.obj T'')
  have nb := sig_natural R R₀ I hI π hπ hk R₁ α _ _ (L₂.p (G.obj T')) (L₂.semi _) (L₂.surj _) (L₂.ker _) _ _
    (L₂.p (G.obj T'')) (L₂.semi _) (L₂.surj _) (L₂.ker _) (L₂.ρ (G.map b)) (mp F₂ (G.map b)) (L₂.nat (G.map b))
    (σ₂ _) (σ₂ _) (hσ₂ _) (hσ₂ _)
  have nl := sig_natural R R₀ I hI π hπ hk R₁ α _ _ (L.p (n.G.obj T'')) (L.semi _) (L.surj _) (L.ker _) _ _
    (L₂.p (G.obj T'')) (L₂.semi _) (L₂.surj _) (L₂.ker _) (l T'') (coefHom n T'') (hl T'')
    (σ _) (σ₂ _) (hσ _) (hσ₂ _)
  change extHom R₁ (mp F₂ (G.map b)) (-g T T' a) - -g T T'' (a ≫ b) + -g T' T'' b =
    extHom R₁ (coefHom n T'') (z.1 _ _ _ (n.G.map a) (n.G.map b)) -
      extHom R₁ (coefHom (CoefMap.restrict F₂ G) T'') (z₂.1 _ _ _ (G.map a) (G.map b))
  rw [extHom_coefHom_restrict, ← sub_eq_zero]
  refine GlobalTheory.T.augmentation_sigma_map_injective_of_flat R R₀ I hI π hπ hk R₁ α _ _ (L₂.p (G.obj T'')) (L₂.semi _) (L₂.surj _) (L₂.ker _)
    (σ₂ _) (hσ₂ _) _ ?_ ?_
  · refine ksub _ _ (kadd _ _ (ksub _ _ ?_ (kneg _ (hgK _ _ _))) (kneg _ (hgK _ _ _)))
      (ksub _ _ (nl.2 _ (hz _ _ _ _ _).1) (hz₂ _ _ _ _ _).1)
    rw [map_neg]; exact kneg _ (nb.2 _ (hgK _ _ _))
  · change σ₂ (G.obj T'') ((_ : R₁ ⊗[R₀] F₂.obj (G.obj T'')) -
      (_ - z₂.1 (G.obj T) (G.obj T') (G.obj T'') (G.map a) (G.map b))) = 0
    simp only [map_sub, map_add (f := _), map_neg]
    rw [← nb.1, ← nl.1, hg, hg, hg, (hz _ _ _ _ _).2, (hz₂ _ _ _ _ _).2, ← hw, w.2 (n.G.map a)]
    linear_combination key T T' T'' a b (w.1 _)

end GlobalTheory.Obs
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeTwoObstructionClassNaturalStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degreeTwoObstructionClass_natural : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (C₂ : Type) [Category.{0} C₂] (F₂ : C₂ ⥤ CommAlgCat.{0} R₀) (C' : Type) [Category.{0} C'] (G : C' ⥤ C₂) (n : CoefMap (RingHom.id R₀) F (G ⋙ F₂)) (L : Pre I π F) (L₂ : Pre I π F₂) (w : Glob1 F) (w₂ : Glob1 F₂) (c : GlobalTheory.CatCoh.H2 (ext R₁ F)) (c₂ : GlobalTheory.CatCoh.H2 (ext R₁ F₂)), (∀ T, q1 n T (w.1 _) = w₂.1 (G.obj T)) → L.IsOb2 α w c → L₂.IsOb2 α w₂ c₂ → (extMap R₁ n).pull2 c = (extMap R₁ (CoefMap.restrict F₂ G)).pull2 c₂ := by
  first | exact @GlobalTheory.Obs.isOb2_natural | exact GlobalTheory.Obs.isOb2_natural | (intros; apply GlobalTheory.Obs.isOb2_natural <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegreeTwoObstructionClass
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegreeTwoObstructionClass
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.Obs

theorem exists_isOb2 : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (w : Glob1 F), ∃ c, L.IsOb2 α w c := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F L w
  have hθ : ∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T''), ∃ θ : Ω[F.obj T⁄R₀] →+ L.B T'',
      IsTheta I (L.p T) ((L.ρ b).comp (L.ρ a)) (L.ρ (a ≫ b)) θ := by
    intro T T' T'' a b
    obtain ⟨θ, hθ, -⟩ := (theta_classify R R₀ (L.B T) (F.obj T) (L.B T'') I hI π hπ (L.p T) (L.semi T)
      (L.surj T) (L.ker T) ((L.ρ b).comp (L.ρ a))).1 (L.ρ (a ≫ b)) (fun x ↦ by
        rw [← L.ker T'', map_sub, AlgHom.comp_apply, L.nat, L.nat, L.nat, mp_comp, sub_self])
    exact ⟨θ, hθ⟩
  choose θ hθ using hθ
  have hσ : ∀ T, ∃ σ : R₁ ⊗[R₀] F.obj T →+ L.B T, α.IsSig (L.p T) σ := fun T ↦
    GlobalTheory.T.exists_augmentation_tensor_sigma_map R R₀ I hI π hπ hk R₁ α (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T) (L.ker T)
  choose σ hσ using hσ
  have hz : ∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T''), ∃ y : R₁ ⊗[R₀] F.obj T'',
      α.KerQ y ∧ σ T'' y = θ T T' T'' a b (w.1 T) := fun T T' T'' a b ↦
    (GlobalTheory.T.augmentation_sigma_map_basic_properties R R₀ I hI π hπ hk R₁ α (L.B T'') (F.obj T'') (L.p T'') (L.semi T'') (L.surj T'')
      (L.ker T'') (σ T'') (hσ T'')).2.2.2 _ ((hθ T T' T'' a b).mem _)
  choose z hzK hzσ using hz
  have key : ∀ (T T' T'' T''' : C) (a : T ⟶ T') (b : T' ⟶ T'') (c : T'' ⟶ T''') (x : Ω[F.obj T⁄R₀]),
      L.ρ c (θ T T' T'' a b x) + θ T T'' T''' (a ≫ b) c x =
        θ T T' T''' a (b ≫ c) x + θ T' T'' T''' b c (p1 F a x) := by
    intro T T' T'' T''' a b c x
    have h1 := (GlobalTheory.T.isDifferenceDerivationOfLifts_comp R R₀ I hI π hπ hk (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T) (L.ker T)
      (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T) (L.ker T) (L.B T'') (L.B T''') _ _ _
      (hθ T T' T'' a b)).1 (L.ρ c)
    have s1 := (GlobalTheory.T.isDifferenceDerivationOfLifts_add_swap_unique R R₀ I hI π hπ hk (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T) (L.ker T)
      (L.B T''') _ _ _ _ _ h1).2.1 (hθ T T'' T''' (a ≫ b) c)
    have h2 := (GlobalTheory.T.isDifferenceDerivationOfLifts_comp R R₀ I hI π hπ hk (L.B T') (F.obj T') (L.p T') (L.semi T') (L.surj T')
      (L.ker T') (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T) (L.ker T) (L.B T''') (L.B T''') _ _ _
      (hθ T' T'' T''' b c)).2 (L.ρ a) (mp F a) (L.nat a)
    have s2 := (GlobalTheory.T.isDifferenceDerivationOfLifts_add_swap_unique R R₀ I hI π hπ hk (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T) (L.ker T)
      (L.B T''') _ _ _ _ _ h2).2.1 (hθ T T' T''' a (b ≫ c))
    rw [Category.assoc] at s1
    rw [AlgHom.comp_assoc] at s2
    have e := (GlobalTheory.T.isDifferenceDerivationOfLifts_add_swap_unique R R₀ I hI π hπ hk (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T) (L.ker T)
      (L.B T''') _ _ (L.ρ (a ≫ b ≫ c)) _ _ s1).2.2.1 s2
    have ex := DFunLike.congr_fun e x
    simp only [AddMonoidHom.add_apply, AddMonoidHom.comp_apply] at ex
    exact ex.trans (add_comm _ _)
  have hZ : (fun T T' T'' a b ↦ z T T' T'' a b : C2 (ext R₁ F)) ∈ Z2 (ext R₁ F) := by
    intro T T' T'' T''' a b c
    haveI := L.smooth T'''
    haveI : Module.Flat R (L.B T''') := Algebra.Smooth.flat R _
    have nat := GlobalTheory.T.augmentation_sigma_map_natural R R₀ I hI π hπ hk R₁ α (L.B T'') (F.obj T'') (L.p T'') (L.semi T'')
      (L.surj T'') (L.ker T'') (L.B T''') (F.obj T''') (L.p T''') (L.semi T''') (L.surj T''') (L.ker T''')
      (L.ρ c) (mp F c) (L.nat c) (σ T'') (σ T''') (hσ T'') (hσ T''')
    have em : ∀ y, mp (ext R₁ F) c y = extHom R₁ (mp F c) y := fun _ ↦ rfl
    rw [← sub_eq_zero]
    apply GlobalTheory.T.augmentation_sigma_map_injective_of_flat R R₀ I hI π hπ hk R₁ α (L.B T''') (F.obj T''') (L.p T''') (L.semi T''')
      (L.surj T''') (L.ker T''') (σ T''') (hσ T''')
    · have k1 := nat.2 _ (hzK T T' T'' a b)
      have k2 := hzK T T'' T''' (a ≫ b) c
      have k3 := hzK T T' T''' a (b ≫ c)
      have k4 := hzK T' T'' T''' b c
      unfold Aug.KerQ at k1 k2 k3 k4 ⊢
      rw [em]
      simp only [map_sub, map_add (f := _), k1, k2, k3, k4, sub_self, add_zero]
    · rw [em, map_sub, map_add (f := _), map_add (f := _), ← (nat.1 _), hzσ, hzσ, hzσ, hzσ, w.2 a, key, sub_self]
  exact ⟨H2.mk _ ⟨_, hZ⟩, θ, σ, ⟨_, hZ⟩, hθ, hσ, rfl, fun T T' T'' a b ↦ ⟨hzK T T' T'' a b, hzσ T T' T'' a b⟩⟩

end GlobalTheory.Obs
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegreeTwoObstructionClassStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_degreeTwoObstructionClass : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (w : Glob1 F), ∃ c, L.IsOb2 α w c := by
  first | exact @GlobalTheory.Obs.exists_isOb2 | exact GlobalTheory.Obs.exists_isOb2 | (intros; apply GlobalTheory.Obs.exists_isOb2 <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaEq
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs

theorem isTheta_eq {R R₀ B B₀ B' : Type} [CommRing R] [CommRing R₀] [CommRing B] [Algebra R B] [CommRing B₀]
    [Algebra R₀ B₀] [CommRing B'] [Algebra R B'] {I : Ideal R} {p : B →+* B₀} (hp : Function.Surjective p)
    {α β : B →ₐ[R] B'} {θ₁ θ₂ : Ω[B₀⁄R₀] →+ B'} (h₁ : IsTheta I p α β θ₁) (h₂ : IsTheta I p α β θ₂) :
    θ₁ = θ₂ := by
  ext w
  have hw : w ∈ Submodule.span B₀ (Set.range (D R₀ B₀)) := by
    rw [span_range_derivation]; trivial
  refine Submodule.span_induction (p := fun z _ ↦ θ₁ z = θ₂ z) ?_ ?_ ?_ ?_ hw
  · rintro z ⟨y, rfl⟩
    obtain ⟨b, rfl⟩ := hp y
    rw [h₁.der, h₂.der]
  · rw [map_zero, map_zero]
  · intro y z _ _ hy hz; rw [map_add (f := _), map_add (f := _), hy, hz]
  · intro c z _ hz
    obtain ⟨b, rfl⟩ := hp c
    rw [h₁.smul, h₂.smul, hz]

theorem isSig_eq {R R₀ R₁ : Type} [CommRing R] [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] {I : Ideal R}
    {π : R →+* R₀} (α : Aug I π R₁) {B B₀ : Type} [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀]
    {p : B →+* B₀} (hp : Function.Surjective p) {σ σ' : R₁ ⊗[R₀] B₀ →+ B} (h : α.IsSig p σ) (h' : α.IsSig p σ') :
    σ = σ' := by
  ext x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul y x =>
    obtain ⟨b, rfl⟩ := hp x
    rw [h, h']
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem isOb2_add : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (w w' : Glob1 F) (c c' : GlobalTheory.CatCoh.H2 (ext R₁ F)), L.IsOb2 α w c → L.IsOb2 α w' c' → L.IsOb2 α (w + w') (c + c') := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F L w w' c c' h h'
  obtain ⟨θ, σ, z, hθ, hσ, rfl, hz⟩ := h
  obtain ⟨θ', σ', z', hθ', hσ', rfl, hz'⟩ := h'
  refine ⟨θ, σ, z + z', hθ, hσ, (map_add _ _ _).symm, fun T T' T'' a b ↦ ?_⟩
  have eθ : θ T T' T'' a b = θ' T T' T'' a b := isTheta_eq (L.surj T) (hθ T T' T'' a b) (hθ' T T' T'' a b)
  have eσ : σ T'' = σ' T'' := isSig_eq α (L.surj T'') (hσ T'') (hσ' T'')
  obtain ⟨k₁, s₁⟩ := hz T T' T'' a b
  obtain ⟨k₂, s₂⟩ := hz' T T' T'' a b
  have ez : (z + z').1 T T' T'' a b = z.1 T T' T'' a b + z'.1 T T' T'' a b := rfl
  refine ⟨?_, ?_⟩
  · unfold Aug.KerQ at k₁ k₂ ⊢
    rw [ez, map_add (f := _), k₁, k₂, add_zero]
  · rw [ez, map_add (f := _), s₁, eσ, s₂, ← eθ]
    exact (map_add (θ T T' T'' a b) (w.1 T) (w'.1 T)).symm

end GlobalTheory.Obs
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptySquareZeroSmoothLiftSystemOfIsFun
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptySquareZeroSmoothLiftSystemOfIsFun
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs

theorem rho_id_eq {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} (hI : I ^ 2 = 0) {π : R →+* R₀}
    {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R₀} (L : Pre I π F) (hL : L.IsFun) (T : C) (y : L.B T) :
    L.ρ (𝟙 T) y = y := by
  set e := L.ρ (𝟙 T) with he
  have idem : ∀ x, e (e x) = e x := fun x ↦ by
    have := hL (𝟙 T) (𝟙 T) x
    rw [Category.comp_id] at this
    exact this.symm
  have hJ := LiftSys.map_sq hI (L.B T)
  have memJ : ∀ x, x - e x ∈ I.map (algebraMap R (L.B T)) := fun x ↦ by
    rw [← L.ker]
    rw [map_sub, L.nat, mp_id, sub_self]
  have sq0 : ∀ u v, u ∈ I.map (algebraMap R (L.B T)) → v ∈ I.map (algebraMap R (L.B T)) → u * v = 0 := by
    intro u v hu hv
    have : u * v ∈ I.map (algebraMap R (L.B T)) ^ 2 := by
      rw [pow_two]; exact Ideal.mul_mem_mul hu hv
    rw [hJ] at this
    simpa using this
  have fix : ∀ z ∈ I.map (algebraMap R (L.B T)), e z = z := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, -, rfl⟩ := hx
      exact e.commutes i
    | zero => exact map_zero e
    | add x w _ _ hx hw => rw [map_add (f := _), hx, hw]
    | smul b x hxm hx =>
      rw [smul_eq_mul, map_mul, hx]
      have := sq0 _ _ (memJ b) hxm
      rw [sub_mul] at this
      exact (sub_eq_zero.1 this).symm
  have h1 := fix _ (memJ y)
  rw [map_sub, idem, sub_self] at h1
  exact (sub_eq_zero.1 h1.symm).symm

theorem nonempty_sys_of_isFun : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (L : Pre I π (OAff s₀)), L.IsFun → Nonempty (Sys I π s₀) := by
  intro R R₀ _ _ I hI π _ _ X₀ s₀ L hL
  exact ⟨{
    F := {
      obj := L.B
      map := fun a ↦ CommAlgCat.ofHom (L.ρ a)
      map_id := fun T ↦ CommAlgCat.hom_ext (AlgHom.ext fun y ↦ rho_id_eq hI L hL T y)
      map_comp := fun a b ↦ CommAlgCat.hom_ext (AlgHom.ext fun x ↦ hL a b x) }
    p := L.p
    semi := L.semi
    nat := fun a b ↦ L.nat a b
    surj := L.surj
    ker := L.ker
    smooth := L.smooth }⟩

end GlobalTheory.Obs
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptySquareZeroSmoothLiftSystemOfIsFunStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_squareZeroSmoothLiftSystem_of_isFun : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (L : Pre I π (OAff s₀)), L.IsFun → Nonempty (Sys I π s₀) := by
  first | exact @GlobalTheory.Obs.nonempty_sys_of_isFun | exact GlobalTheory.Obs.nonempty_sys_of_isFun | (intros; apply GlobalTheory.Obs.nonempty_sys_of_isFun <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothLiftAbelianSchemeSquareZero
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.Obs.exists_smooth_lift_of_abelian : FormSt → PrimitiveExtendedDegTwoVanish → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (A₀ : Over (Sp R₀)) [GrpObj A₀] (g : ℕ), IsAbelianScheme A₀ → SmoothOfRelativeDimension g A₀.hom → ∃ (X : Over (Sp R)) (i : A₀.left ⟶ X.left), IsPullback i A₀.hom X.hom (spMap π) ∧ Smooth X.hom := by
  intro hF hP R R₀ _ _ I hI π hπ hk A₀ _ g hab hsm
  haveI := hsm
  haveI : Smooth A₀.hom := SmoothOfRelativeDimension.smooth g _
  haveI : Smooth (A₀ ⊗ A₀).hom := inferInstanceAs (Smooth (Limits.pullback.fst A₀.hom A₀.hom ≫ A₀.hom))
  obtain ⟨R₁, _, _, ⟨α⟩⟩ := GlobalTheory.Obs.exists_aug R R₀ I hI π hπ hk
  obtain ⟨hPar, hProj, hadd⟩ := hF R₀ A₀ g hab hsm
  obtain ⟨L⟩ := GlobalTheory.T.nonempty_smoothLiftPresystem_squareZero R R₀ I hI π hπ hk _ (OAff A₀.hom) (fun T ↦ smooth_sec_affine A₀.hom T.unop)
  obtain ⟨L₂⟩ := GlobalTheory.T.nonempty_smoothLiftPresystem_squareZero R R₀ I hI π hπ hk _ (OAff (A₀ ⊗ A₀).hom)
    (fun T ↦ smooth_sec_affine (A₀ ⊗ A₀).hom T.unop)
  have key : ∀ w, L.IsOb2 α w 0 := by
    intro w
    obtain ⟨c, hc⟩ := GlobalTheory.T.exists_degreeTwoObstructionClass R R₀ I hI π hπ hk R₁ α _ _ L w
    have nat : ∀ (f : A₀ ⊗ A₀ ⟶ A₀) (w' : GlobForm (A₀ ⊗ A₀).hom) (c' : CatCoh.H2 (ext R₁ (OAff (A₀ ⊗ A₀).hom))),
        IsPullForm (overW f) w w' → L₂.IsOb2 α w' c' → IsExtendedPullbackDegTwo R₁ (overW f) c c' := by
      intro f w' c' hw hc'
      refine GlobalTheory.T.degreeTwoObstructionClass_natural R R₀ I hI π hπ hk R₁ α _ (OAff A₀.hom) _ (OAff (A₀ ⊗ A₀).hom) _ (pairFst f.left)
        (pairPull (overW f)) L L₂ w w' c c' (fun T ↦ ?_) hc hc'
      exact (congrArg (fun z : Glob1 (OPair f.left (A₀ ⊗ A₀).hom) ↦ z.1 T) hw).trans
        (cechDeRhamCoefMapOneForms_restrictAlongFunctor (OAff (A₀ ⊗ A₀).hom) (pairFst f.left) T _)
    obtain ⟨c₁, hc₁⟩ := GlobalTheory.T.exists_degreeTwoObstructionClass R R₀ I hI π hπ hk R₁ α _ _ L₂ (pullForm (overW (fst A₀ A₀)) w)
    obtain ⟨c₂, hc₂⟩ := GlobalTheory.T.exists_degreeTwoObstructionClass R R₀ I hI π hπ hk R₁ α _ _ L₂ (pullForm (overW (snd A₀ A₀)) w)
    have hm : pullForm (overW μ[A₀]) w = pullForm (overW (fst A₀ A₀)) w + pullForm (overW (snd A₀ A₀)) w :=
      hadd w _ _ _ (isPullForm_pullForm _ w) (isPullForm_pullForm _ w) (isPullForm_pullForm _ w)
    have hcm : L₂.IsOb2 α (pullForm (overW μ[A₀]) w) (c₁ + c₂) := by
      rw [hm]; exact isOb2_add R R₀ I hI π hπ hk R₁ α _ _ L₂ _ _ c₁ c₂ hc₁ hc₂
    have h0 : c = 0 := hP R₀ R₁ α.q α.sq A₀ g hab hsm c c₁ c₂
      (nat _ _ _ (isPullForm_pullForm _ w) hcm) (nat _ _ _ (isPullForm_pullForm _ w) hc₁)
      (nat _ _ _ (isPullForm_pullForm _ w) hc₂)
    rw [← h0]; exact hc
  obtain ⟨L', hL'⟩ := GlobalTheory.T.exists_functorial_lifts_of_obstructionTwo_zero R R₀ I hI π hπ hk R₁ α _ A₀.hom hPar hProj L key
  obtain ⟨S⟩ := GlobalTheory.T.nonempty_squareZeroSmoothLiftSystem_of_isFun R R₀ I hI π hπ hk _ A₀.hom L' hL'
  obtain ⟨X, s, i, hci, hsi, ⟨hpres⟩⟩ := GlobalTheory.LiftGlue.exists_presents R R₀ I hI π hπ hk _ A₀.hom S
  obtain ⟨hpb, hsmooth⟩ := GlobalTheory.LiftSys.presents_isLift R R₀ I hI π hπ hk _ A₀.hom S X s i hci hsi hpres
  exact ⟨Over.mk s, i, hpb, hsmooth⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothLiftAbelianSchemeSquareZeroStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_lift_abelian_scheme_square_zero : FormSt → PrimitiveExtendedDegTwoVanish → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (A₀ : Over (Sp R₀)) [GrpObj A₀] (g : ℕ), IsAbelianScheme A₀ → SmoothOfRelativeDimension g A₀.hom → ∃ (X : Over (Sp R)) (i : A₀.left ⟶ X.left), IsPullback i A₀.hom X.hom (spMap π) ∧ Smooth X.hom := by
  first | exact @GlobalTheory.Obs.exists_smooth_lift_of_abelian | exact GlobalTheory.Obs.exists_smooth_lift_of_abelian | (intros; apply GlobalTheory.Obs.exists_smooth_lift_of_abelian <;> assumption)
end

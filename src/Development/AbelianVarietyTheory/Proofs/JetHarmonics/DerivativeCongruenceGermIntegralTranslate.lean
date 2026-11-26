module

public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CoeffDofSubMem
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SurjectiveAppTop
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaNormQuotientEllipticUnitSeries

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLiftPointTranslationFieldPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLiftPointTranslationFieldPoint
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FieldBaseChange (constVal isoVal)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_lift_translT_general {S S' : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (f : S' ⟶ S)
    (P : Over S') (x : P ⟶ (Over.pullback f).obj G) (T : Over S) (e : T.left ⟶ P.left) (r g : T ⟶ G)
    (hg : g.left = e ≫ x.left ≫ pullback.fst G.hom f) :
    ∃ ρ : T.left ⟶ (P ⊗ (Over.pullback f).obj G).left,
      ρ ≫ (fst P ((Over.pullback f).obj G)).left = e ∧
      ρ ≫ (snd P ((Over.pullback f).obj G)).left ≫ pullback.fst G.hom f = r.left ∧
      (ρ ≫ (translT ((Over.pullback f).obj G) x).left) ≫ (fst P ((Over.pullback f).obj G)).left = e ∧
      (ρ ≫ (translT ((Over.pullback f).obj G) x).left) ≫ (snd P ((Over.pullback f).obj G)).left ≫
        pullback.fst G.hom f = (r * g).left := by
  have hx : x.left ≫ pullback.snd G.hom f = P.hom := Over.w x
  have hT : T.hom = (e ≫ P.hom) ≫ f := by
    rw [← Over.w g, hg, ← hx]
    simp only [Category.assoc, pullback.condition]
  let T' : Over S' := Over.mk (e ≫ P.hom)
  let e' : T' ⟶ P := Over.homMk e rfl
  let r' : T' ⟶ (Over.pullback f).obj G :=
    Over.homMk (pullback.lift r.left (e ≫ P.hom) ((Over.w r).trans hT)) (pullback.lift_snd _ _ _)
  have hr' : r'.left ≫ pullback.fst G.hom f = r.left := pullback.lift_fst _ _ _
  let U : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk (𝟙 T.left) ((Category.id_comp _).trans hT)
  have hU : ∀ z : T ⟶ G, (U ≫ z).left = z.left := fun z => Category.id_comp _
  have h1 : lift e' r' ≫ translT ((Over.pullback f).obj G) x ≫ fst _ _ = e' := by
    simp [translT]
  have h2 : lift e' r' ≫ translT ((Over.pullback f).obj G) x ≫ snd _ _ = (e' ≫ x) * r' := by
    simp only [translT, translPt, lift_snd, Hom.mul_def]
    rw [← Category.assoc, comp_lift, lift_fst_assoc, lift_snd]
  have h3 := (isGrpPullback_pullback G f).2 T' (e' ≫ x) r' (U ≫ g) (U ≫ r)
    ((hU g).trans (hg.trans (Category.assoc _ _ _).symm)) ((hU r).trans hr'.symm)
  refine ⟨(lift e' r').left, congrArg (fun z => z.left) (lift_fst e' r'), ?_, ?_, ?_⟩
  · exact ((Category.assoc _ _ _).symm.trans
      (congrArg (fun z : T' ⟶ (Over.pullback f).obj G => z.left ≫ pullback.fst G.hom f) (lift_snd e' r'))).trans hr'
  · exact (Category.assoc _ _ _).trans (congrArg (fun z => z.left) h1)
  · have h4 : ((lift e' r').left ≫ (translT ((Over.pullback f).obj G) x).left) ≫
        (snd P ((Over.pullback f).obj G)).left = ((e' ≫ x) * r').left :=
      (Category.assoc _ _ _).trans (congrArg (fun z => z.left) h2)
    refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ pullback.fst G.hom f) h4)).trans (h3.symm.trans ?_)
    rw [← MonObj.comp_mul, hU, mul_comm]

theorem exists_lift_translT : ∀ (R : Type) [CommRing R] [IsDomain R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (F : Type) [Field F] [Algebra (FractionRing R) F] (x : TFK (R := R) F ⟶ (Over.pullback (jK R)).obj G) (T : Over (Spec (CommRingCat.of R))) (e : T.left ⟶ Spec (CommRingCat.of F)) (r g : T ⟶ G), g.left = e ≫ x.left ≫ pullback.fst G.hom (jK R) → ∃ ρ : T.left ⟶ (UnifPre.GF (G := G) F).left, ρ ≫ (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left = e ∧ ρ ≫ UnifPre.gFK (G := G) F = r.left ∧ (ρ ≫ (translT ((Over.pullback (jK R)).obj G) x).left) ≫ (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left = e ∧ (ρ ≫ (translT ((Over.pullback (jK R)).obj G) x).left) ≫ UnifPre.gFK (G := G) F = (r * g).left := by
  intro R _ _ G _ _ F _ _ x T e r g hg
  exact exists_lift_translT_general G (jK R) (TFK (R := R) F) x T e r g hg

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLiftPointTranslationFieldPointStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FieldBaseChange (constVal isoVal)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_point_translation_fieldPoint : ∀ (R : Type) [CommRing R] [IsDomain R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (F : Type) [Field F] [Algebra (FractionRing R) F] (x : TFK (R := R) F ⟶ (Over.pullback (jK R)).obj G) (T : Over (Spec (CommRingCat.of R))) (e : T.left ⟶ Spec (CommRingCat.of F)) (r g : T ⟶ G), g.left = e ≫ x.left ≫ pullback.fst G.hom (jK R) → ∃ ρ : T.left ⟶ (UnifPre.GF (G := G) F).left, ρ ≫ (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left = e ∧ ρ ≫ UnifPre.gFK (G := G) F = r.left ∧ (ρ ≫ (translT ((Over.pullback (jK R)).obj G) x).left) ≫ (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left = e ∧ (ρ ≫ (translT ((Over.pullback (jK R)).obj G) x).left) ≫ UnifPre.gFK (G := G) F = (r * g).left := by
  first | exact @GlobalTheory.exists_lift_translT | exact GlobalTheory.exists_lift_translT | (intros; apply GlobalTheory.exists_lift_translT <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FnEigenEquationOfForallGeometricPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FnEigenEquationOfForallGeometricPoint
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FieldBaseChange (constVal isoVal)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EigenSpread

theorem gs_sum {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {l : ℕ}
    (a : Fin l → Γ(X, U)) : gs f y U (∑ i, a i) = ∑ i, gs f y U (a i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gs_eq f y U h, map_sum]

theorem exists_defect_sum {O : Type} [CommRing O] {Y G H : Scheme.{0}} (m s : Y ⟶ G) (p : Y ⟶ H)
    (π : H ⟶ Spec (CommRingCat.of O)) (V : G.Opens) {l : ℕ} (c : Fin l → O) (t : Fin l → Γ(G, V))
    (u : Γ(H, ⊤)) : ∃ f : Γ(Y, m ⁻¹ᵁ V ⊓ s ⁻¹ᵁ V), ∀ (Z : Scheme.{0}) (g : Z ⟶ Y) (z : Z),
      g z ∈ m ⁻¹ᵁ V ⊓ s ⁻¹ᵁ V → gs g z (m ⁻¹ᵁ V ⊓ s ⁻¹ᵁ V) f =
        ∑ i, constVal ((g ≫ p) ≫ π) z (c i) * gs (g ≫ m) z V (t i) -
          gs (g ≫ p) z ⊤ u * ∑ i, constVal ((g ≫ p) ≫ π) z (c i) * gs (g ≫ s) z V (t i) := by
  choose f hf using fun i => EigenAll.exists_defect m s p V (t i) u
  refine ⟨∑ i, resTop _ (scal (p ≫ π) (c i)) * f i, fun Z g z hz => ?_⟩
  rw [gs_sum g z _ hz, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gs_mul g z _ hz, FieldBaseChange.gs_const _ g z _ hz, hf i Z g z hz, Category.assoc]
  ring

end GlobalTheory.EigenSpread

namespace GlobalTheory

theorem fn_eigen_equation_of_forall_geometric_point :
    ∀ (V O F : Type) [CommRing V] [CommRing O] [Field F] [IsAlgClosed F] [Algebra O F], Function.Injective (algebraMap O F) → ∀ (β : V →+* O) (G : Over (Spec (CommRingCat.of V))) [GrpObj G], Flat G.hom → ∀ (Z : Over (Spec (CommRingCat.of O))), IsFinite Z.hom → Flat Z.hom → IsReduced (Pdiv.specO O F ⊗ Z).left → ∀ (jZ : Z.left ⟶ G.left), jZ ≫ G.hom = Z.hom ≫ Spec.map (CommRingCat.ofHom β) → ∀ (U : G.left.Opens) (l : ℕ) (c : Fin l → O) (s : Fin l → Γ(G.left, U)) (k : Γ(Z.left, ⊤)), (∀ (T : Over (Spec (CommRingCat.of V))) (e : T.left ⟶ Spec (CommRingCat.of F)) (c₀ : Pdiv.specO O F ⟶ Z) (r g : T ⟶ G), g.left = (e ≫ c₀.left) ≫ jZ → ∀ z : T.left, r.left z ∈ U → (r * g).left z ∈ U → ∑ i, constVal e z (algebraMap O F (c i)) * gs (r * g).left z U (s i) = gs (e ≫ c₀.left) z ⊤ k * ∑ i, constVal e z (algebraMap O F (c i)) * gs r.left z U (s i)) → ∀ (T : Over (Spec (CommRingCat.of V))) (q : T.left ⟶ Z.left) (r g : T ⟶ G), g.left = q ≫ jZ → ∀ z : T.left, r.left z ∈ U → (r * g).left z ∈ U → ∑ i, constVal (q ≫ Z.hom) z (c i) * gs (r * g).left z U (s i) = gs q z ⊤ k * ∑ i, constVal (q ≫ Z.hom) z (c i) * gs r.left z U (s i) := by
  intro V O F _ _ _ _ _ hinj β G _ hG Z hfin hflat hred jZ hj U l c s k hyp
  let Y : Over (Spec (CommRingCat.of O)) :=
    Over.mk (pullback.snd G.hom (Spec.map (CommRingCat.ofHom β)))
  have hY : Flat Y.hom := inferInstanceAs (Flat (pullback.snd G.hom (Spec.map (CommRingCat.ofHom β))))
  let p : (Z ⊗ Y).left ⟶ Z.left := pullback.fst Z.hom Y.hom
  let PV : Over (Spec (CommRingCat.of V)) := Over.mk (p ≫ Z.hom ≫ Spec.map (CommRingCat.ofHom β))
  let r₀ : PV ⟶ G := Over.homMk (pullback.snd Z.hom Y.hom ≫ pullback.fst G.hom (Spec.map (CommRingCat.ofHom β))) (by
    change _ = pullback.fst Z.hom Y.hom ≫ Z.hom ≫ _
    rw [Category.assoc, pullback.condition, pullback.condition_assoc]
    rfl)
  let g₀ : PV ⟶ G := Over.homMk (p ≫ jZ) (by
    change _ = p ≫ Z.hom ≫ _
    rw [Category.assoc, hj])
  obtain ⟨f, hf⟩ := EigenSpread.exists_defect_sum (Y := (Z ⊗ Y).left) (r₀ * g₀).left r₀.left p Z.hom U c s k
  have h0 : f = 0 := by
    refine section_eq_zero_of_forall_geometric_point O F hinj Z Y hfin hflat hred hY _ f fun c₀ => ?_
    refine fn_ext fun x hx => ?_
    rw [EigenAll.gs_zero, gs_pull (𝟙 _) (c₀ ▷ Y).left x _ hx, Category.id_comp, hf _ _ x hx, sub_eq_zero]
    let ρ : Over.mk ((c₀ ▷ Y).left ≫ PV.hom) ⟶ PV := Over.homMk (c₀ ▷ Y).left rfl
    let e : (Pdiv.specO O F ⊗ Y).left ⟶ Spec (CommRingCat.of F) := pullback.fst (Pdiv.specO O F).hom Y.hom
    have e₁ : (c₀ ▷ Y).left ≫ p = e ≫ c₀.left := Over.whiskerRight_left_fst c₀
    have e₂ : (e ≫ c₀.left) ≫ Z.hom = e ≫ Spec.map (CommRingCat.ofHom (algebraMap O F)) := by
      rw [Category.assoc, Over.w c₀]
      rfl
    have e₃ : (ρ ≫ r₀ * ρ ≫ g₀).left = (c₀ ▷ Y).left ≫ (r₀ * g₀).left := by
      rw [← MonObj.comp_mul]
      rfl
    have := hyp _ e c₀ (ρ ≫ r₀) (ρ ≫ g₀) (by rw [← e₁, Category.assoc]; rfl) x hx.2 (by rw [e₃]; exact hx.1)
    rw [e₃] at this
    rw [e₁, e₂]
    simp only [FieldBaseChange.constVal_specMap]
    exact this
  intro T q r g hg z hr hrg
  have hT : T.hom = q ≫ Z.hom ≫ Spec.map (CommRingCat.ofHom β) := by
    rw [← Over.w g, hg, Category.assoc, hj]
  let a : T.left ⟶ (Z ⊗ Y).left := pullback.lift q
    (pullback.lift r.left (q ≫ Z.hom) (by rw [Over.w r, hT, Category.assoc]))
    (pullback.lift_snd _ _ _).symm
  have e₁ : a ≫ p = q := pullback.lift_fst _ _ _
  let ρ : T ⟶ PV := Over.homMk a (by
    change a ≫ p ≫ _ = _
    rw [← Category.assoc, e₁, hT])
  have e₂ : a ≫ r₀.left = r.left := by
    change a ≫ pullback.snd Z.hom Y.hom ≫ pullback.fst G.hom (Spec.map (CommRingCat.ofHom β)) = _
    rw [← Category.assoc, pullback.lift_snd, pullback.lift_fst]
  have e₃ : ρ ≫ r₀ = r := Over.OverMorphism.ext e₂
  have e₄ : ρ ≫ g₀ = g := Over.OverMorphism.ext (by
    change a ≫ p ≫ jZ = _
    rw [← Category.assoc, e₁, hg])
  have e₅ : a ≫ (r₀ * g₀).left = (r * g).left := by
    rw [← e₃, ← e₄, ← MonObj.comp_mul]
    rfl
  rw [← e₅] at hrg
  rw [← e₂] at hr
  have := hf _ a z ⟨hrg, hr⟩
  rw [h0, EigenAll.gs_zero, e₁, e₂, e₅] at this
  exact sub_eq_zero.1 this.symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FnEigenEquationOfForallGeometricPointStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FieldBaseChange (constVal isoVal)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fn_eigen_equation_of_forall_geometric_point_alt : ∀ (V O F : Type) [CommRing V] [CommRing O] [Field F] [IsAlgClosed F] [Algebra O F], Function.Injective (algebraMap O F) → ∀ (β : V →+* O) (G : Over (Spec (CommRingCat.of V))) [GrpObj G], Flat G.hom → ∀ (Z : Over (Spec (CommRingCat.of O))), IsFinite Z.hom → Flat Z.hom → IsReduced (Pdiv.specO O F ⊗ Z).left → ∀ (jZ : Z.left ⟶ G.left), jZ ≫ G.hom = Z.hom ≫ Spec.map (CommRingCat.ofHom β) → ∀ (U : G.left.Opens) (l : ℕ) (c : Fin l → O) (s : Fin l → Γ(G.left, U)) (k : Γ(Z.left, ⊤)), (∀ (T : Over (Spec (CommRingCat.of V))) (e : T.left ⟶ Spec (CommRingCat.of F)) (c₀ : Pdiv.specO O F ⟶ Z) (r g : T ⟶ G), g.left = (e ≫ c₀.left) ≫ jZ → ∀ z : T.left, r.left z ∈ U → (r * g).left z ∈ U → ∑ i, constVal e z (algebraMap O F (c i)) * gs (r * g).left z U (s i) = gs (e ≫ c₀.left) z ⊤ k * ∑ i, constVal e z (algebraMap O F (c i)) * gs r.left z U (s i)) → ∀ (T : Over (Spec (CommRingCat.of V))) (q : T.left ⟶ Z.left) (r g : T ⟶ G), g.left = q ≫ jZ → ∀ z : T.left, r.left z ∈ U → (r * g).left z ∈ U → ∑ i, constVal (q ≫ Z.hom) z (c i) * gs (r * g).left z U (s i) = gs q z ⊤ k * ∑ i, constVal (q ≫ Z.hom) z (c i) * gs r.left z U (s i) := by
  first | exact @GlobalTheory.fn_eigen_equation_of_forall_geometric_point | exact GlobalTheory.fn_eigen_equation_of_forall_geometric_point | (intros; apply GlobalTheory.fn_eigen_equation_of_forall_geometric_point <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CharacterEqWeilPairing
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem datum_character_eq_zpow {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H)
    {F : Type} [Field F] {M : ℕ} (hM : 0 < M) {ζ : Fˣ} (hζ : IsPrimitiveRoot ζ M)
    (φ : Dw.La →+ Additive Fˣ) (hφ : ∀ a, φ (M • a) = 0) :
    ∃ d : Dw.La, ∀ a, Additive.toMul (φ a) = ζ ^ Dw.EF a d := by
  haveI : NeZero M := ⟨hM.ne'⟩
  haveI : Module.Projective ℤ Dw.La := by
    obtain ⟨s, hs⟩ := Module.projective_def'.1 Dw.proj
    haveI : Module.Free ℤ (Dw.La →₀ 𝓞 E) := inferInstance
    exact Module.Projective.of_split (s.restrictScalars ℤ)
      ((Finsupp.linearCombination (𝓞 E) id).restrictScalars ℤ)
      (LinearMap.ext fun x => LinearMap.congr_fun hs x)
  let f : ℤ →ₗ[ℤ] Additive Fˣ := LinearMap.toSpanSingleton ℤ (Additive Fˣ) (Additive.ofMul ζ)
  have hmem : ∀ a, φ.toIntLinearMap a ∈ LinearMap.range f := by
    intro a
    have h1 : Additive.toMul (φ a) ∈ rootsOfUnity M F := by
      rw [mem_rootsOfUnity, ← toMul_nsmul, ← map_nsmul, hφ]; rfl
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_mem_rootsOfUnity h1
    refine ⟨i, ?_⟩
    change (i : ℤ) • Additive.ofMul ζ = φ a
    rw [natCast_zsmul, ← ofMul_pow, hi]; rfl
  obtain ⟨ψ, hψ⟩ := Module.projective_lifting_property f.rangeRestrict
    (φ.toIntLinearMap.codRestrict _ hmem) f.surjective_rangeRestrict
  obtain ⟨d, hd⟩ := Dw.unimod.2 ψ
  refine ⟨-d, fun a => ?_⟩
  have skew : Dw.EF a (-d) = ψ a := by
    have := Dw.alt (d + a)
    simp only [map_add (f := _), LinearMap.add_apply, Dw.alt] at this
    rw [map_neg, ← hd]
    linarith
  have h2 : f (ψ a) = φ a := congrArg Subtype.val (LinearMap.congr_fun hψ a)
  rw [skew, ← h2]
  rfl

theorem character_eq_weil_pairing :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F] (A : PolAV (Sp (FractionRing R))), letI := H.starRing; ∀ (oA : A.OAct (𝓞 E)) (Dw : Datum H) (_I : TateIso Dw F (TFK (R := R) F ⟶ A.A) (fun a g => g ≫ oA.act a) (fun n g g' c => WeilIs A.A A.L n g g' (unitOn c))) (N k : ℕ), 1 ≤ N → 1 ≤ k → Nat.Coprime N k → ∀ β u u' : 𝓞 E, β * star β = (N : 𝓞 E) → u * β + u' * star β = 1 → ∀ κ : (TFK (R := R) F ⟶ A.A) → Fˣ, (∀ z z', z ≫ oA.act β = 1 → z' ≫ oA.act β = 1 → κ (z * z') = κ z * κ z') → ∃ b : TFK (R := R) F ⟶ A.A, b ≫ oA.act (star β) = 1 ∧ ∀ z, z ≫ oA.act β = 1 → WeilIs A.A A.L ((k * N : ℕ) : ℤ) z b (unitOn (κ z)) := by
  intro E _ _ _ H R _ _ F _ _ A
  let _ := H.starRing
  intro oA Dw I N k hN hk hco β u u' hβ huu κ hκ
  have hM : 0 < k * N := Nat.mul_pos hk hN
  have hlin : ∀ (c : 𝓞 E) b, I.ev (k * N) (c • b) = I.ev (k * N) b ≫ oA.act c := fun c b => I.lin _ c b
  obtain ⟨t, k', htk⟩ := (Nat.isCoprime_iff_coprime.2 hco).map (Int.castRingHom (𝓞 E))
  simp only [eq_intCast, Int.cast_natCast] at htk
  obtain ⟨ε, w, v, hw, hv⟩ : ∃ ε w v : 𝓞 E, β * ε = ((k * N : ℕ) : 𝓞 E) * w ∧ 1 = ε + v * β := by
    refine ⟨k * k' * u' * star β, k' * u', star β * t + k * k' * u, ?_, ?_⟩
    · push_cast
      rw [← hβ]; ring
    · linear_combination (-(k * k' : 𝓞 E)) * huu - htk - t * hβ
  have hzero : ∀ (c : 𝓞 E) (a : Dw.La), I.ev (k * N) ((((k * N : ℕ) : 𝓞 E) * c) • a) = 1 := by
    intro c a
    rw [mul_smul, Nat.cast_smul_eq_nsmul]
    exact (I.ker _ hM _).2 ⟨_, rfl⟩
  have hkill : ∀ a, I.ev (k * N) (ε • a) ≫ oA.act β = 1 := by
    intro a
    rw [← hlin, smul_smul, hw, hzero]
  have hfix : ∀ a, I.ev (k * N) a ≫ oA.act β = 1 → I.ev (k * N) (ε • a) = I.ev (k * N) a := by
    intro a ha
    obtain ⟨f, hf⟩ := (I.ker _ hM (β • a)).1 (by rw [hlin]; exact ha)
    have h1 : a = ε • a + (k * N) • (v • f) := by
      rw [smul_comm (k * N) v f, ← hf, smul_smul, ← add_smul, ← hv, one_smul]
    conv_rhs => rw [h1, I.add, (I.ker _ hM _).2 ⟨_, rfl⟩, _root_.mul_one]
  let φ : Dw.La →+ Additive Fˣ := AddMonoidHom.mk' (fun a => Additive.ofMul (κ (I.ev (k * N) (ε • a))))
    (fun a b => by rw [smul_add, I.add, hκ _ _ (hkill a) (hkill b), ofMul_mul])
  have hφ : ∀ a, φ ((k * N) • a) = 0 := by
    intro a
    rw [← map_zero φ]
    change Additive.ofMul (κ (I.ev (k * N) (ε • (k * N) • a))) = Additive.ofMul (κ (I.ev (k * N) (ε • 0)))
    rw [smul_comm ε (k * N) a, (I.ker _ hM _).2 ⟨_, rfl⟩, smul_zero,
      (I.ker _ hM 0).2 ⟨0, (smul_zero _).symm⟩]
  obtain ⟨d, hd⟩ := datum_character_eq_zpow Dw hM (I.ζ_prim _ hM) φ hφ
  refine ⟨I.ev (k * N) (H.bar ε • d), ?_, fun z hz => ?_⟩
  · rw [← hlin, smul_smul]
    change I.ev (k * N) ((H.bar β * H.bar ε) • d) = 1
    rw [← map_mul, hw, map_mul, map_natCast, hzero]
  · have hzN : z ^ N = 1 := pow_eq_one_of_kill oA.toRingAct (by rw [_root_.mul_comm]; exact hβ) z hz
    obtain ⟨a, rfl⟩ := (I.onto _ hM z).1 (by rw [pow_mul', hzN, one_pow])
    have h1 : κ (I.ev (k * N) a) = I.ζ (k * N) ^ Dw.EF a (H.bar ε • d) := by
      rw [← Dw.adj, ← hd]
      change _ = κ (I.ev (k * N) (ε • ε • a))
      rw [hfix _ (hkill a), hfix a hz]
    rw [h1]
    exact I.isom _ hM _ _

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DerivativeCongruenceGermIntegralTranslate
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open GlobalTheory GlobalTheory.FamGerm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EigenGerm

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt FB FGLaw ev pt Dof)
open GlobalTheory.FieldBaseChange (constVal constVal_specMap gs_scal)
open GlobalTheory.JetSer (fnVal IsSer1)

theorem gs_comp_eq_constVal {A : Type} [CommRing A] {X Z : Scheme.{0}} (e : Z ⟶ Spec (CommRingCat.of A))
    (p : Spec (CommRingCat.of A) ⟶ X) (U : X.Opens) (h : ⊤ ≤ p ⁻¹ᵁ U) (a : Γ(X, U)) (z : Z) :
    gs (e ≫ p) z U a = constVal e z (fnVal p U a) := by
  rw [fnVal, dite_eq_left h, constVal]
  have i : ∀ b, (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom b) = b :=
    fun b => congrArg (fun q => q.hom b) (Scheme.ΓSpecIso (CommRingCat.of A)).hom_inv_id
  rw [i]
  exact (gs_pull e p z U (h trivial) a).symm.trans (gs_res e z h trivial _).symm

theorem dof_of_tangent (hJ : JetSer.JetAlgSt) (hRep : JetSer.RepSt) (hSer : JetSer.SerSt) {V O : Type} [CommRing V]
    [IsLocalRing V] [CommRing O] (β : V →+* O) (I : Ideal O)
    {G : Over (Spec (CommRingCat.of V))} [GrpObj G] {d : ℕ} {x : JetSer.Fam G (Fin d)} (hx : Chart.IsUnivChart G d x)
    (Gl : FGLaw V d) (hGl : JetSer.IsLawOf x Gl.F) {U : G.left.Opens} (hU : ⊤ ≤ η[G].left ⁻¹ᵁ U) {l : ℕ}
    (s : Fin l → Γ(G.left, U)) (S : Fin l → PS V 1 d) (hS : ∀ i, IsSer1 x U (s i) (S i)) (c : Fin l → O)
    {Z : Over (Spec (CommRingCat.of O))} (jZ : Z.left ⟶ G.left)
    (hj : jZ ≫ G.hom = Z.hom ≫ Spec.map (CommRingCat.ofHom β)) (k : Γ(Z.left, ⊤))
    (hall : ∀ (T : Over (Spec (CommRingCat.of V))) (q : T.left ⟶ Z.left) (r g : T ⟶ G), g.left = q ≫ jZ →
      ∀ z : T.left, r.left z ∈ U → (r * g).left z ∈ U →
      ∑ i, constVal (q ≫ Z.hom) z (c i) * gs (r * g).left z U (s i) =
        gs q z ⊤ k * ∑ i, constVal (q ≫ Z.hom) z (c i) * gs r.left z U (s i))
    (e : Fin d → O) (yy : O) (w : Pdiv.specO O (DualNumber (O ⧸ I)) ⟶ Z)
    (φ : Chart.JetR V (Fin d) 1 →+* DualNumber (O ⧸ I))
    (hφ : ∀ i, φ (Chart.zR 1 i) = TrivSqZeroExt.inr (Ideal.Quotient.mk I (e i)))
    (hw : w.left ≫ jZ = Spec.map (CommRingCat.ofHom φ) ≫ (x 1).left)
    (hk : fnVal w.left ⊤ k = 1 + TrivSqZeroExt.inr (Ideal.Quotient.mk I yy)) :
    Dof (fun i => MvPowerSeries.map ((Ideal.Quotient.mk I).comp β) (Gl.F i)) (fun i => Ideal.Quotient.mk I (e i))
        (MvPowerSeries.map (Ideal.Quotient.mk I) (∑ i, MvPowerSeries.C (c i) * MvPowerSeries.map β (S i))) =
      MvPowerSeries.C (Ideal.Quotient.mk I yy) *
        MvPowerSeries.map (Ideal.Quotient.mk I) (∑ i, MvPowerSeries.C (c i) * MvPowerSeries.map β (S i)) := by
  letI : Algebra V (O ⧸ I) := ((Ideal.Quotient.mk I).comp β).toAlgebra
  have hc : φ.comp (algebraMap V _) = (algebraMap O (DualNumber (O ⧸ I))).comp β := by
    have h₁ : Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom (algebraMap V _)) =
        Spec.map (CommRingCat.ofHom (algebraMap O (DualNumber (O ⧸ I)))) ≫ Spec.map (CommRingCat.ofHom β) := by
      have a₁ : (x 1).left ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap V _)) := Over.w (x 1)
      have a₂ : w.left ≫ Z.hom = Spec.map (CommRingCat.ofHom (algebraMap O (DualNumber (O ⧸ I)))) := Over.w w
      rw [← a₁, ← a₂, ← Category.assoc, ← hw, Category.assoc, Category.assoc, hj]
    rw [← Spec.map_comp, ← Spec.map_comp] at h₁
    exact congrArg (fun q => q.hom) (Spec.map_injective h₁)
  let φ' : Chart.JetR V (Fin d) 1 →ₐ[V] DualNumber (O ⧸ I) := { φ with commutes' := fun v => RingHom.congr_fun hc v }
  have e₀ : MvPowerSeries.map (Ideal.Quotient.mk I) (∑ i, MvPowerSeries.C (c i) * MvPowerSeries.map β (S i)) =
      ∑ i, MvPowerSeries.C (Ideal.Quotient.mk I (c i)) * MvPowerSeries.map (algebraMap V (O ⧸ I)) (S i) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, MvPowerSeries.map_C]
    congr 1
  rw [e₀]
  refine dof_baseChange hJ hRep hSer hx Gl hGl hU s S hS _ _ _ φ' hφ fun A _ _ θ r h₁ h₂ => ?_
  refine JetSer.FBOf.eq_of_germ fun z => ?_
  have H := hall (Chart.sp (R₀ := V) A) (Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ w.left) r
    (Chart.spMap θ ≫ Chart.spMap φ' ≫ x 1) (by rw [Category.assoc, hw]; rfl) z (h₁ trivial) (h₂ trivial)
  let Φ := ((Spec (CommRingCat.of A)).presheaf.germ ⊤ z trivial).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  have c₀ : ∀ b, constVal (𝟙 (Spec (CommRingCat.of A))) z b = Φ b := fun b => gs_eq _ z ⊤ trivial _
  have c₁ : ∀ o, constVal ((Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ w.left) ≫ Z.hom) z o =
      Φ (θ (TrivSqZeroExt.inl (Ideal.Quotient.mk I o))) := fun o => by
    have a₂ : w.left ≫ Z.hom = Spec.map (CommRingCat.ofHom (algebraMap O (DualNumber (O ⧸ I)))) := Over.w w
    rw [Category.assoc, a₂, constVal_specMap, ← Category.id_comp (Spec.map _), constVal_specMap, c₀]
    rfl
  have c₂ : gs (Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ w.left) z ⊤ k =
      Φ (θ (1 + TrivSqZeroExt.inr (Ideal.Quotient.mk I yy))) := by
    rw [gs_comp_eq_constVal _ _ ⊤ le_top, hk, ← Category.id_comp (Spec.map _), constVal_specMap, c₀]
    rfl
  have c₃ := fun i => PullGerm.gs_eq_germ_fnVal _ U h₁ (s i) z
  have c₄ := fun i => PullGerm.gs_eq_germ_fnVal _ U h₂ (s i) z
  show Φ _ = Φ _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_mul, map_sum, map_sum, ← c₂]
  simp only [map_mul, ← c₁]
  refine Eq.trans (Finset.sum_congr rfl fun i _ => congrArg _ (c₄ i).symm) (H.trans ?_)
  exact congrArg _ (Finset.sum_congr rfl fun i _ => congrArg _ (c₃ i))

theorem comp_map_eq_one {S S' : Scheme.{0}} (f : S' ⟶ S) {G : Over S} [GrpObj G] (a : G ⟶ G) {T : Over S'}
    (x : T ⟶ (Over.pullback f).obj G)
    (h : (x.left ≫ pullback.fst G.hom f) ≫ a.left = (x.left ≫ pullback.fst G.hom f) ≫ (1 : G ⟶ G).left) :
    x ≫ (Over.pullback f).map a = 1 := by
  let P := pushHom (isGrpPullback_pullback G f) T
  have e : P (x ≫ (Over.pullback f).map a) = P 1 := by
    rw [map_one, ← MonObj.comp_one (P x)]
    apply Over.OverMorphism.ext
    refine Eq.trans ?_ h
    show (x.left ≫ ((Over.pullback f).map a).left) ≫ pullback.fst G.hom f = _
    rw [Category.assoc, Category.assoc]
    exact congrArg _ (pullback.lift_fst _ _ _)
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact congrArg (fun q => q.left) e
  · exact (Over.w _).trans (Over.w _).symm

theorem gs_div_mul {X Z : Scheme.{0}} {L : LB X} (f : X ⟶ X) {N q : ℕ} (k : ℕ) (j : L.ι)
    (mu : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![(N : ℤ), -1])) (σ : H0 L q)
    (hle : LB.wchart L ![𝟙 X, f] (fun _ => j) ≤ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => j))
    (m : Γ(X, LB.wchart L ![𝟙 X, f] (fun _ => j))ˣ) (hm : m = mu.s (fun _ => j))
    (s : Γ(X, LB.wchart L ![𝟙 X, f] (fun _ => j)))
    (hs : s * m.val ^ k = (X.presheaf.map (homOfLE hle).op).hom (σ.f (fun _ => j)))
    (ψ : Z ⟶ X) (z : Z) (hz : ψ z ∈ LB.wchart L ![𝟙 X, f] (fun _ => j)) {J : (Z ⟶ X) → L.ι}
    (hJ : ∀ χ : Z ⟶ X, χ z ∈ L.U j → J χ = j) :
    sval σ ψ z J = gs ψ z (LB.wchart L ![𝟙 X, f] (fun _ => j)) s * (val mu ψ z J).val ^ k := by
  rw [sval_of σ ψ z J (fun _ => j) fun i => hJ _ (Set.mem_iInter.1 (hle hz) i),
    val_of mu ψ z J (fun _ => j) fun i => hJ _ (Set.mem_iInter.1 hz i), ← hm]
  refine (gs_res ψ z hle hz _).symm.trans ((congrArg (gs ψ z _) hs.symm).trans ?_)
  rw [gs_mul ψ z _ hz, ← Units.val_pow_eq_pow_val, gs_unit ψ z _ hz, map_pow, Units.val_pow_eq_pow_val]

theorem solve_germ {A : Type} [CommRing A] {f W R R' M K K' E E' S : A} {k p : ℕ} (hM : IsUnit M)
    (h₁ : W * R ^ p = K * M * E) (hR : R * R' = 1) (hE : E * E' = 1) (hK : K * K' = 1)
    (h₂ : f * W ^ k = S * (M ^ k * R' ^ (k * p))) : f = K' ^ k * S * E' ^ k := by
  have a₁ : f * (K * E) ^ k * M ^ k = S * M ^ k := by
    have b₁ : (W * R ^ p) ^ k = (K * M * E) ^ k := by rw [h₁]
    have b₂ : (R * R') ^ (k * p) = 1 := by rw [hR, one_pow]
    rw [mul_pow, ← pow_mul, mul_comm p k] at b₁
    rw [mul_pow] at b₂
    calc f * (K * E) ^ k * M ^ k = f * (K * M * E) ^ k := by ring
      _ = f * W ^ k * R ^ (k * p) := by rw [← b₁]; ring
      _ = S * M ^ k * (R ^ (k * p) * R' ^ (k * p)) := by rw [h₂]; ring
      _ = _ := by rw [b₂, _root_.mul_one]
  have a₂ := (hM.pow k).mul_right_cancel a₁
  have a₃ : (K * K' * (E * E')) ^ k = 1 := by rw [hK, hE, _root_.mul_one, one_pow]
  calc f = f * (K * K' * (E * E')) ^ k := by rw [a₃, _root_.mul_one]
    _ = _ := by rw [← a₂]; ring

theorem eigen_at_field_points (hL : Laws) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type}
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {t : SAB H (Sp V)} (P : PELUnif (maximalIdeal V) t)
    (F : Type) [Field F] [Algebra (FractionRing V) F] (a : 𝓞 E) {N k : ℕ} (hN : 1 ≤ N) (hk : 4 ≤ k)
    (ha : letI := H.starRing; a * star a = (N : 𝓞 E))
    (mu : LB.Gen (LB.LinComb P.U.LG.L (K := Fin 2) ![𝟙 t.G.left, (t.act.act a).left] ![(N : ℤ), -1])) (hmu : mu.IsGen)
    (hn : ∀ (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of V)) (z : Z) (J), Good P.U.LG.L z J →
      val mu (r ≫ eSec t.G) z J = val (GeneratorPullback.powGen P.U.LG.L _ _ P.U.LG.rig (N - 1)) r z J)
    (pt : QkPt P.D.toPre F (k * N)) (b : TFK (R := V) F ⟶ P.A.A) (hb : P.ToA F (k * N) pt b)
    (w : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F pt.g.b) (DegPre.lineε (k * N)))) (hw : w.IsGen)
    (s : Fam P.D.toPre F k) (s' t' : Fam P.D.toPre F (k * N))
    (hP : letI := H.starRing; PullAl P.D F P.oD a k N s s') (hΦ : PhiRel P.D.toPre F (k * N) pt w s' t')
    {l : ℕ} (c : Fin l → F) (σ : Fin l → H0 P.U.LG.L (k * N)) (f : Fin l → ∀ α, P.D.toPre.SecB (k * N) α)
    (hσ : ∀ i e, P.U.ExpandsAt e (k * N) (σ i) (f i))
    (hlin : ∀ α, GeneratorPullback.SecLin P.D.toPre.P.L (DegPre.famφ P.D.toPre F α) (DegPre.famε (k * N)) (t'.s α)
      (P.D.toPre.famφB α) (DegPre.famε (k * N)) (fun i => f i α) (DegPre.prB P.D.toPre F).left
      (fun i => scal (fst (TF (R := V) F) P.D.toPre.P.A).left (c i)))
    (z₀ : TFK (R := V) F ⟶ P.A.A) (ε : Fˣ) (hz₀ : letI := H.starRing; z₀ ≫ P.oA.act a = 1)
    (hW : WeilIs P.A.A P.A.L ((k * N : ℕ) : ℤ) z₀ b (unitOn ε))
    (T : Over (Spec (CommRingCat.of V))) (e : T.left ⟶ Spec (CommRingCat.of F)) (r g : T ⟶ t.G)
    (hg : g.left = e ≫ (z₀ ≫ P.U.gen.inv).left ≫ pullback.fst t.G.hom (jK V)) (z : T.left) (J)
    (hJ : Good P.U.LG.L z J) :
    (∑ i, constVal e z (c i) * sval (σ i) (r * g).left z J) * (val mu r.left z J).val ^ k =
      constVal e z (ε : F) *
        ((∑ i, constVal e z (c i) * sval (σ i) r.left z J) * (val mu (r * g).left z J).val ^ k) := by
  let _ := H.starRing
  have hG := hL.globalFns
  have hLB := P.U.LG.isLB
  have hk₁ : 1 ≤ k := by omega
  have hq : 1 ≤ k * N := Nat.mul_pos hk₁ hN
  obtain ⟨u, hu, hc, vu⟩ := PullGerm.exists_generic P.U.LG (t.act.act a) N k mu hmu hn
  obtain ⟨wI, hwI⟩ := P.U.ext
  obtain ⟨θ, rfl, hθ⟩ := ThetaTranslate.exists_theta_actVal P.U F hG hL.kerPow hq pt b hb wI hwI w hw
  obtain ⟨σ₀, hσ₀⟩ := ((FieldBaseChange.expandsG_bijective P.U.toUnifPre F hG hk₁ (P.U.expand k hk₁)).2 s).exists
  have g₂ := (FieldBaseChange.expandsG_bijective P.U.toUnifPre F hG hq (P.U.expand _ hq)).2
  have f₂ := (FieldBaseChange.expandsF_bijective P.U.toUnifPre F hG hq (P.U.expand _ hq) hwI).2
  have e₁ : (TFK (R := V) F ◁ (Over.pullback (jK V)).map (t.act.act a)).left ≫ UnifPre.gFK (G := t.G) F =
      UnifPre.gFK (G := t.G) F ≫ (t.act.act a).left := by
    rw [← Category.assoc, ← Over.comp_left, whiskerLeft_snd, Over.comp_left, Category.assoc, Category.assoc]
    exact congrArg _ (pullback.lift_fst _ _ _)
  have hpow := DVR.pullGen_isGen _ _ _ _ (FrameGeo.powGen_isGen _ _ _ _ hmu k) (UnifPre.gFK (G := t.G) F)
  obtain ⟨σ', hσ'⟩ := exists_sec hLB (φ' := fun _ : Fin 1 => UnifPre.gFK (G := t.G) F)
    (ε' := fun _ => ((k * N : ℕ) : ℤ)) (fun W _ g => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr, Finset.univ_unique,
        Finset.prod_singleton, Matrix.cons_val_zero, Matrix.cons_val_one, mul_neg, _root_.mul_one, zpow_neg,
        Category.comp_id, Nat.cast_mul, e₁]
      rw [mul_left_comm, mul_inv_cancel, _root_.mul_one])
    (pullMulSec σ₀ (TFK (R := V) F ◁ (Over.pullback (jK V)).map (t.act.act a)).left _ hpow)
  have v' : ∀ (y : (UnifPre.GF (G := t.G) F).left) (J), Good P.U.LG.L y J → sval σ' (𝟙 _) y J =
      sval σ₀ (TFK (R := V) F ◁ (Over.pullback (jK V)).map (t.act.act a)).left y J *
        (val mu (UnifPre.gFK (G := t.G) F) y J).val ^ k := fun y J hJ => by
    refine (hσ' _ _ y J hJ).trans ((sval_pullMulSec _ _ _ hpow _ y hJ).trans ?_)
    rw [val_pull hJ, FrameGeo.val_powGen, Category.id_comp, Category.id_comp, Units.val_pow_eq_pow_val]
  obtain ⟨s'', hs'', hE⟩ := PullExpField.of_generic hL P.U P.oD a (t.act.act a) k N hk₁
    (GlobalTheory.T.expansion_commutes_pullback_cmEndo_four_le hL V E H t P a N ha hN k hk) u hu hc F σ₀ s hσ₀ σ' (fun y J hJ => by
      rw [v' y J hJ, vu _ _ y J hJ, Units.val_pow_eq_pow_val])
  obtain rfl := PullLin.pullAl_unique hG _ a k N hP hs''
  obtain ⟨tA', ht'⟩ := (f₂ s').exists
  obtain ⟨tA, ht⟩ := (f₂ t').exists
  have hact := ((hθ tA' tA s' t' ht' ht).1 hΦ).isActOf P.A.isLB
  obtain ⟨σ₂, r₂, x₂⟩ := ht'
  obtain rfl := (g₂ s').unique hE x₂
  obtain ⟨τ, r₃, x₃⟩ := ht
  have lin := (FieldBaseChange.secLin_iff hLB
    (∑ i, c i • FieldBaseChange.extendSec P.U.toUnifPre F (k * N)
      (FieldBaseChange.genericSec P.U.toUnifPre (k * N) (σ i)) : FieldBaseChange.GroupSec P.U.toUnifPre F (k * N)) σ
    (UnifPre.gFK (G := t.G) F) c (fun i => FieldBaseChange.extendSec P.U.toUnifPre F (k * N)
      (FieldBaseChange.genericSec P.U.toUnifPre (k * N) (σ i))) (fun i y J hJ =>
      (FieldBaseChange.sval_pullOver _ _ _ _ hJ).trans ((FieldBaseChange.sval_pullOver _ _ _ _ hJ).trans
        (congrArg (fun q => sval (σ i) q y J) (Category.assoc _ _ _))))).2 rfl
  have eτ := (g₂ t').unique x₃ ⟨l, c, σ, f, hσ, lin, hlin⟩
  rw [← eτ] at lin
  obtain ⟨ρ, a₁, a₂, a₃, a₄⟩ := GlobalTheory.T.exists_lift_point_translation_fieldPoint V t.G F (z₀ ≫ P.U.gen.inv) T e r g hg
  have key := GlobalTheory.T.eigenEquation_translation_kernel_genericFibre V _ P.D P.A t.G P.U.toUnifPre F (t.act.act a) (P.oA.act a) (P.oA.hom a) (P.lin.ext a) N k
    mu hmu wI hwI σ₀ σ' τ tA' tA v' r₂ r₃ θ hact z₀ ε hz₀ hW _ ρ z J hJ
  rw [PullExpField.secLin_val lin _ z hJ, PullExpField.secLin_val lin _ z hJ] at key
  simp only [gs_scal, FieldBaseChange.groupBase] at key
  rw [a₁, a₂, a₃, a₄] at key
  exact key

theorem eigen_germ : Laws → Laws4 → TwistBCSpanStatement → JetSer.JetAlgSt → JetSer.RepSt → JetSer.SerSt →
    JetSer.SerExSt → JetSer.RosIdSt → JetSer.ChartBCSt → FamGerm.GermExSt → EigGermSt := by
  intro hL _ _ hJet hRep hSer hEx hRos _ hGerm E _ _ _ H V _ _ _ F _ _ _ _ _ _ y a p k hp hk ha Λ e yy α hα he
    ⟨κ, Z, jZ, kZ, hκ, hfin, hflat, hred, hjZ, hja, hval, htan⟩ Dw I hco ⟨u₁, u₂, huu⟩
  let _ := H.starRing
  have := y.P.U.smooth
  have := y.t.act.hom a
  have hLB := y.P.U.LG.isLB
  have hk₁ : 1 ≤ k := by omega
  have hq : 1 ≤ k * p := Nat.mul_pos hk₁ hp.pos
  obtain ⟨b, hb, hW⟩ := character_eq_weil_pairing E H V F y.P.A y.P.oA Dw I p k hp.pos hk₁ hco a u₁ u₂ ha huu κ hκ
  obtain ⟨fT, h₁, h₂, -⟩ := y.tors F (k * p) hq
  obtain ⟨pt, hpt⟩ := h₂ b (by rw [pow_mul', pow_eq_one_of_kill y.P.oA.toRingAct ha b hb, one_pow])
  have hTo := (h₁ pt b).2 hpt.symm
  refine ⟨pt, b, hTo, hb, fun w hw s s' t' c hP hΦ hV h ω hh hω f hf l mo => ?_⟩
  obtain ⟨s₂, s₃⟩ := surjective_appTop_sq_cube y.P.U.toUnifPre
  obtain ⟨⟨mu₀, hmu₀⟩, hgeo⟩ := FrameGeo.frame_pullback_geo hJet hRep hSer hEx hRos V y.t.G
    (PullGerm.surjective_appTop s₂) s₂ s₃ y.P.U.LG y.P.U.cubG (𝓞 E) y.t.act y.u y.hu y.d y.x y.hx y.j y.hj y.B y.hB
    H.w0 y.ρ y.hρ a p ha
  obtain ⟨mu, hmu, hn⟩ := PullGerm.exists_norm y.P.U.LG (y.t.act.act a) hp.pos mu₀ hmu₀
  obtain ⟨r, hr⟩ := y.exists_frameSer
  let U : y.t.G.left.Opens := LB.wchart y.P.U.LG.L ![𝟙 y.t.G.left, (y.t.act.act a).left] (fun _ => y.j)
  have hU : ⊤ ≤ η[y.t.G].left ⁻¹ᵁ U := by
    refine GermExist.top_le_preimage_wchart _ _ _ _ fun i => ?_
    have key : η[y.t.G].left ≫ (![𝟙 y.t.G.left, (y.t.act.act a).left] : Fin 2 → _) i = η[y.t.G].left := by
      fin_cases i
      · exact Category.comp_id _
      · show η[y.t.G].left ≫ (y.t.act.act a).left = _
        rw [← Over.comp_left, IsMonHom.one_hom]
    rw [key]; exact y.hj
  have hle : U ≤ LB.wchart y.P.U.LG.L (fun _ : Fin 1 => 𝟙 y.t.G.left) (fun _ => y.j) :=
    fun x hx => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hx 0
  have ser := fun g => ((hEx V y.t.G y.d y.x y.hx).1 U hU g).exists
  obtain ⟨M, hM⟩ := ser (mu.s (fun _ => y.j)).val
  obtain ⟨w₁, κ₁, hw₁, hexp⟩ := hgeo mu hmu M r hM hr
  obtain ⟨r', hr'⟩ := (GermExist.isUnit_of_isSer1 hRep hSer y.hx (Units.isUnit _) hr).exists_right_inv
  have hMu := GermExist.isUnit_of_isSer1 hRep hSer y.hx (Units.isUnit _) hM
  obtain ⟨n, cc, σ, fi, hcc, hσ, hlin⟩ := GlobalTheory.T.exists_integralExpansions_of_valuation_ge hL V y.ϖ y.hϖ y.P.D y.P.A y.t.G y.P.U y.Q y.hQ F y.v y.hv
    (k * p) hq (c • t') 0 hV
  let cO : Fin n → TWO.Ov y.v := fun i => ⟨cc i, hcc i⟩
  obtain ⟨m, hm⟩ : ∃ m : Γ(y.t.G.left, U)ˣ, m = mu.s (fun _ => y.j) := ⟨_, rfl⟩
  obtain ⟨sl, hsl⟩ : ∃ sl : Fin n → Γ(y.t.G.left, U), ∀ i, sl i * m.val ^ k =
      (y.t.G.left.presheaf.map (homOfLE hle).op).hom ((σ i).f (fun _ => y.j)) :=
    ⟨fun i => (y.t.G.left.presheaf.map (homOfLE hle).op).hom ((σ i).f (fun _ => y.j)) * (m⁻¹).val ^ k, fun i => by
      rw [_root_.mul_assoc, ← mul_pow, Units.inv_mul, one_pow, _root_.mul_one]⟩
  choose S hS using fun i => ser (sl i)
  have hS' : ∀ i, IsSer1 y.x _ ((σ i).f (fun _ => y.j)) (S i * M ^ k) := fun i => by
    refine isSer1_res hle ?_
    rw [← hsl i]
    exact isSer1_mul_pow hJet (hS i) (by rw [hm]; exact hM) k
  obtain ⟨gm₀, hgm⟩ := hGerm E H V F y (k * p) hq
  have hfe := ((hgm _ _).1 hf).trans ((hgm _ _).1 ⟨n, cc, σ, fi, fun i => S i * (M ^ k * r' ^ (k * p)), r, hσ, hlin,
    hr, fun i => ⟨_, hS' i, by
      rw [_root_.mul_assoc, _root_.mul_assoc, ← mul_pow, _root_.mul_comm r', hr', one_pow, _root_.mul_one]⟩, rfl⟩).symm
  obtain ⟨Φ, hΦ'⟩ := phiFun_of hL V (maximalIdeal V) y.P.D F (k * p) hq pt w hw
  have hΦc : PhiRel y.P.D.toPre F (k * p) pt w (c • s') (c • t') :=
    (hΦ' _ _).2 (by rw [(hΦ' _ _).1 hΦ, map_smul])
  have hall := GlobalTheory.T.fn_eigen_equation_of_forall_geometric_point_alt V (TWO.Ov y.v) F Subtype.val_injective (TWO.fO y.v y.hϖ y.hv) y.t.G inferInstance Z hfin
    hflat hred jZ hjZ U n cO sl kZ (fun T e c₀ r g hg z hz hz' => by
      have w₀ : (c₀.left ≫ jZ) ≫ y.t.G.hom = jFK (R := V) F ≫ jK V := by
        have a₁ : c₀.left ≫ Z.hom = Spec.map (CommRingCat.ofHom (algebraMap (TWO.Ov y.v) F)) := Over.w c₀
        rw [Category.assoc, hjZ, ← Category.assoc, a₁, PullExpField.hom_TF, ← Spec.map_comp]
        rfl
      let x₀ : TFK (R := V) F ⟶ (Over.pullback (jK V)).obj y.t.G :=
        Over.homMk (pullback.lift (c₀.left ≫ jZ) (jFK (R := V) F) w₀) (pullback.lift_snd _ _ _)
      have hx₀ : x₀.left ≫ pullback.fst y.t.G.hom (jK V) = c₀.left ≫ jZ := pullback.lift_fst _ _ _
      have hx₁ : ((x₀ ≫ y.P.U.gen.hom) ≫ y.P.U.gen.inv).left ≫ pullback.fst y.t.G.hom (jK V) = c₀.left ≫ jZ := by
        rw [Category.assoc, Iso.hom_inv_id, Category.comp_id, hx₀]
      have hkill : (x₀ ≫ y.P.U.gen.hom) ≫ y.P.oA.act a = 1 := by
        have := y.P.U.gen_hom
        have e₂ : (Over.pullback (jK V)).map (y.t.act.act a) ≫ y.P.U.gen.hom = y.P.U.gen.hom ≫ y.P.oA.act a :=
          y.P.lin.ext a
        rw [Category.assoc, ← e₂, ← Category.assoc, comp_map_eq_one (jK V) _ x₀
          (by rw [hx₀, Category.assoc, Category.assoc, hja]), MonObj.one_comp]
      obtain ⟨J, hJ, hJ'⟩ := JetSer.FBOf.exists_good_const _ hLB y.j z
      have key := eigen_at_field_points hL y.P F a hp.pos hk ha mu hmu hn pt b hTo w hw (c • s) (c • s') (c • t')
        (PullLin.pullAl_smul _ a k p c hP) hΦc cc σ fi hσ hlin _ _ hkill (hW _ hkill) T e r g
        (by rw [hx₁, hg, Category.assoc]) z J hJ
      simp only [fun i => gs_div_mul _ k y.j mu (σ i) hle m hm _ (hsl i) _ z hz hJ',
        fun i => gs_div_mul _ k y.j mu (σ i) hle m hm _ (hsl i) _ z hz' hJ',
        ← _root_.mul_assoc, ← Finset.sum_mul] at key
      rw [gs_comp_eq_constVal e c₀.left ⊤ le_top, hval c₀ _ hx₁]
      refine (((val mu (r * g).left z J).isUnit.pow k).mul ((val mu r.left z J).isUnit.pow k)).mul_right_cancel ?_
      refine (_root_.mul_assoc _ _ _).symm.trans (key.trans ?_)
      exact (mul_right_comm _ _ _).trans (_root_.mul_assoc _ _ _))
  obtain ⟨wt, φ, hφ, hwφ, hwk⟩ := htan l
  have hD := dof_of_tangent hJet hRep hSer (TWO.fO y.v y.hϖ y.hv) _ y.hx y.B.G y.hB.law hU sl S hS cO jZ hjZ kZ hall
    (e l) (yy l) wt φ hφ hwφ hwk
  have eV : TWO.algVF (V := V) (F := F) = algebraMap V F := (IsScalarTower.algebraMap_eq V _ F).symm
  have hβ : (algebraMap (TWO.Ov y.v) F).comp (TWO.fO y.v y.hϖ y.hv) = algebraMap V F := eV
  obtain ⟨Ψ, hΨ⟩ := exists_evHom (a := ![y.B.A.act a]) (TB.WickVanishing.single_point_zero_constant (y.B.A.const a))
  obtain ⟨x, hx, hxe⟩ := coeff_dof_sub_mem (TWO.fO y.v y.hϖ y.hv) (algebraMap (TWO.Ov y.v) F) Subtype.val_injective hβ
    _ y.B a (e l) (α l) (yy l) (hα l) (he l) _ hD r' ((κ₁⁻¹ ^ k : Vˣ) : V) k f (by
      rw [Units.val_pow_eq_pow_val, map_pow, map_pow]
      refine solve_germ (W := FB.toK F ω) (R := FB.toK F r) (R' := FB.toK F r') (M := FB.toK F M)
        (K := MvPowerSeries.C (algebraMap V F κ₁)) (E := FB.toK F (ev (n := 1) ![y.B.A.act a] r)) (p := p)
        (hMu.map _) ?_ ?_ ?_ ?_ ?_
      · rw [hω, ← hexp F h hh, ← map_pow, ← map_mul, hw₁, map_mul, map_mul, MvPowerSeries.map_C]
      · rw [← map_mul, hr', map_one]
      · rw [← map_mul, hΨ, hΨ, ← map_mul, hr', map_one, map_one]
      · rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
      set_option synthInstance.maxHeartbeats 100000 in
        · rw [hfe, map_sum, Finset.sum_mul, eV]
          refine Finset.sum_congr rfl fun i _ => ?_
          have mm : MvPowerSeries.map (algebraMap (TWO.Ov y.v) F) (MvPowerSeries.map (TWO.fO y.v y.hϖ y.hv) (S i)) =
              MvPowerSeries.map (algebraMap V F) (S i) := by
            rw [← hβ]; rfl
          rw [map_mul, map_mul, map_pow, map_pow, map_mul, MvPowerSeries.map_C, mm, _root_.mul_assoc]
          rfl) mo
  obtain ⟨x', rfl⟩ := Ideal.mem_span_singleton'.1 hx
  refine le_of_le_of_eq ?_ (congrArg y.v hxe).symm
  rw [map_mul, map_natCast (algebraMap (TWO.Ov y.v) F), AddValuation.map_mul]
  exact le_add_of_nonneg_left (TWO.v_nonneg y.v x')

end GlobalTheory.EigenGerm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DerivativeCongruenceGermIntegralTranslateStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open GlobalTheory GlobalTheory.FamGerm
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivative_congruence_germ_integral_translate : Laws → Laws4 → TwistBCSpanStatement → JetSer.JetAlgSt → JetSer.RepSt → JetSer.SerSt → JetSer.SerExSt → JetSer.RosIdSt → JetSer.ChartBCSt → FamGerm.GermExSt → EigGermSt := by
  first | exact @GlobalTheory.EigenGerm.eigen_germ | exact GlobalTheory.EigenGerm.eigen_germ | (intros; apply GlobalTheory.EigenGerm.eigen_germ <;> assumption)
end

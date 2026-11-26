module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisTranslateCoefficientsZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorPeriodDefectIsCocycle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreCechCocyclesCombinationCoefficientNon

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreIndependenceLogDerivativesClosedFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberUnitTranslateEqIdFieldPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberUnitTranslateEqIdFieldPoints
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.InfTranslPts

theorem factor_fst {S K : Type} [CommRing S] [Field K] (w : Sp K ⟶ Sp (DualNumber S)) :
    w = (w ≫ spMap (algebraMap S (DualNumber S))) ≫ spMap (TrivSqZeroExt.fstHom S S S).toRingHom := by
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective w
  have hε : ψ.hom (DualNumber.eps : DualNumber S) = 0 := by
    have h : ψ.hom (DualNumber.eps : DualNumber S) * ψ.hom (DualNumber.eps : DualNumber S) = 0 := by
      rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
    exact mul_self_eq_zero.1 h
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  refine RingHom.ext fun x => ?_
  change ψ.hom x = ψ.hom (algebraMap S (DualNumber S) x.fst)
  have hx : x = algebraMap S (DualNumber S) x.fst + algebraMap S (DualNumber S) x.snd * DualNumber.eps := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  conv_lhs => rw [hx]
  rw [map_add (f := _), map_mul, hε, mul_zero, add_zero]

theorem transl_field_point {X : Scheme.{0}} (G : Over X) [GrpObj G] {S : Type} [CommRing S] (x0 : Sp S ⟶ X)
    (P : tEpsG x0 ⟶ G)
    (hP : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ P.left = (1 : Over.mk x0 ⟶ G).left)
    {K : Type} [Field K] (z : Sp K ⟶ (tEpsG x0 ⊗ G).left) :
    z ≫ (lift (fst (tEpsG x0) G ≫ P) (snd (tEpsG x0) G) ≫ μ[G]).left = z ≫ (snd (tEpsG x0) G).left := by
  let zz : Over.mk (z ≫ (tEpsG x0 ⊗ G).hom) ⟶ tEpsG x0 ⊗ G := Over.homMk z rfl
  let p : tEpsG x0 ⟶ Over.mk x0 := Over.homMk (spMap (algebraMap S (DualNumber S))) rfl
  have h1 : GlobalTheory.VertSpanZero.redOver x0 ≫ P = 1 := Over.OverMorphism.ext hP
  have h2 : zz ≫ fst (tEpsG x0) G = (zz ≫ fst (tEpsG x0) G ≫ p) ≫ GlobalTheory.VertSpanZero.redOver x0 := by
    apply Over.OverMorphism.ext
    have := factor_fst (S := S) (K := K) (z ≫ (fst (tEpsG x0) G).left)
    exact this
  have h3 : zz ≫ fst (tEpsG x0) G ≫ P = 1 := by
    rw [← Category.assoc, h2, Category.assoc, h1, MonObj.comp_one]
  have h4 : zz ≫ ((fst (tEpsG x0) G ≫ P) * snd (tEpsG x0) G) = zz ≫ snd (tEpsG x0) G := by
    rw [MonObj.comp_mul, h3, _root_.one_mul]
  exact congrArg (fun q => q.left) h4

theorem transl_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (S : Type) [CommRing S] (x0 : Sp S ⟶ X) (P : tEpsG x0 ⟶ t.G), spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ P.left = (1 : Over.mk x0 ⟶ t.G).left → ∀ y : (tEpsG x0 ⊗ t.G).left, ∃ (K : Type) (_ : Field K) (z : Sp K ⟶ (tEpsG x0 ⊗ t.G).left), y ∈ Set.range z.base ∧ z ≫ (lift (fst (tEpsG x0) t.G ≫ P) (snd (tEpsG x0) t.G) ≫ μ[t.G]).left = z ≫ (snd (tEpsG x0) t.G).left := by
  intro E _ _ _ H X t S _ x0 P hP y
  refine ⟨(tEpsG x0 ⊗ t.G).left.residueField y, inferInstance,
    (tEpsG x0 ⊗ t.G).left.fromSpecResidueField y, ?_, transl_field_point t.G x0 P hP _⟩
  exact ⟨IsLocalRing.closedPoint _, Scheme.fromSpecResidueField_apply y _⟩

end GlobalTheory.InfTranslPts
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberUnitTranslateEqIdFieldPointsStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualNumber_unit_translate_eq_id_field_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (S : Type) [CommRing S] (x0 : Sp S ⟶ X) (P : tEpsG x0 ⟶ t.G), spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ P.left = (1 : Over.mk x0 ⟶ t.G).left → ∀ y : (tEpsG x0 ⊗ t.G).left, ∃ (K : Type) (_ : Field K) (z : Sp K ⟶ (tEpsG x0 ⊗ t.G).left), y ∈ Set.range z.base ∧ z ≫ (lift (fst (tEpsG x0) t.G ≫ P) (snd (tEpsG x0) t.G) ≫ μ[t.G]).left = z ≫ (snd (tEpsG x0) t.G).left := by
  first | exact @GlobalTheory.InfTranslPts.transl_points | exact GlobalTheory.InfTranslPts.transl_points | (intros; apply GlobalTheory.InfTranslPts.transl_points <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstOrderTranslationFormulaGerms
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstOrderTranslationFormulaGerms
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TranslGerm

open GlobalTheory.Points (valR_eq valR_add valR_mul valR_res valR_comp)

theorem point_formula {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
    {U : X.affineOpens} {n : ℕ} {v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)}
    (hv : ∀ a, IsTanAtG t (chart U) (v a))
    {δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)}
    (hδv : ∀ a (O : t.G.left.Opens), O ≤ t.G.hom ⁻¹ᵁ U.1 → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S]
      (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left),
      g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → IsTranslate t φ g₀ (v a) w →
      valR g₀ O (δ a O f) = (valR w O f).snd)
    {r : Fin n → Γ(X, U.1)} {x : tEpsG (chart U) ⟶ t.G} (hx : IsCombAtG t (chart U) v r x.left)
    {S : Type} [CommRing S] {φ : Γ(X, U.1) →+* S} {P : tEpsG (spMap φ ≫ chart U) ⟶ t.G}
    (hP : P.left = spMap (dualMap φ) ≫ x.left) {O : t.G.left.Opens} (hO : O ≤ t.G.hom ⁻¹ᵁ U.1)
    (f : Γ(t.G.left, O)) {C : Type} [CommRing C] (z : Sp C ⟶ (tEpsG (spMap φ ≫ chart U) ⊗ t.G).left)
    (hz : ⊤ ≤ z ⁻¹ᵁ ((snd (tEpsG (spMap φ ≫ chart U)) t.G).left ⁻¹ᵁ O)) :
    ⊤ ≤ (z ≫ (lift (fst (tEpsG (spMap φ ≫ chart U)) t.G ≫ P) (snd (tEpsG (spMap φ ≫ chart U)) t.G) ≫
        μ[t.G]).left) ⁻¹ᵁ O ∧
    valR (z ≫ (lift (fst (tEpsG (spMap φ ≫ chart U)) t.G ≫ P) (snd (tEpsG (spMap φ ≫ chart U)) t.G) ≫
        μ[t.G]).left) O f =
      valR (z ≫ (snd (tEpsG (spMap φ ≫ chart U)) t.G).left) O f +
      valR (z ≫ (fst (tEpsG (spMap φ ≫ chart U)) t.G).left) ⊤
          ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber S))).inv.hom DualNumber.eps) *
        valR (z ≫ (snd (tEpsG (spMap φ ≫ chart U)) t.G).left) O
          (∑ b, (t.G.hom.appLE U.1 O hO).hom (r b) * δ b O f) := by

  obtain ⟨g₀, hg₀⟩ : ∃ g₀, g₀ = z ≫ (snd (tEpsG (spMap φ ≫ chart U)) t.G).left := ⟨_, rfl⟩
  have hg₀O : ⊤ ≤ g₀ ⁻¹ᵁ O := by rw [hg₀]; exact hz
  obtain ⟨ψ₀, hψ₀⟩ : ∃ ψ₀ : DualNumber S →+* C, z ≫ (fst (tEpsG (spMap φ ≫ chart U)) t.G).left = spMap ψ₀ :=
    ⟨(Spec.preimage (z ≫ (fst (tEpsG (spMap φ ≫ chart U)) t.G).left)).hom, (Spec.map_preimage _).symm⟩
  let ψ : DualNumber Γ(X, U.1) →+* C := ψ₀.comp (dualMap φ)
  have hd : (dualMap φ).comp (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))) = (algebraMap S (DualNumber S)).comp φ := by
    apply RingHom.ext; intro s; ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have hbase : g₀ ≫ t.G.hom = spMap (ψ.comp (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1)))) ≫ chart U := by
    have e1 : (snd (tEpsG (spMap φ ≫ chart U)) t.G).left ≫ t.G.hom =
        (fst (tEpsG (spMap φ ≫ chart U)) t.G).left ≫ (tEpsG (spMap φ ≫ chart U)).hom :=
      (Over.w _).trans (Over.w _).symm
    rw [hg₀, Category.assoc, e1, ← Category.assoc, hψ₀]
    show spMap ψ₀ ≫ spMap (algebraMap S (DualNumber S)) ≫ spMap φ ≫ chart U = _
    rw [← Category.assoc, ← Category.assoc, GlobalTheory.KSLin.spMap_comp_spMap, GlobalTheory.KSLin.spMap_comp_spMap]
    congr 2
    simp only [ψ, RingHom.comp_assoc, hd]
  let a : Over.mk (g₀ ≫ t.G.hom) ⟶ tEpsG (chart U) := Over.homMk (spMap ψ) (by
    show spMap ψ ≫ spMap (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))) ≫ chart U = g₀ ≫ t.G.hom
    rw [hbase, ← Category.assoc, GlobalTheory.KSLin.spMap_comp_spMap])
  choose w hw using fun b => (existsUnique_isTranslate t (ψ.comp (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))))
    hbase (hv b)).exists
  obtain ⟨h1, h2⟩ := GlobalTheory.FirstOrderValue.valR_mul_comb E H X t U n v hv r x hx C ψ g₀ a w rfl hw O f hg₀O

  let zO : Over.mk (g₀ ≫ t.G.hom) ⟶ tEpsG (spMap φ ≫ chart U) ⊗ t.G := Over.homMk z (by
    show z ≫ (tEpsG (spMap φ ≫ chart U) ⊗ t.G).hom = g₀ ≫ t.G.hom
    rw [hg₀, ← Over.w (snd (tEpsG (spMap φ ≫ chart U)) t.G), Category.assoc])
  have hzs : zO ≫ snd (tEpsG (spMap φ ≫ chart U)) t.G = (Over.homMk g₀ rfl : Over.mk (g₀ ≫ t.G.hom) ⟶ t.G) :=
    Over.OverMorphism.ext hg₀.symm
  have hzf : zO ≫ fst (tEpsG (spMap φ ≫ chart U)) t.G ≫ P = a ≫ x := by
    apply Over.OverMorphism.ext
    show z ≫ (fst (tEpsG (spMap φ ≫ chart U)) t.G).left ≫ P.left = spMap ψ ≫ x.left
    rw [hP, ← Category.assoc, hψ₀, ← Category.assoc, GlobalTheory.KSLin.spMap_comp_spMap]
  have hτ : zO ≫ lift (fst (tEpsG (spMap φ ≫ chart U)) t.G ≫ P) (snd (tEpsG (spMap φ ≫ chart U)) t.G) ≫ μ[t.G] =
      (a ≫ x) * (Over.homMk g₀ rfl : Over.mk (g₀ ≫ t.G.hom) ⟶ t.G) := by
    rw [← Category.assoc, comp_lift, hzs, hzf]
    rfl
  have hτl : z ≫ (lift (fst (tEpsG (spMap φ ≫ chart U)) t.G ≫ P) (snd (tEpsG (spMap φ ≫ chart U)) t.G) ≫
      μ[t.G]).left = ((a ≫ x) * (Over.homMk g₀ rfl : Over.mk (g₀ ≫ t.G.hom) ⟶ t.G)).left :=
    congrArg Over.Hom.left hτ
  rw [hτl, ← hg₀]
  refine ⟨h1, ?_⟩
  rw [h2, hψ₀]
  congr 1
  have hε : ψ DualNumber.eps = ψ₀ DualNumber.eps := by simp [ψ, dualMap]
  have hsp : valR (spMap ψ₀) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber S))).inv.hom DualNumber.eps) =
      ψ₀ DualNumber.eps := GlobalTheory.Points.valR_specMap (CommRingCat.ofHom ψ₀) _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hsp, ← hε, valR_eq _ _ hg₀O, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_mul, ← valR_eq _ _ hg₀O, ← valR_eq _ _ hg₀O, GlobalTheory.LogKSLin.valR_base U hO hbase hg₀O,
    hδv b O hO f C _ g₀ (w b) hbase hg₀O (hw b)]
  rfl

theorem transl_germ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → ∀ (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → (∀ a (O : t.G.left.Opens) (h : O ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), δ a O ((t.G.hom.appLE U.1 O h).hom r) = 0) → (∀ a (O : t.G.left.Opens), O ≤ t.G.hom ⁻¹ᵁ U.1 → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → IsTranslate t φ g₀ (v a) w → valR g₀ O (δ a O f) = (valR w O f).snd) → ∀ (r : Fin n → Γ(X, U.1)) (x : tEpsG (chart U) ⟶ t.G), IsCombAtG t (chart U) v r x.left → ∀ (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (P : tEpsG (spMap φ ≫ chart U) ⟶ t.G), P.left = spMap (dualMap φ) ≫ x.left → ∀ (O : t.G.left.Opens) (hO : O ≤ t.G.hom ⁻¹ᵁ U.1) (f : Γ(t.G.left, O)) (y : (tEpsG (spMap φ ≫ chart U) ⊗ t.G).left), (snd (tEpsG (spMap φ ≫ chart U)) t.G).left.base y ∈ O → gs (lift (fst (tEpsG (spMap φ ≫ chart U)) t.G ≫ P) (snd (tEpsG (spMap φ ≫ chart U)) t.G) ≫ μ[t.G]).left y O f = gs (snd (tEpsG (spMap φ ≫ chart U)) t.G).left y O f + gs (fst (tEpsG (spMap φ ≫ chart U)) t.G).left y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber S))).inv.hom DualNumber.eps) * gs (snd (tEpsG (spMap φ ≫ chart U)) t.G).left y O (∑ b, (t.G.hom.appLE U.1 O hO).hom (r b) * δ b O f) := by
  intro E _ _ _ H X t U n v hv δ _ _ hδv r x hx S _ φ P hP O hO f y hy
  have key := fun (C : Type) [CommRing C] z hz => point_formula hv hδv hx hP hO f (C := C) z hz

  have hVτ : (snd (tEpsG (spMap φ ≫ chart U)) t.G).left ⁻¹ᵁ O ≤
      (lift (fst (tEpsG (spMap φ ≫ chart U)) t.G ≫ P) (snd (tEpsG (spMap φ ≫ chart U)) t.G) ≫ μ[t.G]).left ⁻¹ᵁ O := by
    intro y' hy'
    obtain ⟨W, hW, hyW, hWV⟩ := exists_isAffineOpen_mem_and_subset hy'
    have hz : ⊤ ≤ hW.fromSpec ⁻¹ᵁ ((snd (tEpsG (spMap φ ≫ chart U)) t.G).left ⁻¹ᵁ O) :=
      GlobalTheory.Points.le_preimage_mono _ hWV hW.fromSpec_preimage_self.ge
    obtain ⟨p, rfl⟩ : y' ∈ Set.range hW.fromSpec := by rw [hW.range_fromSpec]; exact hyW
    have := (key Γ((tEpsG (spMap φ ≫ chart U) ⊗ t.G).left, W) hW.fromSpec hz).1 (Set.mem_univ p)
    exact this
  have hVπ : (snd (tEpsG (spMap φ ≫ chart U)) t.G).left ⁻¹ᵁ O ≤ (fst (tEpsG (spMap φ ≫ chart U)) t.G).left ⁻¹ᵁ ⊤ :=
    fun _ _ => trivial

  have hAB : ((tEpsG (spMap φ ≫ chart U) ⊗ t.G).left.presheaf.map (homOfLE hVτ).op).hom
      (((lift (fst (tEpsG (spMap φ ≫ chart U)) t.G ≫ P) (snd (tEpsG (spMap φ ≫ chart U)) t.G) ≫ μ[t.G]).left.app O).hom f) =
      ((snd (tEpsG (spMap φ ≫ chart U)) t.G).left.app O).hom f +
      ((tEpsG (spMap φ ≫ chart U) ⊗ t.G).left.presheaf.map (homOfLE hVπ).op).hom
        (((fst (tEpsG (spMap φ ≫ chart U)) t.G).left.app ⊤).hom
          ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber S))).inv.hom DualNumber.eps)) *
      ((snd (tEpsG (spMap φ ≫ chart U)) t.G).left.app O).hom (∑ b, (t.G.hom.appLE U.1 O hO).hom (r b) * δ b O f) := by
    refine GlobalTheory.CechInv.ext_of_valR _ _ _ fun C _ z hz => ?_
    rw [valR_res _ hVτ hz, ← valR_comp, (key C z hz).2, valR_add _ _ hz, valR_mul _ _ hz, valR_res _ hVπ hz,
      ← valR_comp, ← valR_comp, ← valR_comp]
  have hτy := hVτ hy
  rw [gs_eq _ y O hτy, gs_eq _ y O hy, gs_eq _ y ⊤ trivial, gs_eq _ y O hy,
    ← TopCat.Presheaf.germ_res_apply _ (homOfLE hVτ) y hy, hAB, map_add, map_mul,
    TopCat.Presheaf.germ_res_apply _ (homOfLE hVπ) y hy]

end GlobalTheory.TranslGerm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstOrderTranslationFormulaGermsStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstOrder_translation_formula_germs : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → ∀ (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → (∀ a (O : t.G.left.Opens) (h : O ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), δ a O ((t.G.hom.appLE U.1 O h).hom r) = 0) → (∀ a (O : t.G.left.Opens), O ≤ t.G.hom ⁻¹ᵁ U.1 → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → IsTranslate t φ g₀ (v a) w → valR g₀ O (δ a O f) = (valR w O f).snd) → ∀ (r : Fin n → Γ(X, U.1)) (x : tEpsG (chart U) ⟶ t.G), IsCombAtG t (chart U) v r x.left → ∀ (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (P : tEpsG (spMap φ ≫ chart U) ⟶ t.G), P.left = spMap (dualMap φ) ≫ x.left → ∀ (O : t.G.left.Opens) (hO : O ≤ t.G.hom ⁻¹ᵁ U.1) (f : Γ(t.G.left, O)) (y : (tEpsG (spMap φ ≫ chart U) ⊗ t.G).left), (snd (tEpsG (spMap φ ≫ chart U)) t.G).left.base y ∈ O → gs (lift (fst (tEpsG (spMap φ ≫ chart U)) t.G ≫ P) (snd (tEpsG (spMap φ ≫ chart U)) t.G) ≫ μ[t.G]).left y O f = gs (snd (tEpsG (spMap φ ≫ chart U)) t.G).left y O f + gs (fst (tEpsG (spMap φ ≫ chart U)) t.G).left y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber S))).inv.hom DualNumber.eps) * gs (snd (tEpsG (spMap φ ≫ chart U)) t.G).left y O (∑ b, (t.G.hom.appLE U.1 O hO).hom (r b) * δ b O f) := by
  first | exact @GlobalTheory.TranslGerm.transl_germ | exact GlobalTheory.TranslGerm.transl_germ | (intros; apply GlobalTheory.TranslGerm.transl_germ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationDlogCocycleCoboundaryClosedFibreChar
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationDlogCocycleCoboundaryClosedFibreChar
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

set_option autoImplicit false

namespace GlobalTheory.ChartCob

theorem resG_appLE {Y Z : Scheme.{0}} (f : Y ⟶ Z) {O : Z.Opens} {V V' : Y.Opens} (h : V ≤ f ⁻¹ᵁ O) (h' : V' ≤ V)
    (s : Γ(Z, O)) : resG Y h' ((f.appLE O V h).hom s) = (f.appLE O V' (h'.trans h)).hom s := by
  simp only [resG]
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

theorem appLE_resG {Y Z : Scheme.{0}} (f : Y ⟶ Z) {O O' : Z.Opens} {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ O') (h' : O' ≤ O)
    (s : Γ(Z, O)) :
    (f.appLE O' V h).hom (resG Z h' s) = (f.appLE O V (fun _ hx => h' (h hx))).hom s := by
  simp only [resG]
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem isCoc_pullback {Y Z : Scheme.{0}} (f : Y ⟶ Z) {J : Type} (W : J → Z.Opens)
    (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')) (hc : GlobalTheory.CechFin.IsCoc W c) :
    GlobalTheory.CechFin.IsCoc (fun i => f ⁻¹ᵁ W i)
      (fun i i' => (f.appLE (W i ⊓ W i') (f ⁻¹ᵁ W i ⊓ f ⁻¹ᵁ W i') (fun _ hx => hx)).hom (c i i')) := by
  intro i i' i''
  have h3 : f ⁻¹ᵁ W i ⊓ f ⁻¹ᵁ W i' ⊓ f ⁻¹ᵁ W i'' ≤ f ⁻¹ᵁ (W i ⊓ W i' ⊓ W i'') := fun _ hx => hx
  have e := congrArg (f.appLE (W i ⊓ W i' ⊓ W i'') (f ⁻¹ᵁ W i ⊓ f ⁻¹ᵁ W i' ⊓ f ⁻¹ᵁ W i'') h3).hom
    (hc i i' i'')
  rw [map_add (f := _), appLE_resG, appLE_resG, appLE_resG] at e
  exact (congrArg₂ (· + ·) (resG_appLE f _ _ _) (resG_appLE f _ _ _)).trans (e.trans (resG_appLE f _ _ _).symm)

theorem isCoc_sum {Z X : Scheme.{0}} (p : Z ⟶ X) (U : X.Opens) (L : LB Z) (hL : L.IsLB) {n : ℕ}
    (δ : Fin n → ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)) (hδ : ∀ a, IsField (p ⁻¹ᵁ U) (δ a))
    {J : Type} (W : J → Z.Opens) (j : J → L.ι) (hWU : ∀ i, W i ≤ p ⁻¹ᵁ U) (hj : ∀ i, W i ≤ L.U (j i))
    (r : Fin n → Γ(X, U)) :
    GlobalTheory.CechFin.IsCoc W (fun i i' => ∑ b, (p.appLE U (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r b) *
      (δ b (W i ⊓ W i') (resG Z (inf_le_inf (hj i) (hj i')) (L.g (j i) (j i')).val) *
        resG Z (inf_le_inf (hj i) (hj i')) (L.g (j i) (j i'))⁻¹.val)) := by
  intro i i' i''
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  have e := GlobalTheory.DlogCocycle.dlog_cocycle Z L hL _ (δ b) (hδ b) J W j hWU hj i i' i''
  rw [map_mul (resG Z _) ((p.appLE _ _ _).hom _), map_mul (resG Z _) ((p.appLE _ _ _).hom _),
    map_mul (resG Z _) ((p.appLE _ _ _).hom _), resG_appLE, resG_appLE, resG_appLE, ← e, mul_add]

theorem isCob_pbT {Y Z : Scheme.{0}} (f : Y ⟶ Z) {I : Type} (V Ω : I → Z.Opens)
    (hle : ∀ a, f ⁻¹ᵁ V a ≤ f ⁻¹ᵁ Ω a) (c : ∀ a b : I, Γ(Z, Ω a ⊓ Ω b)) (h : ∀ a, Γ(Y, f ⁻¹ᵁ Ω a))
    (hh : ∀ a b, (f.appLE (Ω a ⊓ Ω b) (f ⁻¹ᵁ Ω a ⊓ f ⁻¹ᵁ Ω b) (fun _ hx => hx)).hom (c a b) =
      resG Y inf_le_left (h a) - resG Y inf_le_right (h b)) :
    GlobalTheory.KS.IsCob (fun a => f ⁻¹ᵁ V a) (fun a b => GlobalTheory.KS.pbT f (c a b) (f ⁻¹ᵁ V a ⊓ f ⁻¹ᵁ V b)) := by
  refine ⟨fun a => -resG Y (hle a) (h a), fun a b => ?_⟩
  have e := (resG_appLE f _ (inf_le_inf (hle a) (hle b)) _).symm.trans
    (congrArg (resG Y (inf_le_inf (hle a) (hle b))) (hh a b))
  rw [map_sub, GlobalTheory.DlogCocycle.resG_resG, GlobalTheory.DlogCocycle.resG_resG] at e
  have hab : f ⁻¹ᵁ V a ⊓ f ⁻¹ᵁ V b ≤ f ⁻¹ᵁ (Ω a ⊓ Ω b) := fun x hx => ⟨hle a hx.1, hle b hx.2⟩
  simp only [GlobalTheory.KS.pbT, GlobalTheory.KS.rsT]
  rw [dite_eq_left hab, dite_eq_left inf_le_left, dite_eq_left inf_le_right, map_neg, map_neg,
    GlobalTheory.DlogCocycle.resG_resG, GlobalTheory.DlogCocycle.resG_resG]
  refine e.trans ?_
  ring

theorem chart_isCob : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (n : ℕ) (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (hj : ∀ i, W i ≤ t.PP.L.U (j i)) (m : Ideal Γ(X, U.1)) (A : Over (Sp (Γ(X, U.1) ⧸ m))) [GrpObj A] (ι : A.left ⟶ t.G.left), IsGrpPullback A t.G (spMap (Ideal.Quotient.mk m) ≫ chart U) ι → ∀ (r : Fin n → Γ(X, U.1)) (h' : ∀ i, Γ(A.left, ι ⁻¹ᵁ W i)), (∀ i i', (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (∑ b, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r b) * (δ b (W i ⊓ W i') (resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i'))⁻¹.val)) = resG A.left inf_le_left (h' i) - resG A.left inf_le_right (h' i')) → GlobalTheory.KS.IsCob (fun a => ι ⁻¹ᵁ t.PP.L.U a) (fun a b => GlobalTheory.KS.pbT ι (∑ c, (t.G.hom.appLE U.1 ((t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) ⊓ (t.PP.L.U b ⊓ t.G.hom ⁻¹ᵁ U.1)) (inf_le_left.trans inf_le_right)).hom (r c) * (δ c ((t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) ⊓ (t.PP.L.U b ⊓ t.G.hom ⁻¹ᵁ U.1)) (resG t.G.left (inf_le_inf inf_le_left inf_le_left) (t.PP.L.g a b).val) * resG t.G.left (inf_le_inf inf_le_left inf_le_left) (t.PP.L.g a b)⁻¹.val)) (ι ⁻¹ᵁ t.PP.L.U a ⊓ ι ⁻¹ᵁ t.PP.L.U b)) := by
  intro E _ _ _ H X t U n δ hδ J W j _ hsup hWU hj m A _ ι hι r h' hh'
  have htop : ∀ x : A.left, x ∈ ι ⁻¹ᵁ (t.G.hom ⁻¹ᵁ U.1) := by
    intro x
    have hw := hι.1.w
    have : x ∈ (ι ≫ t.G.hom) ⁻¹ᵁ U.1 := by
      rw [hw]
      show (A.hom ≫ spMap (Ideal.Quotient.mk m) ≫ chart U) x ∈ (U.1 : Set X)
      rw [← U.2.range_fromSpec]
      exact ⟨(A.hom ≫ spMap (Ideal.Quotient.mk m)) x, rfl⟩
    exact this
  let Ω : J ⊕ t.PP.L.ι → t.G.left.Opens := Sum.elim W (fun a => t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1)
  let jj : J ⊕ t.PP.L.ι → t.PP.L.ι := Sum.elim j id
  have hΩU : ∀ q, Ω q ≤ t.G.hom ⁻¹ᵁ U.1 := by
    rintro (i | a)
    · exact hWU i
    · exact inf_le_right
  have hΩj : ∀ q, Ω q ≤ t.PP.L.U (jj q) := by
    rintro (i | a)
    · exact hj i
    · exact inf_le_left
  have hc := isCoc_pullback ι Ω _ (isCoc_sum t.G.hom U.1 t.PP.L t.PP.isLB δ hδ Ω jj hΩU hΩj r)
  obtain ⟨h, hh⟩ := GlobalTheory.CechFin.isCob_of_isCob_subcover A.left (J ⊕ t.PP.L.ι) (fun q => ι ⁻¹ᵁ Ω q)
    (Set.range Sum.inl) (by
      intro q x _
      have hx : ι x ∈ ⨆ i, W i := by rw [hsup]; exact htop x
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨Sum.inl i, TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, rfl⟩, hi⟩⟩)
    _ hc (fun q => match q with | Sum.inl i => h' i | Sum.inr _ => 0) (by
      rintro _ ⟨i, rfl⟩ _ ⟨i', rfl⟩
      exact hh' i i')
  exact isCob_pbT ι t.PP.L.U (fun a => t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) (fun a x hx => ⟨hx, htop x⟩) _
    (fun a => h (Sum.inr a)) (fun a b => hh (Sum.inr a) (Sum.inr b))

end GlobalTheory.ChartCob
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationDlogCocycleCoboundaryClosedFibreCharStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisation_dlog_cocycle_coboundary_closed_fibre_charts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (n : ℕ) (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (hj : ∀ i, W i ≤ t.PP.L.U (j i)) (m : Ideal Γ(X, U.1)) (A : Over (Sp (Γ(X, U.1) ⧸ m))) [GrpObj A] (ι : A.left ⟶ t.G.left), IsGrpPullback A t.G (spMap (Ideal.Quotient.mk m) ≫ chart U) ι → ∀ (r : Fin n → Γ(X, U.1)) (h' : ∀ i, Γ(A.left, ι ⁻¹ᵁ W i)), (∀ i i', (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (∑ b, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r b) * (δ b (W i ⊓ W i') (resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i'))⁻¹.val)) = resG A.left inf_le_left (h' i) - resG A.left inf_le_right (h' i')) → GlobalTheory.KS.IsCob (fun a => ι ⁻¹ᵁ t.PP.L.U a) (fun a b => GlobalTheory.KS.pbT ι (∑ c, (t.G.hom.appLE U.1 ((t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) ⊓ (t.PP.L.U b ⊓ t.G.hom ⁻¹ᵁ U.1)) (inf_le_left.trans inf_le_right)).hom (r c) * (δ c ((t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) ⊓ (t.PP.L.U b ⊓ t.G.hom ⁻¹ᵁ U.1)) (resG t.G.left (inf_le_inf inf_le_left inf_le_left) (t.PP.L.g a b).val) * resG t.G.left (inf_le_inf inf_le_left inf_le_left) (t.PP.L.g a b)⁻¹.val)) (ι ⁻¹ᵁ t.PP.L.U a ⊓ ι ⁻¹ᵁ t.PP.L.U b)) := by
  first | exact @GlobalTheory.ChartCob.chart_isCob | exact GlobalTheory.ChartCob.chart_isCob | (intros; apply GlobalTheory.ChartCob.chart_isCob <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreIndependenceLogDerivativesClosedFibre
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FibreIndep
open MonObj


set_option maxHeartbeats 2000000 in
theorem fibre_indep' : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → (∀ a (O : t.G.left.Opens) (h : O ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), δ a O ((t.G.hom.appLE U.1 O h).hom r) = 0) → (∀ a (O : t.G.left.Opens), O ≤ t.G.hom ⁻¹ᵁ U.1 → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → IsTranslate t φ g₀ (v a) w → valR g₀ O (δ a O f) = (valR w O f).snd) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (hj : ∀ i, W i ≤ t.PP.L.U (j i)) (m : Ideal Γ(X, U.1)), m.IsMaximal → ∀ (A : Over (Sp (Γ(X, U.1) ⧸ m))) [GrpObj A] (ιA : A.left ⟶ t.G.left), IsGrpPullback A t.G (spMap (Ideal.Quotient.mk m) ≫ chart U) ιA → ∀ (r : Fin n → Γ(X, U.1)) (h' : ∀ i, Γ(A.left, ιA ⁻¹ᵁ W i)), (∀ i i', (ιA.appLE (W i ⊓ W i') (ιA ⁻¹ᵁ W i ⊓ ιA ⁻¹ᵁ W i') (fun _ hx => hx)).hom (∑ b, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r b) * (δ b (W i ⊓ W i') (resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i'))⁻¹.val)) = resG A.left inf_le_left (h' i) - resG A.left inf_le_right (h' i')) → ∀ b, r b ∈ m := by
  intro E _ _ _ H X t _hprop _hamp hK U n v hv hb δ hδ hδ0 hδt J W j hWa hWcov hWU hj m hm A _ ιA hι r h' hcob
  haveI := hm
  letI : Field (Γ(X, U.1) ⧸ m) := Ideal.Quotient.field m
  set q := Ideal.Quotient.mk m with hq
  set x0 : Sp (Γ(X, U.1) ⧸ m) ⟶ X := spMap q ≫ chart U with hx0
  have hB := GlobalTheory.LineNorm.isTanBasis_of_basis E H X t Γ(X, U.1) (chart U) n v hv hb
  have hT : ∀ b, IsTanAtG t x0 (spMap (dualMap q) ≫ v b) := fun b => GlobalTheory.VertSpanZero.isTanAtG_bc t q (hv b)
  let uR : Fin n → (tEpsG (chart U) ⟶ t.G) := fun b => Over.homMk (spMap (epsMul (r b)) ≫ v b) (by
    change (spMap (epsMul (r b)) ≫ v b) ≫ t.G.hom = spMap (algebraMap _ (DualNumber _)) ≫ chart U
    rw [Category.assoc, (hv b).1, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      GlobalTheory.VertSpanZero.epsMul_comp_algebraMap])
  obtain ⟨xR, hxRdef⟩ : ∃ xR : tEpsG (chart U) ⟶ t.G, xR = (List.ofFn uR).prod := ⟨_, rfl⟩
  have hxR : IsCombAtG t (chart U) v r xR.left := ⟨uR, fun b => rfl, by rw [hxRdef]⟩
  have eq0 : (dualMap q).comp (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))) =
      (algebraMap (Γ(X, U.1) ⧸ m) (DualNumber (Γ(X, U.1) ⧸ m))).comp q := by
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let jq : tEpsG x0 ⟶ tEpsG (chart U) := Over.homMk (spMap (dualMap q)) (by
    change spMap (dualMap q) ≫ spMap (algebraMap _ (DualNumber _)) ≫ chart U = spMap (algebraMap _ (DualNumber _)) ≫ spMap q ≫ chart U
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, eq0])
  obtain ⟨P, hPdef⟩ : ∃ P : tEpsG x0 ⟶ t.G, P = jq ≫ xR := ⟨_, rfl⟩
  have hPl : P.left = spMap (dualMap q) ≫ xR.left := by rw [hPdef]; rfl
  have hP : IsCombAtG t x0 (fun b => spMap (dualMap q) ≫ v b) (fun b => q (r b)) P.left := by
    refine ⟨fun b => jq ≫ uR b, fun b => ?_, ?_⟩
    · change spMap (dualMap q) ≫ spMap (epsMul (r b)) ≫ v b = spMap (epsMul (q (r b))) ≫ spMap (dualMap q) ≫ v b
      have e1 : (dualMap q).comp (epsMul (r b)) = (epsMul (q (r b))).comp (dualMap q) := by
        apply RingHom.ext; intro z; ext
        · simp [epsMul, dualMap]
        · simp [epsMul, dualMap, mul_comm]
      rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← CommRingCat.ofHom_comp]
      exact congrArg (fun g => Spec.map (CommRingCat.ofHom g) ≫ v b) e1
    · rw [← GlobalTheory.FirstOrderValue.comp_prod_ofFn, ← hxRdef, hPdef]
  have hPt : spMap (TrivSqZeroExt.fstHom (Γ(X, U.1) ⧸ m) (Γ(X, U.1) ⧸ m) (Γ(X, U.1) ⧸ m)).toRingHom ≫ P.left = (1 : Over.mk x0 ⟶ t.G).left := by
    obtain ⟨u', hu', hu'P⟩ := hP
    let s : Over.mk x0 ⟶ tEpsG x0 := Over.homMk (spMap (TrivSqZeroExt.fstHom (Γ(X, U.1) ⧸ m) (Γ(X, U.1) ⧸ m) (Γ(X, U.1) ⧸ m)).toRingHom) (by
      change _ ≫ spMap (algebraMap _ _) ≫ x0 = x0
      rw [← Category.assoc, GlobalTheory.VertSpanZero.spMap_fst_algebraMap, Category.id_comp])
    have hs : ∀ b, s ≫ u' b = 1 := fun b => Over.OverMorphism.ext (by
      change spMap _ ≫ (u' b).left = _
      rw [hu' b, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, GlobalTheory.VertSpanZero.fst_comp_epsMul]
      exact (hT b).2)
    have h1 : s ≫ (List.ofFn u').prod = 1 := by
      rw [GlobalTheory.FirstOrderValue.comp_prod_ofFn]; simp [hs]
    have h2 : (s ≫ (List.ofFn u').prod).left = (1 : Over.mk x0 ⟶ t.G).left := by rw [h1]
    rw [Over.comp_left, hu'P] at h2
    exact h2

  have hgen : ∃ c : LB.Gen (Out.translDiff t.G t.PP.L P), c.IsGen := by
    let T := tEpsG x0
    let π : (T ⊗ t.G).left ⟶ Sp (DualNumber (Γ(X, U.1) ⧸ m)) := (fst T t.G).left
    let τ : (T ⊗ t.G).left ⟶ t.G.left := (lift (fst T t.G ≫ P) (snd T t.G) ≫ μ[t.G]).left
    let ρ : (T ⊗ t.G).left ⟶ t.G.left := (snd T t.G).left
    have wπ : π ≫ spMap (algebraMap _ (DualNumber (Γ(X, U.1) ⧸ m))) ≫ x0 = (T ⊗ t.G).hom := Over.w (fst T t.G)
    have wρ : ρ ≫ t.G.hom = (π ≫ spMap (algebraMap _ (DualNumber (Γ(X, U.1) ⧸ m)))) ≫ (spMap q ≫ chart U) := by
      rw [Category.assoc, wπ]; exact Over.w (snd T t.G)
    have wτ : τ ≫ t.G.hom = (π ≫ spMap (algebraMap _ (DualNumber (Γ(X, U.1) ⧸ m)))) ≫ (spMap q ≫ chart U) := by
      rw [Category.assoc, wπ]; exact Over.w (lift (fst T t.G ≫ P) (snd T t.G) ≫ μ[t.G])
    obtain ⟨ρ', hρ', hρs⟩ : ∃ ρ' : (T ⊗ t.G).left ⟶ A.left, ρ' ≫ ιA = ρ ∧
        ρ' ≫ A.hom = π ≫ spMap (algebraMap _ (DualNumber (Γ(X, U.1) ⧸ m))) :=
      ⟨hι.1.lift ρ _ wρ, hι.1.lift_fst _ _ _, hι.1.lift_snd _ _ _⟩
    obtain ⟨τ', hτ', hτs⟩ : ∃ τ' : (T ⊗ t.G).left ⟶ A.left, τ' ≫ ιA = τ ∧
        τ' ≫ A.hom = π ≫ spMap (algebraMap _ (DualNumber (Γ(X, U.1) ⧸ m))) :=
      ⟨hι.1.lift τ _ wτ, hι.1.lift_fst _ _ _, hι.1.lift_snd _ _ _⟩
    have hpts : ∀ y, τ'.base y = ρ'.base y := by
      intro y
      obtain ⟨K, _, z, ⟨p, rfl⟩, hz⟩ := GlobalTheory.T.dualNumber_unit_translate_eq_id_field_points E H X t _ x0 P hPt y
      have hzz : z ≫ τ' = z ≫ ρ' := hι.1.hom_ext (by rw [Category.assoc, Category.assoc, hτ', hρ']; exact hz)
        (by rw [Category.assoc, Category.assoc, hτs, hρs])
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hzz]
    have hιU : ∀ z, ιA.base z ∈ t.G.hom ⁻¹ᵁ U.1 := fun z => by
      show (ιA ≫ t.G.hom).base z ∈ U.1
      rw [hι.1.w, hx0, ← Category.assoc, Scheme.Hom.comp_apply]
      have h : (chart U).base ((A.hom ≫ spMap q).base z) ∈ Set.range (chart U).base := ⟨_, rfl⟩
      rwa [chart, U.2.range_fromSpec] at h
    have e : (fun n : Fin 2 => ![τ', ρ'] n ≫ ιA) = ![τ, ρ] := by
      funext n; fin_cases n
      · exact hτ'
      · exact hρ'
    have key := GlobalTheory.KS.DlogPol.exists_gen (K := Γ(X, U.1) ⧸ m) π τ' ρ' (fun y W hy => by rwa [← hpts y]) ιA t.PP.L
      t.PP.isLB (fun a b => GlobalTheory.KS.pbT ιA (∑ c, (t.G.hom.appLE U.1 ((t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) ⊓ (t.PP.L.U b ⊓ t.G.hom ⁻¹ᵁ U.1)) (inf_le_left.trans inf_le_right)).hom (r c) * (δ c ((t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) ⊓ (t.PP.L.U b ⊓ t.G.hom ⁻¹ᵁ U.1)) (resG t.G.left (inf_le_inf inf_le_left inf_le_left) (t.PP.L.g a b).val) * resG t.G.left (inf_le_inf inf_le_left inf_le_left) (t.PP.L.g a b)⁻¹.val)) (ιA ⁻¹ᵁ t.PP.L.U a ⊓ ιA ⁻¹ᵁ t.PP.L.U b)) ?_ (GlobalTheory.T.polarisation_dlog_cocycle_coboundary_closed_fibre_charts E H X t U n δ hδ J W j hWa hWcov hWU hj m A ιA hι r h' hcob)
    · rw [e] at key
      exact key
    intro a b y ha hb
    beta_reduce
    have hτy : τ.base y = ρ.base y := by
      rw [← hτ', ← hρ', Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hpts]
    have hρU : ρ.base y ∈ t.G.hom ⁻¹ᵁ U.1 := by rw [← hρ', Scheme.Hom.comp_apply]; exact hιU _
    have ha' : ρ.base y ∈ t.PP.L.U a := by rw [← hτy, ← hτ', Scheme.Hom.comp_apply]; exact ha
    have hb' : ρ.base y ∈ t.PP.L.U b := by rw [← hτy, ← hτ', Scheme.Hom.comp_apply]; exact hb
    have hyO : ρ.base y ∈ (t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) ⊓ (t.PP.L.U b ⊓ t.G.hom ⁻¹ᵁ U.1) := ⟨⟨ha', hρU⟩, ⟨hb', hρU⟩⟩
    have hOab : (t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) ⊓ (t.PP.L.U b ⊓ t.G.hom ⁻¹ᵁ U.1) ≤ t.PP.L.U a ⊓ t.PP.L.U b :=
      inf_le_inf inf_le_left inf_le_left
    have hOU : (t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) ⊓ (t.PP.L.U b ⊓ t.G.hom ⁻¹ᵁ U.1) ≤ t.G.hom ⁻¹ᵁ U.1 :=
      inf_le_left.trans inf_le_right
    have hρ'y : ρ'.base y ∈ ιA ⁻¹ᵁ t.PP.L.U a ⊓ ιA ⁻¹ᵁ t.PP.L.U b := by
      rw [← hpts y]; exact ⟨ha, hb⟩
    have e2a := GlobalTheory.T.firstOrder_translation_formula_germs E H X t U n v hv δ hδ hδ0 hδt r xR hxR (Γ(X, U.1) ⧸ m) q P hPl
    have e2 := e2a _ hOU (resG t.G.left hOab (t.PP.L.g a b).val) y hyO
    rw [GlobalTheory.KS.DlogPol.gs_pbT ρ' ιA y (O₀ := (t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) ⊓ (t.PP.L.U b ⊓ t.G.hom ⁻¹ᵁ U.1)) (O := ιA ⁻¹ᵁ t.PP.L.U a ⊓ ιA ⁻¹ᵁ t.PP.L.U b) (fun z hz => ⟨⟨hz.1, hιU z⟩, ⟨hz.2, hιU z⟩⟩) hρ'y, hτ', hρ',
      ← gs_res τ y hOab (hτy ▸ hyO), ← gs_res ρ y hOab hyO]
    rw [e2]
    have hκ : (∑ c, (t.G.hom.appLE U.1 _ hOU).hom (r c) * (δ c _ (resG t.G.left hOab (t.PP.L.g a b).val) *
        resG t.G.left hOab (t.PP.L.g a b)⁻¹.val)) = (∑ c, (t.G.hom.appLE U.1 _ hOU).hom (r c) *
        δ c _ (resG t.G.left hOab (t.PP.L.g a b).val)) * resG t.G.left hOab (t.PP.L.g a b)⁻¹.val := by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun c _ => by ring
    have hFF : resG t.G.left hOab (t.PP.L.g a b).val * resG t.G.left hOab (t.PP.L.g a b)⁻¹.val = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have hFF' := congrArg (gs ρ y _) hFF
    rw [gs_mul ρ y _ hyO, GlobalTheory.KS.DlogPol.gs_one ρ y _ hyO] at hFF'
    rw [hκ, gs_mul ρ y _ hyO]
    linear_combination (-(gs π y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber (Γ(X, U.1) ⧸ m)))).inv.hom DualNumber.eps) *
      gs ρ y _ (∑ c, (t.G.hom.appLE U.1 _ hOU).hom (r c) * δ c _ (resG t.G.left hOab (t.PP.L.g a b).val)))) * hFF'
  have hP1 : P = toUnit _ ≫ η[t.G] := hK (DualNumber (Γ(X, U.1) ⧸ m)) _ P fun p => by
    obtain ⟨c, hc⟩ := hgen
    exact ⟨⊤, trivial, gen_chartPull (GlobalTheory.chartPullPull (Out.translDiff t.G t.PP.L P) _) c hc⟩
  have hP1' : P.left = (1 : tEpsG x0 ⟶ t.G).left := by rw [hP1, Hom.one_def]
  have h0 := GlobalTheory.VertSpanZero.isCombAtG_zero t x0 _ hT
  have huniq := (hB.2 (Γ(X, U.1) ⧸ m) q _ (GlobalTheory.VertSpanZero.isTanAtG_one t x0)).unique (hP1' ▸ hP) h0
  intro b
  have := congrFun huniq b
  exact Ideal.Quotient.eq_zero_iff_mem.1 this

end GlobalTheory.FibreIndep

theorem GlobalTheory.FibreIndep.fibre_indep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → (∀ a (O : t.G.left.Opens) (h : O ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), δ a O ((t.G.hom.appLE U.1 O h).hom r) = 0) → (∀ a (O : t.G.left.Opens), O ≤ t.G.hom ⁻¹ᵁ U.1 → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → IsTranslate t φ g₀ (v a) w → valR g₀ O (δ a O f) = (valR w O f).snd) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (hj : ∀ i, W i ≤ t.PP.L.U (j i)) (m : Ideal Γ(X, U.1)), m.IsMaximal → ∀ (A : Over (Sp (Γ(X, U.1) ⧸ m))) [GrpObj A] (ι : A.left ⟶ t.G.left), IsGrpPullback A t.G (spMap (Ideal.Quotient.mk m) ≫ chart U) ι → ∀ (r : Fin n → Γ(X, U.1)) (h' : ∀ i, Γ(A.left, ι ⁻¹ᵁ W i)), (∀ i i', (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (∑ b, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r b) * (δ b (W i ⊓ W i') (resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i'))⁻¹.val)) = resG A.left inf_le_left (h' i) - resG A.left inf_le_right (h' i')) → ∀ b, r b ∈ m := GlobalTheory.FibreIndep.fibre_indep'
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreIndependenceLogDerivativesClosedFibreStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibreIndependence_logDerivatives_closedFibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → (∀ a (O : t.G.left.Opens) (h : O ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), δ a O ((t.G.hom.appLE U.1 O h).hom r) = 0) → (∀ a (O : t.G.left.Opens), O ≤ t.G.hom ⁻¹ᵁ U.1 → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → IsTranslate t φ g₀ (v a) w → valR g₀ O (δ a O f) = (valR w O f).snd) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (hj : ∀ i, W i ≤ t.PP.L.U (j i)) (m : Ideal Γ(X, U.1)), m.IsMaximal → ∀ (A : Over (Sp (Γ(X, U.1) ⧸ m))) [GrpObj A] (ι : A.left ⟶ t.G.left), IsGrpPullback A t.G (spMap (Ideal.Quotient.mk m) ≫ chart U) ι → ∀ (r : Fin n → Γ(X, U.1)) (h' : ∀ i, Γ(A.left, ι ⁻¹ᵁ W i)), (∀ i i', (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (∑ b, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r b) * (δ b (W i ⊓ W i') (resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i'))⁻¹.val)) = resG A.left inf_le_left (h' i) - resG A.left inf_le_right (h' i')) → ∀ b, r b ∈ m := by
  first | exact @GlobalTheory.FibreIndep.fibre_indep | exact GlobalTheory.FibreIndep.fibre_indep | (intros; apply GlobalTheory.FibreIndep.fibre_indep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIdealElementPullbackClosedFibreZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIdealElementPullbackClosedFibreZero
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.FibreScalar

theorem appLE_eq_of_eq {A Y : Scheme.{0}} {f g : A ⟶ Y} (h : f = g) (U : Y.Opens) (W : A.Opens)
    (e : W ≤ f ⁻¹ᵁ U) : f.appLE U W e = g.appLE U W (h ▸ e) := by
  subst h; rfl

theorem fromSpec_appLE_top {Y : Scheme.{0}} {U : Y.Opens} (hU : IsAffineOpen U) (e : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U) :
    hU.fromSpec.appLE U ⊤ e ≫ (Scheme.ΓSpecIso Γ(Y, U)).hom = 𝟙 _ := by
  rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, Category.assoc,
    ← Functor.map_comp_assoc]
  have : ((eqToHom hU.fromSpec_preimage_self).op ≫ (homOfLE e).op : Opposite.op _ ⟶ Opposite.op _) = 𝟙 _ :=
    Subsingleton.elim _ _
  rw [this, CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id]

theorem specMap_appLE_top {A B : CommRingCat.{0}} (f : A ⟶ B) (e : (⊤ : (Spec B).Opens) ≤ Spec.map f ⁻¹ᵁ ⊤) :
    (Spec.map f).appLE ⊤ ⊤ e ≫ (Scheme.ΓSpecIso B).hom = (Scheme.ΓSpecIso A).hom ≫ f := by
  rw [← Scheme.ΓSpecIso_naturality]
  rfl

theorem spMap_chart_appLE_top {X : Scheme.{0}} (U : X.affineOpens) (m : Ideal Γ(X, U.1))
    (e : ⊤ ≤ (spMap (Ideal.Quotient.mk m) ≫ chart U) ⁻¹ᵁ U.1) :
    (spMap (Ideal.Quotient.mk m) ≫ chart U).appLE U.1 ⊤ e ≫
        (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U.1) ⧸ m))).hom =
      CommRingCat.ofHom (Ideal.Quotient.mk m) := by
  have e1 : (⊤ : (Sp Γ(X, U.1)).Opens) ≤ U.2.fromSpec ⁻¹ᵁ U.1 := U.2.fromSpec_preimage_self.ge
  have e2 : (⊤ : (Sp (Γ(X, U.1) ⧸ m)).Opens) ≤ spMap (Ideal.Quotient.mk m) ⁻¹ᵁ ⊤ := le_top
  have hk := fromSpec_appLE_top U.2 e1
  change (spMap (Ideal.Quotient.mk m) ≫ U.2.fromSpec).appLE U.1 ⊤ e ≫ _ = _
  have hk' : U.2.fromSpec.appLE U.1 ⊤ e1 ≫ (Scheme.ΓSpecIso (CommRingCat.of Γ(X, U.1))).hom = 𝟙 _ := hk
  rw [← Scheme.Hom.appLE_comp_appLE (spMap (Ideal.Quotient.mk m)) U.2.fromSpec _ ⊤ _ e1 e2, Category.assoc,
    specMap_appLE_top, ← Category.assoc, hk', Category.id_comp]

theorem fibre_scalar_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (m : Ideal Γ(X, U.1)) (A : Over (Sp (Γ(X, U.1) ⧸ m))) [GrpObj A] (ι : A.left ⟶ t.G.left), IsGrpPullback A t.G (spMap (Ideal.Quotient.mk m) ≫ chart U) ι → ∀ (O : t.G.left.Opens) (hO : O ≤ t.G.hom ⁻¹ᵁ U.1) (O' : A.left.Opens) (hO' : O' ≤ ι ⁻¹ᵁ O) (r : Γ(X, U.1)), r ∈ m → (ι.appLE O O' hO').hom ((t.G.hom.appLE U.1 O hO).hom r) = 0 := by
  intro E _ _ _ H X t U m A _ ι hpb O hO O' hO' r hr
  set g := spMap (Ideal.Quotient.mk m) ≫ chart U with hg
  have hw : ι ≫ t.G.hom = A.hom ≫ g := hpb.1.w
  have e5 : (⊤ : (Sp (Γ(X, U.1) ⧸ m)).Opens) ≤ g ⁻¹ᵁ U.1 := by
    intro x _
    change g x ∈ U.1
    rw [hg, Scheme.Hom.comp_apply]
    exact U.2.fromSpec_preimage_self.ge (Set.mem_univ _)
  have hz : (g.appLE U.1 ⊤ e5).hom r = 0 := by
    have h := congrArg (fun φ => φ.hom r) (spMap_chart_appLE_top U m e5)
    simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom, Ideal.Quotient.eq_zero_iff_mem.mpr hr] at h
    have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U.1) ⧸ m))).hom.hom :=
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U.1) ⧸ m))).hom).1
    exact hinj (h.trans (map_zero _).symm)
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, appLE_eq_of_eq hw,
    ← Scheme.Hom.appLE_comp_appLE A.hom g U.1 ⊤ O' e5 (fun x _ => trivial), CommRingCat.comp_apply, hz, map_zero]

end GlobalTheory.FibreScalar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIdealElementPullbackClosedFibreZeroStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximalIdeal_element_pullback_closedFibre_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (m : Ideal Γ(X, U.1)) (A : Over (Sp (Γ(X, U.1) ⧸ m))) [GrpObj A] (ι : A.left ⟶ t.G.left), IsGrpPullback A t.G (spMap (Ideal.Quotient.mk m) ≫ chart U) ι → ∀ (O : t.G.left.Opens) (hO : O ≤ t.G.hom ⁻¹ᵁ U.1) (O' : A.left.Opens) (hO' : O' ≤ ι ⁻¹ᵁ O) (r : Γ(X, U.1)), r ∈ m → (ι.appLE O O' hO').hom ((t.G.hom.appLE U.1 O hO).hom r) = 0 := by
  first | exact @GlobalTheory.FibreScalar.fibre_scalar_zero | exact GlobalTheory.FibreScalar.fibre_scalar_zero | (intros; apply GlobalTheory.FibreScalar.fibre_scalar_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationLogDerivativeCechCocycle
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationLogDerivativeCechCocycle
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

namespace GlobalTheory.KappaCoc

theorem resG_resG' (Z : Scheme.{0}) {U V O : Z.Opens} (h : V ≤ U) (h' : O ≤ V) (f : Γ(Z, U)) :
    resG Z h' (resG Z h f) = resG Z (h'.trans h) f := by
  simp only [resG, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem dlog_cocycle {Z : Scheme.{0}} {W₀ : Z.Opens} {d : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)} (hd : IsField W₀ d)
    (L : LB Z) (hL : L.IsLB) {a b c : L.ι} {W₁ W₂ W₃ : Z.Opens} (h₁ : W₁ ≤ L.U a) (h₂ : W₂ ≤ L.U b)
    (h₃ : W₃ ≤ L.U c) (hW₁ : W₁ ≤ W₀) (hW₂ : W₂ ≤ W₀) :
    resG Z (inf_le_left : W₁ ⊓ W₂ ⊓ W₃ ≤ W₁ ⊓ W₂) (d (W₁ ⊓ W₂) (resG Z (inf_le_inf h₁ h₂) (L.g a b).val) *
        resG Z (inf_le_inf h₁ h₂) (L.g a b)⁻¹.val) +
      resG Z (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W₁ ⊓ W₂ ⊓ W₃ ≤ W₂ ⊓ W₃)
        (d (W₂ ⊓ W₃) (resG Z (inf_le_inf h₂ h₃) (L.g b c).val) * resG Z (inf_le_inf h₂ h₃) (L.g b c)⁻¹.val) =
    resG Z (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W₁ ⊓ W₂ ⊓ W₃ ≤ W₁ ⊓ W₃)
        (d (W₁ ⊓ W₃) (resG Z (inf_le_inf h₁ h₃) (L.g a c).val) * resG Z (inf_le_inf h₁ h₃) (L.g a c)⁻¹.val) := by
  have l₁ : W₁ ⊓ W₂ ⊓ W₃ ≤ W₁ ⊓ W₂ := inf_le_left
  have l₂ : W₁ ⊓ W₂ ⊓ W₃ ≤ W₂ ⊓ W₃ := le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have l₃ : W₁ ⊓ W₂ ⊓ W₃ ≤ W₁ ⊓ W₃ := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hV : W₁ ⊓ W₂ ⊓ W₃ ≤ W₀ := inf_le_left.trans (inf_le_left.trans hW₁)
  have lU : W₁ ⊓ W₂ ⊓ W₃ ≤ L.U a ⊓ L.U b ⊓ L.U c := inf_le_inf (inf_le_inf h₁ h₂) h₃
  have comm : ∀ {O : Z.Opens} (h : W₁ ⊓ W₂ ⊓ W₃ ≤ O), O ≤ W₀ → ∀ x : Γ(Z, O),
      resG Z h (d O x) = d _ (resG Z h x) := fun h hO x => (hd.2.2 _ _ h hO x).symm
  rw [map_mul, map_mul, map_mul, comm l₁ (inf_le_left.trans hW₁), comm l₂ (inf_le_left.trans hW₂),
    comm l₃ (inf_le_left.trans hW₁), resG_resG', resG_resG', resG_resG', resG_resG', resG_resG', resG_resG']
  have uv : ∀ {p q : L.ι} (h : W₁ ⊓ W₂ ⊓ W₃ ≤ L.U p ⊓ L.U q),
      resG Z h (L.g p q).val * resG Z h (L.g p q)⁻¹.val = 1 := fun h => by
    rw [← map_mul, Units.mul_inv, map_one]
  have co := congrArg (fun u : Γ(Z, L.U a ⊓ L.U b ⊓ L.U c)ˣ => resG Z lU u.val) (hL.cocycle a b c)
  simp only [Units.val_mul, map_mul] at co
  change resG Z lU (resG Z _ (L.g a b).val) * resG Z lU (resG Z _ (L.g b c).val) =
    resG Z lU (resG Z _ (L.g a c).val) at co
  rw [resG_resG', resG_resG', resG_resG'] at co
  have e := hd.2.1 _ hV (resG Z (l₁.trans (inf_le_inf h₁ h₂)) (L.g a b).val)
    (resG Z (l₂.trans (inf_le_inf h₂ h₃)) (L.g b c).val)
  rw [co] at e
  have ua := uv (l₁.trans (inf_le_inf h₁ h₂))
  have ub := uv (l₂.trans (inf_le_inf h₂ h₃))
  have uc := uv (l₃.trans (inf_le_inf h₁ h₃))
  set A := resG Z (l₁.trans (inf_le_inf h₁ h₂)) (L.g a b).val
  set B := resG Z (l₂.trans (inf_le_inf h₂ h₃)) (L.g b c).val
  set C := resG Z (l₃.trans (inf_le_inf h₁ h₃)) (L.g a c).val
  set A' := resG Z (l₁.trans (inf_le_inf h₁ h₂)) (L.g a b)⁻¹.val
  set B' := resG Z (l₂.trans (inf_le_inf h₂ h₃)) (L.g b c)⁻¹.val
  set C' := resG Z (l₃.trans (inf_le_inf h₁ h₃)) (L.g a c)⁻¹.val
  set dA := d _ A
  set dB := d _ B
  set dC := d _ C
  linear_combination (-C') * e - (dA * A' * C' + dB * B' * C') * co + dA * B * C' * ua + dB * A * C' * ub -
    (dA * A' + dB * B') * uc

end GlobalTheory.KappaCoc

theorem GlobalTheory.KappaCoc.kappa_cocycle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (n : ℕ) (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (hj : ∀ i, W i ≤ t.PP.L.U (j i)), ∀ (b : Fin n) (i i' i'' : J), resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (δ b (W i ⊓ W i') (resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i'))⁻¹.val) + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (δ b (W i' ⊓ W i'') (resG t.G.left (inf_le_inf (hj i') (hj i'')) (t.PP.L.g (j i') (j i'')).val) * resG t.G.left (inf_le_inf (hj i') (hj i'')) (t.PP.L.g (j i') (j i''))⁻¹.val) = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (δ b (W i ⊓ W i'') (resG t.G.left (inf_le_inf (hj i) (hj i'')) (t.PP.L.g (j i) (j i'')).val) * resG t.G.left (inf_le_inf (hj i) (hj i'')) (t.PP.L.g (j i) (j i''))⁻¹.val) := by
  intro E _ _ _ H X t U n δ hδ J W j _ _ hWU hj b i i' i''
  exact GlobalTheory.KappaCoc.dlog_cocycle (hδ b) t.PP.L t.PP.isLB (hj i) (hj i') (hj i'') (hWU i) (hWU i')
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationLogDerivativeCechCocycleStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisation_logDerivative_cechCocycle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (n : ℕ) (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (hj : ∀ i, W i ≤ t.PP.L.U (j i)), ∀ (b : Fin n) (i i' i'' : J), resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (δ b (W i ⊓ W i') (resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i'))⁻¹.val) + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (δ b (W i' ⊓ W i'') (resG t.G.left (inf_le_inf (hj i') (hj i'')) (t.PP.L.g (j i') (j i'')).val) * resG t.G.left (inf_le_inf (hj i') (hj i'')) (t.PP.L.g (j i') (j i''))⁻¹.val) = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (δ b (W i ⊓ W i'') (resG t.G.left (inf_le_inf (hj i) (hj i'')) (t.PP.L.g (j i) (j i'')).val) * resG t.G.left (inf_le_inf (hj i) (hj i'')) (t.PP.L.g (j i) (j i''))⁻¹.val) := by
  first | exact @GlobalTheory.KappaCoc.kappa_cocycle | exact GlobalTheory.KappaCoc.kappa_cocycle | (intros; apply GlobalTheory.KappaCoc.kappa_cocycle <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreCechCocycleInTangentSpan
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

namespace GlobalTheory.FibreSpan

theorem pull_cocycle {Y Z : Scheme.{0}} (ι : Y ⟶ Z) {J : Type} (W : J → Z.Opens) (d : ∀ i i' : J, Γ(Z, W i ⊓ W i'))
    (hd : ∀ i i' i'', resG Z (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (d i i') + resG Z (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (d i' i'') = resG Z (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (d i i'')) :
    ∀ i i' i'', resG Y (inf_le_left : ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i' ⊓ ι ⁻¹ᵁ W i'' ≤ ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') ((ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (d i i')) + resG Y (le_inf (inf_le_left.trans inf_le_right) inf_le_right : ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i' ⊓ ι ⁻¹ᵁ W i'' ≤ ι ⁻¹ᵁ W i' ⊓ ι ⁻¹ᵁ W i'') ((ι.appLE (W i' ⊓ W i'') (ι ⁻¹ᵁ W i' ⊓ ι ⁻¹ᵁ W i'') (fun _ hx => hx)).hom (d i' i'')) = resG Y (le_inf (inf_le_left.trans inf_le_left) inf_le_right : ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i' ⊓ ι ⁻¹ᵁ W i'' ≤ ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i'') ((ι.appLE (W i ⊓ W i'') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i'') (fun _ hx => hx)).hom (d i i'')) := by
  intro i i' i''
  have e0 : ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i' ⊓ ι ⁻¹ᵁ W i'' ≤ ι ⁻¹ᵁ (W i ⊓ W i' ⊓ W i'') := fun _ hx => hx
  have := congrArg (ι.appLE (W i ⊓ W i' ⊓ W i'') _ e0).hom (hd i i' i'')
  simp only [map_add (f := _), ← CommRingCat.comp_apply, Scheme.Hom.map_appLE] at this
  simp only [← CommRingCat.comp_apply]
  erw [Scheme.Hom.appLE_map, Scheme.Hom.appLE_map, Scheme.Hom.appLE_map]
  exact this

theorem sum_divisible_eq_sum_mul {R : Type} [CommRing R] {n : ℕ} (a : R) (x F : Fin n → R) :
    ∑ b, -(a * x b) * F b = -a * ∑ b, x b * F b := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring


set_option maxHeartbeats 1600000 in
theorem fibre_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → (∀ a (O : t.G.left.Opens) (h : O ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), δ a O ((t.G.hom.appLE U.1 O h).hom r) = 0) → (∀ a (O : t.G.left.Opens), O ≤ t.G.hom ⁻¹ᵁ U.1 → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → IsTranslate t φ g₀ (v a) w → valR g₀ O (δ a O f) = (valR w O f).snd) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (hj : ∀ i, W i ≤ t.PP.L.U (j i)) (m : Ideal Γ(X, U.1)), m.IsMaximal → ∀ (A : Over (Sp (Γ(X, U.1) ⧸ m))) [GrpObj A] (ι : A.left ⟶ t.G.left), IsGrpPullback A t.G (spMap (Ideal.Quotient.mk m) ≫ chart U) ι → ∀ (c : ∀ i i' : J, Γ(t.G.left, W i ⊓ W i')), (∀ i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → ∃ θ : Fin n → Γ(X, U.1), ∃ h' : ∀ i, Γ(A.left, ι ⁻¹ᵁ W i), ∀ i i', (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (c i i' - ∑ b, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (θ b) * (δ b (W i ⊓ W i') (resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i'))⁻¹.val)) = resG A.left inf_le_left (h' i) - resG A.left inf_le_right (h' i') := by
  intro E _ _ _ H X t hP hA hK U n v hv hu δ hδ hδR hδT J W j hW hcov hWU hj m hm A _ ι hpb c hc
  have hκ := GlobalTheory.T.polarisation_logDerivative_cechCocycle E H X t U n δ hδ J W j hW hcov hWU hj
  have hz := GlobalTheory.T.maximalIdeal_element_pullback_closedFibre_zero E H X t U m A ι hpb
  have hind : ∀ (r : Fin n → Γ(X, U.1)) (h' : ∀ i, Γ(A.left, ι ⁻¹ᵁ W i)), (∀ i i', ∑ b, (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom ((t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r b)) * (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (δ b (W i ⊓ W i') (resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i'))⁻¹.val) = resG A.left inf_le_left (h' i) - resG A.left inf_le_right (h' i')) → ∀ b, r b ∈ m :=
    fun r h'' hr => GlobalTheory.T.fibreIndependence_logDerivatives_closedFibre E H X t hP hA hK U n v hv hu δ hδ hδR hδT J W j hW hcov hWU hj m hm A ι hpb r h''
      (fun i i' => by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        exact (Finset.sum_congr rfl fun b _ => map_mul _ _ _).trans (hr i i'))
  obtain ⟨r, ⟨b₀, hb₀⟩, h', hh⟩ := GlobalTheory.T.closed_fibre_cechCocycles_combination_coefficient_nonunit E H X t hP hA U n v hv hu J W hW hcov hWU m hm A ι hpb
    (Fin.cons (fun i i' => (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (c i i')) (fun b i i' => (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (δ b (W i ⊓ W i') (resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i'))⁻¹.val)))
    (fun b => Fin.cases (pull_cocycle ι W c hc) (fun b => pull_cocycle ι W _ (hκ b)) b)
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at hh
  have hr0 : r 0 ∉ m := by
    intro h0
    have := hind (fun b => r b.succ) h' (fun i i' => by
      have h1 := hh i i'
      rw [hz (W i ⊓ W i') (inf_le_left.trans (hWU i)) (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx) (r 0) h0, zero_mul, zero_add] at h1
      exact h1)
    refine hb₀ ?_
    cases b₀ using Fin.cases with
    | zero => exact h0
    | succ b => exact this b
  have hex := hm.exists_inv hr0
  choose y i₀ hi₀ hy using hex
  refine ⟨fun b => -(y * r b.succ), fun i => (ι.appLE (W i) (ι ⁻¹ᵁ W i) le_rfl).hom ((t.G.hom.appLE U.1 (W i) (hWU i)).hom y) * h' i, fun i i' => ?_⟩
  have key1 : ∀ (O : t.G.left.Opens) (hO : O ≤ t.G.hom ⁻¹ᵁ U.1) (O' : A.left.Opens) (hO' : O' ≤ ι ⁻¹ᵁ O)
      (x : Γ(X, U.1)), (ι.appLE O O' hO').hom ((t.G.hom.appLE U.1 O hO).hom x) =
        ((ι ≫ t.G.hom).appLE U.1 O' (hO'.trans fun _ h => hO h)).hom x := by
    intro O hO O' hO' x
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  have key2 : ∀ (O O' : A.left.Opens) (h : O' ≤ O) (hO : O ≤ (ι ≫ t.G.hom) ⁻¹ᵁ U.1) (x : Γ(X, U.1)),
      resG A.left h (((ι ≫ t.G.hom).appLE U.1 O hO).hom x) = ((ι ≫ t.G.hom).appLE U.1 O' (h.trans hO)).hom x := by
    intro O O' h hO x
    have e := Scheme.Hom.appLE_map (ι ≫ t.G.hom) hO (homOfLE h).op
    exact congrArg (fun φ => φ.hom x) e
  have hle : ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i' ≤ (ι ≫ t.G.hom) ⁻¹ᵁ U.1 := fun x hx => hWU i hx.1
  have h1 := hh i i'
  have hy' : ((ι ≫ t.G.hom).appLE U.1 _ hle).hom y * ((ι ≫ t.G.hom).appLE U.1 _ hle).hom (r 0) = 1 := by
    have := congrArg ((ι ≫ t.G.hom).appLE U.1 _ hle).hom hy
    rw [map_add (f := _), map_mul, map_one] at this
    have h0 : ((ι ≫ t.G.hom).appLE U.1 _ hle).hom i₀ = 0 :=
      (key1 (W i ⊓ W i') (inf_le_left.trans (hWU i)) (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx) i₀).symm.trans
        (hz (W i ⊓ W i') (inf_le_left.trans (hWU i)) (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx) i₀ hi₀)
    rw [h0, add_zero] at this
    exact this
  have hA1 : ∀ x : Γ(X, U.1), (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom ((t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom x) =
      ((ι ≫ t.G.hom).appLE U.1 _ hle).hom x := fun x => key1 _ _ _ _ x
  have hB1 : resG A.left (inf_le_left : ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i' ≤ ι ⁻¹ᵁ W i) ((ι.appLE (W i) (ι ⁻¹ᵁ W i) le_rfl).hom ((t.G.hom.appLE U.1 (W i) (hWU i)).hom y)) = ((ι ≫ t.G.hom).appLE U.1 _ hle).hom y := by
    rw [key1, key2]
  have hB2 : resG A.left (inf_le_right : ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i' ≤ ι ⁻¹ᵁ W i') ((ι.appLE (W i') (ι ⁻¹ᵁ W i') le_rfl).hom ((t.G.hom.appLE U.1 (W i') (hWU i')).hom y)) = ((ι ≫ t.G.hom).appLE U.1 _ hle).hom y := by
    rw [key1, key2]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, map_sum]
  simp only [map_neg, map_mul, hA1, hB1, hB2] at h1 ⊢
  rw [sum_divisible_eq_sum_mul]
  linear_combination (((ι ≫ t.G.hom).appLE U.1 _ hle).hom y) * h1 + (-((ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (c i i'))) * hy'

end GlobalTheory.FibreSpan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreCechCocycleInTangentSpanStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedFibre_cechCocycle_in_tangentSpan : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → (∀ a (O : t.G.left.Opens) (h : O ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), δ a O ((t.G.hom.appLE U.1 O h).hom r) = 0) → (∀ a (O : t.G.left.Opens), O ≤ t.G.hom ⁻¹ᵁ U.1 → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → IsTranslate t φ g₀ (v a) w → valR g₀ O (δ a O f) = (valR w O f).snd) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (hj : ∀ i, W i ≤ t.PP.L.U (j i)) (m : Ideal Γ(X, U.1)), m.IsMaximal → ∀ (A : Over (Sp (Γ(X, U.1) ⧸ m))) [GrpObj A] (ι : A.left ⟶ t.G.left), IsGrpPullback A t.G (spMap (Ideal.Quotient.mk m) ≫ chart U) ι → ∀ (c : ∀ i i' : J, Γ(t.G.left, W i ⊓ W i')), (∀ i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → ∃ θ : Fin n → Γ(X, U.1), ∃ h' : ∀ i, Γ(A.left, ι ⁻¹ᵁ W i), ∀ i i', (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (c i i' - ∑ b, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (θ b) * (δ b (W i ⊓ W i') (resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i'))⁻¹.val)) = resG A.left inf_le_left (h' i) - resG A.left inf_le_right (h' i') := by
  first | exact @GlobalTheory.FibreSpan.fibre_span | exact GlobalTheory.FibreSpan.fibre_span | (intros; apply GlobalTheory.FibreSpan.fibre_span <;> assumption)
end

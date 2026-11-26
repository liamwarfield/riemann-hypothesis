module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerChangeOfTangentFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleTrivialOfSamePolarization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonKltCentreOfNotKltAfterAdding
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerConditionRestrictBasicOpenOfAffine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeStalkEvalAtOriginOriginStalkConstants

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCombAtZeroSectionEigenBlockFlattenedFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCombAtZeroSectionEigenBlockFlattenedFrame
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogKSDiv


attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory in
open MonObj in
theorem isCombAtG_extend {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {X0 : Scheme.{0}} (t : SAB H X0) {R : Type} [CommRing R] (x : Sp R ⟶ X0) {m n : ℕ}
    (f : Fin m → Fin n) (hf : Function.Injective f)
    {v : Fin m → (Sp (DualNumber R) ⟶ t.G.left)} {v' : Fin n → (Sp (DualNumber R) ⟶ t.G.left)}
    (hv : ∀ j, IsTanAtG t x (v' j)) {cf : Fin m → R} {cf' : Fin n → R}
    (hvf : ∀ k, v' (f k) = v k) (hcf : ∀ k, cf' (f k) = cf k) (hz : ∀ c, (¬ ∃ k, f k = c) → cf' c = 0)
    {w : Sp (DualNumber R) ⟶ t.G.left} (h : IsCombAtG t x v cf w) : IsCombAtG t x v' cf' w := by
  classical
  have h0 : spMap (epsMul (0 : R)) =
      spMap (algebraMap R (DualNumber R)) ≫ spMap (TrivSqZeroExt.fstHom R R R).toRingHom := by
    have e : epsMul (0 : R) = (algebraMap R (DualNumber R)).comp (TrivSqZeroExt.fstHom R R R).toRingHom :=
      RingHom.ext fun z => by ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
    rw [← Spec.map_comp, e]
    rfl
  obtain ⟨u, hu, hw⟩ := h
  refine ⟨Function.extend f u 1, fun c => ?_, ?_⟩
  · by_cases hc : ∃ k, f k = c
    · obtain ⟨k, rfl⟩ := hc
      rw [hf.extend_apply, hu, hvf, hcf]
    · let p : tEpsG x ⟶ Over.mk x := Over.homMk (spMap (algebraMap R (DualNumber R))) rfl
      rw [Function.extend_apply' _ _ _ hc, hz c hc, h0, Category.assoc, (hv c).2, Pi.one_apply,
        ← MonObj.comp_one p]
      rfl
  · rw [← hw]
    congr 1
    letI : CommMonoid (tEpsG x ⟶ t.G) := Hom.commMonoid
    rw [List.prod_ofFn, List.prod_ofFn]
    symm
    refine Finset.prod_of_injOn f hf.injOn (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) ?_ ?_
    · intro c _ hc
      rw [Function.extend_apply' _ _ _ ?_, Pi.one_apply]
      rintro ⟨k, rfl⟩
      exact hc ⟨k, by simp, rfl⟩
    · intro k _
      rw [hf.extend_apply]

theorem isCombAtG_flatFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (X : Scheme.{0}) (t : SAB H X) (S : Type) [CommRing S] (x : Sp S ⟶ X) (n n' : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n') (w' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber S) ⟶ t.G.left)) (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) (w : Sp (DualNumber S) ⟶ t.G.left), (∀ τ k, IsTanAtG t x (w' τ k)) → IsCombAtG t x (w' σ) (A σ i) w → IsCombAtG t x (fun c => w' (e'.symm c).1 (e'.symm c).2) (fun c => GlobalTheory.LogKSDiv.flatFrame A e e' (e ⟨σ, i⟩) c) w := by
  classical
  intro E _ _ _ H Dw X t S _ x n n' e e' w' A σ i w htan h
  refine isCombAtG_extend t x (fun k => e' ⟨σ, k⟩) (fun a b hab => ?_) (fun c => htan _ _) (fun k => ?_)
    (fun k => flatFrame_apply A e e' σ i k) (fun c hc => ?_) h
  · exact sigma_mk_injective (β := fun τ : E →+* ℂ => Fin (Dw.mult τ)) (e'.injective hab)
  · show (fun z : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) => w' z.1 z.2) (e'.symm (e' ⟨σ, k⟩)) = _
    rw [Equiv.symm_apply_apply]
  · obtain ⟨⟨τ, k⟩, rfl⟩ := e'.surjective c
    have hne : σ ≠ τ := by
      rintro rfl
      exact hc ⟨k, rfl⟩
    simp [flatFrame, Matrix.blockDiagonal'_apply_ne _ _ _ hne]

end GlobalTheory.LogKSDiv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCombAtZeroSectionEigenBlockFlattenedFrameStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCombAtZeroSection_eigenBlock_flattened_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (X : Scheme.{0}) (t : SAB H X) (S : Type) [CommRing S] (x : Sp S ⟶ X) (n n' : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n') (w' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber S) ⟶ t.G.left)) (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) (w : Sp (DualNumber S) ⟶ t.G.left), (∀ τ k, IsTanAtG t x (w' τ k)) → IsCombAtG t x (w' σ) (A σ i) w → IsCombAtG t x (fun c => w' (e'.symm c).1 (e'.symm c).2) (fun c => GlobalTheory.LogKSDiv.flatFrame A e e' (e ⟨σ, i⟩) c) w := by
  first | exact @GlobalTheory.LogKSDiv.isCombAtG_flatFrame | exact GlobalTheory.LogKSDiv.isCombAtG_flatFrame | (intros; apply GlobalTheory.LogKSDiv.isCombAtG_flatFrame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericTangentCoefficientsUniqueAffineOpenBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericTangentCoefficientsUniqueAffineOpenBasis
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogKSDiv.GenUniq

open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (spMap_comp_spMap)

attribute [local instance] Over.cartesianMonoidalCategory

theorem dualMap_injective {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Injective f) : Function.Injective (Formalism.L2.Pj.dualMap f) := by
  intro a b h
  have h1 := congrArg TrivSqZeroExt.fst h
  have h2 := congrArg TrivSqZeroExt.snd h
  simp only [Formalism.L2.Pj.dualMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.fst_add,
    TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
    TrivSqZeroExt.snd_inr, zero_add] at h1 h2
  exact TrivSqZeroExt.ext (hf h1) (hf h2)

theorem exists_common_denom {A K : Type} [CommRing A] [Field K] (ρ : A →+* K)
    (hfr : ∀ x : K, ∃ a b : A, ρ b ≠ 0 ∧ x * ρ b = ρ a) {κ : Type} [Fintype κ] (c : κ → K) :
    ∃ (b : A) (a : κ → A), ρ b ≠ 0 ∧ ∀ i, ρ b * c i = ρ (a i) := by
  classical
  choose a b hb hab using hfr
  refine ⟨∏ i, b (c i), fun i => a (c i) * ∏ j ∈ Finset.univ.erase i, b (c j), ?_, fun i => ?_⟩
  · rw [map_prod]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hb _
  · rw [← Finset.mul_prod_erase Finset.univ (fun j => b (c j)) (Finset.mem_univ i), map_mul, map_mul, ← hab]
    ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

def bcEps {A K : Type} [CommRing A] [CommRing K] (ρ : A →+* K) (x : Sp A ⟶ X) :
    tEpsG (spMap ρ ≫ x) ⟶ tEpsG x :=
  Over.homMk (spMap (Formalism.L2.Pj.dualMap ρ)) (by
    show spMap (Formalism.L2.Pj.dualMap ρ) ≫ spMap (algebraMap A (DualNumber A)) ≫ x =
      spMap (algebraMap K (DualNumber K)) ≫ spMap ρ ≫ x
    rw [← Category.assoc, ← Category.assoc, spMap_comp_spMap, spMap_comp_spMap, Formalism.L2.Pj.dualMap_comp_alg])

theorem bcEps_smT {A K : Type} [CommRing A] [CommRing K] (ρ : A →+* K) (x : Sp A ⟶ X) (a : A)
    (v : tEpsG x ⟶ t.G) :
    bcEps ρ x ≫ smT x a v = smT (spMap ρ ≫ x) (ρ a) (bcEps ρ x ≫ v) := by
  apply Over.OverMorphism.ext
  show spMap (Formalism.L2.Pj.dualMap ρ) ≫ spMap (epsMul a) ≫ v.left =
    spMap (epsMul (ρ a)) ≫ spMap (Formalism.L2.Pj.dualMap ρ) ≫ v.left
  rw [← Category.assoc, ← Category.assoc, spMap_comp_spMap, spMap_comp_spMap, Formalism.L2.Pj.dualMap_comp_epsMul]

theorem bcEps_combT {A K : Type} [CommRing A] [CommRing K] (ρ : A →+* K) (x : Sp A ⟶ X) {n : ℕ}
    (v : Fin n → (tEpsG x ⟶ t.G)) (a : Fin n → A) :
    bcEps ρ x ≫ combT x v a = combT (spMap ρ ≫ x) (fun i => bcEps ρ x ≫ v i) (fun i => ρ (a i)) := by
  let f : (tEpsG x ⟶ t.G) →* (tEpsG (spMap ρ ≫ x) ⟶ t.G) :=
    { toFun := fun u => bcEps ρ x ≫ u
      map_one' := MonObj.comp_one _
      map_mul' := fun u w => MonObj.comp_mul _ _ _ }
  have h := map_prod f (fun j => smT x (a j) (v j)) Finset.univ
  refine h.trans ?_
  exact Finset.prod_congr rfl fun i _ => bcEps_smT t ρ x (a i) (v i)

theorem coeff_unique {A K : Type} [CommRing A] [Field K] (ρ : A →+* K) (hinj : Function.Injective ρ)
    (hfr : ∀ x : K, ∃ a b : A, ρ b ≠ 0 ∧ x * ρ b = ρ a) (x : Sp A ⟶ X) {n : ℕ}
    (v : Fin n → (Sp (DualNumber A) ⟶ t.G.left)) (hv : ∀ i, IsTanAtG t x (v i))
    (hb : ∀ w, IsTanAtG t x w → ∃! cf : Fin n → A, IsCombAtG t x v cf w)
    (cf cf' : Fin n → K) (w : Sp (DualNumber K) ⟶ t.G.left)
    (h : IsCombAtG t (spMap ρ ≫ x) (fun i => spMap (Formalism.L2.Pj.dualMap ρ) ≫ v i) cf w)
    (h' : IsCombAtG t (spMap ρ ≫ x) (fun i => spMap (Formalism.L2.Pj.dualMap ρ) ≫ v i) cf' w) : cf = cf' := by
  let V : Fin n → (tEpsG x ⟶ t.G) := fun i => ovT (hv i)
  have e := (isCombAtG_iff t (spMap ρ ≫ x) (fun i => bcEps ρ x ≫ V i) cf w).1 h
  have e' := (isCombAtG_iff t (spMap ρ ≫ x) (fun i => bcEps ρ x ≫ V i) cf' w).1 h'
  have hc : combT (spMap ρ ≫ x) (fun i => bcEps ρ x ≫ V i) cf =
      combT (spMap ρ ≫ x) (fun i => bcEps ρ x ≫ V i) cf' := Over.OverMorphism.ext (e.trans e'.symm)
  obtain ⟨b, a, hb0, ha⟩ := exists_common_denom ρ hfr (Sum.elim cf cf')
  have hs := congrArg (smT (spMap ρ ≫ x) (ρ b)) hc
  rw [smT_combT, smT_combT] at hs
  have a1 : (fun j => ρ b * cf j) = fun j => ρ (a (Sum.inl j)) := funext fun j => ha (Sum.inl j)
  have a2 : (fun j => ρ b * cf' j) = fun j => ρ (a (Sum.inr j)) := funext fun j => ha (Sum.inr j)
  rw [a1, a2, ← bcEps_combT, ← bcEps_combT] at hs
  have hsep : IsSeparated t.G.hom := t.semi.separated
  have hdom : IsSchemeTheoreticallyDominant (spMap (Formalism.L2.Pj.dualMap ρ)) :=
    GlobalTheory.ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom _) (dualMap_injective ρ hinj)
  have hA : (combT x V fun j => a (Sum.inl j)).left = (combT x V fun j => a (Sum.inr j)).left :=
    GlobalTheory.ExtUnique.hom_ext_of_dominant t.G.hom
      ((Over.w (combT x V fun j => a (Sum.inl j))).trans (Over.w (combT x V fun j => a (Sum.inr j))).symm)
      (spMap (Formalism.L2.Pj.dualMap ρ)) (congrArg (fun φ => φ.left) hs)
  have ht : IsTanAtG t x (combT x V fun j => a (Sum.inl j)).left :=
    isTanAtG_of _ (combT_tan x V (fun j => smT_zero_ovT (hv j)) _)
  have haa : (fun j => a (Sum.inl j)) = fun j => a (Sum.inr j) :=
    (hb _ ht).unique ((isCombAtG_iff t x V _ _).2 rfl) ((isCombAtG_iff t x V _ _).2 hA.symm)
  funext j
  apply mul_left_cancel₀ hb0
  rw [congrFun a1 j, congrFun a2 j, congrFun haa j]

end GlobalTheory.LogKSDiv.GenUniq

namespace GlobalTheory.LogKSDiv

theorem generic_coeff_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (W : X.affineOpens) (K : Type) [Field K] (ρW : Γ(X, W.1) →+* K), Function.Injective ρW → (∀ x : K, ∃ a b : Γ(X, W.1), ρW b ≠ 0 ∧ x * ρW b = ρW a) → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, W.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (GlobalTheory.LogKS.chart W) (v i)) → (∀ w, IsTanAtG t (GlobalTheory.LogKS.chart W) w → ∃! cf : Fin n → Γ(X, W.1), IsCombAtG t (GlobalTheory.LogKS.chart W) v cf w) → ∀ (cf cf' : Fin n → K) (w : Sp (DualNumber K) ⟶ t.G.left), IsCombAtG t (spMap ρW ≫ GlobalTheory.LogKS.chart W) (fun i => spMap (Formalism.L2.Pj.dualMap ρW) ≫ v i) cf w → IsCombAtG t (spMap ρW ≫ GlobalTheory.LogKS.chart W) (fun i => spMap (Formalism.L2.Pj.dualMap ρW) ≫ v i) cf' w → cf = cf' :=
  fun _ _ _ _ _ _ t W _ _ ρW hinj hfr _ v hv hb cf cf' w h h' =>
    GenUniq.coeff_unique t ρW hinj hfr (GlobalTheory.LogKS.chart W) v hv hb cf cf' w h h'

end GlobalTheory.LogKSDiv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericTangentCoefficientsUniqueAffineOpenBasisStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_tangentCoefficients_unique_affineOpen_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (W : X.affineOpens) (K : Type) [Field K] (ρW : Γ(X, W.1) →+* K), Function.Injective ρW → (∀ x : K, ∃ a b : Γ(X, W.1), ρW b ≠ 0 ∧ x * ρW b = ρW a) → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, W.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (GlobalTheory.LogKS.chart W) (v i)) → (∀ w, IsTanAtG t (GlobalTheory.LogKS.chart W) w → ∃! cf : Fin n → Γ(X, W.1), IsCombAtG t (GlobalTheory.LogKS.chart W) v cf w) → ∀ (cf cf' : Fin n → K) (w : Sp (DualNumber K) ⟶ t.G.left), IsCombAtG t (spMap ρW ≫ GlobalTheory.LogKS.chart W) (fun i => spMap (dualMap ρW) ≫ v i) cf w → IsCombAtG t (spMap ρW ≫ GlobalTheory.LogKS.chart W) (fun i => spMap (dualMap ρW) ≫ v i) cf' w → cf = cf' := by
  first | exact @GlobalTheory.LogKSDiv.generic_coeff_unique | exact GlobalTheory.LogKSDiv.generic_coeff_unique | (intros; apply GlobalTheory.LogKSDiv.generic_coeff_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineOpenToFunctionFieldInjectiveAndFraction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineOpenToFunctionFieldInjectiveAndFraction
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory.GenFrac

theorem injective_and_frac : ∀ (X : Scheme.{0}) (V : X.Opens) [IsIntegral V.toScheme] (W : X.affineOpens), W.1 ≤ V → ∀ (ρW : Γ(X, W.1) →+* V.toScheme.functionField), spMap ρW ≫ GlobalTheory.LogKS.chart W = V.toScheme.fromSpecStalk (genericPoint V.toScheme) ≫ V.ι → Function.Injective ρW ∧ ∀ x : V.toScheme.functionField, ∃ a b : Γ(X, W.1), ρW b ≠ 0 ∧ x * ρW b = ρW a := by
  intro X V _ W hWV ρW h
  set η := genericPoint V.toScheme with hη
  have hx : V.ι η ∈ W.1 := by
    have h1 := congrArg (fun f : Spec (V.toScheme.presheaf.stalk η) ⟶ X =>
      f (IsLocalRing.closedPoint (V.toScheme.presheaf.stalk η))) h
    have h3 : (V.toScheme.fromSpecStalk η ≫ V.ι)
        (IsLocalRing.closedPoint (V.toScheme.presheaf.stalk η)) = V.ι η :=
      congrArg V.ι (Scheme.fromSpecStalk_closedPoint (x := η))
    rw [← h1.trans h3]
    have h2 : Set.range (W.2.fromSpec) = (W.1 : Set X) := W.2.range_fromSpec
    rw [← SetLike.mem_coe, ← h2]
    exact ⟨_, rfl⟩
  have he : CommRingCat.ofHom ρW = X.presheaf.germ W.1 (V.ι η) hx ≫ V.ι.stalkMap η := by
    apply Spec.map_injective
    have hW : IsAffineOpen W.1 := W.2
    haveI : IsOpenImmersion hW.fromSpec := hW.isOpenImmersion_fromSpec
    rw [← cancel_mono hW.fromSpec, Spec.map_comp, Category.assoc]
    refine Eq.trans h ?_
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, ← W.2.fromSpecStalk_eq_fromSpecStalk hx]
    rfl
  have he' : ∀ a, ρW a = V.ι.stalkMap η (X.presheaf.germ W.1 (V.ι η) hx a) := fun a =>
    congrArg (fun f : Γ(X, W.1) ⟶ V.toScheme.presheaf.stalk η => f a) he
  have hbij : Function.Bijective (V.ι.stalkMap η) := ConcreteCategory.bijective_of_isIso _
  refine ⟨?_, fun x => ?_⟩
  · have hiso : IsIso (V.ι.app W.1) := V.ι.isIso_app W.1 (by simpa using hWV)
    have hinj1 : Function.Injective (V.ι.app W.1) := (ConcreteCategory.bijective_of_isIso _).1
    have hinj2 := germ_injective_of_isIntegral V.toScheme (U := V.ι ⁻¹ᵁ W.1) η hx
    intro a b hab
    rw [he', he', Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.germ_stalkMap_apply] at hab
    exact hinj1 (hinj2 hab)
  · obtain ⟨y, rfl⟩ := hbij.2 x
    letI : Algebra Γ(X, W.1) (X.presheaf.stalk (V.ι η)) :=
      (X.presheaf.germ W.1 (V.ι η) hx).hom.toAlgebra
    haveI : IsLocalization.AtPrime (X.presheaf.stalk (V.ι η))
        (W.2.primeIdealOf ⟨V.ι η, hx⟩).asIdeal := W.2.isLocalization_stalk ⟨V.ι η, hx⟩
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj
      (W.2.primeIdealOf ⟨V.ι η, hx⟩).asIdeal.primeCompl y
    have hu := IsLocalization.map_units (X.presheaf.stalk (V.ι η)) b
    refine ⟨a, b, ?_, ?_⟩
    · rw [he']
      exact (hu.map (V.ι.stalkMap η).hom).ne_zero
    · rw [he', he']
      exact (map_mul (V.ι.stalkMap η).hom _ _).symm.trans (congrArg (V.ι.stalkMap η) hab)

end GlobalTheory.GenFrac
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineOpenToFunctionFieldInjectiveAndFractionStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affineOpen_to_functionField_injective_and_fraction : ∀ (X : Scheme.{0}) (V : X.Opens) [IsIntegral V.toScheme] (W : X.affineOpens), W.1 ≤ V → ∀ (ρW : Γ(X, W.1) →+* V.toScheme.functionField), spMap ρW ≫ GlobalTheory.LogKS.chart W = V.toScheme.fromSpecStalk (genericPoint V.toScheme) ≫ V.ι → Function.Injective ρW ∧ ∀ x : V.toScheme.functionField, ∃ a b : Γ(X, W.1), ρW b ≠ 0 ∧ x * ρW b = ρW a := by
  first | exact @GlobalTheory.GenFrac.injective_and_frac | exact GlobalTheory.GenFrac.injective_and_frac | (intros; apply GlobalTheory.GenFrac.injective_and_frac <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransposeMulSymPairMemSpanBalancedTensors
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransposeMulSymPairMemSpanBalancedTensors
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

namespace GlobalTheory.LogKSDiv

theorem blockRow_eq_sum {ι R : Type} [CommRing R] {m : ι → ℕ} {n n' : ℕ} (e : (Σ τ : ι, Fin (m τ)) ≃ Fin n)
    (e' : (Σ τ : ι, Fin (m τ)) ≃ Fin n') (B : Matrix (Fin n) (Fin n') R)
    (hB : ∀ (τ σ : ι) (i : Fin (m τ)) (k : Fin (m σ)), τ ≠ σ → B (e ⟨τ, i⟩) (e' ⟨σ, k⟩) = 0)
    (τ : ι) (i : Fin (m τ)) (c : Fin n') :
    B (e ⟨τ, i⟩) c = ∑ j : Fin (m τ), B (e ⟨τ, i⟩) (e' ⟨τ, j⟩) * (if c = e' ⟨τ, j⟩ then 1 else 0) := by
  obtain ⟨⟨σ, k⟩, rfl⟩ := e'.surjective c
  by_cases h : τ = σ
  · subst h
    rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hj
      rw [if_neg, mul_zero]
      intro h
      exact hj (eq_of_heq (Sigma.mk.inj (e'.injective h)).2).symm
    · simp
  · rw [hB _ _ _ _ h]
    symm
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg, mul_zero]
    intro h'
    exact h (Sigma.mk.inj (e'.injective h')).1.symm

theorem transpose_mul_symm_mul_apply {R : Type} [CommRing R] {n n' : ℕ} (B : Matrix (Fin n) (Fin n') R) (a b : Fin n)
    (c d : Fin n') :
    (_root_.Matrix.transpose B * (Matrix.of fun x y : Fin n =>
      ((if x = a ∧ y = b then 1 else 0) + (if x = b ∧ y = a then 1 else 0) : R)) * B) c d =
      B a c * B b d + B b c * B a d := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, mul_add, Finset.sum_add_distrib, add_mul,
    ite_and, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, ite_mul, zero_mul]

theorem transpose_mul_symPair_mul_mem_span :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (R : Type) [CommRing R] (n n' : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n') (ε' : Fin Dw.dim ≃ GlobalTheory.LogKSDiv.PairIx H Dw) (B : Matrix (Fin n) (Fin n') R), (∀ (τ σ : E →+* ℂ) (i : Fin (Dw.mult τ)) (k : Fin (Dw.mult σ)), τ ≠ σ → B (e ⟨τ, i⟩) (e' ⟨σ, k⟩) = 0) → ∀ P : GlobalTheory.LogKSDiv.PairIx H Dw, ∃ cf : Fin Dw.dim → R, _root_.Matrix.transpose B * GlobalTheory.LogKSDiv.symPair (R := R) e P * B = ∑ k, cf k • GlobalTheory.LogKSDiv.symPair (R := R) e' (ε' k) := by
  intro E _ _ _ H Dw R _ n n' e e' ε' B hB P
  have key : _root_.Matrix.transpose B * symPair (R := R) e P * B =
      ∑ j : Fin (Dw.mult P.1.1), ∑ k : Fin (Dw.mult ((starRingEnd ℂ).comp P.1.1)),
        (B (e ⟨P.1.1, P.2.1⟩) (e' ⟨P.1.1, j⟩) *
          B (e ⟨(starRingEnd ℂ).comp P.1.1, P.2.2⟩) (e' ⟨(starRingEnd ℂ).comp P.1.1, k⟩)) •
          symPair (R := R) e' (⟨P.1, (j, k)⟩ : PairIx H Dw) := by
    ext c d
    unfold symPair
    rw [transpose_mul_symm_mul_apply, blockRow_eq_sum e e' B hB _ _ c, blockRow_eq_sum e e' B hB _ P.2.2 d,
      blockRow_eq_sum e e' B hB _ P.2.2 c, blockRow_eq_sum e e' B hB _ P.2.1 d, mul_comm (Finset.sum _ _) (∑ j : Fin (Dw.mult P.1.1), _ * (if d = _ then _ else _)),
      Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [ite_and]
    split_ifs <;> ring
  have hmem : _root_.Matrix.transpose B * symPair (R := R) e P * B ∈
      Submodule.span R (Set.range fun k => symPair (R := R) e' (ε' k)) := by
    rw [key]
    refine Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span ⟨ε'.symm ⟨P.1, (j, k)⟩, by simp⟩
  obtain ⟨cf, hcf⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hmem
  exact ⟨cf, hcf.symm⟩

end GlobalTheory.LogKSDiv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransposeMulSymPairMemSpanBalancedTensorsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transpose_mul_symPair_mem_span_balancedTensors : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (R : Type) [CommRing R] (n n' : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n') (ε' : Fin Dw.dim ≃ GlobalTheory.LogKSDiv.PairIx H Dw) (B : Matrix (Fin n) (Fin n') R), (∀ (τ σ : E →+* ℂ) (i : Fin (Dw.mult τ)) (k : Fin (Dw.mult σ)), τ ≠ σ → B (e ⟨τ, i⟩) (e' ⟨σ, k⟩) = 0) → ∀ P : GlobalTheory.LogKSDiv.PairIx H Dw, ∃ cf : Fin Dw.dim → R, _root_.Matrix.transpose B * GlobalTheory.LogKSDiv.symPair (R := R) e P * B = ∑ k, cf k • GlobalTheory.LogKSDiv.symPair (R := R) e' (ε' k) := by
  first | exact @GlobalTheory.LogKSDiv.transpose_mul_symPair_mul_mem_span | exact GlobalTheory.LogKSDiv.transpose_mul_symPair_mul_mem_span | (intros; apply GlobalTheory.LogKSDiv.transpose_mul_symPair_mul_mem_span <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointLogKodairaSpencerFrameChange
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory.LogKSDiv.GenChange

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem dualMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    dualMap (g.comp f) = (dualMap g).comp (dualMap f) := by
  ext x <;> simp [dualMap]

theorem chart_res {X : Scheme.{0}} (U W : X.affineOpens) (h : W.1 ≤ U.1) :
    spMap (X.presheaf.map (homOfLE h).op).hom ≫ GlobalTheory.LogKS.chart U = GlobalTheory.LogKS.chart W := by
  simpa [spMap, GlobalTheory.LogKS.chart] using U.2.map_fromSpec W.2 (homOfLE h).op

theorem common_basic {X : Scheme.{0}} (U U' : X.affineOpens) (x : X) (hx : x ∈ U.1) (hx' : x ∈ U'.1) :
    ∃ (W : X.affineOpens) (hW : W.1 ≤ U.1) (hW' : W.1 ≤ U'.1) (f : Γ(X, U.1)) (f' : Γ(X, U'.1)),
      W.1 = X.basicOpen f ∧ W.1 = X.basicOpen f' ∧ x ∈ W.1 := by
  obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter U.2 U'.2 x ⟨hx, hx'⟩
  exact ⟨X.affineBasicOpen f, X.basicOpen_le f, (show X.basicOpen f ≤ U'.1 from hfg ▸ X.basicOpen_le g), f, g, rfl,
    hfg, hxf⟩

theorem exists_rho {X : Scheme.{0}} (W : X.affineOpens) {K : Type} [Field K] (y : Sp K ⟶ X)
    (hy : ∃ z, y z ∈ W.1) : ∃ ρW : Γ(X, W.1) →+* K, spMap ρW ≫ GlobalTheory.LogKS.chart W = y := by
  have hr : Set.range y ⊆ Set.range (GlobalTheory.LogKS.chart W) := by
    rw [GlobalTheory.LogKS.chart, W.2.range_fromSpec]
    rintro _ ⟨z', rfl⟩
    obtain ⟨z, hz⟩ := hy
    have : z' = z := Subsingleton.elim _ _
    exact this ▸ hz
  have : IsOpenImmersion (GlobalTheory.LogKS.chart W) := W.2.isOpenImmersion_fromSpec
  refine ⟨(Spec.preimage (IsOpenImmersion.lift (GlobalTheory.LogKS.chart W) y hr)).hom, ?_⟩
  simp only [spMap, CommRingCat.ofHom_hom, Spec.map_preimage]
  exact IsOpenImmersion.lift_fac _ _ _

theorem rho_fac {X : Scheme.{0}} (U W : X.affineOpens) (h : W.1 ≤ U.1) {K : Type} [CommRing K]
    (ρ : Γ(X, U.1) →+* K) (ρW : Γ(X, W.1) →+* K)
    (hρ : spMap ρ ≫ GlobalTheory.LogKS.chart U = spMap ρW ≫ GlobalTheory.LogKS.chart W) :
    ρ = ρW.comp (X.presheaf.map (homOfLE h).op).hom := by
  have : IsOpenImmersion (GlobalTheory.LogKS.chart U) := U.2.isOpenImmersion_fromSpec
  rw [← chart_res U W h, ← Category.assoc, ← spMap_comp'] at hρ
  have h2 := Spec.map_inj.1 ((cancel_mono (GlobalTheory.LogKS.chart U)).1 hρ)
  simpa using congrArg CommRingCat.Hom.hom h2

theorem basic_loc {X : Scheme.{0}} (U W : X.affineOpens) (hW : W.1 ≤ U.1) (f : Γ(X, U.1))
    (hf : W.1 = X.basicOpen f) :
    IsUnit ((X.presheaf.map (homOfLE hW).op).hom f) ∧
    ∀ r' : Γ(X, W.1), ∃ (r : Γ(X, U.1)) (m : ℕ),
      r' * (X.presheaf.map (homOfLE hW).op).hom f ^ m = (X.presheaf.map (homOfLE hW).op).hom r := by
  obtain ⟨W, hWa⟩ := W
  simp only at hf hW ⊢
  subst hf
  letI := (X.presheaf.map (homOfLE hW).op).hom.toAlgebra
  have : IsLocalization.Away f Γ(X, X.basicOpen f) := U.2.isLocalization_basicOpen f
  refine ⟨IsLocalization.Away.algebraMap_isUnit f, fun r' => ?_⟩
  obtain ⟨m, r, h⟩ := IsLocalization.Away.surj f r'
  exact ⟨r, m, h⟩

theorem der_through {k K R RW : Type} [CommRing k] [Field K] [Algebra k K] [CommRing R] [CommRing RW]
    (res : R →+* RW) (ρW : RW →+* K) (f : R) (hf : IsUnit (res f))
    (hloc : ∀ r' : RW, ∃ (r : R) (m : ℕ), r' * res f ^ m = res r)
    (Dl : Derivation ℤ R R) (DlW : Derivation ℤ RW RW) (hc : ∀ r, DlW (res r) = res (Dl r))
    (D : Derivation k K K) (hD : ∀ r, D (ρW (res r)) = ρW (res (Dl r))) :
    ∀ r', D (ρW r') = ρW (DlW r') := by
  have hδmul : ∀ x y, D (ρW (x * y)) - ρW (DlW (x * y)) =
      ρW x * (D (ρW y) - ρW (DlW y)) + ρW y * (D (ρW x) - ρW (DlW x)) := by
    intro x y
    rw [map_mul, Derivation.leibniz, Derivation.leibniz, map_add (f := _), smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      map_mul, map_mul]
    ring
  have hδres : ∀ r, D (ρW (res r)) - ρW (DlW (res r)) = 0 := fun r => by rw [hD, hc, sub_self]
  have hpow : ∀ m : ℕ, D (ρW (res f ^ m)) - ρW (DlW (res f ^ m)) = 0 := fun m => by
    rw [← map_pow]; exact hδres _
  intro r'
  obtain ⟨r, m, h⟩ := hloc r'
  have := hδmul r' (res f ^ m)
  rw [h, hδres, hpow, mul_zero, zero_add] at this
  have hu : ρW (res f ^ m) ≠ 0 := ((hf.pow m).map ρW).ne_zero
  exact sub_eq_zero.1 ((mul_eq_zero.1 this.symm).resolve_left hu)

theorem der_ext_frac {k K R : Type} [CommRing k] [Field K] [Algebra k K] [CommRing R] (ρ : R →+* K)
    (hfr : ∀ x : K, ∃ a b : R, ρ b ≠ 0 ∧ x * ρ b = ρ a) (D₁ D₂ : Derivation k K K)
    (h : ∀ r, D₁ (ρ r) = D₂ (ρ r)) : D₁ = D₂ := by
  ext x
  obtain ⟨a, b, hb, hx⟩ := hfr x
  have h1 := congrArg D₁ hx
  have h2 := congrArg D₂ hx
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul] at h1 h2
  rw [← h a, ← h b] at h2
  exact mul_left_cancel₀ hb (by linear_combination h1 - h2)

theorem map_symPair {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {n : ℕ}
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (P : GlobalTheory.LogKSDiv.PairIx H Dw) :
    (GlobalTheory.LogKSDiv.symPair (R := R) e P).map φ = GlobalTheory.LogKSDiv.symPair (R := S) e P := by
  ext a b
  simp only [Matrix.map_apply, GlobalTheory.LogKSDiv.symPair, Matrix.of_apply]
  split_ifs <;> simp

theorem der_sum_apply {k A M ι : Type} [CommRing k] [CommRing A] [Algebra k A] [AddCommGroup M] [Module A M]
    [Module k M] [IsScalarTower k A M] (s : Finset ι) (d : ι → Derivation k A M) (x : A) :
    (∑ i ∈ s, d i) x = ∑ i ∈ s, d i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]

end GlobalTheory.LogKSDiv.GenChange

namespace GlobalTheory.LogKSDiv.GenChange

set_option maxHeartbeats 800000 in
theorem genKS_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → FnAlgClosed (Xo := Xo) (c := c) → ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)], ∀ (w w' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber (X₀ TF.Y Z).functionField) ⟶ TF.Y.t.G.left)) (D D' : Fin Dw.dim → GlobalTheory.LogKSDiv.GenDer TF Z) (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (X₀ TF.Y Z).functionField), GlobalTheory.LogKSDiv.GenKS TF Z w D → GlobalTheory.LogKSDiv.GenKS TF Z w' D' → (∀ τ i, IsCombAtG TF.Y.t ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι) (w' τ) (A τ i) (w τ i)) →
    ∃ (n n' : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n')
      (ε ε' : Fin Dw.dim ≃ GlobalTheory.LogKSDiv.PairIx H Dw) (L : Matrix (Fin Dw.dim) (Fin Dw.dim) (X₀ TF.Y Z).functionField),
      (∀ j, _root_.Matrix.transpose (GlobalTheory.LogKSDiv.flatFrame A e e') * GlobalTheory.LogKSDiv.symPair (R := (X₀ TF.Y Z).functionField) e (ε j) * GlobalTheory.LogKSDiv.flatFrame A e e' =
        ∑ k, L k j • GlobalTheory.LogKSDiv.symPair (R := (X₀ TF.Y Z).functionField) e' (ε' k)) ∧
      (letI := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra; ∀ j, D j = ∑ k, L k j • D' k) := by
  intro E _ _ _ H Dw l Xo c TF Z hpq hFA _ _ w w' D D' A hG hG' hA
  letI := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra
  obtain ⟨U, hU, ρ, n, e, v, ε, Dl, hρ, hvT, hvB, hw, hKS, hD⟩ := hG
  obtain ⟨U', hU', ρ', n', e', v', ε', Dl', hρ', hvT', hvB', hw', hKS', hD'⟩ := hG'
  have hin : ∀ (U₀ : TF.Y.X.affineOpens) (ρ₀ : Γ(TF.Y.X, U₀.1) →+* (X₀ TF.Y Z).functionField)
      (_ : spMap ρ₀ ≫ GlobalTheory.LogKS.chart U₀ = genPt TF Z ≫ (barComp TF.Y Z).ι) (z : Sp (X₀ TF.Y Z).functionField),
      (genPt TF Z ≫ (barComp TF.Y Z).ι) z ∈ U₀.1 := by
    intro U₀ ρ₀ h z
    rw [← h, Scheme.Hom.comp_apply, GlobalTheory.LogKS.chart]
    show _ ∈ (U₀.1 : Set TF.Y.X)
    rw [← U₀.2.range_fromSpec]
    exact ⟨_, rfl⟩
  let z0 : Sp (X₀ TF.Y Z).functionField := IsLocalRing.closedPoint _
  obtain ⟨W, hWU, hWU', f, f', hWf, hWf', hxW⟩ :=
    common_basic U U' ((genPt TF Z ≫ (barComp TF.Y Z).ι) z0) (hin U ρ hρ z0) (hin U' ρ' hρ' z0)
  obtain ⟨ρW, hρW⟩ := exists_rho W (genPt TF Z ≫ (barComp TF.Y Z).ι) ⟨z0, hxW⟩
  have hfacU : ρ = ρW.comp (TF.Y.X.presheaf.map (homOfLE hWU).op).hom := rho_fac U W hWU ρ ρW (hρ.trans hρW.symm)
  have hfacU' : ρ' = ρW.comp (TF.Y.X.presheaf.map (homOfLE hWU').op).hom :=
    rho_fac U' W hWU' ρ' ρW (hρ'.trans hρW.symm)
  obtain ⟨hinj, hfr⟩ := GlobalTheory.T.affineOpen_to_functionField_injective_and_fraction TF.Y.X (barComp TF.Y Z) W (hWU.trans hU) ρW hρW
  have hcr := chart_res U W hWU
  have hcr' := chart_res U' W hWU'
  obtain ⟨hfu, hfloc⟩ := basic_loc U W hWU f hWf
  obtain ⟨hfu', hfloc'⟩ := basic_loc U' W hWU' f' hWf'
  have hv'WB := GlobalTheory.T.tangentBasis_affineOpen_restrict_basicOpen E H TF.Y.X TF.Y.t U' W hWU' f' hWf' n' v' hvT' hvB'
  choose DlW hDlW hDlWc using fun j => GlobalTheory.T.exists_logDerivation_extension_basicOpen TF.Y.X c.F TF.Y.s
    (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U W hWU f hWf (Dl j).1 (Dl j).2
  choose Dl'W hDl'W hDl'Wc using fun k => GlobalTheory.T.exists_logDerivation_extension_basicOpen TF.Y.X c.F TF.Y.s
    (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U' W hWU' f' hWf' (Dl' k).1 (Dl' k).2
  have hKS0 := fun j => GlobalTheory.T.kodairaSpencer_condition_restrict_basicOpen_of_affine E H TF.Y.X TF.Y.t (LogKS.interior TF.Y) U W hWU f hWf n v (Dl j).1 (DlW j)
    (symPair e (ε j)) (hDlWc j) (hKS j)
  have hKS0' := fun k => GlobalTheory.T.kodairaSpencer_condition_restrict_basicOpen_of_affine E H TF.Y.X TF.Y.t (LogKS.interior TF.Y) U' W hWU' f' hWf' n' v' (Dl' k).1 (Dl'W k)
    (symPair e' (ε' k)) (hDl'Wc k) (hKS' k)
  simp only [RingHom.mapMatrix_apply, map_symPair] at hKS0 hKS0'
  generalize (TF.Y.X.presheaf.map (homOfLE hWU).op).hom = resU at hfacU hcr hfu hfloc hDlWc hKS0
  generalize (TF.Y.X.presheaf.map (homOfLE hWU').op).hom = resU' at hfacU' hcr' hfu' hfloc' hv'WB hDl'Wc hKS0'
  let vW : Fin n → (Sp (DualNumber Γ(TF.Y.X, W.1)) ⟶ TF.Y.t.G.left) := fun a => spMap (dualMap resU) ≫ v a
  let v'W : Fin n' → (Sp (DualNumber Γ(TF.Y.X, W.1)) ⟶ TF.Y.t.G.left) := fun c => spMap (dualMap resU') ≫ v' c
  have hbc := GlobalTheory.T.tangent_combination_preserved_by_baseChange E H TF.Y.X TF.Y.t _ _ resU (GlobalTheory.LogKS.chart U) (GlobalTheory.LogKS.chart W) hcr
  have hbc' := GlobalTheory.T.tangent_combination_preserved_by_baseChange E H TF.Y.X TF.Y.t _ _ resU' (GlobalTheory.LogKS.chart U') (GlobalTheory.LogKS.chart W) hcr'
  have hvWT : ∀ a, IsTanAtG TF.Y.t (GlobalTheory.LogKS.chart W) (vW a) := fun a => hbc.1 _ (hvT a)
  have hv'WT : ∀ c, IsTanAtG TF.Y.t (GlobalTheory.LogKS.chart W) (v'W c) := fun c => hbc'.1 _ (hvT' c)
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin n) (Fin n') Γ(TF.Y.X, W.1),
      ∀ a, IsCombAtG TF.Y.t (GlobalTheory.LogKS.chart W) v'W (B a) (vW a) :=
    ⟨fun a => (hv'WB (vW a) (hvWT a)).exists.choose, fun a => (hv'WB (vW a) (hvWT a)).exists.choose_spec⟩
  have htan' : ∀ τ k, IsTanAtG TF.Y.t (spMap ρW ≫ GlobalTheory.LogKS.chart W) (w' τ k) := by
    intro τ k
    rw [hw']
    exact (GlobalTheory.T.tangent_combination_preserved_by_baseChange E H TF.Y.X TF.Y.t _ _ ρ' (GlobalTheory.LogKS.chart U') (spMap ρW ≫ GlobalTheory.LogKS.chart W)
      (hρ'.trans hρW.symm)).1 _ (hvT' _)
  have hgen : ∀ τ i c, ρW (B (e ⟨τ, i⟩) c) = flatFrame A e e' (e ⟨τ, i⟩) c := by
    intro τ i
    have h1 := (GlobalTheory.T.tangent_combination_preserved_by_baseChange E H TF.Y.X TF.Y.t _ _ ρW (GlobalTheory.LogKS.chart W) (spMap ρW ≫ GlobalTheory.LogKS.chart W) rfl).2 _ v'W
      (B (e ⟨τ, i⟩)) (vW (e ⟨τ, i⟩)) (hB (e ⟨τ, i⟩))
    have hvw : spMap (dualMap ρW) ≫ vW (e ⟨τ, i⟩) = w τ i := by
      rw [hw, hfacU, dualMap_comp', spMap_comp', Category.assoc]
    have hv'w : (fun c => spMap (dualMap ρW) ≫ v'W c) = fun c => w' (e'.symm c).1 (e'.symm c).2 := by
      funext c
      rw [hw', Sigma.eta, Equiv.apply_symm_apply, hfacU', dualMap_comp', spMap_comp', Category.assoc]
    rw [hvw, hv'w] at h1
    have h2 := GlobalTheory.T.isCombAtZeroSection_eigenBlock_flattened_frame E H Dw TF.Y.X TF.Y.t _ (spMap ρW ≫ GlobalTheory.LogKS.chart W) n n' e e' w' A τ i (w τ i) htan'
      (by rw [hρW]; exact hA τ i)
    have h3 := GlobalTheory.T.generic_tangentCoefficients_unique_affineOpen_basis E H TF.Y.X TF.Y.t W _ ρW hinj hfr n' v'W hv'WT hv'WB _ _ (w τ i) (hv'w ▸ h1) (hv'w ▸ h2)
    exact fun c => congrFun h3 c

  have hρB : ∀ a c, ρW (B a c) = flatFrame A e e' a c := by
    intro a c
    obtain ⟨⟨τ, i⟩, rfl⟩ := e.surjective a
    exact hgen τ i c
  have hBmap : B.map ρW = flatFrame A e e' := by
    ext a c; exact hρB a c
  have hBd : ∀ (τ σ : E →+* ℂ) (i : Fin (Dw.mult τ)) (k : Fin (Dw.mult σ)), τ ≠ σ → B (e ⟨τ, i⟩) (e' ⟨σ, k⟩) = 0 := by
    intro τ σ i k hne
    apply hinj
    rw [hρB, map_zero]
    simp [flatFrame, Matrix.blockDiagonal'_apply, hne]
  choose cfs hcfs using fun j => GlobalTheory.T.transpose_mul_symPair_mem_span_balancedTensors E H Dw _ n n' e e' ε' B hBd (ε j)
  let LW : Matrix (Fin Dw.dim) (Fin Dw.dim) Γ(TF.Y.X, W.1) := Matrix.of fun k j => cfs j k
  have hKSW := fun j =>
    GlobalTheory.T.kodairaSpencer_change_of_tangent_frame E H TF.Y.X TF.Y.t (LogKS.interior TF.Y) W n n' vW v'W B (DlW j) _ hvWT hv'WT hB (hKS0 j)
  obtain ⟨Aact, hAact⟩ := GlobalTheory.T.existsUnique_cmOrderActionMatrix_on_affineOpen E H TF.Y.X TF.Y.t W n' v'W hv'WT hv'WB
  obtain ⟨eW, heW⟩ := TF.logKS W n' v'W Aact hv'WT hv'WB hAact
  have hrel : ∀ j, DlW j = ∑ k, LW k j • Dl'W k := by
    intro j
    have h1 := (heW ⟨DlW j, hDlW j⟩ _).1 (hKSW j)
    have h2 := fun k => (heW ⟨Dl'W k, hDl'W k⟩ _).1 (hKS0' k)
    have h3 : eW ⟨DlW j, hDlW j⟩ = eW (∑ k, LW k j • (⟨Dl'W k, hDl'W k⟩ : LogKS.logDer TF.Y.s
        (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) W)) := by
      apply Subtype.ext
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← h1, map_sum, Submodule.coe_sum, hcfs j]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, Submodule.coe_smul, ← h2 k]
      rfl
    have := congrArg Subtype.val (eW.injective h3)
    simpa [Submodule.coe_sum] using this
  have hDW : ∀ j r, D j (ρW r) = ρW (DlW j r) := fun j =>
    der_through resU ρW f hfu hfloc (Dl j).1 (DlW j) (hDlWc j) (D j) (fun r => by
      have := hD j r; rw [hfacU] at this; exact this)
  have hD'W : ∀ k r, D' k (ρW r) = ρW (Dl'W k r) := fun k =>
    der_through resU' ρW f' hfu' hfloc' (Dl' k).1 (Dl'W k) (hDl'Wc k) (D' k) (fun r => by
      have := hD' k r; rw [hfacU'] at this; exact this)
  refine ⟨n, n', e, e', ε, ε', Matrix.of fun k j => ρW (cfs j k), fun j => ?_, fun j => ?_⟩
  · have h := congrArg (fun M => Matrix.map M ρW) (hcfs j)
    simp only [Matrix.map_mul, Matrix.transpose_map, hBmap, map_symPair] at h
    rw [h]
    ext a b
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, map_sum, map_mul, Matrix.of_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← map_symPair ρW e' (ε' k)]
    rfl
  · apply der_ext_frac ρW hfr
    intro r
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hDW j r, hrel j, der_sum_apply, der_sum_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Derivation.smul_apply, Derivation.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, hD'W]
    rfl

end GlobalTheory.LogKSDiv.GenChange
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointLogKodairaSpencerFrameChangeStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericPoint_logKodairaSpencer_frame_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → FnAlgClosed (Xo := Xo) (c := c) → ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)], ∀ (w w' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber (X₀ TF.Y Z).functionField) ⟶ TF.Y.t.G.left)) (D D' : Fin Dw.dim → GlobalTheory.LogKSDiv.GenDer TF Z) (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (X₀ TF.Y Z).functionField), GlobalTheory.LogKSDiv.GenKS TF Z w D → GlobalTheory.LogKSDiv.GenKS TF Z w' D' → (∀ τ i, IsCombAtG TF.Y.t ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι) (w' τ) (A τ i) (w τ i)) →
    ∃ (n n' : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n')
      (ε ε' : Fin Dw.dim ≃ GlobalTheory.LogKSDiv.PairIx H Dw) (L : Matrix (Fin Dw.dim) (Fin Dw.dim) (X₀ TF.Y Z).functionField),
      (∀ j, _root_.Matrix.transpose (GlobalTheory.LogKSDiv.flatFrame A e e') * GlobalTheory.LogKSDiv.symPair (R := (X₀ TF.Y Z).functionField) e (ε j) * GlobalTheory.LogKSDiv.flatFrame A e e' =
        ∑ k, L k j • GlobalTheory.LogKSDiv.symPair (R := (X₀ TF.Y Z).functionField) e' (ε' k)) ∧
      (letI := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra; ∀ j, D j = ∑ k, L k j • D' k) := by
  first | exact @GlobalTheory.LogKSDiv.GenChange.genKS_change | exact GlobalTheory.LogKSDiv.GenChange.genKS_change | (intros; apply GlobalTheory.LogKSDiv.GenChange.genKS_change <;> assumption)
end

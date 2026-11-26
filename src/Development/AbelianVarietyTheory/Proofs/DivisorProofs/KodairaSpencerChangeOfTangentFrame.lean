module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SndSectionValueTranslateProdFirstOrderLinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentFlagHodgeIndexVanishing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDualOfIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingEqOneTrivialOnAxis
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCompletedLatticeConjugateHalfIffDual
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsEmptyOfNotAll
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodRowCuspParam

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerChangeOfTangentFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateTangentCombinationEqProd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateTangentCombinationEqProd
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
attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory CartesianMonoidalCategory MonObj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogKSDiv

def precompHom {C : Type*} [Category C] [CartesianMonoidalCategory C] {M P Q : C} [MonObj M] (f : P ⟶ Q) :
    (Q ⟶ M) →* (P ⟶ M) where
  toFun := fun g => f ≫ g
  map_one' := MonObj.comp_one f
  map_mul' := fun g₁ g₂ => MonObj.comp_mul f g₁ g₂

theorem comp_list_prod {C : Type*} [Category C] [CartesianMonoidalCategory C] {M P Q : C} [MonObj M]
    (f : P ⟶ Q) {m : ℕ} (u : Fin m → (Q ⟶ M)) :
    f ≫ (List.ofFn u).prod = (List.ofFn fun c => f ≫ u c).prod := by
  have h := map_list_prod (precompHom (M := M) f) (List.ofFn u)
  rw [List.map_ofFn] at h
  exact h

theorem translate_comb : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
    (t : SAB H X) (U : X.affineOpens) {m : ℕ} (v' : Fin m → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left))
    (cf : Fin m → Γ(X, U.1)) (va : Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left) {S : Type} [CommRing S]
    (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ GlobalTheory.LogKS.chart U →
    ∀ (g' : overAt (g₀ ≫ t.G.hom) (DualNumber S) ⟶ t.G) (y : Fin m → (overAt (g₀ ≫ t.G.hom) (DualNumber S) ⟶ t.G)),
    (∀ c, IsTanAtG t (GlobalTheory.LogKS.chart U) (v' c)) → IsCombAtG t (GlobalTheory.LogKS.chart U) v' cf va →
    g'.left = spMap (algebraMap S (DualNumber S)) ≫ g₀ → (∀ c, (y c).left = spMap (dualMap φ) ≫ v' c) →
    (∀ c, smT (g₀ ≫ t.G.hom) 0 (y c) = 1) ∧
      ∀ w, GlobalTheory.LogKS.IsTranslate t φ g₀ va w →
        w = (g' * (List.ofFn fun c => smT (g₀ ≫ t.G.hom) (φ (cf c)) (y c)).prod).left := by
  intro E _ _ _ H X t U m v' cf va S _ φ g₀ hg g' y hTan hComb hg' hy
  have hr0 : (epsMul (0 : S)).comp (dualMap φ) =
      ((algebraMap S (DualNumber S)).comp φ).comp (TrivSqZeroExt.fstHom Γ(X, U.1) Γ(X, U.1) Γ(X, U.1)).toRingHom := by
    apply RingHom.ext
    intro r
    ext <;> simp [epsMul, dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have hra : (dualMap φ).comp (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))) =
      (algebraMap S (DualNumber S)).comp φ := by
    apply RingHom.ext
    intro r
    ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  refine ⟨fun c => ?_, fun w hw => ?_⟩
  · let gA : overAt (g₀ ≫ t.G.hom) (DualNumber S) ⟶ Over.mk (GlobalTheory.LogKS.chart U) :=
      Over.homMk (spMap ((algebraMap S (DualNumber S)).comp φ)) (by
        show spMap _ ≫ GlobalTheory.LogKS.chart U = spMap (algebraMap S (DualNumber S)) ≫ g₀ ≫ t.G.hom
        rw [hg, spMap_comp, Category.assoc])
    have h1 : gA ≫ (1 : Over.mk (GlobalTheory.LogKS.chart U) ⟶ t.G) = 1 := MonObj.comp_one gA
    apply Over.OverMorphism.ext
    rw [← h1, smT_left, Over.comp_left, hy c, ← (hTan c).2]
    simp only [gA, Over.homMk_left]
    rw [← Category.assoc, spMap_comp', hr0, spMap_comp, Category.assoc]
  · obtain ⟨g'', V, h1, h2, h3⟩ := hw
    obtain ⟨u, hu, hprod⟩ := hComb
    have hg'' : g'' = g' := Over.OverMorphism.ext (h1.trans hg'.symm)
    let bA : overAt (g₀ ≫ t.G.hom) (DualNumber S) ⟶ tEpsG (GlobalTheory.LogKS.chart U) :=
      Over.homMk (spMap (dualMap φ)) (by
        show spMap (dualMap φ) ≫ spMap (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))) ≫ GlobalTheory.LogKS.chart U =
          spMap (algebraMap S (DualNumber S)) ≫ g₀ ≫ t.G.hom
        rw [hg, ← Category.assoc, spMap_comp', hra, spMap_comp, Category.assoc])
    have hV : V = bA ≫ (List.ofFn u).prod := by
      apply Over.OverMorphism.ext
      rw [h2, Over.comp_left, hprod]
      rfl
    have hbAu : ∀ c, bA ≫ u c = smT (g₀ ≫ t.G.hom) (φ (cf c)) (y c) := by
      intro c
      apply Over.OverMorphism.ext
      rw [Over.comp_left, hu c, smT_left, hy c]
      simp only [bA, Over.homMk_left]
      rw [← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', Formalism.L2.Pj.dualMap_comp_epsMul]
    rw [← h3, hg'', hV, comp_list_prod]
    simp only [hbAu]

end GlobalTheory.LogKSDiv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateTangentCombinationEqProdStatement
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
attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory CartesianMonoidalCategory MonObj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translate_tangent_combination_eq_prod : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
    (t : SAB H X) (U : X.affineOpens) {m : ℕ} (v' : Fin m → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left))
    (cf : Fin m → Γ(X, U.1)) (va : Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left) {S : Type} [CommRing S]
    (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ GlobalTheory.LogKS.chart U →
    ∀ (g' : overAt (g₀ ≫ t.G.hom) (DualNumber S) ⟶ t.G) (y : Fin m → (overAt (g₀ ≫ t.G.hom) (DualNumber S) ⟶ t.G)),
    (∀ c, IsTanAtG t (GlobalTheory.LogKS.chart U) (v' c)) → IsCombAtG t (GlobalTheory.LogKS.chart U) v' cf va →
    g'.left = spMap (algebraMap S (DualNumber S)) ≫ g₀ → (∀ c, (y c).left = spMap (dualMap φ) ≫ v' c) →
    (∀ c, smT (g₀ ≫ t.G.hom) 0 (y c) = 1) ∧
      ∀ w, GlobalTheory.LogKS.IsTranslate t φ g₀ va w →
        w = (g' * (List.ofFn fun c => smT (g₀ ≫ t.G.hom) (φ (cf c)) (y c)).prod).left := by
  first | exact @GlobalTheory.LogKSDiv.translate_comb | exact GlobalTheory.LogKSDiv.translate_comb | (intros; apply GlobalTheory.LogKSDiv.translate_comb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerChangeOfTangentFrame
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

attribute [local instance] Over.cartesianMonoidalCategory

open MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.KSFrameChange

theorem sum_four_comm {R : Type} [AddCommMonoid R] {ι₁ ι₂ ι₃ ι₄ : Type} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    [Fintype ι₄] (F : ι₁ → ι₂ → ι₃ → ι₄ → R) :
    ∑ a, ∑ b, ∑ x, ∑ y, F a b x y = ∑ y, ∑ x, ∑ b, ∑ a, F a b x y :=
  calc ∑ a, ∑ b, ∑ x, ∑ y, F a b x y = ∑ a, ∑ b, ∑ y, ∑ x, F a b x y :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a, ∑ y, ∑ b, ∑ x, F a b x y := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ y, ∑ a, ∑ b, ∑ x, F a b x y := Finset.sum_comm
    _ = ∑ y, ∑ a, ∑ x, ∑ b, F a b x y :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ y, ∑ x, ∑ a, ∑ b, F a b x y := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ y, ∑ x, ∑ b, ∑ a, F a b x y :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem sum_four_comm' {R : Type} [AddCommMonoid R] {ι₁ ι₂ ι₃ ι₄ : Type} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    [Fintype ι₄] (F : ι₁ → ι₂ → ι₃ → ι₄ → R) :
    ∑ a, ∑ b, ∑ x, ∑ y, F a b x y = ∑ x, ∑ y, ∑ b, ∑ a, F a b x y :=
  (sum_four_comm F).trans Finset.sum_comm

theorem isKS_frame_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X)
    (V : X.Opens) (U : X.affineOpens) (n n' : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left))
    (v' : Fin n' → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (B : Matrix (Fin n) (Fin n') Γ(X, U.1))
    (D : Γ(X, U.1) → Γ(X, U.1)) (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1)),
    (∀ a, IsTanAtG t (GlobalTheory.LogKS.chart U) (v a)) → (∀ c, IsTanAtG t (GlobalTheory.LogKS.chart U) (v' c)) →
    (∀ a, IsCombAtG t (GlobalTheory.LogKS.chart U) v' (B a) (v a)) → GlobalTheory.LogKS.IsKS t V U v D Θ →
    GlobalTheory.LogKS.IsKS t V U v' D (_root_.Matrix.transpose B * Θ * B) := by
  intro E _ _ _ H X t V U n n' v v' B D Θ hv hv' hB hKS
  obtain ⟨J, W, j, d, hcov, hWL, hF, hD, hc⟩ := hKS
  refine ⟨J, W, j, d, hcov, hWL, hF, hD, ?_⟩
  intro i i' O hO f S _ φ g₀ w' hg hgO htr'
  choose w hw using fun a => (GlobalTheory.LogKS.existsUnique_isTranslate t φ hg (hv a)).exists
  rw [hc i i' O hO f S φ g₀ w hg hgO hw]
  let g' : overAt (g₀ ≫ t.G.hom) (DualNumber S) ⟶ t.G :=
    Over.homMk (spMap (algebraMap S (DualNumber S)) ≫ g₀) (Category.assoc _ _ _)
  choose gc yc hgc hyc hwc using htr'
  have hgc' : ∀ c, gc c = g' := fun c => Over.OverMorphism.ext (hgc c)
  have key : ∀ a (O' : t.G.left.Opens) (f' : Γ(t.G.left, O')), ⊤ ≤ g₀ ⁻¹ᵁ O' →
      (valR (w a) O' f').snd = ∑ c, φ (B a c) * (valR (w' c) O' f').snd := by
    intro a O' f' hO'
    obtain ⟨h0, hw'⟩ := GlobalTheory.T.translate_tangent_combination_eq_prod t U v' (B a) (v a) φ g₀ hg g' yc hv' (hB a) rfl hyc
    rw [hw' (w a) (hw a), GlobalTheory.T.snd_sectionValue_translate_prod_first_order_linear (g₀ ≫ t.G.hom) t.G g₀ g' rfl yc (fun c => φ (B a c)) h0 O' f' hO']
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← hwc c, hgc' c]
  simp_rw [key _ O f hgO]
  have hO2 : ⊤ ≤ g₀ ⁻¹ᵁ (t.PP.L.U (j i) ⊓ t.PP.L.U (j i')) :=
    hgO.trans (fun x hx => (hO.trans (inf_le_inf (hWL i) (hWL i'))) hx)
  simp_rw [key _ _ _ hO2]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, Matrix.transpose_apply, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [sum_four_comm']
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.KSFrameChange
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerChangeOfTangentFrameStatement
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
theorem _root_.GlobalTheory.T.kodairaSpencer_change_of_tangent_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X)
    (V : X.Opens) (U : X.affineOpens) (n n' : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left))
    (v' : Fin n' → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (B : Matrix (Fin n) (Fin n') Γ(X, U.1))
    (D : Γ(X, U.1) → Γ(X, U.1)) (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1)),
    (∀ a, IsTanAtG t (GlobalTheory.LogKS.chart U) (v a)) → (∀ c, IsTanAtG t (GlobalTheory.LogKS.chart U) (v' c)) →
    (∀ a, IsCombAtG t (GlobalTheory.LogKS.chart U) v' (B a) (v a)) → GlobalTheory.LogKS.IsKS t V U v D Θ →
    GlobalTheory.LogKS.IsKS t V U v' D (_root_.Matrix.transpose B * Θ * B) := by
  first | exact @GlobalTheory.KSFrameChange.isKS_frame_change | exact GlobalTheory.KSFrameChange.isKS_frame_change | (intros; apply GlobalTheory.KSFrameChange.isKS_frame_change <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversalFirstOrderDeformation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModuliPointTrivSqZeroExtTangentBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModuliPointTrivSqZeroExtTangentBasis
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TanBasis

open TensorProduct

theorem exists_tan_basis {R A K ι : Type} [CommRing R] [CommRing A] [Algebra R A] [Field K] [Fintype ι] {n : ℕ}
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap R A))
    (xr : A →+* K) (hι : Fintype.card ι = n) :
    ∃ Φ : A →+* TrivSqZeroExt K (ι → K), (∀ a, (Φ a).fst = xr a) ∧ (∀ r, (Φ (algebraMap R A r)).snd = 0) ∧
      ∀ M M' : ι → K, (∀ a, ∑ k, (Φ a).snd k * M k = ∑ k, (Φ a).snd k * M' k) → M = M' := by
  classical
  haveI := GlobalTheory.AugCot.smooth_of_locally h
  letI : Algebra A K := xr.toAlgebra
  have hrank : Module.finrank K (K ⊗[A] Ω[A⁄R]) = n := by
    have h1 := Module.rankAtStalk_baseChange (R := A) (M := Ω[A⁄R]) (S := K) (IsLocalRing.closedPoint K)
    rw [Module.rankAtStalk_eq_finrank_of_free, GlobalTheory.AugCot.rankAtStalk_kaehler_of_locally h] at h1
    exact_mod_cast h1
  let b : Module.Basis ι K (K ⊗[A] Ω[A⁄R]) :=
    (Module.finBasisOfFinrankEq K _ hrank).reindex (Fintype.equivFinOfCardEq hι).symm
  let δ : A → (ι → K) := fun a => b.equivFun (1 ⊗ₜ KaehlerDifferential.D R A a)
  have hsm : ∀ (a : A) (m : Ω[A⁄R]), (1 : K) ⊗ₜ[A] (a • m) = xr a • ((1 : K) ⊗ₜ[A] m) := by
    intro a m
    rw [TensorProduct.tmul_smul, ← algebraMap_smul K a]
    rfl
  have hδmul : ∀ a a', δ (a * a') = xr a • δ a' + xr a' • δ a := by
    intro a a'
    simp only [δ, Derivation.leibniz, TensorProduct.tmul_add, hsm, map_add (f := _), map_smul]
  have hδadd : ∀ a a', δ (a + a') = δ a + δ a' := by
    intro a a'; simp only [δ, map_add (f := _), TensorProduct.tmul_add]
  have hδalg : ∀ r, δ (algebraMap R A r) = 0 := by
    intro r; simp only [δ, Derivation.map_algebraMap, TensorProduct.tmul_zero, map_zero]
  have hδ1 : δ 1 = 0 := by simpa using hδalg 1
  have hδ0 : δ 0 = 0 := by simp only [δ, map_zero, TensorProduct.tmul_zero]
  let Φ : A →+* TrivSqZeroExt K (ι → K) :=
    { toFun := fun a => TrivSqZeroExt.inl (xr a) + TrivSqZeroExt.inr (δ a)
      map_one' := by ext <;> simp [hδ1]
      map_mul' := fun a a' => by
        ext k
        · simp
        · simp [hδmul, TrivSqZeroExt.snd_mul, add_comm]
      map_zero' := by ext <;> simp [hδ0]
      map_add' := fun a a' => by ext <;> simp [hδadd] }
  refine ⟨Φ, fun a => by simp [Φ], fun r => by simp [Φ, hδalg], fun M M' hM => ?_⟩
  let L : (ι → K) → (K ⊗[A] Ω[A⁄R] →ₗ[K] K) := fun M => Fintype.linearCombination K M ∘ₗ b.equivFun.toLinearMap
  have hL : ∀ M : ι → K, ∀ a, L M (1 ⊗ₜ KaehlerDifferential.D R A a) = ∑ k, (Φ a).snd k * M k := by
    intro M a
    simp [L, Φ, δ, Fintype.linearCombination_apply, smul_eq_mul]
  have hLL : L M = L M' := by
    apply (LinearMap.liftBaseChangeEquiv K).symm.injective
    refine LinearMap.ext_on_range (KaehlerDifferential.span_range_derivation R A) fun a => ?_
    rw [LinearMap.liftBaseChangeEquiv_symm_apply, LinearMap.liftBaseChangeEquiv_symm_apply, hL, hL, hM]
  funext j
  have := LinearMap.congr_fun hLL (b j)
  simpa [L, Finsupp.single_eq_pi_single, Fintype.linearCombination_apply_single] using this

end GlobalTheory.TanBasis

namespace GlobalTheory.TanBasis

theorem exists_point_tanBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (ι : Type) [Fintype ι], Fintype.card ι = Dw.dim → ∃ X : Sp (TrivSqZeroExt K (ι → K)) ⟶ Xo.X, X ≫ Xo.s = sOf c _ ∧ spMap (TrivSqZeroExt.fstHom c.F K (ι → K)).toRingHom ≫ X = y.x ∧ Function.Injective (fun M : ι → K => spMap (GlobalTheory.FlagTan.dir c M).toRingHom ≫ X) := by
  intro E _ _ _ H Dw l Xo c K _ _ y ι _ hι
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := y.x (IsLocalRing.closedPoint K)) (U := ⊤) trivial
  have hrange : Set.range y.x ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨p, rfl⟩
    rwa [Subsingleton.elim p (IsLocalRing.closedPoint K)]
  let y' := IsOpenImmersion.lift hU.fromSpec y.x hrange
  have hy' : y' ≫ hU.fromSpec = y.x := IsOpenImmersion.lift_fac _ _ _
  let g := Spec.preimage (hU.fromSpec ≫ Xo.s)
  have hg : Spec.map g = hU.fromSpec ≫ Xo.s := Spec.map_preimage _
  let xr := Spec.preimage y'
  have hxr : Spec.map xr = y' := Spec.map_preimage _
  haveI := Xo.smooth
  have hsm : SmoothOfRelativeDimension Dw.dim (Spec.map g) := by
    rw [hg]
    have := (inferInstance : SmoothOfRelativeDimension (0 + Dw.dim) (hU.fromSpec ≫ Xo.s))
    rwa [zero_add] at this
  have hloc := HasRingHomProperty.Spec_iff.1 hsm
  letI : Algebra (KA l) Γ(Xo.X, U) := g.hom.toAlgebra
  obtain ⟨Φ, h1, h2, h3⟩ := exists_tan_basis (R := KA l) (A := Γ(Xo.X, U)) hloc xr.hom hι
  have hbase : ∀ r, xr.hom (g.hom r) = algebraMap c.F K (IntermediateField.inclusion c.le r) := by
    have : Spec.map (g ≫ xr) = sOf c K := by
      rw [Spec.map_comp, hxr, hg, ← Category.assoc, hy', y.x_over]
    intro r
    exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom (Spec.map_injective this)) r
  have hfst : (TrivSqZeroExt.fstHom c.F K (ι → K)).toRingHom.comp Φ = xr.hom := by
    ext a; exact h1 a
  refine ⟨spMap Φ ≫ hU.fromSpec, ?_, ?_, ?_⟩
  · rw [Category.assoc, ← hg, spMap, ← Spec.map_comp, sOf]
    have hΦg : Φ.comp g.hom =
        (algebraMap c.F (TrivSqZeroExt K (ι → K))).comp (IntermediateField.inclusion c.le).toRingHom := by
      refine RingHom.ext fun r => TrivSqZeroExt.ext ?_ ?_
      · rw [RingHom.comp_apply, h1, hbase]
        simp [TrivSqZeroExt.algebraMap_eq_inl']
      · rw [RingHom.comp_apply, show g.hom r = algebraMap (KA l) Γ(Xo.X, U) r from rfl, h2]
        simp [TrivSqZeroExt.algebraMap_eq_inl']
    rw [← hΦg]
    rfl
  · rw [← Category.assoc, spMap, spMap, ← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom ((TrivSqZeroExt.fstHom c.F K (ι → K)).toRingHom.comp Φ)) ≫ _ = _
    rw [hfst]
    change Spec.map xr ≫ _ = _
    rw [hxr, hy']
  · intro M M' hMM
    simp only at hMM
    rw [← Category.assoc, ← Category.assoc, cancel_mono, spMap, spMap, spMap, ← Spec.map_comp,
      ← Spec.map_comp] at hMM
    have hr := congrArg CommRingCat.Hom.hom (Spec.map_injective hMM)
    apply h3
    intro a
    have := congrArg TrivSqZeroExt.snd (RingHom.congr_fun hr a)
    simpa using this

end GlobalTheory.TanBasis
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModuliPointTrivSqZeroExtTangentBasisStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_moduliPoint_trivSqZeroExt_tangentBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (ι : Type) [Fintype ι], Fintype.card ι = Dw.dim → ∃ X : Sp (TrivSqZeroExt K (ι → K)) ⟶ Xo.X, X ≫ Xo.s = sOf c _ ∧ spMap (TrivSqZeroExt.fstHom c.F K (ι → K)).toRingHom ≫ X = y.x ∧ Function.Injective (fun M : ι → K => spMap (GlobalTheory.FlagTan.dir c M).toRingHom ≫ X) := by
  first | exact @GlobalTheory.TanBasis.exists_point_tanBasis | exact GlobalTheory.TanBasis.exists_point_tanBasis | (intros; apply GlobalTheory.TanBasis.exists_point_tanBasis <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversalFirstOrderDeformation
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.FlagTan.KSUniv

theorem spMap_comp_spMap' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

noncomputable def reparam {K : Type} [Field K] (F : Type) [Field F] [Algebra F K] {ι : Type} [Fintype ι]
    (P : Matrix ι ι K) : TrivSqZeroExt K (ι → K) →ₐ[F] TrivSqZeroExt K (ι → K) :=
  (TrivSqZeroExt.map (Matrix.mulVecLin P.transpose)).restrictScalars F

theorem isTanX_dir {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {K : Type} [Field K] [Algebra c.F K] {y : FrPt Xo c K}
    {ι : Type} [Fintype ι] {X : Sp (TrivSqZeroExt K (ι → K)) ⟶ Xo.X} (h1 : X ≫ Xo.s = sOf c _)
    (h2 : spMap (TrivSqZeroExt.fstHom c.F K (ι → K)).toRingHom ≫ X = y.x) (M : ι → K) :
    GlobalTheory.FlagTan.IsTanX y (spMap (GlobalTheory.FlagTan.dir c M).toRingHom ≫ X) := by
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, h1, sOf, sOf, spMap_comp_spMap']
    congr 1
    rw [← RingHom.comp_assoc]
    congr 1
    exact (GlobalTheory.FlagTan.dir c M).comp_algebraMap
  · rw [← Category.assoc, spMap_comp_spMap', ← h2]
    congr 2
    ext z
    simp

theorem dir_comp_reparam {K : Type} [Field K] {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {l : Level H} {c : Coeff l} [Algebra c.F K] {ι : Type} [Fintype ι] (P : Matrix ι ι K) (M : ι → K) :
    (GlobalTheory.FlagTan.dir c M).toRingHom.comp (reparam c.F P).toRingHom = (GlobalTheory.FlagTan.dir c (P.mulVec M)).toRingHom := by
  ext z
  · simp [reparam]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, GlobalTheory.FlagTan.snd_dir, reparam,
      AlgHom.restrictScalars_apply, GlobalTheory.FlagTan.fst_dir, TrivSqZeroExt.snd_map, Matrix.mulVecLin_apply]
    have e := Matrix.dotProduct_mulVec z.snd P M
    rw [← Matrix.mulVec_transpose] at e
    simpa [dotProduct, mul_comm] using e.symm


open GlobalTheory.FlagTan in
theorem ksUniv : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), 1 ≤ Dw.p + Dw.q → ∃ X : Sp (TrivSqZeroExt K (GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K)) ⟶ Xo.X, X ≫ Xo.s = sOf c _ ∧ spMap (TrivSqZeroExt.fstHom c.F K (GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K)).toRingHom ≫ X = y.x ∧ ∀ M : GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K, GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y (spMap (GlobalTheory.FlagTan.dir c M).toRingHom ≫ X) M := by
  intro hP hG E _ _ _ H Dw l Xo c K _ _ y hpq
  classical
  obtain ⟨X₀, h1, h2, hinj⟩ :=
    GlobalTheory.T.exists_moduliPoint_trivSqZeroExt_tangentBasis E H Dw l Xo c K y (HIx Dw (psiSet H)) (card_HIx (isHalf_psiSet H))
  choose N hN using fun k : HIx Dw (psiSet H) =>
    GlobalTheory.T.kodaira_spencer_matrix_exists hP E H Dw l Xo c K y _ hpq (isTanX_dir h1 h2 (Pi.single k 1))
  have hL := GlobalTheory.T.tangent_flag_hodge_index_vanishing hP E H Dw l Xo c K y _ X₀ hpq h1 h2 N hN
  let L : (HIx Dw (psiSet H) → K) →ₗ[K] (HIx Dw (psiSet H) → K) := Fintype.linearCombination K N
  have hLa : ∀ M, L M = ∑ k, M k • N k := fun M => Fintype.linearCombination_apply _ _ _
  have h0 : spMap (dir c (0 : HIx Dw (psiSet H) → K)).toRingHom ≫ X₀ =
      spMap (algebraMap K (DualNumber K)) ≫ y.x := by
    rw [← h2, ← Category.assoc, spMap_comp_spMap']
    congr 2
    ext z <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have Linj : Function.Injective L := (injective_iff_map_eq_zero L).2 fun M hM =>
    hinj ((GlobalTheory.T.kodaira_spencer_zero_tangent_trivial hP hG E H Dw l Xo c K y _ hpq (isTanX_dir h1 h2 M)
      (by rw [← hM, hLa]; exact hL M)).trans h0.symm)
  let e := LinearEquiv.ofInjectiveEndo L Linj
  let P := LinearMap.toMatrix' (e.symm : (HIx Dw (psiSet H) → K) →ₗ[K] (HIx Dw (psiSet H) → K))
  have hP' : ∀ M, P.mulVec M = e.symm M := fun M => LinearMap.toMatrix'_mulVec _ M
  refine ⟨spMap (reparam c.F P).toRingHom ≫ X₀, ?_, ?_, fun M => ?_⟩
  · rw [Category.assoc, h1, sOf, spMap_comp_spMap']
    congr 1
    rw [← RingHom.comp_assoc]
    congr 1
    exact (reparam c.F P).comp_algebraMap
  · rw [← Category.assoc, spMap_comp_spMap', ← h2]
    congr 2
    ext z
    simp [reparam]
  · rw [← Category.assoc, spMap_comp_spMap', dir_comp_reparam, hP']
    have := hL (e.symm M)
    rwa [← hLa, show L (e.symm M) = M from e.apply_symm_apply M] at this

end GlobalTheory.FlagTan.KSUniv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversalFirstOrderDeformationStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.universal_first_order_deformation : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), 1 ≤ Dw.p + Dw.q → ∃ X : Sp (TrivSqZeroExt K (GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K)) ⟶ Xo.X, X ≫ Xo.s = sOf c _ ∧ spMap (TrivSqZeroExt.fstHom c.F K (GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K)).toRingHom ≫ X = y.x ∧ ∀ M : GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K, GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y (spMap (GlobalTheory.FlagTan.dir c M).toRingHom ≫ X) M := by
  first | exact @GlobalTheory.FlagTan.KSUniv.ksUniv | exact GlobalTheory.FlagTan.KSUniv.ksUniv | (intros; apply GlobalTheory.FlagTan.KSUniv.ksUniv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenModelBaseChangeUniv
noncomputable section

namespace GlobalTheory.UPel.HT.Gen.BaseChange

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.Gen

section Pull

open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud GlobalTheory.HTPull GlobalTheory.SiegelPull ReciprocityTheory.ChartRestriction.G.Pdiv
open scoped CategoryTheory.Obj

variable {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R]

theorem exists_gObjMap_pull {b : GBase G R} {N : ℕ} {S S' : Scheme.{0}} {s : S ⟶ Sp R} (f : S' ⟶ S)
    (o : GObj b N s) : ∃ o' : GObj b N (f ≫ s), Nonempty (GObjMap o' o f) := by
  let A' := (Over.pullback f).obj o.A
  let φ := PullbackComparison.pφ f o.A
  let φ₂ := PullbackComparison.pφ₂ f o.A
  have pb : IsGrpPullback A' o.A f φ := PullbackComparison.isGrpPullback f o.A
  have sq : IsSquare φ φ₂ := PullbackComparison.isSquare f o.A
  have hab : IsAbelianScheme A' :=
    { comm := by have := o.ab.comm; infer_instance
      smooth := by have := o.ab.smooth; show Smooth (Limits.pullback.snd _ _); infer_instance
      proper := by have := o.ab.proper; show IsProper (Limits.pullback.snd _ _); infer_instance
      geomConnected := by
        have := o.ab.geomConnected
        show GeometricallyConnected (Limits.pullback.snd _ _); infer_instance }
  obtain ⟨act', ⟨hhom, hone, hmul, hadd⟩, hact'⟩ := ActPull.exists_act_pull S S' f o.A A' φ pb G.Oᵐᵒᵖ
    (fun a => o.act.act a.unop) (fun a => o.act.hom _) (by simpa using o.act.one)
    (fun a b => by simpa using o.act.mul b.unop a.unop) (fun a b => by simpa using o.act.add a.unop b.unop)
  let actN : OActN G.O A' :=
    { act := fun c => act' (MulOpposite.op c)
      hom := fun c => hhom _
      one := by simpa using hone
      mul := fun c d => by rw [MulOpposite.op_mul]; exact hmul _ _
      add := fun c d => by rw [MulOpposite.op_add]; exact hadd _ _ }
  have hact : ∀ c, (actN.act c).left ≫ φ = φ ≫ (o.act.act c).left := fun c => hact' (MulOpposite.op c)
  let P' : LB (G2 A').left := o.P.pull φ₂
  have hP' : P'.IsLB := pull_isLB o.isLB φ₂
  have iso : LBIso P' (o.P.pull φ₂) := PullbackComparison.gen_refl _ hP'
  have dg := SiegelPull.diag_iso sq iso
  have sqL : ∀ (x' y' : G2 A' ⟶ A') (x y : G2 o.A ⟶ o.A), x'.left ≫ φ = φ₂ ≫ x.left → y'.left ≫ φ = φ₂ ≫ y.left →
      (lift x' y').left ≫ φ₂ = φ₂ ≫ (lift x y).left := fun x' y' x y hx hy =>
    (Category.id_comp _).symm.trans (SiegelPull.lift_sq sq (T := Over.mk (φ₂ ≫ (G2 o.A).hom)) (T' := G2 A') (𝟙 _) x' y'
      (Z := G2 o.A) φ₂ x y (by rw [Category.id_comp]; exact hx) (by rw [Category.id_comp]; exact hy))
  obtain ⟨t₁, ht₁⟩ := o.rig₁
  obtain ⟨t₂, ht₂⟩ := o.rig₂
  let o' : GObj b N (f ≫ s) :=
    { A := A'
      ab := hab
      act := actN
      P := P'
      isLB := hP'
      rig₁ := gen_chartPull (chartPullLinComb o.P _ _ _ _ φ (fun _ => PullbackComparison.lift_one_id f o.A)) t₁ ht₁
      rig₂ := gen_chartPull (chartPullLinComb o.P _ _ _ _ φ (fun _ => PullbackComparison.lift_id_one f o.A)) t₂ ht₂
      symm := LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull o.P _ _ rfl)
        (chartPullLinComb o.P _ _ _ _ φ₂ (fun _ => PullbackComparison.lift_swap f o.A)) o.symm
      ample := (pol_pull S S' o.A A' f φ _ _ (pull_isLB o.isLB _) (pull_isLB hP' _) o.ab pb dg).2.1 o.ample
      rosati := fun c => LBIso.chartPull
        (chartPullLinComb o.P _ _ _ _ φ₂ (fun _ => sqL _ _ _ _ (by
          rw [Over.comp_left, Over.comp_left, Category.assoc, hact, ← Category.assoc, ← sq.1, Category.assoc])
          (by rw [sq.2])))
        (chartPullLinComb o.P _ _ _ _ φ₂ (fun _ => sqL _ _ _ _ (by rw [sq.1]) (by
          rw [Over.comp_left, Over.comp_left, Category.assoc, hact, ← Category.assoc, ← sq.2, Category.assoc])))
        (o.rosati c)
      lie := fun R' _ β x hx v hv => by
        obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv pb (epsPtR x) (spMap (algebraMap R' (DualNumber R')) ≫ x ≫ f)
          (Category.assoc _ _ _).symm
        obtain ⟨w, hw, hvw⟩ := o.lie R' β (x ≫ f) (by rw [Category.assoc, hx]) (e v)
          ((isTanScal_iff pb o.act actN hact x e he _ _ v).1 hv)
        refine ⟨fun i => e.symm (w i), fun i c => (isTanScal_iff pb o.act actN hact x e he _ _ _).2
          (by rw [e.apply_symm_apply]; exact hw i c), e.injective ?_⟩
        rw [hvw, map_list_prod, List.map_ofFn]
        simp [Function.comp_def]
      lieRank := fun k _ _ x β hx i => (GlobalTheory.LiePull.lieMult_pull (𝓞 G.F) S S' o.A A' f φ (actF o.act) (actF actN) pb
        (fun c => hact _) k x (β.comp (b.t i)) G.m).2 (o.lieRank k (x ≫ f) β (by rw [Category.assoc, hx]) i)
      eta := fun y => SiegelPull.secPull pb (o.eta y)
      eta_add := fun y z => SiegelPull.push_injective pb _ (by
        rw [map_mul, push_secPull', push_secPull', push_secPull', o.eta_add, MonObj.comp_mul])
      eta_lin := fun c y => SiegelPull.push_injective pb _ (by
        rw [push_comp pb (hact c), push_secPull', push_secPull', o.eta_lin, Category.assoc])
      eta_ker := fun y => SiegelPull.push_injective pb _ (by
        rw [push_secPull', o.eta_ker, map_one, MonObj.comp_one])
      geom := fun k _ _ x β hx => by
        obtain ⟨I, hI⟩ := o.geom k (x ≫ f) β (by rw [Category.assoc, hx])
        let e : (Over.mk x ⟶ A') ≃* (Over.mk (x ≫ f) ⟶ o.A) := MulEquiv.ofBijective (pushHom pb (Over.mk x))
          ⟨SiegelPull.push_injective pb _, SiegelPull.push_surjective pb _⟩
        have ea : ∀ c g, e (g ≫ actN.act c) = e g ≫ o.act.act c := fun c g => push_comp pb (hact c) _ g
        have ex : ∀ z, z.left = (e.symm z).left ≫ φ := fun z =>
          (congrArg (fun q => q.left) (e.apply_symm_apply z)).symm
        refine ⟨{ ζ := I.ζ, ζ_prim := I.ζ_prim, ζ_pow := I.ζ_pow, ev := fun n y => e.symm (I.ev n y)
                  add := fun n y z => by rw [I.add, map_mul]
                  lin := fun n c y => e.injective (by rw [ea, e.apply_symm_apply, e.apply_symm_apply, I.lin])
                  ker := fun n hn y => by rw [map_eq_one_iff _ e.symm.injective]; exact I.ker n hn y
                  onto := fun n hn q => by
                    rw [← map_eq_one_iff e e.injective, map_pow, I.onto n hn (e q)]
                    exact exists_congr fun y => e.symm_apply_eq.symm
                  tower := fun n m hn hm y => by rw [← map_pow, I.tower n m hn hm]
                  isom := fun n hn y z => (weilIs_grpPullback_of_comm S S' o.A A' f φ _ _ (pull_isLB o.isLB _)
                    (pull_isLB hP' _) pb dg (Over.mk x) n _ _ (I.ev n y) (I.ev n z) _ (ex _) (ex _)).2
                    (I.isom n hn y z) }, fun y => ?_⟩
        show toUnit _ ≫ SiegelPull.secPull pb (o.eta y) = e.symm (I.ev N y)
        rw [eq_comm, e.symm_apply_eq, ← hI y]
        exact (SiegelPull.push_secPull pb (o.eta y) (Over.mk x)).symm }
  exact ⟨o', ⟨{ φ := φ, φ₂ := φ₂, cart := pb, sq := sq, act := hact, pol := iso, eta := fun y => SiegelPull.secPull_left pb _ }⟩⟩

end Pull

section Cancel

open GlobalTheory.UPel.HT.MapComp

variable {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R]

theorem gObjMap_cancel {b : GBase G R} {N : ℕ} {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R}
    {s₃ : S₃ ⟶ Sp R} {o₁ : GObj b N s₁} {o₂ : GObj b N s₂} {o₃ : GObj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃}
    (m : GObjMap o₁ o₃ (f ≫ g)) (m₂ : GObjMap o₂ o₃ g) : Nonempty (GObjMap o₁ o₂ f) := by
  have w : m.φ ≫ o₃.A.hom = (o₁.A.hom ≫ f) ≫ g := by rw [m.cart.1.w, Category.assoc]
  set φ := m₂.cart.1.lift m.φ (o₁.A.hom ≫ f) w
  have hφ : φ ≫ m₂.φ = m.φ := m₂.cart.1.lift_fst _ _ _
  have hφ' : φ ≫ o₂.A.hom = o₁.A.hom ≫ f := m₂.cart.1.lift_snd _ _ _
  have n : IsGrpPullback o₁.A o₃.A (f ≫ g) (φ ≫ m₂.φ) := by rw [hφ]; exact m.cart
  obtain ⟨φ₂, sq⟩ := exists_isSquare hφ'
  have e : m.φ₂ = φ₂ ≫ m₂.φ₂ := isSquare_unique m.sq (hφ ▸ isSquare_comp sq m₂.sq)
  have hact : ∀ c, (o₁.act.act c).left ≫ φ = φ ≫ (o₂.act.act c).left := by
    intro c
    apply m₂.cart.1.hom_ext
    · rw [Category.assoc, hφ, m.act, Category.assoc, m₂.act, ← Category.assoc, hφ]
    · rw [Category.assoc, hφ', ← Category.assoc, Over.w, Category.assoc, Over.w, hφ']
  have heta : ∀ y, (o₁.eta y).left ≫ φ = f ≫ (o₂.eta y).left := by
    intro y
    apply m₂.cart.1.hom_ext
    · rw [Category.assoc, hφ, m.eta, Category.assoc, Category.assoc, m₂.eta]
    · rw [Category.assoc, hφ', ← Category.assoc, Over.w, Category.assoc, Over.w]
      show 𝟙 _ ≫ f = f ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]
  exact ⟨{ φ := φ
           φ₂ := φ₂
           cart := m₂.cart.cancel n hφ'
           sq := sq
           act := hact
           pol := LBIso.trans o₁.isLB (pull_isLB o₃.isLB _) (pull_isLB o₂.isLB _) m.pol
             (LBIso.symm (lbIso_pull_comp m₂.pol φ₂ e))
           eta := heta }⟩

end Cancel

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f :=
  Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)

theorem exists_ext {R₁ R₂ R' : Type} [CommRing R₁] [CommRing R₂] [CommRing R'] (ψ : R₁ →+* R₂) (β₁ : R₁ →+* R')
    (x : Sp R' ⟶ Sp R₂) (hx : x ≫ spMap ψ = spMap β₁) : ∃ β₂ : R₂ →+* R', x = spMap β₂ ∧ β₁ = β₂.comp ψ := by
  obtain ⟨g, hg⟩ := Spec.map_surjective (R := CommRingCat.of R₂) (S := CommRingCat.of R') x
  have e : x = spMap g.hom := hg.symm
  refine ⟨g.hom, e, ?_⟩
  rw [e, ← spMap_comp'] at hx
  have := Spec.map_injective (R := CommRingCat.of R₁) (S := CommRingCat.of R') hx
  exact (congrArg CommRingCat.Hom.hom this).symm

section Rebase

variable {G : GDatum} {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] [Algebra ℚ R₁] [Algebra ℚ R₂] {ψ : R₁ →+* R₂}
  {gb₁ : GBase G R₁} {gb₂ : GBase G R₂} (hρ : gb₂.ρ = ψ gb₁.ρ) (ht : ∀ i, gb₂.t i = ψ.comp (gb₁.t i)) {N : ℕ}
  {S : Scheme.{0}} {s₁ : S ⟶ Sp R₁} {s₂ : S ⟶ Sp R₂} (hs : s₂ ≫ spMap ψ = s₁)

def down (o : GObj gb₂ N s₂) : GObj gb₁ N s₁ where
  A := o.A
  ab := o.ab
  act := o.act
  P := o.P
  isLB := o.isLB
  rig₁ := o.rig₁
  rig₂ := o.rig₂
  symm := o.symm
  ample := o.ample
  rosati := o.rosati
  lie := fun R' _ β x hx v hv => by
    obtain ⟨β₂, e, rfl⟩ := exists_ext ψ β (x ≫ s₂) (by rw [Category.assoc, hs, hx])
    obtain ⟨w, hw, hv⟩ := o.lie R' β₂ x e v (by rw [hρ]; exact hv)
    exact ⟨w, fun i c => by have := hw i c; rw [ht] at this; exact this, hv⟩
  lieRank := fun k _ _ x β hx i => by
    obtain ⟨β₂, e, rfl⟩ := exists_ext ψ β (x ≫ s₂) (by rw [Category.assoc, hs, hx])
    have := o.lieRank k x β₂ e i
    rw [ht] at this
    exact this
  eta := o.eta
  eta_add := o.eta_add
  eta_lin := o.eta_lin
  eta_ker := o.eta_ker
  geom := fun k _ _ x β hx => by
    obtain ⟨β₂, e, rfl⟩ := exists_ext ψ β (x ≫ s₂) (by rw [Category.assoc, hs, hx])
    exact o.geom k x β₂ e

def up (o : GObj gb₁ N s₁) : GObj gb₂ N s₂ where
  A := o.A
  ab := o.ab
  act := o.act
  P := o.P
  isLB := o.isLB
  rig₁ := o.rig₁
  rig₂ := o.rig₂
  symm := o.symm
  ample := o.ample
  rosati := o.rosati
  lie := fun R' _ β x hx v hv => by
    obtain ⟨w, hw, hv⟩ := o.lie R' (β.comp ψ) x (by rw [← hs, ← Category.assoc, hx, spMap_comp']) v
      (by rw [hρ] at hv; exact hv)
    exact ⟨w, fun i c => by rw [ht]; exact hw i c, hv⟩
  lieRank := fun k _ _ x β hx i => by
    rw [ht]
    exact o.lieRank k x (β.comp ψ) (by rw [← hs, ← Category.assoc, hx, spMap_comp']) i
  eta := o.eta
  eta_add := o.eta_add
  eta_lin := o.eta_lin
  eta_ker := o.eta_ker
  geom := fun k _ _ x β hx => o.geom k x (β.comp ψ) (by rw [← hs, ← Category.assoc, hx, spMap_comp'])

end Rebase

end GlobalTheory.UPel.HT.Gen.BaseChange
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullUInjectiveOfFlatSurjective
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.EigenDescent
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EigenDescent

theorem app_injective_of_flat_surjective {X Y : Scheme.{0}} (π : X ⟶ Y) [Flat π] [Surjective π]
    (V : Y.Opens) : Function.Injective (π.app V) := by
  intro s t h
  apply TopCat.Presheaf.section_ext Y.sheaf V s t
  intro y hy
  obtain ⟨x, rfl⟩ := π.surjective y
  have hinj : Function.Injective (π.stalkMap x) := by
    have hf := Flat.stalkMap π x
    algebraize [(π.stalkMap x).hom]
    have : IsLocalHom (algebraMap (Y.presheaf.stalk (π x)) (X.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom (π.stalkMap x).hom)
    have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Y.presheaf.stalk (π x))
      (B := X.presheaf.stalk x)
    exact FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (π x)) (X.presheaf.stalk x)
  apply hinj
  change π.stalkMap x (Y.presheaf.germ V (π x) hy s) = π.stalkMap x (Y.presheaf.germ V (π x) hy t)
  rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.germ_stalkMap_apply, h]

theorem pullU_injective_of_flat_surjective : ∀ {X Y : Scheme.{0}} (π : X ⟶ Y), Flat π → Surjective π →
    ∀ V : Y.Opens, Function.Injective (pullU π V) := by
  intro X Y π _ _ V u v h
  exact Units.ext (app_injective_of_flat_surjective π V (congrArg Units.val h))

end GlobalTheory.EigenDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjFixAt
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp.TwConj

open GlobalTheory.ConjTwist

theorem de_chi_eq {D : D7} {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (x : (AE D)ˣ) :
    ∃ σ, (((ρ.B i j b).de.chi x : Circle) : ℂ) = ρ.eO i b (algebraMap (D.ntw.O0 i) (D.ntw.O i)
        ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)) := _root_.GlobalTheory.PlaceFix.de_chi_eq (D := D) (ρ := ρ) hρ i j b x

end GlobalTheory.BigOn.Exp.TwConj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealCochainOfCoboundaryConstants
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealCochainOfCoboundaryConstants
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem LiftSys.cobound_I : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Const s₀ → ∀ (S : Sys I π s₀) (z : Z1 S.F), S.IsIdealValuedLiftSystemCocycle z → H1.mk _ z = 0 → ∃ g : C0 S.F, S.IsIdealValuedLiftSystemCochain g ∧ d0 _ g = z.1 := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ hc S z hz h0
  obtain ⟨g, hg⟩ := H1.mk_eq_zero.1 h0
  obtain ⟨r₀, hr₀⟩ := hc (fun U ↦ S.p U (g U)) (by
    funext U V a
    have e := congrFun (congrFun (congrFun hg U) V) a
    rw [amitsur_d0_apply] at e
    rw [amitsur_d0_apply, ← S.nat a, ← map_sub, e]
    exact (S.ker V _).2 (hz U V a))
  obtain ⟨r, rfl⟩ := hπ r₀
  refine ⟨fun U ↦ g U - algebraMap R (S.F.obj U) r, fun U ↦ (S.ker U _).1 ?_, ?_⟩
  · rw [map_sub, hr₀ U, (S.semi U).map_algebraMap, sub_self]
  · rw [← hg]
    funext U V a
    simp only [amitsur_d0_apply, map_sub, AlgHom.commutes]
    ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealCochainOfCoboundaryConstantsStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ideal_cochain_of_coboundary_constants : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Const s₀ → ∀ (S : Sys I π s₀) (z : Z1 S.F), S.IsIdealValuedLiftSystemCocycle z → H1.mk _ z = 0 → ∃ g : C0 S.F, S.IsIdealValuedLiftSystemCochain g ∧ d0 _ g = z.1 := by
  first | exact @GlobalTheory.LiftSys.cobound_I | exact GlobalTheory.LiftSys.cobound_I | (intros; apply GlobalTheory.LiftSys.cobound_I <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDifferenceDerivationOfLiftsComp
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDifferenceDerivationOfLiftsComp
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.Obs.isTheta_comp : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (B B₀ : Type) [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀) (hs : SemiHom π p) (hp : Function.Surjective p) (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) (B' B₀' : Type) [CommRing B'] [Algebra R B'] [CommRing B₀'] [Algebra R₀ B₀'] (p' : B' →+* B₀') (hs' : SemiHom π p') (hp' : Function.Surjective p') (hker' : ∀ b, p' b = 0 ↔ b ∈ I.map (algebraMap R B')) (E E' : Type) [CommRing E] [Algebra R E] [CommRing E'] [Algebra R E'] (a b : B →ₐ[R] E) (θ : Ω[B₀⁄R₀] →+ E), IsTheta I p a b θ → (∀ g : E →ₐ[R] E', IsTheta I p (g.comp a) (g.comp b) ((g : E →+* E').toAddMonoidHom.comp θ)) ∧ ∀ (h : B' →ₐ[R] B) (h₀ : B₀' →ₐ[R₀] B₀), (∀ x, p (h x) = h₀ (p' x)) → IsTheta I p' (a.comp h) (b.comp h) (θ.comp (SemiHom.of_algHom h₀).m1.toAddMonoidHom) := by
  intro R R₀ _ _ I hI π hπ hk B B₀ _ _ _ _ p hs hp hker B' B₀' _ _ _ _ p' hs' hp' hker' E E' _ _ _ _ a b θ hθ
  refine ⟨fun g ↦ ⟨fun x w ↦ ?_, fun x ↦ ?_, fun w ↦ ?_⟩, fun h h₀ hh ↦ ⟨fun x w ↦ ?_, fun x ↦ ?_, fun w ↦ ?_⟩⟩
  · change g (θ (p x • w)) = g (a x) * g (θ w)
    rw [hθ.smul, map_mul]
  · change g (θ (KaehlerDifferential.D R₀ B₀ (p x))) = g (a x) - g (b x)
    rw [hθ.der, map_sub]
  · have h1 := Ideal.mem_map_of_mem (g : E →+* E') (hθ.mem w)
    rw [Ideal.map_map, g.comp_algebraMap] at h1
    simpa using h1
  · change θ ((SemiHom.of_algHom h₀).m1 (p' x • w)) = a (h x) * θ ((SemiHom.of_algHom h₀).m1 w)
    rw [SemiHom.oneFormMap_smul_semilinear]
    change θ (h₀ (p' x) • _) = _
    rw [← hh, hθ.smul]
  · change θ ((SemiHom.of_algHom h₀).m1 (KaehlerDifferential.D R₀ B₀' (p' x))) = a (h x) - b (h x)
    rw [SemiHom.m1_D]
    change θ (KaehlerDifferential.D R₀ B₀ (h₀ (p' x))) = _
    rw [← hh, hθ.der]
  · exact hθ.mem _
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDifferenceDerivationOfLiftsCompStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDifferenceDerivationOfLifts_comp : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (B B₀ : Type) [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀) (hs : SemiHom π p) (hp : Function.Surjective p) (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) (B' B₀' : Type) [CommRing B'] [Algebra R B'] [CommRing B₀'] [Algebra R₀ B₀'] (p' : B' →+* B₀') (hs' : SemiHom π p') (hp' : Function.Surjective p') (hker' : ∀ b, p' b = 0 ↔ b ∈ I.map (algebraMap R B')) (E E' : Type) [CommRing E] [Algebra R E] [CommRing E'] [Algebra R E'] (a b : B →ₐ[R] E) (θ : Ω[B₀⁄R₀] →+ E), IsTheta I p a b θ → (∀ g : E →ₐ[R] E', IsTheta I p (g.comp a) (g.comp b) ((g : E →+* E').toAddMonoidHom.comp θ)) ∧ ∀ (h : B' →ₐ[R] B) (h₀ : B₀' →ₐ[R₀] B₀), (∀ x, p (h x) = h₀ (p' x)) → IsTheta I p' (a.comp h) (b.comp h) (θ.comp (SemiHom.of_algHom h₀).m1.toAddMonoidHom) := by
  first | exact @GlobalTheory.Obs.isTheta_comp | exact GlobalTheory.Obs.isTheta_comp | (intros; apply GlobalTheory.Obs.isTheta_comp <;> assumption)
end
end

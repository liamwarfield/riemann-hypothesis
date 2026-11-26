module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilQDivisorAvoidsPointCartierIffNotMemSupp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.L2MatrixCoeffBoundedHolomorphicFormEqExtremalVec

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupNonzeroLocusSecPullLin
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SpanVA

open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi (LB)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp PSpace resG)
open GlobalTheory.ProjSpace (toProj O1 coord)

variable {R : Type} [CommRing R] {m N : ℕ}

def lin (a : Matrix (Fin (m + 1)) (Fin (N + 1)) R) : Fin (m + 1) → (O1 R N).Sec :=
  fun i => ∑ j, GlobalTheory.AbLaw.cst (PSpace.str R N) ⊤ (a i j) • coord R N j

def dom (a : Matrix (Fin (m + 1)) (Fin (N + 1)) R) : (PSpace R N).Opens := ⨆ i, nonzeroLocus (lin a i)

theorem iSup_nonzeroLocus_secPull_lin (a : Matrix (Fin (m + 1)) (Fin (N + 1)) R) :
    ⨆ i, nonzeroLocus (GlobalTheory.Cartier.secPull (lin a i) (dom a).ι) = ⊤ := by
  simp only [GlobalTheory.Cartier.nonzeroLocus_secPull]
  rw [← Scheme.Hom.preimage_iSup]
  exact (dom a).ι_preimage_self

def proj (a : Matrix (Fin (m + 1)) (Fin (N + 1)) R) : (dom a).toScheme ⟶ PSpace R m :=
  toProj ((dom a).ι ≫ PSpace.str R N) (fun i => GlobalTheory.Cartier.secPull (lin a i) (dom a).ι)
    (iSup_nonzeroLocus_secPull_lin a)

def liftDom {X : Scheme.{0}} (a : Matrix (Fin (m + 1)) (Fin (N + 1)) R) (φ : X ⟶ PSpace R N)
    (h : φ ⁻¹ᵁ dom a = ⊤) : X ⟶ (dom a).toScheme :=
  IsOpenImmersion.lift (dom a).ι φ (by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hx : x ∈ φ ⁻¹ᵁ dom a := h.ge trivial
    exact hx)

theorem liftDom_fac {X : Scheme.{0}} (a : Matrix (Fin (m + 1)) (Fin (N + 1)) R) (φ : X ⟶ PSpace R N)
    (h : φ ⁻¹ᵁ dom a = ⊤) : liftDom a φ h ≫ (dom a).ι = φ :=
  IsOpenImmersion.lift_fac _ _ _

end GlobalTheory.SpanVA
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVeryAmpleBySectionsOfLinearSpanCombination
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismToProjSpacePreimageNonzeroLocusLinearFor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismToProjSpacePreimageNonzeroLocusLinearFor
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

noncomputable section

namespace GlobalTheory.SpanVA

open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi (LB)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp PSpace resG)
open GlobalTheory.ProjSpace (toProj O1 coord)

theorem comb_f {R : Type} [CommRing R] {X : Scheme.{0}} {H : LB X} {n : ℕ} (g : X ⟶ Sp R) (c : Fin n → R)
    (t : Fin n → H.Sec) (k : H.ι) :
    (∑ j, GlobalTheory.AbLaw.cst g ⊤ (c j) • t j).f k = ∑ j, GlobalTheory.AbLaw.cst g (H.U k) (c j) * (t j).f k := by
  rw [GlobalTheory.LinChange.sum_f]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [GlobalTheory.LB.smul_f, GlobalTheory.LinChange.resG_cst]

theorem secPull_comb_f {R : Type} [CommRing R] {X Y : Scheme.{0}} {L : LB X} {n : ℕ} (p : X ⟶ Sp R)
    (c : Fin n → R) (t : Fin n → L.Sec) (φ : Y ⟶ X) (q : (L.pull φ).ι) :
    (GlobalTheory.Cartier.secPull (∑ j, GlobalTheory.AbLaw.cst p ⊤ (c j) • t j) φ).f q =
      ∑ j, GlobalTheory.AbLaw.cst (φ ≫ p) ((L.pull φ).U q) (c j) * (GlobalTheory.Cartier.secPull (t j) φ).f q := by
  have hc : ∀ (U : X.Opens) (r : R),
      (φ.app U).hom (GlobalTheory.AbLaw.cst p U r) = GlobalTheory.AbLaw.cst (φ ≫ p) (φ ⁻¹ᵁ U) r := fun U r => by
    rw [Scheme.Hom.app_eq_appLE]
    exact GlobalTheory.LinChange.appLE_cst p φ le_rfl r
  dsimp only [GlobalTheory.Cartier.secPull]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [comb_f, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_mul, hc, GlobalTheory.LinChange.resG_cst]

end GlobalTheory.SpanVA


open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus) in
theorem GlobalTheory.SpanVA.toProj_preimage_nonzeroLocus_lin : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (H : LB X) (m N : ℕ) (s : Fin (m + 1) → LB.Sec H) (t : Fin (N + 1) → LB.Sec H) (a : Matrix (Fin (m + 1)) (Fin (N + 1)) R), H.IsLB → ∀ (ht : ⨆ j, nonzeroLocus (t j) = ⊤), (∀ i, s i = ∑ j, GlobalTheory.AbLaw.cst f ⊤ (a i j) • t j) → ∀ i, GlobalTheory.ProjSpace.toProj f t ht ⁻¹ᵁ nonzeroLocus (GlobalTheory.SpanVA.lin a i) = nonzeroLocus (s i) := by
  intro R _ X f H m N s t a hH ht hst i
  rw [← GlobalTheory.Cartier.nonzeroLocus_secPull]
  refine GlobalTheory.Cartier.SecMaps.nonzeroLocus_eq (pull_isLB (GlobalTheory.ProjSpace.O1_isLB R N) _) hH
    (w := GlobalTheory.ProjSpace.toProjIso f t ht) ?_
  rintro ⟨k, q⟩
  have hc := fun j => GlobalTheory.ProjSpace.secMaps_toProjIso f t ht j (k, q)
  change resG X _ ((s i).f k) = _ * resG X _ ((GlobalTheory.Cartier.secPull (GlobalTheory.SpanVA.lin a i) (GlobalTheory.ProjSpace.toProj f t ht)).f q)
  rw [GlobalTheory.SpanVA.lin]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hst i, GlobalTheory.SpanVA.comb_f, GlobalTheory.SpanVA.secPull_comb_f, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_mul, GlobalTheory.LinChange.resG_cst, GlobalTheory.LinChange.resG_cst, hc j, GlobalTheory.ProjSpace.toProj_str]
  ring
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismToProjSpacePreimageNonzeroLocusLinearForStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.morphismToProjSpace_preimage_nonzeroLocus_linearForm : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (H : LB X) (m N : ℕ) (s : Fin (m + 1) → LB.Sec H) (t : Fin (N + 1) → LB.Sec H) (a : Matrix (Fin (m + 1)) (Fin (N + 1)) R), H.IsLB → ∀ (ht : ⨆ j, nonzeroLocus (t j) = ⊤), (∀ i, s i = ∑ j, GlobalTheory.AbLaw.cst f ⊤ (a i j) • t j) → ∀ i, GlobalTheory.ProjSpace.toProj f t ht ⁻¹ᵁ nonzeroLocus (GlobalTheory.SpanVA.lin a i) = nonzeroLocus (s i) := by
  first | exact @GlobalTheory.SpanVA.toProj_preimage_nonzeroLocus_lin | exact GlobalTheory.SpanVA.toProj_preimage_nonzeroLocus_lin | (intros; apply GlobalTheory.SpanVA.toProj_preimage_nonzeroLocus_lin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismToProjSpaceEqLinearProjectionComp
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismToProjSpaceEqLinearProjectionComp
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.SpanVA

open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi (LB)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp PSpace resG)
open GlobalTheory.ProjSpace (toProj toProj_str toProj_preimage_chart O1 coord coord_f chart pullRatio secRatio_on
  pullRatio_toProj_on appLE_resG appLE_appLE appLE_of_eq)

theorem lin_f {R : Type} [CommRing R] {m N : ℕ} (a : Matrix (Fin (m + 1)) (Fin (N + 1)) R) (j : Fin (m + 1))
    (i : Fin (N + 1)) :
    (lin a j).f i = ∑ n, GlobalTheory.AbLaw.cst (PSpace.str R N) (chart R N i) (a j n) * GlobalTheory.ProjSpace.ratio R N i n := by
  refine (GlobalTheory.LinChange.sum_f (H := O1 R N) _ i).trans (Finset.sum_congr rfl fun n _ => ?_)
  refine (GlobalTheory.LB.smul_f (L := O1 R N) _ _ i).trans ?_
  rw [GlobalTheory.LinChange.resG_cst]
  exact congrArg (_ * ·) (coord_f R N n i)

end GlobalTheory.SpanVA

theorem GlobalTheory.SpanVA.toProj_eq_liftDom_proj : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (H : LB X) (m N : ℕ) (s : Fin (m + 1) → LB.Sec H) (t : Fin (N + 1) → LB.Sec H) (a : Matrix (Fin (m + 1)) (Fin (N + 1)) R), H.IsLB → ∀ (hs : ⨆ i, nonzeroLocus (s i) = ⊤) (ht : ⨆ j, nonzeroLocus (t j) = ⊤) (hst : ∀ i, s i = ∑ j, GlobalTheory.AbLaw.cst f ⊤ (a i j) • t j) (h : GlobalTheory.ProjSpace.toProj f t ht ⁻¹ᵁ GlobalTheory.SpanVA.dom a = ⊤), GlobalTheory.ProjSpace.toProj f s hs = GlobalTheory.SpanVA.liftDom a (GlobalTheory.ProjSpace.toProj f t ht) h ≫ GlobalTheory.SpanVA.proj a := by
  intro R _ X f H m N s t a _ hs ht hst h
  have hg : GlobalTheory.SpanVA.liftDom a (GlobalTheory.ProjSpace.toProj f t ht) h ≫ (GlobalTheory.SpanVA.dom a).ι ≫ PSpace.str R N = f := by
    rw [← Category.assoc, GlobalTheory.SpanVA.liftDom_fac, GlobalTheory.ProjSpace.toProj_str]
  have e := GlobalTheory.ProjSpace.toProj_eq_comp_of_locally (f := (GlobalTheory.SpanVA.dom a).ι ≫ PSpace.str R N)
    (GlobalTheory.SpanVA.iSup_nonzeroLocus_secPull_lin a) (GlobalTheory.SpanVA.liftDom a (GlobalTheory.ProjSpace.toProj f t ht) h)
    (t := s) hs ?_
  · rw [hg] at e
    exact e
  intro z
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (ht.ge (Set.mem_univ z))
  obtain ⟨l, hl⟩ := GlobalTheory.exists_chart_of_mem_nonzeroLocus hi
  have hW : nonzeroLocus (t i) ⊓ H.U l ≤ GlobalTheory.ProjSpace.toProj f t ht ⁻¹ᵁ GlobalTheory.ProjSpace.chart R N i :=
    inf_le_left.trans (GlobalTheory.ProjSpace.toProj_preimage_chart f t ht i).ge
  have hk : nonzeroLocus (t i) ⊓ H.U l ≤ GlobalTheory.SpanVA.liftDom a (GlobalTheory.ProjSpace.toProj f t ht) h ⁻¹ᵁ
      ((GlobalTheory.ProjSpace.O1 R N).pull (GlobalTheory.SpanVA.dom a).ι).U (fun _ => i) := by
    refine hW.trans (le_of_eq ?_)
    erw [GlobalTheory.Cartier.pull_U]
    rw [← Scheme.Hom.comp_preimage, GlobalTheory.SpanVA.liftDom_fac]
    rfl
  refine ⟨nonzeroLocus (t i) ⊓ H.U l, ⟨hi, hl⟩, fun _ => i, hk, l, inf_le_right, ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG X inf_le_right ((t i).f l),
    fun j => ?_⟩
  have key : ((GlobalTheory.SpanVA.liftDom a (GlobalTheory.ProjSpace.toProj f t ht) h).appLE _ _ hk).hom
      ((GlobalTheory.Cartier.secPull (GlobalTheory.SpanVA.lin a j) (GlobalTheory.SpanVA.dom a).ι).f (fun _ => i)) =
      ((GlobalTheory.ProjSpace.toProj f t ht).appLE (GlobalTheory.ProjSpace.chart R N i) _ hW).hom ((GlobalTheory.SpanVA.lin a j).f i) := by
    show ((GlobalTheory.SpanVA.liftDom a (GlobalTheory.ProjSpace.toProj f t ht) h).appLE _ _ hk).hom
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG _ _ (((GlobalTheory.SpanVA.dom a).ι.app _).hom ((GlobalTheory.SpanVA.lin a j).f i))) = _
    rw [GlobalTheory.ProjSpace.appLE_resG, Scheme.Hom.app_eq_appLE, GlobalTheory.ProjSpace.appLE_appLE]
    exact congrArg (fun ψ => ψ.hom ((GlobalTheory.SpanVA.lin a j).f i))
      (GlobalTheory.ProjSpace.appLE_of_eq (GlobalTheory.SpanVA.liftDom_fac a _ h) (GlobalTheory.ProjSpace.chart R N i) _ _ hW)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [key, GlobalTheory.SpanVA.lin_f, map_sum, hst j, GlobalTheory.LinChange.sum_f, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [GlobalTheory.LB.smul_f, map_mul, map_mul, GlobalTheory.LinChange.resG_cst, GlobalTheory.LinChange.resG_cst]
  erw [GlobalTheory.LinChange.appLE_cst (PSpace.str R N) (GlobalTheory.ProjSpace.toProj f t ht) hW (a j n)]
  rw [GlobalTheory.ProjSpace.toProj_str]
  change _ = _ * (_ * GlobalTheory.ProjSpace.pullRatio (GlobalTheory.ProjSpace.toProj f t ht) _ i hW n)
  rw [GlobalTheory.ProjSpace.pullRatio_toProj_on, GlobalTheory.ProjSpace.secRatio_on (t i) (t n) l inf_le_left inf_le_right]
  ring
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismToProjSpaceEqLinearProjectionCompStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.morphismToProjSpace_eq_linearProjection_comp : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (H : LB X) (m N : ℕ) (s : Fin (m + 1) → LB.Sec H) (t : Fin (N + 1) → LB.Sec H) (a : Matrix (Fin (m + 1)) (Fin (N + 1)) R), H.IsLB → ∀ (hs : ⨆ i, nonzeroLocus (s i) = ⊤) (ht : ⨆ j, nonzeroLocus (t j) = ⊤) (hst : ∀ i, s i = ∑ j, GlobalTheory.AbLaw.cst f ⊤ (a i j) • t j) (h : GlobalTheory.ProjSpace.toProj f t ht ⁻¹ᵁ GlobalTheory.SpanVA.dom a = ⊤), GlobalTheory.ProjSpace.toProj f s hs = GlobalTheory.SpanVA.liftDom a (GlobalTheory.ProjSpace.toProj f t ht) h ≫ GlobalTheory.SpanVA.proj a := by
  first | exact @GlobalTheory.SpanVA.toProj_eq_liftDom_proj | exact GlobalTheory.SpanVA.toProj_eq_liftDom_proj | (intros; apply GlobalTheory.SpanVA.toProj_eq_liftDom_proj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVeryAmpleBySectionsOfLinearSpanCombination
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

noncomputable section

namespace GlobalTheory.SpanVA

open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi (LB)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp PSpace resG)
open GlobalTheory.ProjSpace (toProj O1 coord)

theorem iSup_nonzeroLocus_of_span {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) {H : LB X} {m N : ℕ}
    {s : Fin (m + 1) → H.Sec} {t : Fin (N + 1) → H.Sec} {a : Matrix (Fin (m + 1)) (Fin (N + 1)) R}
    (hs : ⨆ i, nonzeroLocus (s i) = ⊤) (hst : ∀ i, s i = ∑ j, GlobalTheory.AbLaw.cst f ⊤ (a i j) • t j) :
    ⨆ j, nonzeroLocus (t j) = ⊤ := by
  refine top_unique fun y _ => ?_
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hs.ge (Set.mem_univ y))
  obtain ⟨k, hk⟩ := GlobalTheory.exists_chart_of_mem_nonzeroLocus hi
  by_contra hne
  have hnu : ∀ j, ¬ IsUnit (X.presheaf.germ (H.U k) y hk ((t j).f k)) := fun j hu =>
    hne (Opens.mem_iSup.2 ⟨j, (GlobalTheory.mem_nonzeroLocus_iff_basicOpen _ hk).2 ((X.mem_basicOpen _ y hk).2 hu)⟩)
  have hu := (X.mem_basicOpen _ y hk).1 ((GlobalTheory.mem_nonzeroLocus_iff_basicOpen _ hk).1 hi)
  have e : (s i).f k = ∑ j, GlobalTheory.AbLaw.cst f (H.U k) (a i j) * (t j).f k := by
    rw [hst i, GlobalTheory.LinChange.sum_f]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [GlobalTheory.LB.smul_f, GlobalTheory.LinChange.resG_cst]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_sum] at hu
  refine (IsLocalRing.mem_maximalIdeal _).1 (Ideal.sum_mem _ fun j _ => ?_) hu
  rw [map_mul]
  exact Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 (hnu j))

theorem isClosedImmersion_of_comp_open {X P Q S : Scheme.{0}} (U : P.Opens) (φ : X ⟶ U.toScheme)
    (ψ : U.toScheme ⟶ Q) (p : P ⟶ S) (q : Q ⟶ S) (hc : IsClosedImmersion (φ ≫ ψ)) (hp : IsSeparated p)
    (hq : ψ ≫ q = U.ι ≫ p) (hpr : IsProper (φ ≫ U.ι ≫ p)) : IsClosedImmersion (φ ≫ U.ι) := by
  have : IsSeparated (ψ ≫ q) := by rw [hq]; infer_instance
  have : IsSeparated ψ := IsSeparated.of_comp ψ q
  have : IsClosedImmersion φ := IsClosedImmersion.of_comp φ ψ
  have : IsProper ((φ ≫ U.ι) ≫ p) := by rw [Category.assoc]; exact hpr
  have : IsProper (φ ≫ U.ι) := IsProper.of_comp _ p
  exact IsClosedImmersion.of_isPreimmersion _ (φ ≫ U.ι).isClosedMap.isClosed_range

end GlobalTheory.SpanVA


open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus) in
theorem GlobalTheory.veryAmpleBy_of_span : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) (m N : ℕ) (s : Fin (m + 1) → LB.Sec H) (t : Fin (N + 1) → LB.Sec H) (a : Matrix (Fin (m + 1)) (Fin (N + 1)) R), H.IsLB → GlobalTheory.AbLaw.VeryAmpleBy f H s → (∀ i, s i = ∑ j, GlobalTheory.AbLaw.cst f ⊤ (a i j) • t j) → GlobalTheory.AbLaw.VeryAmpleBy f H t := by
  intro R _ X f H m N s t a hH hv hst
  obtain ⟨hs, hci⟩ := (GlobalTheory.ProjSpace.veryAmpleBy_iff f s).1 hv
  have ht := GlobalTheory.SpanVA.iSup_nonzeroLocus_of_span f hs hst
  refine (GlobalTheory.ProjSpace.veryAmpleBy_iff f t).2 ⟨ht, ?_⟩
  have hpre : GlobalTheory.ProjSpace.toProj f t ht ⁻¹ᵁ GlobalTheory.SpanVA.dom a = ⊤ := by
    rw [GlobalTheory.SpanVA.dom, Scheme.Hom.preimage_iSup]
    simp only [GlobalTheory.T.morphismToProjSpace_preimage_nonzeroLocus_linearForm R X f H m N s t a hH ht hst]
    exact hs
  have e := GlobalTheory.T.morphismToProjSpace_eq_linearProjection_comp R X f H m N s t a hH hs ht hst hpre
  rw [← GlobalTheory.SpanVA.liftDom_fac a _ hpre]
  have hp : IsSeparated (PSpace.str R N) := by unfold PSpace.str; infer_instance
  refine GlobalTheory.SpanVA.isClosedImmersion_of_comp_open _ _ (GlobalTheory.SpanVA.proj a) (PSpace.str R N) (PSpace.str R m)
    (e ▸ hci) hp (GlobalTheory.ProjSpace.toProj_str _ _ _) ?_
  rw [← Category.assoc, GlobalTheory.SpanVA.liftDom_fac, GlobalTheory.ProjSpace.toProj_str]
  exact GlobalTheory.isProper_of_veryAmpleBy hv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVeryAmpleBySectionsOfLinearSpanCombinationStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isVeryAmpleBySections_of_linear_span_combination : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) (m N : ℕ) (s : Fin (m + 1) → LB.Sec H) (t : Fin (N + 1) → LB.Sec H) (a : Matrix (Fin (m + 1)) (Fin (N + 1)) R), H.IsLB → GlobalTheory.AbLaw.VeryAmpleBy f H s → (∀ i, s i = ∑ j, GlobalTheory.AbLaw.cst f ⊤ (a i j) • t j) → GlobalTheory.AbLaw.VeryAmpleBy f H t := by
  first | exact @GlobalTheory.veryAmpleBy_of_span | exact GlobalTheory.veryAmpleBy_of_span | (intros; apply GlobalTheory.veryAmpleBy_of_span <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVeryAmpleBasisSectionsAbelianSchemeOverDvr
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.exists_veryAmpleBy_basis_of_dvr : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ (M : LB G.left) (m : ℕ) (t₀ : Fin (m + 1) → M.Sec), M.IsLB → GlobalTheory.AbLaw.VeryAmpleBy G.hom M t₀ → ∃ (N : ℕ) (t : Fin (N + 1) → M.Sec), GlobalTheory.AbLaw.VeryAmpleBy G.hom M t ∧ ∀ u : M.Sec, ∃! c : Fin (N + 1) → W, u = ∑ j, GlobalTheory.AbLaw.cst G.hom ⊤ (c j) • t j := by
  intro W _ _ _ G _ hG M m t₀ hM hv
  have hflat : Flat G.hom := by
    haveI := hG.smooth
    infer_instance
  obtain ⟨n, t, ht⟩ := GlobalTheory.T.exists_basis_lineBundleSections_projective_over_dvr W G.left G.hom M hflat ⟨M, hM, m, t₀, hv⟩ hM
  have hne : Nonempty G.left := by
    obtain ⟨x⟩ : Nonempty (Sp W) := inferInstance
    exact ⟨(η[G]).left x⟩
  obtain ⟨x⟩ := hne
  obtain ⟨i₀, hi₀⟩ := TopologicalSpace.Opens.mem_iSup.1 (hv.1.ge (Set.mem_univ x))
  have hn : n ≠ 0 := by
    rintro rfl
    obtain ⟨c, hc, -⟩ := ht (t₀ i₀)
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hc
    rw [hc] at hi₀
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hi₀
    have hk' : x ∈ G.left.basicOpen (0 : Γ(G.left, M.U k)) := hk
    rw [Scheme.basicOpen_zero] at hk'
    exact hk'
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  choose a ha using fun i => (ht (t₀ i)).exists
  exact ⟨N, t, GlobalTheory.T.isVeryAmpleBySections_of_linear_span_combination W G.left G.hom M m N t₀ t a hM hv ha, ht⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVeryAmpleBasisSectionsAbelianSchemeOverDvrStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_veryAmple_basis_sections_abelianScheme_over_dvr : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ (M : LB G.left) (m : ℕ) (t₀ : Fin (m + 1) → M.Sec), M.IsLB → GlobalTheory.AbLaw.VeryAmpleBy G.hom M t₀ → ∃ (N : ℕ) (t : Fin (N + 1) → M.Sec), GlobalTheory.AbLaw.VeryAmpleBy G.hom M t ∧ ∀ u : M.Sec, ∃! c : Fin (N + 1) → W, u = ∑ j, GlobalTheory.AbLaw.cst G.hom ⊤ (c j) • t j := by
  first | exact @GlobalTheory.exists_veryAmpleBy_basis_of_dvr | exact GlobalTheory.exists_veryAmpleBy_basis_of_dvr | (intros; apply GlobalTheory.exists_veryAmpleBy_basis_of_dvr <;> assumption)
end

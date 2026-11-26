module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowEqSpan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionOfChg
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLiftTangentPhiLinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitarisableOfIsLocCompCusp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionDualNumberPointEqConstantCharZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueGenericFibreDualNumberPointOfModel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueGenericFibreDualNumberPointOfModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow

theorem dualMap_comp_dualMapR {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    (dualMap g).comp (Chart.dualMapR f) = dualMap (g.comp f) := by
  ext a <;> simp [dualMap, Chart.dualMapR]

theorem dualMap_comp_algebraMap {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R') :
    (dualMap g).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp g := by
  ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem isPullback_gen {V : Type} [CommRing V] [IsDomain V] {I : Ideal V} {D : DegData V I}
    {A : PolAV (Sp (FractionRing V))} {G : Over (Sp V)} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) :
    IsPullback (U.gen.inv.left ≫ pullback.fst G.hom (jK V)) A.A.hom G.hom (spMap (algebraMap V (FractionRing V))) := by
  haveI : IsIso U.gen.inv.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.inv))
  have sq : IsPullback U.gen.inv.left A.A.hom (pullback.snd G.hom (jK V)) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by simpa using Over.w U.gen.inv⟩
  simpa using sq.paste_horiz (IsPullback.of_hasPullback G.hom (jK V))

theorem vecAt_genFibre : AllV fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (y : epsR V ⟶ G),
    (∃! yA, VecAt U.toUnifPre F y yA) ∧
    (∃! v : epsR (FractionRing V) ⟶ A.A, IsVecOver (algebraMap V (FractionRing V)) (U.gen.inv.left ≫ pullback.fst G.hom (jK V)) y v) ∧
    ∀ (v : epsR (FractionRing V) ⟶ A.A) yA, IsVecOver (algebraMap V (FractionRing V)) (U.gen.inv.left ≫ pullback.fst G.hom (jK V)) y v →
      VecAt U.toUnifPre F y yA → yA ≫ (snd (TFK (R := V) F) A.A).left = spMap (dualMap (algebraMap (FractionRing V) F)) ≫ v.left := by
  intro V _ _ _ _ _ D A G _ _ _ U F _ _ y
  have hφ := isPullback_gen U.toUnifPre
  have hT : IsPullback (fst (TFK (R := V) F) A.A).left (snd (TFK (R := V) F) A.A).left (TFK (R := V) F).hom A.A.hom :=
    IsPullback.of_hasPullback _ _
  have key : ∀ (v : epsR (FractionRing V) ⟶ A.A) yA,
      IsVecOver (algebraMap V (FractionRing V)) (U.gen.inv.left ≫ pullback.fst G.hom (jK V)) y v →
      VecAt U.toUnifPre F y yA →
      yA ≫ (snd (TFK (R := V) F) A.A).left = spMap (dualMap (algebraMap (FractionRing V) F)) ≫ v.left := by
    intro v yA hv hy
    refine hφ.hom_ext ?_ ?_
    · rw [Category.assoc, hy.2, Category.assoc]
      unfold IsVecOver at hv
      rw [hv, ← Category.assoc, spMap_comp_spMap, dualMap_comp_dualMapR]
    · rw [Category.assoc, Over.w (snd _ _), ← Over.w (fst _ _), ← Category.assoc, hy.1, Category.assoc, Over.w v]
      show spMap _ ≫ spMap _ = spMap _ ≫ spMap _
      rw [spMap_comp_spMap, spMap_comp_spMap, dualMap_comp_algebraMap]
  obtain ⟨v, hv, hvu⟩ := existsUnique_isVecOver hφ y
  refine ⟨?_, ⟨v, hv, hvu⟩, key⟩
  have w : (spMap (algebraMap F (DualNumber F)) ≫ (TFK (R := V) F).hom) =
      (spMap (dualMap (algebraMap (FractionRing V) F)) ≫ v.left) ≫ A.A.hom := by
    rw [Category.assoc, Over.w v]
    show spMap _ ≫ spMap _ = spMap _ ≫ spMap _
    rw [spMap_comp_spMap, spMap_comp_spMap, dualMap_comp_algebraMap]
  have hy : VecAt U.toUnifPre F y (hT.lift _ _ w) := by
    refine ⟨hT.lift_fst _ _ w, ?_⟩
    rw [← Category.assoc, hT.lift_snd _ _ w, Category.assoc]
    unfold IsVecOver at hv
    rw [hv, ← Category.assoc, spMap_comp_spMap, dualMap_comp_dualMapR]
  refine ⟨hT.lift _ _ w, hy, fun yA h => ?_⟩
  exact hT.hom_ext ((h.1).trans (hT.lift_fst _ _ w).symm) ((key v yA hv h).trans (hT.lift_snd _ _ w).symm)

end GlobalTheory.MBLow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueGenericFibreDualNumberPointOfModelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_genericFibreDualNumberPoint_of_model : AllV fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (y : epsR V ⟶ G), (∃! yA, VecAt U.toUnifPre F y yA) ∧ (∃! v : epsR (FractionRing V) ⟶ A.A, IsVecOver (algebraMap V (FractionRing V)) (U.gen.inv.left ≫ pullback.fst G.hom (jK V)) y v) ∧ ∀ (v : epsR (FractionRing V) ⟶ A.A) yA, IsVecOver (algebraMap V (FractionRing V)) (U.gen.inv.left ≫ pullback.fst G.hom (jK V)) y v → VecAt U.toUnifPre F y yA → yA ≫ (snd (TFK (R := V) F) A.A).left = spMap (dualMap (algebraMap (FractionRing V) F)) ≫ v.left := by
  first | exact @GlobalTheory.MBLow.vecAt_genFibre | exact GlobalTheory.MBLow.vecAt_genFibre | (intros; apply GlobalTheory.MBLow.vecAt_genFibre <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterConjHalfIdeleEqProdLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterConjHalfIdeleEqProdLocal
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open Formalism.IndefR.Fin Formalism.IndefR.Fin.LevelGroupLemmas
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IdemSumChar

open _root_.Formalism.L2.JoinChr

theorem locE_sum {D : D7} {ι : Type} (s : Finset ι) (f : ι → AE D)
    (hf : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f i * f j = 0) (k : D.host.E) :
    locE D (∑ i ∈ s, f i) k = ∏ i ∈ s, locE D (f i) k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [locE]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha,
      ← ih fun i hi j hj hij => hf i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij]
    have h0 : f a * ∑ i ∈ s, f i = 0 := by
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun i hi => hf a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
        (fun h => ha (h ▸ hi))
    unfold locE
    linear_combination (-(incA D k - 1) * (incA D k - 1)) * h0

theorem char_eq_prod : ∀ (D : D7) (Q : Finset (Pl D.host.E)) (eQ : AE D), IsIdemSum eQ Q → ∀ (k : D.host.Eˣ) (y : (AE D)ˣ), (y : AE D) = Formalism.L2.JoinChr.locE D (cA D eQ) (k : D.host.E) → ∀ (c : (AE D)ˣ →* Circle) (ψ : Formalism.L2.Host.HChar D.host.E), ChrEq c ψ → ((c y : Circle) : ℂ) = ∏ P ∈ Q, ((ψ.locK (conjPl P) k : ℂˣ) : ℂ) := by
  intro D Q eQ h k y hy c ψ hψ
  classical
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := h
  have hIP : ∀ P ∈ Q, Formalism.L2.NTheta.IsIdemAt (cA D (es P)) (conjPl P) := fun P hP =>
    GlobalTheory.MovedIdem.isIdemAt_conj (hes P hP) fun _ => Iff.rfl
  let g : Pl D.host.E → AE D := fun P => if P ∈ Q then cA D (es P) else 0
  have hg : ∀ P, g P * g P = g P := fun P => by
    by_cases hP : P ∈ Q
    · simp only [g, if_pos hP]; exact (hIP P hP).1.1
    · simp only [g, if_neg hP, mul_zero]
  have horth : ∀ P ∈ Q, ∀ P' ∈ Q, P ≠ P' → g P * g P' = 0 := fun P hP P' hP' hne => by
    simp only [g, if_pos hP, if_pos hP', ← map_mul]
    rw [idem_orth (idemAt_split (hes P hP)) (hes P hP) (hes P' hP') hne, map_zero]
  have hsum : cA D (∑ P ∈ Q, es P) = ∑ P ∈ Q, g P := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun P hP => by simp only [g, if_pos hP]
  have hy' : y = ∏ P ∈ Q, locU (hg P) k := by
    apply Units.ext
    rw [hy, Units.coe_prod, hsum, locE_sum Q g horth]
    rfl
  rw [hy', map_prod]
  have hcoe : ∀ (s : Finset (Pl D.host.E)) (u : Pl D.host.E → Circle),
      (((∏ P ∈ s, u P : Circle)) : ℂ) = ∏ P ∈ s, ((u P : Circle) : ℂ) := fun s u =>
    map_prod Circle.coeHom u s
  rw [hcoe]
  refine Finset.prod_congr rfl fun P hP => ?_
  have hpl : IsPlIdem D (g P) (conjPl P) := by
    simp only [g, if_pos hP]; exact GlobalTheory.HeckeDetChar.isPlIdem (hIP P hP)
  exact hψ.2 (conjPl P) (g P) hpl k (locU (hg P) k) (locU_val _ _)

end GlobalTheory.IdemSumChar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterConjHalfIdeleEqProdLocalStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open Formalism.IndefR.Fin Formalism.IndefR.Fin.LevelGroupLemmas
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeCharacter_conjHalfIdele_eq_prod_local : ∀ (D : D7) (Q : Finset (Pl D.host.E)) (eQ : AE D), IsIdemSum eQ Q → ∀ (k : D.host.Eˣ) (y : (AE D)ˣ), (y : AE D) = Formalism.L2.JoinChr.locE D (cA D eQ) (k : D.host.E) → ∀ (c : (AE D)ˣ →* Circle) (ψ : Formalism.L2.Host.HChar D.host.E), ChrEq c ψ → ((c y : Circle) : ℂ) = ∏ P ∈ Q, ((ψ.locK (conjPl P) k : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.IdemSumChar.char_eq_prod | exact GlobalTheory.IdemSumChar.char_eq_prod | (intros; apply GlobalTheory.IdemSumChar.char_eq_prod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVarietyCompactifyingConnectedComponent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVarietyCompactifyingConnectedComponent
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.CompactVar

theorem geometricallyConnected_of_denseRange {F : Type} [Field F] {U V : Scheme.{0}} (g : U ⟶ V) (p : V ⟶ Sp F)
    (hg : Dense (Set.range g)) [GeometricallyConnected (g ≫ p)] : GeometricallyConnected p := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x => ?_⟩
  have h1 : ConnectedSpace ↥(pullback (g ≫ p) x) :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback _ _)
  rw [← (pullbackRightPullbackFstIso p x g).hom.homeomorph.connectedSpace_iff] at h1
  have ho : UniversallyOpen x := inferInstance
  have h2 : Dense (Set.range (pullback.snd g (pullback.fst p x))) := by
    rw [Scheme.Pullback.range_snd]
    exact hg.preimage (pullback.fst p x).isOpenMap
  rw [connectedSpace_iff_univ, ← h2.closure_eq]
  exact (isConnected_range (Scheme.Hom.continuous _)).closure

theorem exists_var : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : (Xo.XF c).Opens), SmoothOfRelativeDimension D.dim (genStr Y) → IsClosed (U : Set (Xo.XF c)) → GeometricallyConnected (U.ι ≫ toF Xo c) → ∃ (B : GlobalTheory.ProjVar.Var c.F) (io : B.X ⟶ gen Y), IsOpenImmersion io ∧ Set.range io = compactOf Y U ∧ io ≫ genStr Y = B.str := by
  intro E _ _ _ H D l Xo c O _ β Z U hsm _ hU
  have hS : Smooth (genStr Z) := SmoothOfRelativeDimension.smooth D.dim _
  have := isProper_genStr Z
  have : IsLocallyNoetherian (gen Z) := LocallyOfFiniteType.isLocallyNoetherian (genStr Z)
  have : CompactSpace (gen Z) := QuasiCompact.compactSpace_of_compactSpace (genStr Z)
  have : IsNoetherian (gen Z) := {}
  have := Z.jQ_open
  have hcc := fun z : gen Z => GlobalTheory.ShFam.PtComp.connectedComponent_mem
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
    (fun W hW W' hW' => GlobalTheory.ShFam.PtComp.disjoint_of_smooth (genStr Z) hS W W' hW hW') z
  have hconn : ConnectedSpace U.toScheme :=
    GeometricallyConnected.connectedSpace_of_subsingleton (U.ι ≫ toF Xo c)
  let π : U.toScheme ⟶ gen Z := U.ι ≫ Z.jQ
  have hπ : Set.range π = Z.jQ '' U := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
  let z : gen Z := π (Classical.arbitrary _)
  let V : (gen Z).Opens := ⟨connectedComponent z, (hcc z).2⟩
  have hred : IsReduced (gen Z) := by
    have := GlobalTheory.isNormalScheme_of_smooth (genStr Z)
    exact GlobalTheory.IsNormalScheme.isReduced
  have hproj : IsProjOver (genStr Z) := (GlobalTheory.ProjSpace.points_and_stability (R := O) (N := 0)).2.2.1 c.F β Z.X Z.s Z.proj
  have : IrreducibleSpace V.toScheme := Subtype.irreducibleSpace (hcc z).1.1
  have hcl : IsClosedImmersion V.ι := IsClosedImmersion.of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι]; exact isClosed_connectedComponent)
  have hp : IsProjOver (V.ι ≫ genStr Z) :=
    (GlobalTheory.ProjSpace.points_and_stability (R := c.F) (N := 0)).2.2.2.1 _ _ _ _ hcl hproj
  have hsd : SmoothOfRelativeDimension D.dim (V.ι ≫ genStr Z) := by
    have h : SmoothOfRelativeDimension (0 + D.dim) (V.ι ≫ genStr Z) := inferInstance
    simpa using h
  have hr : Set.range π ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    exact (isPreconnected_range π.continuous).subset_connectedComponent ⟨_, rfl⟩
  let g : U.toScheme ⟶ V.toScheme := IsOpenImmersion.lift V.ι π hr
  have hg : g ≫ V.ι = π := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (g ≫ V.ι) := by rw [hg]; infer_instance
  have : IsOpenImmersion g := IsOpenImmersion.of_comp g V.ι
  have hd : Dense (Set.range g) := g.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)
  have : GeometricallyConnected (g ≫ V.ι ≫ genStr Z) := by
    rw [reassoc_of% hg, Category.assoc, Z.jQ_over]
    exact hU
  have : GeometricallyConnected (V.ι ≫ genStr Z) := geometricallyConnected_of_denseRange g _ hd
  obtain ⟨X, ε, -, hs⟩ := GlobalTheory.ProjVar.Var.exists_iso _ D.dim hp
  refine ⟨X, ε.inv ≫ V.ι, inferInstance, ?_, ?_⟩
  · rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, ε.inv.surjective.range_eq, Set.image_univ,
      compactOf, ← hπ, ← hg, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      V.ι.isClosedEmbedding.closure_image_eq, hd.closure_eq, Set.image_univ]
  · rw [Category.assoc, ← hs, Iso.inv_hom_id_assoc]

end GlobalTheory.CompactVar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVarietyCompactifyingConnectedComponentStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_variety_compactifying_connected_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : (Xo.XF c).Opens), SmoothOfRelativeDimension D.dim (genStr Y) → IsClosed (U : Set (Xo.XF c)) → GeometricallyConnected (U.ι ≫ toF Xo c) → ∃ (B : GlobalTheory.ProjVar.Var c.F) (io : B.X ⟶ gen Y), IsOpenImmersion io ∧ Set.range io = compactOf Y U ∧ io ≫ genStr Y = B.str := by
  first | exact @GlobalTheory.CompactVar.exists_var | exact GlobalTheory.CompactVar.exists_var | (intros; apply GlobalTheory.CompactVar.exists_var <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationSubringDedekindOpenImmersion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationSubringDedekindOpenImmersion
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CoeffValuation

theorem mem_of_forall_natCast {L : Type} [Field L] [NumberField L] (W : ValuationSubring L)
    (h : ∀ n : ℕ, n ≠ 0 → (n : L) ∉ W.nonunits) (x : L) : x ∈ W := by
  have halg : IsAlgebraic ℤ x := (IsFractionRing.isAlgebraic_iff ℤ ℚ L).mpr (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨m, hm, hint⟩ := halg.exists_integral_multiple
  have h1 : m • x ∈ W := by
    have h : IsIntegral W (m • x) := hint.tower_top
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := W) (K := L)).mp h
    exact hy ▸ y.2
  have h2 : ((m.natAbs : ℕ) : L)⁻¹ ∈ W := by
    have := h m.natAbs (Int.natAbs_ne_zero.mpr hm)
    rw [ValuationSubring.mem_nonunits_iff_or] at this
    by_contra hc
    exact this (Or.inr hc)
  have hm' : (m : L) ≠ 0 := Int.cast_ne_zero.mpr hm
  have h3 : (m : L)⁻¹ ∈ W := by
    rcases Int.natAbs_eq m with e | e
    · rw [e, Int.cast_natCast]; exact h2
    · rw [e, Int.cast_neg, Int.cast_natCast, inv_neg]; exact W.neg_mem _ h2
  have : x = (m : L)⁻¹ * (m • x) := by
    rw [zsmul_eq_mul, inv_mul_cancel_left₀ hm']
  rw [this]
  exact W.mul_mem _ _ h3 h1

theorem dedekind_and_away {L : Type} [Field L] [NumberField L] (W : ValuationSubring L) :
    IsDedekindDomain W ∧ ∃ π : W, IsLocalization.Away π L := by
  by_cases h : ∃ n : ℕ, n ≠ 0 ∧ (n : L) ∈ W.nonunits
  · obtain ⟨n, hn, hW⟩ := h
    have := (GlobalTheory.isDiscreteValuationRing_and_finite_residueField_of_numberField W hn hW).1
    refine ⟨inferInstance, ?_⟩
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W
    refine ⟨π, ?_⟩
    refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
    · rintro ⟨_, k, rfl⟩
      exact IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective W L)).mpr (pow_ne_zero k hπ.ne_zero))
    · intro z
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := W) z
      have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
      obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hπ
      refine ⟨⟨a * (u⁻¹ : Wˣ), ⟨π ^ k, k, rfl⟩⟩, ?_⟩
      have hb1 : algebraMap W L (u * π ^ k) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective W L)).mpr hb0
      rw [div_mul_eq_mul_div, div_eq_iff hb1, ← map_mul, ← map_mul]
      congr 1
      rw [mul_assoc, Units.inv_mul_cancel_left]
    · intro a b hab
      exact ⟨1, by rw [IsFractionRing.injective W L hab]⟩
  · have hall : ∀ x : L, x ∈ W := mem_of_forall_natCast W fun n hn hW => h ⟨n, hn, hW⟩
    have hbij : Function.Bijective (algebraMap W L) :=
      ⟨IsFractionRing.injective W L, fun x => ⟨⟨x, hall x⟩, rfl⟩⟩
    have hF : IsField W := (RingEquiv.ofBijective _ hbij).toMulEquiv.isField (Field.toIsField L)
    have : IsPrincipalIdealRing W := hF.isPrincipalIdealRing
    exact ⟨inferInstance, 1, IsLocalization.away_of_isUnit_of_bijective L isUnit_one hbij⟩

theorem isDedFrac_and_isOpenImmersion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (W : ValuationSubring c.F), GlobalTheory.Models.IsDedFrac W.subtype ∧ IsOpenImmersion (spMap W.subtype) := by
  intro E _ _ _ H l c W
  have := c.fin
  have : NumberField c.F := NumberField.mk
  obtain ⟨hD, π, hπ⟩ := dedekind_and_away W
  exact ⟨⟨⟨inferInstance, hD⟩, inferInstance, (inferInstance : IsFractionRing W c.F)⟩,
    IsOpenImmersion.of_isLocalization (S := c.F) π⟩

end GlobalTheory.CoeffValuation
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationSubringDedekindOpenImmersionStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_subring_dedekind_open_immersion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (W : ValuationSubring c.F), GlobalTheory.Models.IsDedFrac W.subtype ∧ IsOpenImmersion (spMap W.subtype) := by
  first | exact @GlobalTheory.CoeffValuation.isDedFrac_and_isOpenImmersion | exact GlobalTheory.CoeffValuation.isDedFrac_and_isOpenImmersion | (intros; apply GlobalTheory.CoeffValuation.isDedFrac_and_isOpenImmersion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericThetaExpansionScalarNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericThetaExpansionScalarNeZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.KeyScalarNe

theorem polAVSectionInverseImage_ne_zero {K : Type} [Field K] (P : PolAV (Sp K)) (T : Over (Sp K)) (t₀ : T.left) (s : P.L.Sec)
    (hs : ∃ p, p ∈ nonzeroLocus s) (t : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T)) (h : IsPolAVSectionInverseImage P T s t) :
    t ≠ 0 := by
  rintro rfl
  obtain ⟨z, hz⟩ := hs
  obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hz
  have hpb : IsPullback (fst T P.A).left (snd T P.A).left T.hom P.A.hom := by
    rw [Over.fst_left, Over.snd_left]
    exact IsPullback.of_hasPullback _ _
  have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  obtain ⟨y, -, hy⟩ := Scheme.exists_preimage_of_isPullback hpb t₀ z (Subsingleton.elim _ _)
  have hle : (LPow P.A P.L ((1 : ℕ) : ℤ) T).U (fun _ => k) ≤ (snd T P.A).left ⁻¹ᵁ P.L.U k :=
    LB.wchart_le P.L _ (fun _ : Fin 1 => k) 0
  have hyU : y ∈ (LPow P.A P.L ((1 : ℕ) : ℤ) T).U (fun _ => k) := by
    show y ∈ LB.wchart P.L _ _
    refine Set.mem_iInter.2 fun _ => ?_
    show (snd T P.A).left y ∈ (P.L.U k : Set P.A.left)
    rw [hy]; exact hk
  subst hy
  have e := congrArg (gs (𝟙 _) y _) (h k hle)
  rw [gs_appLE _ _ _ hle (𝟙 _) y hyU, Category.id_comp, gs_stalkMap (snd T P.A).left y _ hk] at e
  have u' := u.map ((snd T P.A).left.stalkMap y).hom
  rw [← e] at u'
  have h0 : gs (𝟙 _) y ((LPow P.A P.L ((1 : ℕ) : ℤ) T).U (fun _ => k)) ((0 : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T)).f (fun _ => k)) = 0 := by
    have z0 : (0 : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T)).f (fun _ => k) = 0 := rfl
    rw [z0, gs_eq _ y _ hyU, map_zero, map_zero]
  rw [h0] at u'
  exact not_isUnit_zero u'

end GlobalTheory.KeyScalarNe

theorem GlobalTheory.KeyScalarNe.scalar_ne_zero : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V))
    (x : KeyIn (FractionRing V)) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ (U : Unif (IsLocalRing.maximalIdeal V) D x.P G) (w₀ : GlobalTheory.UT.W0 U.toUnifPre), GlobalTheory.UT.NormW U.toUnifPre w₀ x.rig →
    ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C]
      [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C →
    ∀ (N : NumD C) (ν : NumOf D.toPre C N) (th : GlobalTheory.UT.SecA x.P C 1) (ϑ : Fam D.toPre C 1) (c : C),
      IsPolAVSectionInverseImage x.P (TFK (R := V) C) x.th th → U.ExpandsF C 1 w₀ th ϑ → ν.FamV ϑ (c • N.vth) → c ≠ 0 := by
  intro V _ _ _ _ _ D x G _ _ _ U w₀ hw C _ _ _ _ _ _ _ N ν th ϑ c hon hex hv
  rintro rfl
  rw [zero_smul] at hv
  have h0 : ν.FamV (0 : Fam D.toPre C 1) 0 := by
    have := GlobalTheory.WeilValues.famV_smul ν hv 0
    rwa [zero_smul, zero_smul] at this
  have hϑ : ϑ = 0 := GlobalTheory.Ex.FamVal.famV_inj ν hv h0
  obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF GlobalTheory.allSixLaws.1.globalFns U C (k := 1) le_rfl w₀ hw.1
  have ht : th = 0 := by
    have h1 := (he th ϑ).1 hex
    rw [hϑ] at h1
    exact e.map_eq_zero_iff.1 h1
  obtain ⟨z, -, hz⟩ := x.th_ne (IsLocalRing.closedPoint _)
  exact GlobalTheory.KeyScalarNe.polAVSectionInverseImage_ne_zero x.P (TFK (R := V) C) (IsLocalRing.closedPoint C) x.th ⟨z, hz⟩ th hon ht
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericThetaExpansionScalarNeZeroStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericThetaExpansion_scalar_ne_zero : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V))
    (x : KeyIn (FractionRing V)) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ (U : Unif (IsLocalRing.maximalIdeal V) D x.P G) (w₀ : GlobalTheory.UT.W0 U.toUnifPre), GlobalTheory.UT.NormW U.toUnifPre w₀ x.rig →
    ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C]
      [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C →
    ∀ (N : NumD C) (ν : NumOf D.toPre C N) (th : GlobalTheory.UT.SecA x.P C 1) (ϑ : Fam D.toPre C 1) (c : C),
      IsPolAVSectionInverseImage x.P (TFK (R := V) C) x.th th → U.ExpandsF C 1 w₀ th ϑ → ν.FamV ϑ (c • N.vth) → c ≠ 0 := by
  first | exact @GlobalTheory.KeyScalarNe.scalar_ne_zero | exact GlobalTheory.KeyScalarNe.scalar_ne_zero | (intros; apply GlobalTheory.KeyScalarNe.scalar_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationValuesNormsEqUniformizerZpow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationValuesNormsEqUniformizerZpow
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.MBLow.DiscNorm

theorem norm_eq_zpow {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
    {C : Type} [NormedField C] (f : FractionRing V →+* C) (hf : ∀ r : V, ‖f (algebraMap V _ r)‖ ≤ 1)
    {k : FractionRing V} (hk : k ≠ 0) : ∃ n : ℤ, ‖f k‖ = ‖f (algebraMap V _ ϖ)‖ ^ n := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := V) k
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by rintro rfl; simp at hk
  set g : V →+* C := f.comp (algebraMap V _)
  have key : ∀ x : V, x ≠ 0 → ∃ m : ℕ, ‖g x‖ = ‖g ϖ‖ ^ m := fun x hx => by
    obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
    refine ⟨m, ?_⟩
    rw [map_mul, norm_mul, map_pow, norm_pow, GlobalTheory.Ex.IntVal.norm_unit g hf u.isUnit, _root_.one_mul]
  obtain ⟨ma, ea⟩ := key a ha0
  obtain ⟨mb, eb⟩ := key b hb0
  have ht : ‖g ϖ‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    intro h
    exact hϖ.ne_zero (IsFractionRing.injective V (FractionRing V) (f.injective (by simpa [g] using h)))
  refine ⟨(ma : ℤ) - mb, ?_⟩
  show ‖f (algebraMap V _ a / algebraMap V _ b)‖ = ‖g ϖ‖ ^ ((ma : ℤ) - mb)
  rw [map_div₀, norm_div]
  show ‖g a‖ / ‖g b‖ = _
  rw [zpow_sub₀ ht, zpow_natCast, zpow_natCast]
  exact congrArg₂ (· / ·) ea eb

theorem vF_eq_alg {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]
    {X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → ((TK R).left ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (J : (Sp F ⟶ X) → L.ι)
    (hW : ⊤ ≤ jFK (R := R) F ⁻¹ᵁ LB.wchart L φ (fun k => J (jFK (R := R) F ≫ φ k))) :
    ∃ k : FractionRing R, k ≠ 0 ∧ vF t (jFK (R := R) F) J = algebraMap (FractionRing R) F k := by
  set W := LB.wchart L φ (fun k => J (jFK (R := R) F ≫ φ k))
  have h' : ⊤ ≤ (𝟙 (TK R).left) ⁻¹ᵁ W := by
    intro x _
    obtain ⟨y⟩ : Nonempty (Sp F) := inferInstance
    have hy := hW (Set.mem_univ y)
    have hs : Subsingleton (PrimeSpectrum (FractionRing R)) := inferInstance
    have : (jFK (R := R) F).base y = x := @Subsingleton.elim (PrimeSpectrum (FractionRing R)) hs _ _
    rw [← this]; exact hy
  refine ⟨GlobalTheory.Ex.IntVal.evR (𝟙 _) W h' (t.s _).val, ?_, ?_⟩
  · exact ((Units.isUnit _).map _).ne_zero
  · have := GlobalTheory.Ex.IntVal.valF_comp (algebraMap (FractionRing R) F) (𝟙 (TK R).left) W h' (t.s _).val
    have e : spMap (algebraMap (FractionRing R) F) ≫ 𝟙 (TK R).left = jFK (R := R) F := Category.comp_id _
    rw [e] at this
    exact this

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN → ‖ν.rg‖ = 1 ∧ ∀ χ, ∃ n : ℤ, ‖(N.ψ χ : C)‖ = ‖toF V C ϖ‖ ^ n := by
  intro V _ _ _ ϖ hϖ D C _ _ _ hC N ν hν
  obtain ⟨S, hS, hI⟩ := hν
  let f : V →+* C := toF V C
  let g : V →+* S := f.codRestrict S fun x => (hS _).2 (hC.1 x)
  have hg : spMap S.subtype ≫ spMap g = (TF (R := V) C).hom := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]; rfl
  have hrig : ‖ν.rg‖ = 1 := GlobalTheory.Ex.IntVal.norm_vF hS hI _ _ (spMap g) hg fun _ =>
      (congrArg ((TF (R := V) C).hom ≫ ·) (Over.w η[D.toPre.P.A])).trans (Category.comp_id _)
  refine ⟨hrig, fun χ => ?_⟩
  have hW : ⊤ ≤ jFK (R := V) C ⁻¹ᵁ LB.wchart D.toPre.P.L (fun _ : PUnit => D.toPre.xK (ν.eX χ))
      (fun _ => ν.J (jFK (R := V) C ≫ D.toPre.xK (ν.eX χ))) := fun y hy => Set.mem_iInter.2 fun _ => ν.good _ hy
  obtain ⟨k, hk, ek⟩ := vF_eq_alg (D.toPre.psi (ν.eX χ)) ν.J hW
  obtain ⟨n, hn⟩ := norm_eq_zpow hϖ (algebraMap (FractionRing V) C) hC.1 hk
  refine ⟨n, ?_⟩
  rw [ν.ψ_eq, norm_mul]
  change _ * ‖ν.rg‖ = _
  rw [hrig, _root_.mul_one, ek, hn]
  rfl

end GlobalTheory.MBLow.DiscNorm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationValuesNormsEqUniformizerZpowStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degenerationValues_norms_eq_uniformizer_zpow : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN → ‖ν.rg‖ = 1 ∧ ∀ χ, ∃ n : ℤ, ‖(N.ψ χ : C)‖ = ‖toF V C ϖ‖ ^ n := by
  first | exact @GlobalTheory.MBLow.DiscNorm.main | exact GlobalTheory.MBLow.DiscNorm.main | (intros; apply GlobalTheory.MBLow.DiscNorm.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffectiveCartierDivisorPullbackOfDominant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffectiveCartierDivisorPullbackOfDominant
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
open GlobalTheory.Discrepancy GlobalTheory.QCoh

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Cartier.PullDominant

variable {M W : Scheme.{0}} [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f]

theorem unitAt_map {x : M} {u : W.functionField} (h : UnitAt (f x) u) :
    UnitAt x (GlobalTheory.functionFieldMap f u) := by
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨f.stalkMap x a, ha.map _, (GlobalTheory.functionFieldMap_algebraMap f x a).symm⟩

theorem regAt_map {x : M} {u : W.functionField} (h : RegAt (f x) u) :
    RegAt x (GlobalTheory.functionFieldMap f u) := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨f.stalkMap x a, (GlobalTheory.functionFieldMap_algebraMap f x a).symm⟩

abbrev unitsMap : W.functionFieldˣ →* M.functionFieldˣ := Units.map (GlobalTheory.functionFieldMap f).toMonoidHom

theorem germOf_map_eq {D₀ : CartierDiv W} {x : M} {g g' : W.functionFieldˣ}
    (h : D₀.IsEqn (f x) g) (h' : D₀.IsEqn (f x) g') :
    germOf x (unitsMap f g) = germOf x (unitsMap f g') := by
  rw [germOf_eq_iff]
  have := unitAt_map f (h.iff_unitAt.1 h')
  simpa [map_div₀] using this

def pullGerm (D₀ : CartierDiv W) (x : M) : Germ x :=
  germOf x (unitsMap f (D₀.exists_isEqn (f x)).choose)

theorem pullGerm_eq {D₀ : CartierDiv W} {x : M} {g : W.functionFieldˣ} (h : D₀.IsEqn (f x) g) :
    pullGerm f D₀ x = germOf x (unitsMap f g) :=
  germOf_map_eq f (D₀.exists_isEqn (f x)).choose_spec h

def pull (D₀ : CartierDiv W) : CartierDiv M :=
  show cartierGroup M from ⟨pullGerm f D₀, fun x => by
    obtain ⟨U, hU, g, hg⟩ := D₀.exists_isEqn_nhds (f x)
    exact ⟨f ⁻¹ᵁ U, hU, unitsMap f g, fun y hy => pullGerm_eq f (hg (f y) hy)⟩⟩

theorem isEqn_pull {D₀ : CartierDiv W} {x : M} {g : W.functionFieldˣ} (h : D₀.IsEqn (f x) g) :
    (pull f D₀).IsEqn x (unitsMap f g) :=
  pullGerm_eq f h

theorem eff_pull {D₀ : CartierDiv W} (hD : D₀.Eff) : (pull f D₀).Eff := by
  intro x
  obtain ⟨g, hg⟩ := D₀.exists_isEqn (f x)
  refine ⟨unitsMap f g, isEqn_pull f hg, ?_⟩
  rw [one_mul]
  exact regAt_map f (CartierDiv.eff_iff.1 hD _ _ hg)

end GlobalTheory.Cartier.PullDominant


open GlobalTheory.Cartier.PullDominant in
theorem GlobalTheory.Cartier.exists_pull_dominant :
    ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f] (D₀ : CartierDiv W), D₀.Eff → ∃ D₁ : CartierDiv M, D₁.Eff ∧ ∀ x g, D₀.IsEqn (f x) g → D₁.IsEqn x (Units.map (GlobalTheory.functionFieldMap f).toMonoidHom g) := by
  intro M W _ _ f _ D₀ hD
  exact ⟨pull f D₀, eff_pull f hD, fun x g h => isEqn_pull f h⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffectiveCartierDivisorPullbackOfDominantStatement
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
open GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_effective_cartierDivisorPullback_of_dominant : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f] (D₀ : CartierDiv W), D₀.Eff → ∃ D₁ : CartierDiv M, D₁.Eff ∧ ∀ x g, D₀.IsEqn (f x) g → D₁.IsEqn x (Units.map (GlobalTheory.functionFieldMap f).toMonoidHom g) := by
  first | exact @GlobalTheory.Cartier.exists_pull_dominant | exact GlobalTheory.Cartier.exists_pull_dominant | (intros; apply GlobalTheory.Cartier.exists_pull_dominant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLiftTangentUniqueness
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLiftTangentUniqueness
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj MonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ConstDeform

theorem objMap_const : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (q : A'.left ⟶ A.left), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A Xo.univ.t.G y.x π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π → i ≫ q = 𝟙 _ → IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q → ∀ o : Obj Dw l (baseKA l) (x' ≫ Xo.s), Nonempty (ObjMap o Xo.univ x') → Nonempty (ObjMap o Xo.univ (constPt x')) := by
  intro hP hGD E _ _ _ H Dw l Xo c K _ _ y x' hpq hT A _ A' _ π π' i q hi hπ hπ' hiπ hiq hq o ⟨m⟩
  have hw : m.cm.F ≫ Xo.univ.t.G.hom = o.t.G.hom ≫ x' := m.cart.1.w
  let g : o.t.G.left ⟶ A'.left := hπ'.1.lift m.cm.F o.t.G.hom hw
  have hg : g ≫ π' = m.cm.F := hπ'.1.lift_fst _ _ _
  have hgw : g ≫ A'.hom = o.t.G.hom := hπ'.1.lift_snd _ _ _
  have hgc : IsGrpPullback o.t.G A' (𝟙 _) g :=
    hπ'.cancel (m.cart.congr (Category.id_comp _).symm hg.symm) (by rw [hgw, Category.comp_id])
  have hred : spMap (algebraMap K (DualNumber K)) ≫ y.x = constPt x' := by
    rw [← hT.2]; rfl
  have hF : IsGrpPullback o.t.G Xo.univ.t.G (constPt x') (g ≫ q ≫ π) :=
    (hgc.comp (hq.comp hπ)).congr (by rw [Category.id_comp, hred]) rfl
  haveI : CharZero K := (RingHom.charZero_iff (algebraMap c.F K).injective).1 inferInstance
  have hgq := hgc.comp hq
  have hcomm : ∀ (T : Over (Sp K)) (x y : T ⟶ A), x * y = y * x := by
    intro T x y
    apply Over.OverMorphism.ext
    apply hπ.1.hom_ext
    · have e1 := hπ.2 T x y (pushPt hπ.1.w x) (pushPt hπ.1.w y) rfl rfl
      have e2 := hπ.2 T y x (pushPt hπ.1.w y) (pushPt hπ.1.w x) rfl rfl
      rw [← e1, ← e2, _root_.mul_comm]
    · rw [Over.w (x * y), Over.w (y * x)]

  have key : ∀ (σ : 𝟙_ (Over (Sp (DualNumber K))) ⟶ o.t.G) (τ : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G) (n : ℕ),
      0 < n → σ ^ n = 1 → σ.left ≫ m.cm.F = x' ≫ τ.left →
      σ.left ≫ (g ≫ q ≫ π) = constPt x' ≫ τ.left := by
    intro σ τ n hn hσ hστ
    let u := pushHom hgq (𝟙_ (Over (Sp (DualNumber K)))) σ
    have hu : u ^ n = 1 := by rw [← map_pow, hσ, map_one]
    have e := GlobalTheory.T.torsion_dualNumber_point_eq_constant_charZero K A _ (by simp) (hcomm _) u n hn hu
    have hul : u.left = σ.left ≫ g ≫ q := by
      show σ.left ≫ (g ≫ q) = _; rfl
    rw [hul] at e
    let w := spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ σ.left ≫ g
    have hw' : w ≫ A'.hom = 𝟙 _ ≫ GlobalTheory.DeRham.epsRed K := by
      simp only [w, Category.assoc, hgw, Category.id_comp]
      rw [Over.w σ]; rfl
    let s₀ := hi.1.lift w (𝟙 _) hw'
    have hs₀ : s₀ ≫ i = w := hi.1.lift_fst _ _ _
    calc σ.left ≫ (g ≫ q ≫ π) = (σ.left ≫ g ≫ q) ≫ π := by simp only [Category.assoc]
      _ = (spMap (algebraMap K (DualNumber K)) ≫ w ≫ q) ≫ π := by rw [e]; simp only [w, Category.assoc]
      _ = spMap (algebraMap K (DualNumber K)) ≫ s₀ ≫ i ≫ π' := by
          rw [← hs₀]; simp only [Category.assoc]; rw [reassoc_of% hiq, hiπ]
      _ = spMap (algebraMap K (DualNumber K)) ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ σ.left ≫ m.cm.F := by
          rw [reassoc_of% hs₀]; simp only [w, Category.assoc, hg]
      _ = constPt x' ≫ τ.left := by rw [hστ]; rfl
  have hpow : ∀ (f : Dw.La → (𝟙_ (Over (Sp (DualNumber K))) ⟶ o.t.G)), (∀ a b, f (a + b) = f a * f b) →
      ∀ (n : ℕ) a, f (n • a) = f a ^ n := by
    intro f hf n a
    induction n with
    | zero =>
      have h0 := hf 0 0
      rw [add_zero] at h0
      rw [zero_smul, pow_zero]
      exact mul_left_cancel (h0.symm.trans (_root_.mul_one _).symm)
    | succ n ih => rw [succ_nsmul, hf, ih, pow_succ]
  have hM : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb := by
    have h1 : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]; exact Ideal.mem_span_singleton_self _
    exact Ideal.mul_le_left (I := l.Mb) (J := l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) h1
  exact ⟨{
    cm := cubeMapOf hF
    cart := hF
    base := rfl
    act := GlobalTheory.T.group_lift_tangent_Phi_linear hP hGD E H Dw l Xo c K y x' hpq hT A A' π π' i q hi hπ hπ' hiπ hiq hq o m g hg hgw hF
    lin := GlobalTheory.T.group_lift_tangent_Phi_additive hP hGD E H Dw l Xo c K y x' hpq hT A A' π π' i q hi hπ hπ' hiπ hiq hq o m g hg hgw hF
    eta := fun a => key (o.eta a) (Xo.univ.eta a) l.M (by have := l.three_le; omega)
      (by rw [← hpow _ o.eta_add]; exact o.eta_ker _ (by
        rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]; exact Submodule.smul_mem_smul hM Submodule.mem_top))
      (m.eta a)
    etaA := fun a => key (o.etaA a) (Xo.univ.etaA a) l.A l.A_pos
      (by rw [← hpow _ o.etaA_add]; exact o.etaA_ker a) (m.etaA a) }⟩

end GlobalTheory.ConstDeform
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLiftTangentUniquenessStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.group_lift_tangent_uniqueness : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (q : A'.left ⟶ A.left), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A Xo.univ.t.G y.x π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π → i ≫ q = 𝟙 _ → IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q → ∀ o : Obj Dw l (baseKA l) (x' ≫ Xo.s), Nonempty (ObjMap o Xo.univ x') → Nonempty (ObjMap o Xo.univ (constPt x')) := by
  first | exact @GlobalTheory.ConstDeform.objMap_const | exact GlobalTheory.ConstDeform.objMap_const | (intros; apply GlobalTheory.ConstDeform.objMap_const <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitOfCocycleRightActionCharZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitOfCocycleRightActionCharZero
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

namespace GlobalTheory

theorem exists_unit_of_cocycle_rightAction_charZero :
    ∀ (K : Type) [Field K] [CharZero K] (Γ : Type) [Group Γ] [Finite Γ] (σ : Γ → K →+* K),
    (∀ γ δ a, σ (γ * δ) a = σ δ (σ γ a)) → ∀ (c : Γ → Kˣ),
    (∀ γ δ, (c (γ * δ) : K) = σ δ (c γ) * c δ) → (∀ γ, (∀ a, σ γ a = a) → c γ = 1) →
    ∃ f : Kˣ, ∀ γ, σ γ f = c γ * f := by
  intro K _ _ Γ _ _ σ hσ c hc htriv
  classical
  haveI := Fintype.ofFinite Γ
  have h1 : ∀ a, σ 1 a = a := by
    intro a
    have e := hσ 1 1 a
    rw [mul_one] at e
    exact (σ 1).injective e.symm
  have key : ∀ γ δ, (σ δ (c γ : K))⁻¹ = (c δ : K) * ((c (γ * δ) : K))⁻¹ := by
    intro γ δ
    rw [hc γ δ, mul_inv, mul_left_comm, mul_inv_cancel₀ (Units.ne_zero _), mul_one]
  let F : K → K := fun b => ∑ γ, ((c γ : K))⁻¹ * σ γ b
  have hF : ∀ b δ, σ δ (F b) = c δ * F b := by
    intro b δ
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [F, map_sum, map_mul, map_inv₀, Finset.mul_sum]
    apply Fintype.sum_equiv (Equiv.mulRight δ)
    intro γ
    simp only [Equiv.coe_mulRight]
    rw [key γ δ, hσ]
    ring
  have hex : ∃ b, F b ≠ 0 := by
    by_contra hno
    push_neg at hno
    let φ : Γ → (K →* K) := fun γ => (σ γ : K →* K)
    let s : Finset (K →* K) := Finset.univ.image φ
    let g : (K →* K) → K := fun ψ => ∑ γ ∈ Finset.univ.filter (fun γ => φ γ = ψ), ((c γ : K))⁻¹
    have hli := linearIndependent_monoidHom K K
    have hsum : ∑ ψ ∈ s, g ψ • (ψ : K → K) = 0 := by
      funext b
      rw [Finset.sum_apply, Pi.zero_apply, ← hno b]
      simp only [Pi.smul_apply, smul_eq_mul, g, Finset.sum_mul]
      have hterm : ∀ ψ ∈ s, ∑ i ∈ Finset.univ.filter (fun γ => φ γ = ψ), ((c i : K))⁻¹ * ψ b
          = ∑ i ∈ Finset.univ.filter (fun γ => φ γ = ψ), ((c i : K))⁻¹ * σ i b := fun ψ _ =>
        Finset.sum_congr rfl fun γ hγ => by rw [← (Finset.mem_filter.mp hγ).2]; rfl
      rw [Finset.sum_congr rfl hterm, Finset.sum_fiberwise_of_maps_to
        (fun γ _ => Finset.mem_image_of_mem φ (Finset.mem_univ γ))]
    have hz := linearIndependent_iff'.mp hli s g hsum (φ 1)
      (Finset.mem_image_of_mem φ (Finset.mem_univ 1))
    have hterm : ∀ γ ∈ Finset.univ.filter (fun γ => φ γ = φ 1), ((c γ : K))⁻¹ = 1 := by
      intro γ hγ
      rw [Finset.mem_filter] at hγ
      have hid : ∀ a, σ γ a = a := fun a => (DFunLike.congr_fun hγ.2 a).trans (h1 a)
      rw [htriv γ hid]
      simp
    have hcard : g (φ 1) = ((Finset.univ.filter (fun γ => φ γ = φ 1)).card : K) := by
      simp only [g]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hcard, Nat.cast_eq_zero, Finset.card_eq_zero] at hz
    have hmem : (1 : Γ) ∈ Finset.univ.filter (fun γ => φ γ = φ 1) := by simp
    rw [hz] at hmem
    simp at hmem
  obtain ⟨b, hb⟩ := hex
  refine ⟨Units.mk0 (F b) hb, fun γ => ?_⟩
  simp only [Units.val_mk0]
  exact hF b γ

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitOfCocycleRightActionCharZeroStatement
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
theorem _root_.GlobalTheory.T.hilbert90_finite_rightAction_charZero_field : ∀ (K : Type) [Field K] [CharZero K] (Γ : Type) [Group Γ] [Finite Γ] (σ : Γ → K →+* K),
    (∀ γ δ a, σ (γ * δ) a = σ δ (σ γ a)) → ∀ (c : Γ → Kˣ),
    (∀ γ δ, (c (γ * δ) : K) = σ δ (c γ) * c δ) → (∀ γ, (∀ a, σ γ a = a) → c γ = 1) →
    ∃ f : Kˣ, ∀ γ, σ γ f = c γ * f := by
  first | exact @GlobalTheory.exists_unit_of_cocycle_rightAction_charZero | exact GlobalTheory.exists_unit_of_cocycle_rightAction_charZero | (intros; apply GlobalTheory.exists_unit_of_cocycle_rightAction_charZero <;> assumption)
end
end

module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFrameVec
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPointsOpenIntegralCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsIso
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralNthRootTestModelPoint
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianTorsionFiniteAndMulNSurjective

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TriangularSpanCoeffRatio
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TriangularSpanCoeffRatio
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots

theorem diag_compare_of_triIn : ∀ (V F EC : Type) [CommRing V] [Field F] [Algebra V F] [AddCommGroup EC] [Module F EC] [Module V EC] [IsScalarTower V F EC] (r : ℕ) (u v w : Fin r → EC) (a b : Fin r → F) (d : V), LinearIndependent F u → FinRd.Roots.TriIn u a v → FinRd.Roots.TriIn u b w → (∀ i, b i ≠ 0) → (∀ x ∈ Submodule.span V (Set.range v), d • x ∈ Submodule.span V (Set.range w)) → ∀ i, ∃ c : V, algebraMap V F d * a i = algebraMap V F c * b i := by
  intro V F EC _ _ _ _ _ _ _ r u v w a b d hu hv hw hb hd i
  classical
  obtain ⟨e, he⟩ :=
    (Submodule.mem_span_range_iff_exists_fun V).1 (hd (v i) (Submodule.subset_span ⟨i, rfl⟩))
  obtain ⟨cv, hcvi, hcv0, hvi⟩ := hv i
  choose cw hcwd hcw0 hw' using hw
  have key : ∀ m, algebraMap V F d * cv m = ∑ j, algebraMap V F (e j) * cw j m := by
    have hL : d • v i = ∑ m, (algebraMap V F d * cv m) • u m := by
      rw [hvi, Finset.smul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [mul_smul, algebraMap_smul]
    have hR : ∑ j, e j • w j = ∑ m, (∑ j, algebraMap V F (e j) * cw j m) • u m := by
      simp_rw [hw', Finset.smul_sum, Finset.sum_smul, mul_smul, algebraMap_smul]
      exact Finset.sum_comm
    have h1 : ∑ m, (algebraMap V F d * cv m - ∑ j, algebraMap V F (e j) * cw j m) • u m = 0 := by
      simp_rw [sub_smul]
      rw [Finset.sum_sub_distrib, ← hL, ← hR, he, sub_self]
    intro m
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hu _ h1 m)
  have hzero : ∀ j, i < j → algebraMap V F (e j) = 0 := by
    by_contra hcon
    push_neg at hcon
    set S := Finset.univ.filter (fun j => i < j ∧ algebraMap V F (e j) ≠ 0) with hSdef
    have hS : S.Nonempty := by
      obtain ⟨j, hj⟩ := hcon
      exact ⟨j, by simp [S, hj]⟩
    obtain ⟨J, hJS, hJmax⟩ : ∃ J ∈ S, ∀ j ∈ S, j ≤ J :=
      ⟨S.max' hS, S.max'_mem hS, fun j hj => S.le_max' j hj⟩
    have hJ : i < J ∧ algebraMap V F (e J) ≠ 0 := by simpa [S] using hJS
    have hmax : ∀ j, J < j → algebraMap V F (e j) = 0 := by
      intro j hj
      by_contra hne
      have hjS : j ∈ S := by simp [S, hne, hJ.1.trans hj]
      exact not_le.2 hj (hJmax j hjS)
    have hk := key J
    rw [hcv0 J hJ.1, mul_zero, Finset.sum_eq_single J, hcwd J] at hk
    · exact hJ.2 ((mul_eq_zero.1 hk.symm).resolve_right (hb J))
    · intro j _ hjJ
      rcases lt_or_gt_of_ne hjJ with h | h
      · rw [hcw0 j J h, mul_zero]
      · rw [hmax j h, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ J) h
  refine ⟨e i, ?_⟩
  have hk := key i
  rw [hcvi, Finset.sum_eq_single i, hcwd i] at hk
  · exact hk
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with h | h
    · rw [hcw0 j i h, mul_zero]
    · rw [hzero j h, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TriangularSpanCoeffRatioStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triangular_span_coeff_ratio : ∀ (V F EC : Type) [CommRing V] [Field F] [Algebra V F] [AddCommGroup EC] [Module F EC] [Module V EC] [IsScalarTower V F EC] (r : ℕ) (u v w : Fin r → EC) (a b : Fin r → F) (d : V), LinearIndependent F u → FinRd.Roots.TriIn u a v → FinRd.Roots.TriIn u b w → (∀ i, b i ≠ 0) → (∀ x ∈ Submodule.span V (Set.range v), d • x ∈ Submodule.span V (Set.range w)) → ∀ i, ∃ c : V, algebraMap V F d * a i = algebraMap V F c * b i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.diag_compare_of_triIn | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.diag_compare_of_triIn | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.diag_compare_of_triIn <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointsFiniteNonempty
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointsFiniteNonempty
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Comps

theorem finite_maximal_points (X : Type) [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X]
    [QuasiSober X] [T0Space X] : {x : X | ∀ x' : X, x' ⤳ x → x' = x}.Finite := by
  refine Set.Finite.of_injOn (f := fun x : X => closure {x}) (t := irreducibleComponents X) ?_ ?_
    (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents)
  · intro x hx
    have hZ : irreducibleComponent x ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents x
    have hirr : IsIrreducible (irreducibleComponent x) := isIrreducible_irreducibleComponent
    have hcl : IsClosed (irreducibleComponent x) := isClosed_irreducibleComponent
    have hg := hirr.isGenericPoint_genericPoint_closure
    rw [hcl.closure_eq] at hg
    have hs : hirr.genericPoint ⤳ x := by
      rw [specializes_iff_mem_closure, hg.def]
      exact mem_irreducibleComponent
    have he := hx _ hs
    show closure {x} ∈ irreducibleComponents X
    rw [← he, hg.def]
    exact hZ
  · intro x _ y _ h
    exact (inseparable_iff_closure_eq.2 h).eq

theorem nonempty_maximal_points (X : Type) [TopologicalSpace X] [QuasiSober X] [T0Space X] [Nonempty X] :
    {x : X | ∀ x' : X, x' ⤳ x → x' = x}.Nonempty := by
  obtain ⟨x⟩ := ‹Nonempty X›
  have hZ : irreducibleComponent x ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents x
  have hirr : IsIrreducible (irreducibleComponent x) := isIrreducible_irreducibleComponent
  have hcl : IsClosed (irreducibleComponent x) := isClosed_irreducibleComponent
  have hg := hirr.isGenericPoint_genericPoint_closure
  rw [hcl.closure_eq] at hg
  refine ⟨hirr.genericPoint, fun x' hx' => ?_⟩
  have hm : Maximal IsIrreducible (irreducibleComponent x) := hZ
  have hsub : irreducibleComponent x ⊆ closure {x'} := by
    rw [← hg.def]
    exact hx'.closure_subset
  have hirr' : IsIrreducible (closure {x'}) := isIrreducible_singleton.closure
  have heq : closure {x'} = irreducibleComponent x := (hm.eq_of_subset hirr' hsub).symm
  exact (inseparable_iff_closure_eq.2 (heq.trans hg.def.symm)).eq

theorem exists_typeFn {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (p q : ℕ) :
    ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H p q ty := by
  classical
  let m : (E →+* ℂ) → ℕ := fun τ => if τ (H.rt : E) = H.rt0 then p else q
  let e := Fintype.equivFin (Σ τ : E →+* ℂ, Fin (m τ))
  refine ⟨_, fun i => (e.symm i).1, ?_⟩
  have key : ∀ τ : E →+* ℂ, Nat.card {i // (e.symm i).1 = τ} = m τ := by
    intro τ
    have e1 : {i // (e.symm i).1 = τ} ≃ Fin (m τ) :=
      (e.symm.subtypeEquiv (fun _ => Iff.rfl)).trans (Equiv.sigmaSubtype τ)
    rw [Nat.card_congr e1, Nat.card_fin]
  intro τ
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [key]; simp [m, h]
  · rw [key]; simp [m, h]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}

theorem moduli_nonempty (hc : N1c) (Xo : Moduli D l) : Nonempty Xo.X := by
  rcases Nat.eq_zero_or_pos (D.p + D.q) with h | h
  · obtain ⟨f, -, -⟩ := Xo.rep (Sp (KA l)) (𝟙 _) inferInstance (GlobalTheory.Models.RankZero.zeroObj h l _)
    exact ⟨f (IsLocalRing.closedPoint (KA l))⟩
  · obtain ⟨g, ty, hty⟩ := exists_typeFn H D.p D.q
    obtain ⟨F⟩ := hc E H D l Xo (KA l).val.toRingHom g ty h rfl hty
    exact ⟨F.u ⟨0, F.n_pos⟩ 0 (IsLocalRing.closedPoint ℂ)⟩

theorem model_nonempty {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)
    (h : Nonempty Xo.X) : Nonempty Y.X := by
  obtain ⟨x⟩ := h
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := Xo.s) (g := spMap (IntermediateField.inclusion c.le).toRingHom) x (IsLocalRing.closedPoint c.F)
    (Subsingleton.elim _ _)
  exact ⟨Y.j z⟩

theorem finite_nonempty_maximal : _root_.GlobalTheory.CompanionTheory.Ar.Top.Given →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
      (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)),
      {x : Y.X | ∀ x' : Y.X, x' ⤳ x → x' = x}.Finite ∧
      {x : Y.X | ∀ x' : Y.X, x' ⤳ x → x' = x}.Nonempty := by
  intro hG E _ _ _ H D l Xo c Y
  have : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  have : TopologicalSpace.NoetherianSpace Y.X := GlobalTheory.ModelSum.noetherianSpace_of_isProjOver Y.proj
  have : Nonempty Y.X := model_nonempty Y (moduli_nonempty hG.1.2.2.1 Xo)
  exact ⟨finite_maximal_points Y.X, nonempty_maximal_points Y.X⟩

end GlobalTheory.CompanionTheory.Ar.Comps
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointsFiniteNonemptyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
theorem _root_.GlobalTheory.T.generic_points_finite_nonempty :
    _root_.GlobalTheory.CompanionTheory.Ar.Top.Given →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
      (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)),
      {x : Y.X | ∀ x' : Y.X, x' ⤳ x → x' = x}.Finite ∧
      {x : Y.X | ∀ x' : Y.X, x' ⤳ x → x' = x}.Nonempty := by
  intro hG E _ _ _ H D l Xo c Y
  have : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  have : TopologicalSpace.NoetherianSpace Y.X := GlobalTheory.ModelSum.noetherianSpace_of_isProjOver Y.proj
  have : Nonempty Y.X := Comps.model_nonempty Y (Comps.moduli_nonempty hG.1.2.2.1 Xo)
  exact ⟨Comps.finite_maximal_points Y.X, Comps.nonempty_maximal_points Y.X⟩
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionPointValuationRingLift
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionPointValuationRingLift
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
open GlobalTheory.CompanionTheory.Ar.Sl.Reg
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Sl.Reg

section Helpers

attribute [local instance] Over.cartesianMonoidalCategory


open ReciprocityTheory.ChartRestriction.G.Out in
theorem exists_root_through {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom]
    [GeometricallyConnected G.hom] (n : ℕ)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ Sp V), Finite {x : Over.mk t ⟶ G // x ^ n = 1})
    (O C : Type) [CommRing O] [IsDomain O] [ValuationRing O] [Field C] [IsAlgClosed C] [Algebra O C]
    [IsFractionRing O C] (c : Sp O ⟶ G.left) (K : Type) [Field K] (r : Sp K ⟶ Sp O)
    (hr : r (IsLocalRing.closedPoint K) = IsLocalRing.closedPoint O) (y : Sp K ⟶ G.left)
    (hy : y ≫ (mulA G n).left = r ≫ c) :
    ∃ c' : Sp O ⟶ G.left, c' ≫ (mulA G n).left = c ∧
      c' (IsLocalRing.closedPoint O) = y (IsLocalRing.closedPoint K) := by
  have hm := GlobalTheory.AbLaw.MulN.isMonHom_mulA G n
  have : LocallyOfFiniteType ((mulA G n).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : LocallyOfFiniteType (mulA G n).left := locallyOfFiniteType_of_comp _ G.hom
  have : QuasiCompact ((mulA G n).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact (mulA G n).left := QuasiCompact.of_comp _ G.hom
  have : IsSeparated ((mulA G n).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : IsSeparated (mulA G n).left := IsSeparated.of_comp _ G.hom
  have : LocallyQuasiFinite (mulA G n).left :=
    GlobalTheory.locallyQuasiFinite_of_finite_geometric_ker _ G G _ hm inferInstance inferInstance fun K _ _ t => by
      simp only [GlobalTheory.IntDiv.comp_mulA]
      exact h K t
  have : Flat (mulA G n).left :=
    GlobalTheory.flat_of_flat_fibres_dvr V (FractionRing V) G G _ inferInstance inferInstance inferInstance inferInstance
      (GlobalTheory.IntDiv.flat_fibre G _ _ _) (GlobalTheory.IntDiv.flat_fibre G _ _ _)
  obtain ⟨s, hs, hs'⟩ := GlobalTheory.exists_section_of_quasiFinite_flat O C _ (pullback.snd (mulA G n).left c)
    (pullback.lift y r hy (IsLocalRing.closedPoint K))
    ((congrArg (fun g => g (IsLocalRing.closedPoint K)) (pullback.lift_snd y r hy)).trans hr)
  refine ⟨s ≫ pullback.fst _ _, by rw [Category.assoc, pullback.condition, reassoc_of% hs], ?_⟩
  exact (Scheme.Hom.comp_apply _ _ _).trans ((congrArg _ hs').trans ((Scheme.Hom.comp_apply _ _ _).symm.trans
    (congrArg (fun g => g (IsLocalRing.closedPoint K)) (pullback.lift_fst y r hy))))

theorem exists_torsion_point_through {R V O C K : Type} [CommRing R] [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [CommRing O] [IsDomain O] [ValuationRing O] [Field C] [IsAlgClosed C] [Algebra O C]
    [IsFractionRing O C] [Field K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (n : ℕ)
    (hA : ∀ (K : Type) [Field K] [IsAlgClosed K] (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G],
      Nonempty (TorusExtension G) → Finite {x : 𝟙_ (Over (Sp K)) ⟶ G // x ^ n = 1})
    (α : R →+* V) (ρV : V →+* O) (ρ : R →+* O) (hρ : ρV.comp α = ρ) (r : Sp K ⟶ Sp O)
    (hr : r (IsLocalRing.closedPoint K) = IsLocalRing.closedPoint O) (yG : Over.mk (r ≫ spMap ρ) ⟶ G)
    (hyN : yG ^ n = 1) :
    ∃ y : Over.mk (spMap ρ) ⟶ G, y ^ n = 1 ∧
      y.left (IsLocalRing.closedPoint O) = yG.left (IsLocalRing.closedPoint K) := by
  let j : Sp V ⟶ Sp R := spMap α
  have hjρ : spMap ρV ≫ j = spMap ρ := by
    rw [← hρ]
    simp only [j, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hGV : IsSemiAbelian ((Over.pullback j).obj G) := IsSemiAbelian.pullback j G hG
  have := hGV.comm
  have := hGV.smooth
  have := hGV.separated
  have := hGV.quasiCompact
  have := hGV.geomConnected
  have hfin : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ Sp V),
      Finite {x : Over.mk t ⟶ ((Over.pullback j).obj G) // x ^ n = 1} := by
    intro K _ _ t
    obtain ⟨E⟩ := hGV.fibres K t
    have := (IsSemiAbelian.pullback t ((Over.pullback j).obj G) hGV).comm
    exact GlobalTheory.FewZeros.finite_torsion_of_mulEquiv
      (GlobalTheory.TorsionLift.ptsEquiv t ((Over.pullback j).obj G) (𝟙_ _) t (by simp)) n
      (hA K ((Over.pullback t).obj ((Over.pullback j).obj G)) ⟨E⟩)
  let s : Sp K ⟶ Sp V := r ≫ spMap ρV
  have hs : s ≫ j = r ≫ spMap ρ := by simp only [s, Category.assoc, hjρ]
  let e₀ := GlobalTheory.TorsionLift.ptsEquiv j G (Over.mk s) (r ≫ spMap ρ) hs
  obtain ⟨yV, hyV₀⟩ := e₀.surjective yG
  have hyV : yV ^ n = 1 := by
    apply e₀.injective
    rw [map_pow, hyV₀, hyN, map_one]
  let rr : Over.mk s ⟶ Over.mk (spMap ρV) := Over.homMk r rfl
  let c : Sp O ⟶ ((Over.pullback j).obj G).left := (1 : Over.mk (spMap ρV) ⟶ ((Over.pullback j).obj G)).left
  have hc : yV.left ≫ (ReciprocityTheory.ChartRestriction.G.Out.mulA ((Over.pullback j).obj G) n).left = r ≫ c := by
    have h1 : yV ≫ ReciprocityTheory.ChartRestriction.G.Out.mulA ((Over.pullback j).obj G) n =
        rr ≫ (1 : Over.mk (spMap ρV) ⟶ ((Over.pullback j).obj G)) := by
      rw [GlobalTheory.IntDiv.comp_mulA, hyV, MonObj.comp_one]
    exact congrArg (fun q => q.left) h1
  obtain ⟨c', hc', hcl⟩ := exists_root_through ((Over.pullback j).obj G) n hfin O C c K r hr yV.left hc
  have hcw : c' ≫ ((Over.pullback j).obj G).hom = spMap ρV := by
    have h1 := Over.w (ReciprocityTheory.ChartRestriction.G.Out.mulA ((Over.pullback j).obj G) n)
    have h2 : c ≫ ((Over.pullback j).obj G).hom = spMap ρV :=
      Over.w (1 : Over.mk (spMap ρV) ⟶ ((Over.pullback j).obj G))
    rw [← h1, ← Category.assoc, hc', h2]
  let c₂ : Over.mk (spMap ρV) ⟶ ((Over.pullback j).obj G) := Over.homMk c' hcw
  have hc₂ : c₂ ^ n = 1 := by
    rw [← GlobalTheory.IntDiv.comp_mulA]
    exact Over.OverMorphism.ext hc'
  let e₁ := GlobalTheory.TorsionLift.ptsEquiv j G (Over.mk (spMap ρV)) (spMap ρ) hjρ
  refine ⟨e₁ c₂, by rw [← map_pow, hc₂, map_one], ?_⟩
  have h1 : (e₁ c₂).left = c' ≫ pullback.fst G.hom j := GlobalTheory.TorsionLift.ptsEquiv_left _ _ _ _ _ _
  have h2 : (e₀ yV).left = yV.left ≫ pullback.fst G.hom j := GlobalTheory.TorsionLift.ptsEquiv_left _ _ _ _ _ _
  rw [h1, ← hyV₀, h2]
  refine (Scheme.Hom.comp_apply _ _ _).trans ?_
  rw [hcl]
  exact (Scheme.Hom.comp_apply _ _ _).symm

end Helpers

theorem ker_ne_bot_of_finite (L : Type) [Field L] [NumberField L] (k : Type) [Field k] [Finite k] (a : 𝓞 L →+* k) :
    RingHom.ker a ≠ ⊥ := by
  intro h
  have hinj : Function.Injective a := (RingHom.injective_iff_ker_eq_bot a).2 h
  have : Infinite (𝓞 L) := Infinite.of_injective (Nat.cast : ℕ → 𝓞 L) Nat.cast_injective
  exact not_finite_iff_infinite.2 this (Finite.of_injective a hinj)

theorem exists_valuationSubring_of_ne_top (L : Type) [Field L] [NumberField L] (p : Ideal (𝓞 L)) (hp : p ≠ ⊤) :
    ∃ (O : ValuationSubring (AlgebraicClosure L)) (ρ : 𝓞 L →+* O),
      (∀ a : 𝓞 L, ((ρ a : O) : AlgebraicClosure L) = algebraMap L (AlgebraicClosure L) (a : L)) ∧
      ∀ a ∈ p, ρ a ∈ IsLocalRing.maximalIdeal O := by
  let f : 𝓞 L →+* AlgebraicClosure L := (algebraMap L (AlgebraicClosure L)).comp (algebraMap (𝓞 L) L)
  have hf : Function.Injective f :=
    (algebraMap L (AlgebraicClosure L)).injective.comp (RingOfIntegers.coe_injective)
  have hs : Function.Surjective f.rangeRestrict := f.rangeRestrict_surjective
  have hI : p.map f.rangeRestrict ≠ ⊤ := by
    intro h
    have h1 : (1 : f.range) ∈ p.map f.rangeRestrict := h ▸ Submodule.mem_top
    obtain ⟨x, hx, hx1⟩ := (Ideal.mem_map_iff_of_surjective _ hs).1 h1
    have : x = 1 := hf (by simpa [Subtype.ext_iff] using hx1)
    exact hp ((Ideal.eq_top_iff_one _).2 (this ▸ hx))
  obtain ⟨B, hAB, hB⟩ := Ideal.image_subset_nonunits_valuationSubring (p.map f.rangeRestrict) hI
  refine ⟨B, f.codRestrict B fun x => hAB ⟨x, rfl⟩, fun a => rfl, fun a ha => ?_⟩
  have h1 : f a ∈ B.nonunits := hB ⟨f.rangeRestrict a, Ideal.mem_map_of_mem _ ha, rfl⟩
  exact ValuationSubring.coe_mem_nonunits_iff.1 h1

theorem exists_lift_atPrime {R O : Type} [CommRing R] [CommRing O] [IsLocalRing O] (p : Ideal R) [p.IsMaximal]
    (ρ : R →+* O) (hρ : ∀ a ∈ p, ρ a ∈ IsLocalRing.maximalIdeal O) :
    ∃ ρV : Localization.AtPrime p →+* O, ρV.comp (algebraMap R (Localization.AtPrime p)) = ρ := by
  have hu : ∀ y : p.primeCompl, IsUnit (ρ y) := by
    intro y
    by_contra hy
    have h1 : p ≤ (IsLocalRing.maximalIdeal O).comap ρ := hρ
    have h2 : (IsLocalRing.maximalIdeal O).comap ρ ≠ ⊤ := Ideal.comap_ne_top _ (Ideal.IsPrime.ne_top inferInstance)
    have h3 := (Ideal.IsMaximal.eq_of_le ‹_› h2 h1).symm
    have h4 : (y : R) ∈ (IsLocalRing.maximalIdeal O).comap ρ := by
      simpa [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal] using hy
    exact y.2 (h3 ▸ h4)
  exact ⟨IsLocalization.lift hu, IsLocalization.lift_comp hu⟩

theorem exists_factor_of_finite {R k K : Type} [CommRing R] [Field k] [Finite k] [Field K] [IsAlgClosed K]
    (a : R →+* k) (b : R →+* K) [(RingHom.ker a).IsMaximal] (h : RingHom.ker a ≤ RingHom.ker b) :
    ∃ φ : k →+* K, φ.comp a = b := by
  letI : Field (R ⧸ RingHom.ker a) := Ideal.Quotient.field _
  let a' : (R ⧸ RingHom.ker a) →+* k := Ideal.Quotient.lift _ a fun x hx => hx
  let b' : (R ⧸ RingHom.ker a) →+* K := Ideal.Quotient.lift _ b fun x hx => h hx
  letI := a'.toAlgebra
  letI := b'.toAlgebra
  have : Module.Finite (R ⧸ RingHom.ker a) k := Module.Finite.of_finite
  have : Algebra.IsAlgebraic (R ⧸ RingHom.ker a) k := Algebra.IsAlgebraic.of_finite _ _
  let φ : k →ₐ[R ⧸ RingHom.ker a] K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨φ.toRingHom, RingHom.ext fun x => ?_⟩
  have h1 : φ (a' (Ideal.Quotient.mk _ x)) = b' (Ideal.Quotient.mk _ x) := φ.commutes _
  simp only [a', b', Ideal.Quotient.lift_mk] at h1
  exact h1

theorem exists_geometric_closedPoint {R O : Type} [CommRing R] [CommRing O] [IsLocalRing O] (ρ : R →+* O) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (b : R →+* K) (r : Sp K ⟶ Sp O), r ≫ spMap ρ = spMap b ∧
      (∀ x, ρ x ∈ IsLocalRing.maximalIdeal O → b x = 0) ∧
      r (IsLocalRing.closedPoint K) = IsLocalRing.closedPoint O := by
  let K := AlgebraicClosure (IsLocalRing.ResidueField O)
  let g : O →+* K := (algebraMap (IsLocalRing.ResidueField O) K).comp (IsLocalRing.residue O)
  have : IsLocalHom g := by
    refine ⟨fun x hx => ?_⟩
    have h1 : IsUnit (IsLocalRing.residue O x) := by
      refine isUnit_iff_ne_zero.2 fun h => ?_
      have : g x = 0 := by simp [g, h]
      exact hx.ne_zero this
    exact (isUnit_map_iff (IsLocalRing.residue O) x).1 h1
  refine ⟨K, inferInstance, inferInstance, g.comp ρ, spMap g, ?_, fun x hx => ?_, ?_⟩
  · simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  · have h1 : IsLocalRing.residue O (ρ x) = 0 := (IsLocalRing.residue_eq_zero_iff _).2 hx
    simp [g, h1]
  · exact IsLocalRing.comap_closedPoint g

theorem exists_torsion_point_reducing_to : ∀ (L : Type) [Field L] [NumberField L] (G : Over (Sp (𝓞 L))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (w : G.left), IsClosed ({w} : Set G.left) → ∃ (N : ℕ) (O : ValuationSubring (AlgebraicClosure L)) (ρ : 𝓞 L →+* O) (y : Over.mk (spMap ρ) ⟶ G), 1 ≤ N ∧ y ^ N = 1 ∧ y.left (IsLocalRing.closedPoint O) = w ∧ ∀ a : 𝓞 L, ((ρ a : O) : AlgebraicClosure L) = algebraMap L (AlgebraicClosure L) (a : L) := by
  intro L _ _ G _ _ hG w hw
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  let π : Sp (𝓞 L) ⟶ Sp ℤ := spMap (Int.castRingHom (𝓞 L))
  have : LocallyOfFiniteType π := by
    have h1 : (algebraMap ℤ (𝓞 L)).Finite := RingHom.finite_algebraMap.2 inferInstance
    rw [algebraMap_int_eq] at h1
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 h1.finiteType
  obtain ⟨hA, hB⟩ := GlobalTheory.semiAbelian_torsion_finite_and_closedPoint_finiteOrder
    GlobalTheory.abelian_torsion_finite_and_mulN_surjective.1
  obtain ⟨N, hN1, hN⟩ := hB (Sp (𝓞 L)) π G w hw
  have : Finite (G.left.residueField w) :=
    (GlobalTheory.jacobson_closedPoints_tools_int G.left (G.hom ≫ π)).2.1 w hw
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (G.left.fromSpecResidueField w ≫ G.hom)
  obtain ⟨a, rfl⟩ : ∃ a : 𝓞 L →+* G.left.residueField w, CommRingCat.ofHom a = ψ := ⟨ψ.hom, rfl⟩
  have hp0 : RingHom.ker a ≠ ⊥ := ker_ne_bot_of_finite L _ a
  have hpp : (RingHom.ker a).IsPrime := RingHom.ker_isPrime a
  have hpm : (RingHom.ker a).IsMaximal := hpp.isMaximal hp0
  obtain ⟨O, ρ, hρL, hρp⟩ := exists_valuationSubring_of_ne_top L (RingHom.ker a) hpp.ne_top
  obtain ⟨ρV, hρV⟩ := exists_lift_atPrime (RingHom.ker a) ρ hρp
  have hV : IsDiscreteValuationRing (Localization.AtPrime (RingHom.ker a)) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 L) hp0 _
  obtain ⟨K, _, _, b, r, hb, hbk, hr⟩ := exists_geometric_closedPoint ρ
  obtain ⟨φ, hφ⟩ := exists_factor_of_finite a b (fun x hx => hbk x (hρp x hx))
  have hy₀ : (Spec.map (CommRingCat.ofHom φ) ≫ G.left.fromSpecResidueField w) ≫ G.hom = r ≫ spMap ρ := by
    rw [hb, Category.assoc, ← hψ, ← hφ, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  let yG : Over.mk (r ≫ spMap ρ) ⟶ G := Over.homMk _ hy₀
  have hyl : ∀ z, yG.left z = w := fun z =>
    (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply _ _)
  have hyN : yG ^ N = 1 := hN K _ yG
    (Set.eq_singleton_iff_unique_mem.2 ⟨⟨IsLocalRing.closedPoint K, hyl _⟩, by rintro _ ⟨z, rfl⟩; exact hyl z⟩)
  obtain ⟨y, hy, hyw⟩ := exists_torsion_point_through (C := AlgebraicClosure L) G hG N
    (fun K _ _ G _ _ hE => hA K G hE N hN1) (algebraMap (𝓞 L) (Localization.AtPrime (RingHom.ker a))) ρV ρ hρV r hr yG hyN
  exact ⟨N, O, ρ, y, hN1, hy, hyw.trans (hyl _), hρL⟩

end GlobalTheory.CompanionTheory.Ar.Sl.Reg
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionPointValuationRingLiftStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
open GlobalTheory.CompanionTheory.Ar.Sl.Reg

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_point_valuation_ring_lift : ∀ (L : Type) [Field L] [NumberField L] (G : Over (Sp (𝓞 L))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (w : G.left), IsClosed ({w} : Set G.left) → ∃ (N : ℕ) (O : ValuationSubring (AlgebraicClosure L)) (ρ : 𝓞 L →+* O) (y : Over.mk (spMap ρ) ⟶ G), 1 ≤ N ∧ y ^ N = 1 ∧ y.left (IsLocalRing.closedPoint O) = w ∧ ∀ a : 𝓞 L, ((ρ a : O) : AlgebraicClosure L) = algebraMap L (AlgebraicClosure L) (a : L) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.Reg.exists_torsion_point_reducing_to | exact GlobalTheory.CompanionTheory.Ar.Sl.Reg.exists_torsion_point_reducing_to | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.Reg.exists_torsion_point_reducing_to <;> assumption)
end
end

module

public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CmTypeValuationEmbedding
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ValuationAtCentreOrder
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeExtendScalars
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeEigenDecompositionLocal
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ReduceLatticeCoordsToResidue
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FractionFieldEigenBasisDescends
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeGermEigen
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LeWchartOne
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointFactorsOpen
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FibreLatticeBaseChangeConj
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DvrSpecializationEigenFrame

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DvrPointEigenFrameReduction
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DvrPointEigenFrameReduction
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem exists_modelPoint_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (β : O →+* c.F) (Y : Model Xo c β) (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (j : K →+* ℂ_[p]) (βK : c.F →+* K) (y : Sp K ⟶ Xo.XF c),
    (∀ x : c.F, ‖κ x‖ ≤ 1 ↔ x ∈ β.range) → (∀ a : K, ‖j a‖ ≤ 1 ↔ a ∈ (algebraMap V K).range) → j.comp βK = κ →
    y ≫ pullback.snd _ _ = spMap βK → ∃ z : Sp V ⟶ Y.X, spMap (algebraMap V K) ≫ z = y ≫ Y.j := by
  intro E _ _ _ H D l Xo c O _ _ _ β Y p κ V K _ _ _ _ _ _ j βK y hκ hj hjκ hy
  have hpr : IsProper Y.s := GlobalTheory.SchemeWords.isProper_of_isProjOver Y.proj
  have hmem : ∀ o : O, (βK.comp β) o ∈ (algebraMap V K).range := by
    intro o
    refine (hj _).1 ?_
    have h1 : j (βK (β o)) = κ (β o) := by rw [← hjκ]; rfl
    simp only [RingHom.comp_apply]
    rw [h1]
    exact (hκ _).2 ⟨o, rfl⟩
  let e : V ≃+* (algebraMap V K).range :=
    RingEquiv.ofBijective (algebraMap V K).rangeRestrict
      ⟨fun a b h => IsFractionRing.injective V K (congrArg Subtype.val h),
        (algebraMap V K).rangeRestrict_surjective⟩
  let b : O →+* V := e.symm.toRingHom.comp ((βK.comp β).codRestrict _ hmem)
  have hb : (algebraMap V K).comp b = βK.comp β := by
    ext o
    have h2 : e (b o) = (βK.comp β).codRestrict _ hmem o := e.apply_symm_apply _
    exact congrArg Subtype.val h2
  have hsq : (y ≫ Y.j) ≫ Y.s = Spec.map (CommRingCat.ofHom ((algebraMap V K).comp b)) := by
    rw [hb]
    have h3 : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap β := by
      simp only [Model.j, Category.assoc]
      rw [pullback.condition, ← Category.assoc, Y.jQ_over]
    rw [Category.assoc, h3, ← Category.assoc, hy]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  obtain ⟨z, ⟨hz, _⟩, _⟩ := existsUnique_valuationRing_lift O V K b Y.X Y.s (y ≫ Y.j) hsq
  exact ⟨z, hz⟩

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DvrPointEigenFrameReductionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvr_point_eigen_frame_reduction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (β : O →+* c.F) (Y : Model Xo c β) (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (j : K →+* ℂ_[p]) (βK : c.F →+* K) (y : Sp K ⟶ Xo.XF c),
    (∀ x : c.F, ‖κ x‖ ≤ 1 ↔ x ∈ β.range) → (∀ a : K, ‖j a‖ ≤ 1 ↔ a ∈ (algebraMap V K).range) → j.comp βK = κ →
    y ≫ pullback.snd _ _ = spMap βK → ∃ z : Sp V ⟶ Y.X, spMap (algebraMap V K) ≫ z = y ≫ Y.j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.exists_modelPoint_extension | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.exists_modelPoint_extension | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.exists_modelPoint_extension <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeStableUnderAction
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeStableUnderAction
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem hodgeAt_stable : ∀ (E : Type) [Field E] [NumberField E] (Ω Vs : Type) [Field Ω] [AddCommGroup Vs] [Module Ω Vs]
    (ρ : 𝓞 E →+* Module.End Ω Vs) (ρH : 𝓞 E →+* Module.End Ω (Vs × Module.Dual Ω Vs))
    (R : Subring Ω) (g N : ℕ) (ℓ : Fin g → Vs) (t : Fin N → Vs × Module.Dual Ω Vs)
    (HL : Submodule R (Vs × Module.Dual Ω Vs)),
    (∀ a y, (ρH a y).1 = ρ a y.1) → HodgeAt ρH HL ℓ t →
    (∀ i, t i ∈ HL) ∧ (∀ a, ∀ h ∈ HL, ρH a h ∈ HL) ∧ ∀ a i, ρ a (ℓ i) ∈ Submodule.span R (Set.range ℓ) := by
  intro E _ _ Ω Vs _ _ _ ρ ρH R g N ℓ t HL h1 h
  obtain ⟨⟨-, -, hX⟩, hmap, -⟩ := h
  have key : ∀ (c : 𝓞 E) (i : Fin N), ρH c (t i) ∈ HL := by
    intro c i
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hX, ← (RingOfIntegers.basis E).sum_repr c, map_sum, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_zsmul, LinearMap.smul_apply]
    exact zsmul_mem (Submodule.subset_span (Set.mem_range.2 ⟨(i, k), rfl⟩)) _
  have stable : ∀ a, ∀ y ∈ HL, ρH a y ∈ HL := by
    intro a y hy
    rw [hX] at hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨q, rfl⟩ := hx
      rw [← Module.End.mul_apply, ← map_mul]
      exact key _ _
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add (f := _)]
      exact add_mem hx hy
    | smul r x _ hx =>
      have e : ρH a (r • x) = r • ρH a x := map_smul (ρH a) (r : Ω) x
      rw [e]
      exact HL.smul_mem r hx
  refine ⟨fun i => ?_, stable, fun a i => ?_⟩
  · simpa using key 1 i
  · have hi : ℓ i ∈ HL.map ((LinearMap.fst Ω Vs (Module.Dual Ω Vs)).restrictScalars R) :=
      hmap ▸ Submodule.subset_span ⟨i, rfl⟩
    obtain ⟨y, hy, e⟩ := hi
    rw [← hmap]
    refine ⟨ρH a y, stable a y hy, ?_⟩
    have e' : y.1 = ℓ i := e
    change (ρH a y).1 = _
    rw [h1, e']

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeStableUnderActionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_lattice_stable_under_action : ∀ (E : Type) [Field E] [NumberField E] (Ω Vs : Type) [Field Ω] [AddCommGroup Vs] [Module Ω Vs]
    (ρ : 𝓞 E →+* Module.End Ω Vs) (ρH : 𝓞 E →+* Module.End Ω (Vs × Module.Dual Ω Vs))
    (R : Subring Ω) (g N : ℕ) (ℓ : Fin g → Vs) (t : Fin N → Vs × Module.Dual Ω Vs)
    (HL : Submodule R (Vs × Module.Dual Ω Vs)),
    (∀ a y, (ρH a y).1 = ρ a y.1) → HodgeAt ρH HL ℓ t →
    (∀ i, t i ∈ HL) ∧ (∀ a, ∀ h ∈ HL, ρH a h ∈ HL) ∧ ∀ a i, ρ a (ℓ i) ∈ Submodule.span R (Set.range ℓ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.hodgeAt_stable | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.hodgeAt_stable | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.hodgeAt_stable <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IotaMultiLinearCombinationDet
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IotaMultiLinearCombinationDet
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem ιMulti_matrix_transform : ∀ (Ω Vs : Type) [Field Ω] [AddCommGroup Vs] [Module Ω Vs] (p : ℕ) (P : Matrix (Fin p) (Fin p) Ω) (v : Fin p → Vs),
    exteriorPower.ιMulti Ω p (fun i => ∑ k, P i k • v k) = P.det • exteriorPower.ιMulti Ω p v := by
  intro Ω Vs _ _ _ p P v
  have hA : (exteriorPower.ιMulti Ω p).compLinearMap (Fintype.linearCombination Ω v) =
      (Matrix.detRowAlternating : (Fin p → Ω) [⋀^Fin p]→ₗ[Ω] Ω).smulRight
        (exteriorPower.ιMulti Ω p v) := by
    refine (Pi.basisFun Ω (Fin p)).ext_alternating fun u hu => ?_
    let s : Equiv.Perm (Fin p) := Equiv.ofBijective u (Finite.injective_iff_bijective.1 hu)
    have e : (fun i => Pi.basisFun Ω (Fin p) (u i)) = (fun i => Pi.basisFun Ω (Fin p) i) ∘ s := rfl
    rw [e, AlternatingMap.map_perm, AlternatingMap.map_perm]
    congr 1
    have e1 : (Matrix.detRowAlternating : (Fin p → Ω) [⋀^Fin p]→ₗ[Ω] Ω)
        (fun i => Pi.basisFun Ω (Fin p) i) = 1 := by
      change Matrix.det (Matrix.of fun i => Pi.basisFun Ω (Fin p) i) = 1
      rw [show (Matrix.of fun i => Pi.basisFun Ω (Fin p) i) = 1 from by
        ext i j; simp [Matrix.one_apply, Pi.single_apply, eq_comm], Matrix.det_one]
    rw [AlternatingMap.smulRight_apply, e1, one_smul, AlternatingMap.compLinearMap_apply]
    congr 1
    funext i
    simp [Fintype.linearCombination_apply_single]
  exact AlternatingMap.congr_fun hA P

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IotaMultiLinearCombinationDetStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iota_multi_linear_combination_det : ∀ (Ω Vs : Type) [Field Ω] [AddCommGroup Vs] [Module Ω Vs] (p : ℕ) (P : Matrix (Fin p) (Fin p) Ω) (v : Fin p → Vs),
    exteriorPower.ιMulti Ω p (fun i => ∑ k, P i k • v k) = P.det • exteriorPower.ιMulti Ω p v := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.ιMulti_matrix_transform | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.ιMulti_matrix_transform | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.ιMulti_matrix_transform <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TiedActionComposeResidueMap
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TiedActionComposeResidueMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint.TiedMap

theorem tied_map_comp : ∀ (E : Type) [Field E] [NumberField E] (Ω Vs K C : Type) [Field Ω] [AddCommGroup Vs] [Module Ω Vs] [Field K] [Field C]
    (ρ : 𝓞 E →+* Module.End Ω Vs) (R' : Subring Ω) (g : ℕ) (ℓ : Fin g → Vs) (ψ : R' →+* K) (j : K →+* C)
    (ρK : 𝓞 E →+* Module.End K (Fin g → K)) (ρC : 𝓞 E →+* Module.End C (Fin g → C)),
    (∀ a i, ρ a (ℓ i) ∈ Submodule.span R' (Set.range ℓ)) → Tied ℓ ψ ρ ρK → Tied ℓ (j.comp ψ) ρ ρC →
    ∀ (a : 𝓞 E) (x : Fin g → K), ρC a (fun i => j (x i)) = fun i => j (ρK a x i) := by
  intro E _ _ Ω Vs K C _ _ _ _ _ ρ R' g ℓ ψ j ρK ρC hρ hK hC a x
  have hex : ∀ i, ∃ c : Fin g → R', ρ a (ℓ i) = comb ℓ c := by
    intro i
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R').1 (hρ a i)
    exact ⟨c, by rw [← hc]; rfl⟩
  choose c hc using hex
  have hs : ∀ i, comb ℓ (Pi.single i (1 : R') : Fin g → R') = ℓ i := by
    intro i
    unfold comb
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · simp
  have h1 : ∀ i, ρK a (Pi.single i (1 : K)) = fun k => ψ (c i k) := by
    intro i
    have := hK a (Pi.single i 1) (c i) (by rw [hs, hc])
    rw [← this]
    congr 1
    ext k
    by_cases h : k = i
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  have h2 : ∀ i, ρC a (Pi.single i (1 : C)) = fun k => j (ψ (c i k)) := by
    intro i
    have := hC a (Pi.single i 1) (c i) (by rw [hs, hc])
    simp only [RingHom.comp_apply] at this
    rw [← this]
    congr 1
    ext k
    by_cases h : k = i
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  have hxK : x = ∑ i, x i • (Pi.single i (1 : K) : Fin g → K) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  have hxC : (fun i => j (x i)) = ∑ i, j (x i) • (Pi.single i (1 : C) : Fin g → C) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hxC, map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    conv_rhs => rw [hxK, map_sum]
  ext k
  simp [Finset.sum_apply, h1, h2]

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint.TiedMap
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TiedActionComposeResidueMapStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tied_action_compose_residue_map : ∀ (E : Type) [Field E] [NumberField E] (Ω Vs K C : Type) [Field Ω] [AddCommGroup Vs] [Module Ω Vs] [Field K] [Field C]
    (ρ : 𝓞 E →+* Module.End Ω Vs) (R' : Subring Ω) (g : ℕ) (ℓ : Fin g → Vs) (ψ : R' →+* K) (j : K →+* C)
    (ρK : 𝓞 E →+* Module.End K (Fin g → K)) (ρC : 𝓞 E →+* Module.End C (Fin g → C)),
    (∀ a i, ρ a (ℓ i) ∈ Submodule.span R' (Set.range ℓ)) → Tied ℓ ψ ρ ρK → Tied ℓ (j.comp ψ) ρ ρC →
    ∀ (a : 𝓞 E) (x : Fin g → K), ρC a (fun i => j (x i)) = fun i => j (ρK a x i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.TiedMap.tied_map_comp | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.TiedMap.tied_map_comp | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.TiedMap.tied_map_comp <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BasisOfSubmoduleIffUniqueCoords
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BasisOfSubmoduleIffUniqueCoords
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem basis_iff_unique_combinations : ∀ (K W : Type) [Field K] [AddCommGroup W] [Module K W] (S : Submodule K W) (n : ℕ) (b : Fin n → W),
    (LinearIndependent K b ∧ Submodule.span K (Set.range b) = S) ↔
      (∀ i, b i ∈ S) ∧ ∀ e ∈ S, ∃! x : Fin n → K, e = ∑ i, x i • b i := by
  intro K W _ _ _ S n b
  constructor
  · rintro ⟨hli, hspan⟩
    refine ⟨fun i => hspan ▸ Submodule.subset_span ⟨i, rfl⟩, fun e he => ?_⟩
    rw [← hspan, Submodule.mem_span_range_iff_exists_fun] at he
    obtain ⟨x, hx⟩ := he
    refine ⟨x, hx.symm, fun y hy => ?_⟩
    have h0 : ∑ i, (y - x) i • b i = 0 := by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, ← hy, hx, sub_self]
    funext i
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ h0 i)
  · rintro ⟨hb, huniq⟩
    refine ⟨Fintype.linearIndependent_iff.mpr fun g hg i => ?_, le_antisymm ?_ fun e he => ?_⟩
    · obtain ⟨x, _, hx⟩ := huniq 0 S.zero_mem
      have hg0 : g = x := hx g hg.symm
      have h00 : (0 : Fin n → K) = x := hx 0 (by simp)
      rw [hg0, ← h00]
      rfl
    · exact Submodule.span_le.mpr (Set.range_subset_iff.mpr hb)
    · obtain ⟨x, hx, _⟩ := huniq e he
      rw [hx]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BasisOfSubmoduleIffUniqueCoordsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.basis_of_submodule_iff_unique_coords : ∀ (K W : Type) [Field K] [AddCommGroup W] [Module K W] (S : Submodule K W) (n : ℕ) (b : Fin n → W),
    (LinearIndependent K b ∧ Submodule.span K (Set.range b) = S) ↔
      (∀ i, b i ∈ S) ∧ ∀ e ∈ S, ∃! x : Fin n → K, e = ∑ i, x i • b i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.basis_iff_unique_combinations | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.basis_iff_unique_combinations | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.basis_iff_unique_combinations <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NumberFieldEmbeddingsIntoCpIntegral
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NumberFieldEmbeddingsIntoCpIntegral
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem embeddings_padicComplex : ∀ (E : Type) [Field E] [NumberField E] (p : Nat.Primes),
    (∀ (s : E →+* ℂ_[p]) (a : 𝓞 E), s (a : E) ∈ (algebraMap (OCp p) ℂ_[p]).range) ∧
      Nat.card (E →+* ℂ_[p]) = Module.finrank ℚ E := by
  intro E _ _ p
  refine ⟨fun s a => ?_, ?_⟩
  · have hO : IsIntegral (OCp p) (s (a : E)) :=
      (RingOfIntegers.isIntegral_coe a).map_of_comp_eq (Int.castRingHom (OCp p)) s (RingHom.ext_int _ _)
    have hv := Valuation.valuationSubring.integers (v := NormedField.valuation (K := ℂ_[p]))
    exact hv.exists_of_le_one (hv.isIntegral_iff_v_le_one.mp hO)
  · rw [Nat.card_eq_fintype_card]
    exact NumberField.Embeddings.card E ℂ_[p]

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NumberFieldEmbeddingsIntoCpIntegralStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.number_field_embeddings_into_cp_integral : ∀ (E : Type) [Field E] [NumberField E] (p : Nat.Primes),
    (∀ (s : E →+* ℂ_[p]) (a : 𝓞 E), s (a : E) ∈ (algebraMap (OCp p) ℂ_[p]).range) ∧
      Nat.card (E →+* ℂ_[p]) = Module.finrank ℚ E := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.embeddings_padicComplex | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.embeddings_padicComplex | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.embeddings_padicComplex <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ReduceLatticeActionToResidue
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ReduceLatticeActionToResidue
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

section EvalRank

variable {E : Type} [Field E] [NumberField E]

theorem trace_eigProj {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K) :
    LinearMap.trace K V (HT.eigProj ρ σ) = (Module.finrank K (HT.eigSp ρ σ) : K) := by
  have h : LinearMap.IsProj (HT.eigSp ρ σ) (HT.eigProj ρ σ) :=
    ⟨fun x => HT.LatBasic.eigProj_mem ρ σ x, fun x hx => HT.LatBasic.eigProj_of_mem hx⟩
  exact h.trace

theorem trace_eigProj_eq_sum {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K) :
    LinearMap.trace K V (HT.eigProj ρ σ) =
      ∑ k, σ (HT.dualInt E k) * LinearMap.trace K V (ρ (RingOfIntegers.basis E k)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [HT.eigProj, map_sum, map_smul]

variable {Ω Vs C : Type} [Field Ω] [AddCommGroup Vs] [Module Ω Vs] [Field C]

theorem comb_single {R : Subring Ω} {g : ℕ} (ℓ : Fin g → Vs) (j : Fin g) :
    comb (R := R) ℓ (Pi.single j 1) = ℓ j := by
  classical
  unfold comb
  rw [Finset.sum_eq_single j (fun i _ h => by simp [Pi.single_apply, h]) (by simp)]
  simp

theorem exists_comb {R : Subring Ω} {g : ℕ} {ℓ : Fin g → Vs} {v : Vs}
    (h : v ∈ Submodule.span R (Set.range ℓ)) : ∃ x : Fin g → R, v = comb ℓ x := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 h
  exact ⟨c, by rw [← hc]; rfl⟩

theorem trace_of_comb {R : Subring Ω} {g : ℕ} {ℓ : Fin g → Vs} (hl : LinearIndependent Ω ℓ)
    (hs : Submodule.span Ω (Set.range ℓ) = ⊤) (f : Module.End Ω Vs) (x : Fin g → Fin g → R)
    (hx : ∀ j, f (ℓ j) = comb ℓ (x j)) :
    LinearMap.trace Ω Vs f = ((∑ j, x j j : R) : Ω) := by
  classical
  set b := Module.Basis.mk hl hs.ge with hb
  have hbj : ∀ j, b j = ℓ j := fun j => by simp [hb]
  rw [LinearMap.trace_eq_matrix_trace Ω b f, Matrix.trace]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, hbj, hx j, comb]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← hbj, map_sum, map_smul, Module.Basis.repr_self]
  simp [Finsupp.single_apply]

theorem trace_of_cols {g : ℕ} (f : Module.End C (Fin g → C)) (y : Fin g → Fin g → C)
    (hy : ∀ j, f (Pi.single j 1) = y j) :
    LinearMap.trace C (Fin g → C) f = ∑ j, y j j := by
  classical
  rw [LinearMap.trace_eq_matrix_trace C (Pi.basisFun C (Fin g)) f, Matrix.trace]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  simp [hy j]

end EvalRank

theorem finrank_eigSp_eval : ∀ (E : Type) [Field E] [NumberField E] (Ω Vs C : Type) [Field Ω] [CharZero Ω] [AddCommGroup Vs] [Module Ω Vs]
    [FiniteDimensional Ω Vs] [Field C] [CharZero C] (ρ : 𝓞 E →+* Module.End Ω Vs) (R' : Subring Ω) (g : ℕ)
    (ℓ : Fin g → Vs) (ψ : R' →+* C) (ρC : 𝓞 E →+* Module.End C (Fin g → C)) (σ : E →+* Ω) (σC : E →+* C),
    LinearIndependent Ω ℓ → Submodule.span Ω (Set.range ℓ) = ⊤ →
    (∀ a i, ρ a (ℓ i) ∈ Submodule.span R' (Set.range ℓ)) → Tied ℓ ψ ρ ρC →
    (∀ e : E, ∃ h : σ e ∈ R', ψ ⟨σ e, h⟩ = σC e) →
    Module.finrank C (HT.eigSp ρC σC) = Module.finrank Ω (HT.eigSp ρ σ) := by
  intro E _ _ Ω Vs C _ _ _ _ _ _ _ ρ R' g ℓ ψ ρC σ σC hl hs hst hT hσ
  classical
  choose M hM using fun (a : 𝓞 E) (j : Fin g) => exists_comb (hst a j)
  have hC : ∀ a j, ρC a (Pi.single j 1) = fun i => ψ (M a j i) := by
    intro a j
    have := hT a (Pi.single j 1) (M a j) (by rw [comb_single]; exact hM a j)
    rw [← this]
    congr 1
    ext i
    by_cases h : i = j
    · subst h; simp
    · simp [Pi.single_apply, h]
  have tΩ : ∀ a, LinearMap.trace Ω Vs (ρ a) = ((∑ j, M a j j : R') : Ω) :=
    fun a => trace_of_comb hl hs (ρ a) (M a) (hM a)
  have tC : ∀ a, LinearMap.trace C (Fin g → C) (ρC a) = ψ (∑ j, M a j j) := by
    intro a
    set_option synthInstance.maxHeartbeats 100000 in
      rw [trace_of_cols (ρC a) (fun j i => ψ (M a j i)) (hC a), map_sum]
  set T : R' := ∑ k, ⟨σ (HT.dualInt E k), (hσ _).1⟩ * ∑ j, M (RingOfIntegers.basis E k) j j with hTdef
  have h1 : (Module.finrank Ω (HT.eigSp ρ σ) : Ω) = (T : Ω) := by
    rw [← trace_eigProj, trace_eigProj_eq_sum, hTdef]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [tΩ]
    push_cast
    rfl
  have h2 : T = (Module.finrank Ω (HT.eigSp ρ σ) : R') := by
    apply Subtype.ext
    rw [← h1]
    simp
  have h3 : (Module.finrank C (HT.eigSp ρC σC) : C) = ψ T := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← trace_eigProj, trace_eigProj_eq_sum, hTdef, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [tC, map_mul]
    congr 1
    exact ((hσ _).2).symm
  rw [h2, map_natCast] at h3
  exact_mod_cast h3

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ReduceLatticeActionToResidueStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_eigSp_eq_of_lattice_specialization : ∀ (E : Type) [Field E] [NumberField E] (Ω Vs C : Type) [Field Ω] [CharZero Ω] [AddCommGroup Vs] [Module Ω Vs]
    [FiniteDimensional Ω Vs] [Field C] [CharZero C] (ρ : 𝓞 E →+* Module.End Ω Vs) (R' : Subring Ω) (g : ℕ)
    (ℓ : Fin g → Vs) (ψ : R' →+* C) (ρC : 𝓞 E →+* Module.End C (Fin g → C)) (σ : E →+* Ω) (σC : E →+* C),
    LinearIndependent Ω ℓ → Submodule.span Ω (Set.range ℓ) = ⊤ →
    (∀ a i, ρ a (ℓ i) ∈ Submodule.span R' (Set.range ℓ)) → Tied ℓ ψ ρ ρC →
    (∀ e : E, ∃ h : σ e ∈ R', ψ ⟨σ e, h⟩ = σC e) →
    Module.finrank C (HT.eigSp ρC σC) = Module.finrank Ω (HT.eigSp ρ σ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.finrank_eigSp_eval | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.finrank_eigSp_eval | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.finrank_eigSp_eval <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CpIntegersValuationRing
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CpIntegersValuationRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem norm_prime_padicComplex (p : Nat.Primes) : ‖((p : ℕ) : ℂ_[p])‖ = ((p : ℕ) : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap', Padic.norm_p]

theorem ocp_integers : ∀ p : Nat.Primes, (NormedField.valuation (K := ℂ_[p])).Integers (OCp p) ∧
    (∃ x : ℂ_[p], 0 < NormedField.valuation (K := ℂ_[p]) x ∧ NormedField.valuation (K := ℂ_[p]) x < 1) ∧
    ∀ x : ℂ_[p], x ∈ (algebraMap (OCp p) ℂ_[p]).range ↔ ‖x‖ ≤ 1 := by
  intro p
  have hI : (NormedField.valuation (K := ℂ_[p])).Integers (GlobalTheory.CompanionTheory.Ar.Flat.CPoint.OCp p) :=
    Valuation.valuationSubring.integers _
  refine ⟨hI, ⟨((p : ℕ) : ℂ_[p]), ?_, ?_⟩, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · rw [NormedField.valuation_apply, ← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_zero,
      GlobalTheory.CompanionTheory.Ar.Flat.CPoint.norm_prime_padicComplex]
    exact inv_pos.2 (by exact_mod_cast p.2.pos)
  · rw [NormedField.valuation_apply, ← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one,
      GlobalTheory.CompanionTheory.Ar.Flat.CPoint.norm_prime_padicComplex]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast p.2.one_lt)
  · obtain ⟨y, rfl⟩ := RingHom.mem_range.1 hx
    have h := hI.map_le_one y
    rwa [NormedField.valuation_apply, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one] at h
  · refine RingHom.mem_range.2 (hI.exists_of_le_one ?_)
    rwa [NormedField.valuation_apply, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CpIntegersValuationRingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cp_integers_valuation_ring : ∀ p : Nat.Primes, (NormedField.valuation (K := ℂ_[p])).Integers (OCp p) ∧
    (∃ x : ℂ_[p], 0 < NormedField.valuation (K := ℂ_[p]) x ∧ NormedField.valuation (K := ℂ_[p]) x < 1) ∧
    ∀ x : ℂ_[p], x ∈ (algebraMap (OCp p) ℂ_[p]).range ↔ ‖x‖ ≤ 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.ocp_integers | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.ocp_integers | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.ocp_integers <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.OrderValuationCompare
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.OrderValuationCompare
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem z_value_of_order : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (L : Lat ξ Ω) (σ ϖ : Ω) (M : ℕ) (a : ℤ) (V C : Type) [CommRing V] [IsLocalRing V] [Field C] [Algebra V C] (z : Spec (CommRingCat.of V) ⟶ X) (h : genPt ξ ⤳ centre z) (e : Ω) (γ π : C), IsCptGen ξ → OrderAt L σ ϖ M a ⟨centre z, h⟩ → L.IsGenAt ⟨centre z, h⟩ e → ValAt ξ (Spec.map (CommRingCat.ofHom (algebraMap V C)) ≫ z) (σ / e) γ → ValAt ξ (Spec.map (CommRingCat.ofHom (algebraMap V C)) ≫ z) ϖ π → π ≠ 0 → ∃ u : Vˣ, γ ^ M = π ^ a * algebraMap V C u :=
  @PositivityTheory.Xgn.valuation_at_centre_order

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.OrderValuationCompareStatement
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.order_valuation_compare : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (L : Lat ξ Ω) (σ ϖ : Ω) (M : ℕ) (a : ℤ) (V C : Type) [CommRing V] [IsLocalRing V] [Field C] [Algebra V C] (z : Spec (CommRingCat.of V) ⟶ X) (h : genPt ξ ⤳ centre z) (e : Ω) (γ π : C), IsCptGen ξ → OrderAt L σ ϖ M a ⟨centre z, h⟩ → L.IsGenAt ⟨centre z, h⟩ e → ValAt ξ (Spec.map (CommRingCat.ofHom (algebraMap V C)) ≫ z) (σ / e) γ → ValAt ξ (Spec.map (CommRingCat.ofHom (algebraMap V C)) ≫ z) ϖ π → π ≠ 0 → ∃ u : Vˣ, γ ^ M = π ^ a * algebraMap V C u := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.z_value_of_order | exact GlobalTheory.CompanionTheory.Ar.Flat.z_value_of_order | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.z_value_of_order <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLinePAdicFrame
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem inc_eq : ∀ (E Ωf : Type) [Field E] [NumberField E] [Field Ωf] (σ σ₂ : E →+* Ωf), (∀ b : 𝓞 E, σ (b : E) = σ₂ (b : E)) → σ = σ₂ := by
  intro E Ωf _ _ _ σ σ₂ h
  exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext h)

theorem eig_eq : ∀ (E : Type) [Field E] [NumberField E] (K W : Type) [Field K] [AddCommGroup W] [Module K W] (ρ : 𝓞 E →+* Module.End K W) (σ : 𝓞 E →+* K) (σ' : E →+* K), (∀ a : 𝓞 E, σ a = σ' (a : E)) → eigSp ρ σ = HT.eigSp ρ σ' := by
  intro E _ _ K W _ _ _ ρ σ σ' h
  unfold eigSp HT.eigSp
  congr 1
  funext a
  rw [h a]
  rfl

theorem log_end {F : Type} [NormedField F] (M : ℕ) (a : ℤ) (x pp mu : F) (hM : 0 < M) (hx : x ≠ 0) (hp : pp ≠ 0)
    (hmu : ‖mu‖ = 1) (h : x ^ M = pp ^ a * mu) : Real.log ‖x‖ = (a / M) * Real.log ‖pp‖ := by
  have h1 := congrArg norm h
  rw [norm_pow, norm_mul, hmu, _root_.mul_one, norm_zpow] at h1
  have h2 := congrArg Real.log h1
  rw [Real.log_pow, Real.log_zpow] at h2
  have hM' : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  field_simp
  linarith

theorem norm_eq_one_of {F : Type} [NormedField F] (x y : F) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (h : x * y = 1) : ‖x‖ = 1 := by
  have h4 := congrArg norm h
  rw [norm_mul, norm_one] at h4
  nlinarith [norm_nonneg x, norm_nonneg y]


set_option maxHeartbeats 4000000 in
theorem value_at_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (ϖ : O) (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) (φ : FrameFn Xo c) (𝓗 : HodgeLat Z.M.lat Z.ρ H.bar (D.p + D.q)) (σ : E →+* Z.Ω) (v : Fin D.p → Z.V) (w : Fin D.q → Z.V) (u : Fin (D.p + D.q) → Z.V × Module.Dual Z.Ω Z.V) (α κ' : Z.Ω) (M : ℕ) (a : ℤ), τ (H.rt : E) = H.rt0 → Irreducible ϖ → Function.Injective β → (∀ x : c.F, ‖κ x‖ ≤ 1 ↔ x ∈ β.range) → (∀ b : 𝓞 E, σ (b : E) = Z.inc (tauIn c τ b)) → LinearIndependent Z.Ω v → Submodule.span Z.Ω (Set.range v) = HT.eigSp Z.ρ σ → LinearIndependent Z.Ω w → Submodule.span Z.Ω (Set.range w) = eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ))) → IsAdapted 𝓗.ρH σ v w u → 0 < M → (∀ x, OrderAt (detLat (𝓗.quot σ) u) (α / κ') (Z.inc (β ϖ)) M a x) → κ' ≠ 0 → Represents Y U τ Z.M (α • exteriorPower.ιMulti Z.Ω D.p v) (κ' • exteriorPower.ιMulti Z.Ω D.q w) φ → IsLineFn U τ φ → ∃ t : ℝ, HasFinNorm U τ φ p κ t := by
  intro E _ _ _ H D l Xo c O _ _ _ β Y U Z τ ϖ p κ φ 𝓗 σ v w u α κ' M a hτ hϖ hinj hr hσ hv hvs hw hws had hM hord hκ' hrep hφ
  haveI : CharZero Z.Ω := charZero_of_injective_ringHom Z.inc.injective
  haveI : FiniteDimensional Z.Ω Z.V := HodgeLat.finiteDimensional (𝓗 := 𝓗)
  have hσE : σ = Z.inc.comp (inE c τ) := inc_eq E Z.Ω _ _ hσ
  obtain ⟨f, hf⟩ : ∃ f : (E →+* ℂ_[p]) → (E →+* ℂ), ∀ s, s = κ.comp (inE c (f s)) :=
    ⟨fun s => (GlobalTheory.T.cp_embedding_factors_through_complex E H l c p κ s).choose, fun s => (GlobalTheory.T.cp_embedding_factors_through_complex E H l c p κ s).choose_spec⟩
  obtain ⟨hI, hℓ₀, hnorm⟩ := GlobalTheory.T.cp_integers_valuation_ring p
  obtain ⟨hint, hcard⟩ := GlobalTheory.T.number_field_embeddings_into_cp_integral E p
  have hinv : ∀ a, H.bar (H.bar a) = a := fun a => (GlobalTheory.T.cm_conjugation_compat_complex_conj E H τ a).2
  have hbarF : ∀ a : 𝓞 E, inE c (ComplexEmbedding.conjugate τ) (a : E) = inE c τ (H.bar a : 𝓞 E) := fun a =>
    Subtype.ext (GlobalTheory.T.cm_conjugation_compat_complex_conj E H τ a).1
  obtain ⟨gm, hgm0, hgm⟩ := GlobalTheory.T.cm_type_valuation_embedding E (OCp p) ℂ_[p] H.bar (κ.comp (inE c τ))
    (κ.comp (inE c (ComplexEmbedding.conjugate τ)))
    (fun s => Module.finrank Z.Ω (HT.eigSp Z.ρ (Z.inc.comp (inE c (f s))))) D.p D.q
    (NormedField.valuation (K := ℂ_[p])) hI hℓ₀ hint hcard (fun a => by simp only [RingHom.comp_apply, hbarF]) hinv
  refine ⟨(a / M) * Real.log ‖κ (β ϖ)‖ + Real.log ‖gm‖, ?_⟩
  intro V K _ _ _ _ _ _ j βK y vv ww T tK m m' hj hκ hF hIv hIw

  obtain ⟨z, hz⟩ := GlobalTheory.T.dvr_point_eigen_frame_reduction E H D l Xo c O β Y p κ V K j βK y hr hj hκ hF.1
  obtain ⟨h₁, h₂, ψ, hsp, hle, hval, hval', hVr, hinc⟩ :=
    GlobalTheory.T.dvr_point_component_eigen_reduction E H D l Xo c O β Y U Z p κ V K j βK y z hinj hr hj hκ hF.1 hF.2.1 hz
  haveI : CharZero K := charZero_of_injective_ringHom βK.injective
  obtain ⟨U₁, hU₁, t, ht⟩ := 𝓗.free ⟨_, h₂⟩
  obtain ⟨U₂, hU₂, ℓ, hℓs, hℓ⟩ := 𝓗.vb ⟨_, h₂⟩ trivial
  have hy₁ : centre (y ≫ Y.j) ∈ U₁ := hsp.mem_open U₁.2 hU₁
  have hy₂ : centre (y ≫ Y.j) ∈ U₂ := hsp.mem_open U₂.2 hU₂
  have hH : ∀ q : Cpt (Z.ξ₀ ≫ Y.j), q.1 ∈ U₁ → q.1 ∈ U₂ → HodgeAt 𝓗.ρH (𝓗.HL q) ℓ t := by
    intro q q₁ q₂
    have hfr := hℓ q trivial q₂
    refine ⟨ht q q₁, (congrFun 𝓗.map_fst q).trans hfr.2, fun f => ?_⟩
    have e := congrFun 𝓗.comap_inr q
    have : ((0 : Z.V), f) ∈ 𝓗.HL q ↔ f ∈ (Z.M.lat.dual) q := by
      rw [← e]; exact Iff.rfl
    rw [this, ← hfr.2]
    exact Iff.rfl
  have hHx := hH ⟨_, h₂⟩ hU₁ hU₂
  have hHy := hH ⟨_, h₁⟩ hy₁ hy₂
  have hLI : LinearIndependent Z.Ω ℓ := (hℓ ⟨_, h₂⟩ trivial hU₂).1
  obtain ⟨htmem, hstab, hρst⟩ := GlobalTheory.T.hodge_lattice_stable_under_action E Z.Ω Z.V Z.ρ 𝓗.ρH _ _ _ ℓ t (𝓗.HL ⟨_, h₁⟩) 𝓗.act_fst hHy
  have hmemC : ∀ r : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₂⟩, (j.comp ψ) ⟨r, hle r.2⟩ ∈ (algebraMap (OCp p) ℂ_[p]).range := by
    intro r
    obtain ⟨x, hx⟩ := hVr r (hle r.2) r.2
    rw [hnorm, RingHom.comp_apply, ← hx]
    exact (hj _).2 ⟨x, rfl⟩
  have hmemK : ∀ r : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₂⟩, ψ ⟨r, hle r.2⟩ ∈ (algebraMap V K).range :=
    fun r => hVr r (hle r.2) r.2
  obtain ⟨ρC, ρHC, ev, HV, hC1, hC2, hTC, hEC, hHV1, hHV2, hFC⟩ :=
    GlobalTheory.T.hodge_lattice_extend_scalars E Z.Ω Z.V Z.ρ 𝓗.ρH H.bar _ _ hle _ _ ℓ t (𝓗.HL ⟨_, h₂⟩) (𝓗.HL ⟨_, h₁⟩) ℂ_[p] (OCp p) (j.comp ψ)
      𝓗.act_fst 𝓗.act_inr hLI hℓs hHx hHy hmemC
  obtain ⟨ρK, -, -, -, -, -, hTK, -, -, -, -⟩ :=
    (GlobalTheory.T.hodge_lattice_extend_scalars E Z.Ω Z.V Z.ρ 𝓗.ρH H.bar _ _ hle _ _ ℓ t (𝓗.HL ⟨_, h₂⟩) (𝓗.HL ⟨_, h₁⟩) K V ψ
      𝓗.act_fst 𝓗.act_inr hLI hℓs hHx hHy hmemK)

  haveI : IsLocalRing (regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩) := GlobalTheory.T.generic_point_component_local_ring _ _ _ Z.gen _
  have hcarry : ∀ (τ₀ : E →+* ℂ) (e : E), ∃ h : Z.inc.comp (inE c τ₀) e ∈ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩,
      ψ ⟨_, h⟩ = βK.comp (inE c τ₀) e := fun τ₀ e => hinc _
  have hcarryC : ∀ (τ₀ : E →+* ℂ) (e : E), ∃ h : Z.inc.comp (inE c τ₀) e ∈ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩,
      (j.comp ψ) ⟨_, h⟩ = κ.comp (inE c τ₀) e := fun τ₀ e => by
    obtain ⟨h, e'⟩ := hinc (inE c τ₀ e)
    refine ⟨h, ?_⟩
    have e'' : ψ ⟨(Z.inc.comp (inE c τ₀)) e, h⟩ = βK (inE c τ₀ e) := e'
    rw [RingHom.comp_apply, e'', ← hκ]
    rfl
  have hregF : ∀ (τ₀ : E →+* ℂ) (e : E), Z.inc.comp (inE c τ₀) e ∈ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩ :=
    fun τ₀ e => (hcarry τ₀ e).1
  subst hσE
  have hws' : Submodule.span Z.Ω (Set.range w) = HT.eigSp Z.ρ (Z.inc.comp (inE c (ComplexEmbedding.conjugate τ))) := by
    rw [hws]; exact eig_eq E Z.Ω Z.V Z.ρ _ _ (fun a => rfl)
  have hrk : Module.finrank Z.Ω (HT.eigSp Z.ρ (Z.inc.comp (inE c τ))) = D.p := by
    rw [← hvs, finrank_span_eq_card hv]; simp
  have hrk' : Module.finrank Z.Ω (HT.eigSp Z.ρ (Z.inc.comp (inE c (ComplexEmbedding.conjugate τ)))) = D.q := by
    rw [← hws', finrank_span_eq_card hw]; simp
  obtain ⟨b₁, b₂, u', A', hb₁, hs₁, hb₂, hs₂, had', hu'm, hA', hfA⟩ :=
    GlobalTheory.T.hodge_lattice_eigen_decomposition_local E Z.Ω Z.V Z.ρ 𝓗.ρH H.bar _ _ D.p D.q ℓ t (𝓗.HL ⟨_, h₁⟩) (Z.inc.comp (inE c τ))
      (Z.inc.comp (inE c (ComplexEmbedding.conjugate τ))) 𝓗.act_fst 𝓗.act_inr
      (fun a => by simp only [RingHom.comp_apply, hbarF]) hinv (hregF τ) (hregF _) hLI hℓs hHy hrk hrk'
  have hcoord : ∀ {n : ℕ} (b : Fin n → Z.V) (W' : Submodule _ Z.V), W' ≤ Submodule.span (regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩) (Set.range ℓ) →
      (∀ i, b i ∈ W') → ∃ x : Fin n → Fin _ → regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩, ∀ i, b i = comb ℓ (x i) := by
    intro n b W' hW hb
    choose x hx using fun i => (Submodule.mem_span_range_iff_exists_fun _).1 (hW (hb i))
    exact ⟨x, fun i => (hx i).symm⟩
  have hin₁ : ∀ i, b₁ i ∈ HT.eigSub Z.ρ (Z.inc.comp (inE c τ)) (Submodule.span (regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩) (Set.range ℓ)) :=
    fun i => hs₁ ▸ Submodule.subset_span ⟨i, rfl⟩
  have hin₂ : ∀ i, b₂ i ∈ HT.eigSub Z.ρ (Z.inc.comp (inE c (ComplexEmbedding.conjugate τ))) (Submodule.span (regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩) (Set.range ℓ)) :=
    fun i => hs₂ ▸ Submodule.subset_span ⟨i, rfl⟩
  obtain ⟨x₁, hx₁⟩ := hcoord b₁ _ inf_le_left hin₁
  obtain ⟨x₂, hx₂⟩ := hcoord b₂ _ inf_le_left hin₂
  obtain ⟨hK₁, hK₁s⟩ := GlobalTheory.T.reduce_lattice_coords_to_residue E Z.Ω Z.V K Z.ρ _ _ _ ℓ ψ ρK _ (βK.comp (inE c τ)) b₁ x₁ hLI hℓs hρst hTK
    (hcarry τ) hx₁ hb₁ hs₁ hrk
  obtain ⟨hK₂, hK₂s⟩ := GlobalTheory.T.reduce_lattice_coords_to_residue E Z.Ω Z.V K Z.ρ _ _ _ ℓ ψ ρK _ (βK.comp (inE c (ComplexEmbedding.conjugate τ))) b₂ x₂ hLI hℓs hρst hTK
    (hcarry _) hx₂ hb₂ hs₂ hrk'
  obtain ⟨MU, MY, hSV, hVal, hAU, hAY⟩ := GlobalTheory.T.component_specialization_lattice_basis E H D l Xo c O β Y U Z K y h₁ ψ _ ℓ ρK hval
    (hℓ ⟨_, h₁⟩ trivial hy₂) hTK

  have hfrK : ∀ {n : ℕ} (σ₀ : E →+* K) (σi : 𝓞 E →+* K) (bK : Fin n → Fin _ → K), (∀ a : 𝓞 E, σi a = σ₀ (a : E)) →
      LinearIndependent K bK → Submodule.span K (Set.range bK) = HT.eigSp ρK σ₀ →
      IsEigFrame Xo.univ.t.act (under y) σi (fun i => MU.pt (bK i)) := by
    intro n σ₀ σi bK hi h1 h2
    rw [GlobalTheory.T.eigen_frame_iff_eigenspace_basis _ _ _ _ _ MU _ _ ρK σi n bK hAU, eig_eq E K _ ρK σi σ₀ hi]
    exact (GlobalTheory.T.basis_of_submodule_iff_unique_coords K _ _ n bK).1 ⟨h1, h2⟩
  have hFy : IsFramed U τ βK y (fun i => MU.pt (fun k => ψ (x₁ i k))) (fun i => MU.pt (fun k => ψ (x₂ i k))) :=
    ⟨hF.1, hF.2.1, hfrK (βK.comp (inE c τ)) _ _ (fun a => rfl) hK₁ hK₁s,
      hfrK (βK.comp (inE c (ComplexEmbedding.conjugate τ))) _ _ (fun a => rfl) hK₂ hK₂s⟩
  choose vK hvK using fun i => MU.onto (vv i) (hF.2.2.1.1 i).1
  choose wK hwK using fun i => MU.onto (ww i) (hF.2.2.2.1 i).1
  obtain rfl : vv = fun i => MU.pt (vK i) := funext fun i => (hvK i).symm
  obtain rfl : ww = fun i => MU.pt (wK i) := funext fun i => (hwK i).symm
  have hbasK : ∀ {n : ℕ} (σ₀ : E →+* K) (σi : 𝓞 E →+* K) (bK : Fin n → Fin _ → K), (∀ a : 𝓞 E, σi a = σ₀ (a : E)) →
      IsEigFrame Xo.univ.t.act (under y) σi (fun i => MU.pt (bK i)) →
      LinearIndependent K bK ∧ Submodule.span K (Set.range bK) = HT.eigSp ρK σ₀ := by
    intro n σ₀ σi bK hi h
    rw [GlobalTheory.T.eigen_frame_iff_eigenspace_basis _ _ _ _ _ MU _ _ ρK σi n bK hAU, eig_eq E K _ ρK σi σ₀ hi] at h
    exact (GlobalTheory.T.basis_of_submodule_iff_unique_coords K _ _ n bK).2 h
  obtain ⟨hvLI, hvsp⟩ := hbasK (βK.comp (inE c τ)) _ vK (fun a => rfl) hF.2.2.1
  obtain ⟨hwLI, hwsp⟩ := hbasK (βK.comp (inE c (ComplexEmbedding.conjugate τ))) _ wK (fun a => rfl) hF.2.2.2
  have hfr₁ := hℓ ⟨_, h₁⟩ trivial hy₂
  have hfr₂ := hℓ ⟨_, h₂⟩ trivial hU₂
  have hvV := GlobalTheory.T.dvr_specialization_eigen_frame E H D l Xo c O β Y U Z V K y z h₁ h₂ ψ _ ℓ ρK MU MY T tK m m' _ (βK.comp (inE c τ)) _ vK
    hz hle hVr hfr₂ hfr₁ hSV hVal hAU (fun a => rfl) hIv hvLI
  have hwV := GlobalTheory.T.dvr_specialization_eigen_frame E H D l Xo c O β Y U Z V K y z h₁ h₂ ψ _ ℓ ρK MU MY T tK m m' _
    (βK.comp (inE c (ComplexEmbedding.conjugate τ))) _ wK hz hle hVr hfr₂ hfr₁ hSV hVal hAU (fun a => rfl) hIw hwLI
  have hjmap := GlobalTheory.T.tied_action_compose_residue_map E Z.Ω Z.V K ℂ_[p] Z.ρ _ _ ℓ ψ j ρK ρC hρst hTK hTC
  have hjV : ∀ a : K, a ∈ (algebraMap V K).range → j a ∈ (algebraMap (OCp p) ℂ_[p]).range := fun a ha =>
    (hnorm _).2 ((hj a).2 ha)
  obtain ⟨hvC, hvCs, hvCA⟩ := GlobalTheory.T.fraction_field_eigen_basis_descends E K ℂ_[p] V (OCp p) j _ _ ρK ρC (βK.comp (inE c τ)) vK hjV hjmap hvLI hvV
  obtain ⟨hwC, hwCs, hwCA⟩ := GlobalTheory.T.fraction_field_eigen_basis_descends E K ℂ_[p] V (OCp p) j _ _ ρK ρC (βK.comp (inE c (ComplexEmbedding.conjugate τ))) wK hjV hjmap hwLI hwV
  have hjσ : ∀ τ₀ : E →+* ℂ, j.comp (βK.comp (inE c τ₀)) = κ.comp (inE c τ₀) := fun τ₀ => by
    rw [← RingHom.comp_assoc, hκ]
  rw [hjσ] at hvCs hvCA hwCs hwCA
  choose PK hPK using fun i => (Submodule.mem_span_range_iff_exists_fun K).1
    (show vK i ∈ Submodule.span K (Set.range fun i k => ψ (x₁ i k)) by
      rw [hK₁s, ← hvsp]; exact Submodule.subset_span ⟨i, rfl⟩)
  choose QK hQK using fun i => (Submodule.mem_span_range_iff_exists_fun K).1
    (show wK i ∈ Submodule.span K (Set.range fun i k => ψ (x₂ i k)) by
      rw [hK₂s, ← hwsp]; exact Submodule.subset_span ⟨i, rfl⟩)
  have hchg := hφ.chg K βK y _ _ _ _ (Matrix.of PK) (Matrix.of QK) hFy hF
    (fun i => (GlobalTheory.T.is_comb_tangent_iff_linear_sum _ _ _ _ _ MU _ _ _ _).2 (hPK i).symm)
    (fun i => (GlobalTheory.T.is_comb_tangent_iff_linear_sum _ _ _ _ _ MU _ _ _ _).2 (hQK i).symm)

  have hsp₁ : ∀ i, b₁ i ∈ Submodule.span Z.Ω (Set.range v) := fun i => hvs ▸ (hin₁ i).2
  have hsp₂ : ∀ i, b₂ i ∈ Submodule.span Z.Ω (Set.range w) := fun i => hws' ▸ (hin₂ i).2
  choose P hP using fun i => (Submodule.mem_span_range_iff_exists_fun Z.Ω).1 (hsp₁ i)
  choose Q hQ using fun i => (Submodule.mem_span_range_iff_exists_fun Z.Ω).1 (hsp₂ i)
  have hPb : b₁ = fun i => ∑ k, Matrix.of P i k • v k := funext fun i => (hP i).symm
  have hQb : b₂ = fun i => ∑ k, Matrix.of Q i k • w k := funext fun i => (hQ i).symm
  have hP0 : (Matrix.of P).det ≠ 0 := HodgeDeterminantLattice.det_ne_zero (u := v) (by rw [← hPb]; exact hb₁)
  have hQ0 : (Matrix.of Q).det ≠ 0 := HodgeDeterminantLattice.det_ne_zero (u := w) (by rw [← hQb]; exact hb₂)
  obtain ⟨u₀, hu₀, hu₀s⟩ := 𝓗.exists_basis_eigSp (Z.inc.comp (inE c τ))
  have hdim : Module.finrank Z.Ω (HT.eigSp 𝓗.ρH (Z.inc.comp (inE c τ))) = D.p + D.q := by
    rw [← hu₀s, finrank_span_eq_card hu₀]; simp
  obtain ⟨huLI, huS⟩ := GlobalTheory.T.adapted_basis_spans_eigenspace E Z.Ω Z.V 𝓗.ρH _ D.p D.q v w u had hv hdim inferInstance
  obtain ⟨B, hB, hBdet⟩ := GlobalTheory.T.adapted_bases_change_by_block_matrices E Z.Ω Z.V 𝓗.ρH _ D.p D.q v b₁ w b₂ u u' (Matrix.of P) (Matrix.of Q) had had' hv huS
    (fun i => (hP i).symm) (fun i => (hQ i).symm)
  set A'Ω : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) Z.Ω := (regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩).subtype.mapMatrix A' with hA'Ω
  have hdetA' : A'Ω.det = ((A'.det : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩) : Z.Ω) := by
    rw [hA'Ω, ← RingHom.map_det]; rfl
  have hfu : (fun i => ∑ k, (A'Ω * B) i k • u k) = fun i => HT.eigProj 𝓗.ρH (Z.inc.comp (inE c τ)) (t i) := by
    funext i
    rw [hfA i, ← HodgeDeterminantLattice.sum_smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hB k]
    rfl
  have hσx : ∀ a : 𝓞 E, (Z.inc.comp (inE c τ)) (a : E) ∈ (algebraMap (regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₂⟩) Z.Ω).range := fun a =>
    ⟨⟨_, GlobalTheory.T.cm_integers_regular_at_component E H D l Xo c O β Y U Z τ _ hσ ⟨_, h₂⟩ a⟩, rfl⟩
  have hframe : (𝓗.quot (Z.inc.comp (inE c τ))).IsFrameAt (fun i => ∑ k, (A'Ω * B) i k • u k) ⟨_, h₂⟩ := by
    rw [hfu]
    exact ⟨HodgeDeterminantLattice.linearIndependent_eigProj _ (ht ⟨_, h₂⟩ hU₁), HodgeDeterminantLattice.eigQuot_eq_span _ (ht ⟨_, h₂⟩ hU₁) hσx⟩
  have hgen := HodgeDeterminantLattice.detLat_of_frame huLI hframe
  have hVy := hrep K βK y _ _ b₁ b₂ (α / (Matrix.of P).det) (κ' / (Matrix.of Q).det) hFy
    (by rw [hPb, GlobalTheory.T.iota_multi_linear_combination_det, smul_smul, div_mul_cancel₀ _ hP0]) (by rw [hQb, GlobalTheory.T.iota_multi_linear_combination_det, smul_smul, div_mul_cancel₀ _ hQ0])
    (fun i => ⟨_, by rw [hx₁ i]; exact hVal (x₁ i), hSV _⟩) (fun i => ⟨_, by rw [hx₂ i]; exact hVal (x₂ i), hSV _⟩)
  obtain ⟨hd, hd'⟩ := hval' _ _ hVy
  obtain ⟨ud, hud⟩ := hA'
  set dR : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩ := ⟨_, hd⟩ * ((ud⁻¹ : (regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩)ˣ) : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩) with hdR
  have hud0 : ((ud : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩) : Z.Ω) ≠ 0 := fun h0 =>
    ud.ne_zero (Subtype.ext h0)
  have hdv : (α / κ') / (A'Ω * B).det = (dR : Z.Ω) := by
    have hinvc : (((ud⁻¹ : (regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩)ˣ) : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩) : Z.Ω) =
        ((ud : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩) : Z.Ω)⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      have h2 : (((((ud⁻¹ : (regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩)ˣ) : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩) * (ud : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩)) : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩) : Z.Ω) = 1 := by
        rw [ud.inv_mul]; rfl
      exact h2
    have hBd : B.det = (Matrix.of P).det / (Matrix.of Q).det := eq_div_of_mul_eq hQ0 hBdet
    have hdRc : (dR : Z.Ω) = (α / (Matrix.of P).det) / (κ' / (Matrix.of Q).det) * ((ud : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩) : Z.Ω)⁻¹ := by
      rw [hdR, ← hinvc]; rfl
    rw [Matrix.det_mul, hdetA', ← hud, hBd, hdRc]
    field_simp
  have hβ0 : βK (β ϖ) ≠ 0 := by
    rw [Ne, map_eq_zero, map_eq_zero_iff β hinj]
    exact hϖ.ne_zero
  obtain ⟨hϖr, hϖv⟩ := hinc (β ϖ)
  have hValϖ := hval ⟨_, hϖr⟩
  rw [hϖv] at hValϖ
  have hValϖ' := hval dR
  rw [← hdv] at hValϖ'
  obtain ⟨uV, huV⟩ := GlobalTheory.T.order_valuation_compare Y.X Z.Ω (Z.ξ₀ ≫ Y.j) _ (α / κ') (Z.inc (β ϖ)) M a V K z h₂ (A'Ω * B).det (ψ dR) (βK (β ϖ))
    Z.gen (hord _) hgen (by rw [hz]; exact hValϖ') (by rw [hz]; exact hValϖ) hβ0

  have hmemu : ∀ i, u' i ∈ 𝓗.HL ⟨_, h₁⟩ := hu'm
  have hσtieC := hcarryC τ
  have hadC := GlobalTheory.T.specialize_hodge_lattice_eigenbasis E Z.Ω Z.V ℂ_[p] _ _ D.p D.q ℓ (j.comp ψ) 𝓗.ρH ρHC (𝓗.HL ⟨_, h₁⟩) ev _ (κ.comp (inE c τ)) b₁ b₂ u' x₁ x₂ hu'm
    hEC hσtieC hstab had' hx₁ hx₂
  have hep : ∀ i, HT.eigProj 𝓗.ρH (Z.inc.comp (inE c τ)) (t i) ∈ 𝓗.HL ⟨_, h₁⟩ := fun i => by
    rw [hfA i]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_of_tower_mem _ (A' i k) (hu'm k)
  have hfC : ∀ i, HT.eigProj ρHC (κ.comp (inE c τ)) (ev ⟨t i, htmem i⟩) =
      ∑ k, ((j.comp ψ).mapMatrix A') i k • ev ⟨u' k, hu'm k⟩ := by
    intro i
    rw [← GlobalTheory.T.hodge_lattice_eval_eigProj_comm E Z.Ω Z.V ℂ_[p] _ _ ℓ (j.comp ψ) 𝓗.ρH ρHC (𝓗.HL ⟨_, h₁⟩) ev _ (κ.comp (inE c τ)) ⟨t i, htmem i⟩ (hep i) hEC hσtieC hstab]
    have : (⟨_, hep i⟩ : 𝓗.HL ⟨_, h₁⟩) = ∑ k, A' i k • (⟨u' k, hu'm k⟩ : 𝓗.HL ⟨_, h₁⟩) := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum]
      exact hfA i
    set_option synthInstance.maxHeartbeats 100000 in
      rw [this, map_sum]
    exact Finset.sum_congr rfl fun k _ => (ev.map_smulₛₗ _ _)
  have hrkC : ∀ s, Module.finrank ℂ_[p] (HT.eigSp ρC s) = Module.finrank Z.Ω (HT.eigSp Z.ρ (Z.inc.comp (inE c (f s)))) := by
    intro s
    refine GlobalTheory.T.finrank_eigSp_eq_of_lattice_specialization E Z.Ω Z.V ℂ_[p] Z.ρ _ _ ℓ (j.comp ψ) ρC _ s hLI hℓs hρst hTC ?_
    intro e
    obtain ⟨h, e'⟩ := hcarryC (f s) e
    exact ⟨h, e'.trans (by rw [← hf s])⟩
  obtain ⟨ε, hε⟩ := GlobalTheory.T.residue_hodge_lattice_adapted_basis E ℂ_[p] (OCp p) H.bar (κ.comp (inE c τ)) (κ.comp (inE c (ComplexEmbedding.conjugate τ))) _ D.p D.q
    ρC ρHC HV (fun i => ev ⟨t i, htmem i⟩) (fun i k => (j.comp ψ) (x₁ i k)) (fun i k => j (vK i k))
    (fun i k => (j.comp ψ) (x₂ i k)) (fun i k => j (wK i k)) (fun i => ev ⟨u' i, hu'm i⟩) ((j.comp ψ).mapMatrix A')
    (j.mapMatrix (Matrix.of PK)) (j.mapMatrix (Matrix.of QK)) gm hC1 hC2
    (fun a => by simp only [RingHom.comp_apply, hbarF]) hinv (hint _) (hFC htmem) hadC
    (fun i => by
      funext k
      have := congrFun (hPK i) k
      rw [← this]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Finset.sum_apply, map_sum])
    (fun i => by
      funext k
      have := congrFun (hQK i) k
      rw [← this]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Finset.sum_apply, map_sum])
    (GlobalTheory.T.reduce_lattice_coords_to_residue E Z.Ω Z.V ℂ_[p] Z.ρ _ _ _ ℓ (j.comp ψ) ρC _ (κ.comp (inE c τ)) b₁ x₁ hLI hℓs hρst hTC (hcarryC τ) hx₁ hb₁ hs₁ hrk).1 hfC
    (fun v' w' u'' B' h1 h2 h3 h4 h5 h6 h7 => hgm (Fin _ → ℂ_[p]) ρC ρHC HV (stdLat (OCp p) ℂ_[p] _) (fun i => ev ⟨t i, htmem i⟩) v' w' u'' B'
      hC1 hC2 hHV1 hHV2 (hFC htmem) hrkC h1 h2 h3 h4 h5 h6 h7)
    hvC hvCs hvCA hwC hwCs hwCA

  have hPd : (Matrix.of PK).det ≠ 0 := HodgeDeterminantLattice.det_ne_zero (u := fun i k => ψ (x₁ i k)) (by
    have : (fun i => ∑ k, Matrix.of PK i k • (fun k' => ψ (x₁ k k'))) = vK := funext hPK
    rw [this]; exact hvLI)
  have hφ0 := hφ.ne K βK y _ _ hF
  have hψd : ψ dR * ψ (ud : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩) = φ K y (fun i => MU.pt (fun k => ψ (x₁ i k))) (fun i => MU.pt (fun k => ψ (x₂ i k))) := by
    rw [← map_mul, hdR, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]
    exact hd'
  rw [← RingHom.map_det, ← RingHom.map_det, ← RingHom.map_det, ← hud, RingHom.comp_apply] at hε
  have hjφ : j (φ K y (fun i => MU.pt (vK i)) (fun i => MU.pt (wK i))) =
      j (ψ dR) * (algebraMap (OCp p) ℂ_[p] ε * gm) := by
    apply mul_right_cancel₀ ((map_ne_zero j).2 hPd)
    rw [← map_mul, hchg, ← hψd, map_mul, map_mul, _root_.mul_assoc, hε]
    ring
  have hjφ0 : j (φ K y (fun i => MU.pt (vK i)) (fun i => MU.pt (wK i))) ≠ 0 := (map_ne_zero j).2 hφ0
  have hx0 : j (ψ dR) ≠ 0 := fun h0 => hjφ0 (by rw [hjφ, h0, zero_mul])
  have hκπ : j (βK (β ϖ)) = κ (β ϖ) := by rw [← hκ]; rfl
  have hκ0 : κ (β ϖ) ≠ 0 := by rw [← hκπ]; exact (map_ne_zero j).2 hβ0
  have hmu : ‖j (algebraMap V K uV)‖ = 1 := norm_eq_one_of _ (j (algebraMap V K (uV⁻¹ : Vˣ))) ((hj _).2 ⟨_, rfl⟩) ((hj _).2 ⟨_, rfl⟩)
    (by rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one])
  have hlog := log_end M a (j (ψ dR)) (κ (β ϖ)) (j (algebraMap V K uV)) hM hx0 hκ0 hmu (by
    rw [← hκπ, ← map_pow, huV, map_mul, map_zpow₀])
  have hε1 : ‖algebraMap (OCp p) ℂ_[p] ε‖ = 1 := norm_eq_one_of _ (algebraMap (OCp p) ℂ_[p] (ε⁻¹ : (OCp p)ˣ)) ((hnorm _).1 ⟨_, rfl⟩) ((hnorm _).1 ⟨_, rfl⟩)
    (by rw [← map_mul, Units.mul_inv, map_one])
  rw [hjφ, norm_mul, norm_mul, hε1, _root_.one_mul, Real.log_mul (norm_ne_zero_iff.2 hx0) (norm_ne_zero_iff.2 hgm0), hlog]

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLinePAdicFrameStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_line_p_adic_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (ϖ : O) (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) (φ : FrameFn Xo c) (𝓗 : HodgeLat Z.M.lat Z.ρ H.bar (D.p + D.q)) (σ : E →+* Z.Ω) (v : Fin D.p → Z.V) (w : Fin D.q → Z.V) (u : Fin (D.p + D.q) → Z.V × Module.Dual Z.Ω Z.V) (α κ' : Z.Ω) (M : ℕ) (a : ℤ), τ (H.rt : E) = H.rt0 → Irreducible ϖ → Function.Injective β → (∀ x : c.F, ‖κ x‖ ≤ 1 ↔ x ∈ β.range) → (∀ b : 𝓞 E, σ (b : E) = Z.inc (tauIn c τ b)) → LinearIndependent Z.Ω v → Submodule.span Z.Ω (Set.range v) = HT.eigSp Z.ρ σ → LinearIndependent Z.Ω w → Submodule.span Z.Ω (Set.range w) = eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ))) → IsAdapted 𝓗.ρH σ v w u → 0 < M → (∀ x, OrderAt (detLat (𝓗.quot σ) u) (α / κ') (Z.inc (β ϖ)) M a x) → κ' ≠ 0 → Represents Y U τ Z.M (α • exteriorPower.ιMulti Z.Ω D.p v) (κ' • exteriorPower.ιMulti Z.Ω D.q w) φ → IsLineFn U τ φ → ∃ t : ℝ, HasFinNorm U τ φ p κ t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.value_at_point | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.value_at_point | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.value_at_point <;> assumption)
end

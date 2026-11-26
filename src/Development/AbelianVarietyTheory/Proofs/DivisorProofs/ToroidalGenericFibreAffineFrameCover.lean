module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVecEquiv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisCoverQuotientFreeFiniteAction
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramSmoothOfHolomorphicFrames
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactDefiniteUnitaryRestrictedProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDerivAt0CompLinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantNormFlatSectionEqNormDivNormDet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationValuesTransportFieldIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyRuleScaleSectionPowEight

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalGenericFibreAffineFrameCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalGenericFibreAffineFrameCover
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine

theorem frameCover_gen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (V : (gen Y).Opens) (τ : E →+* ℂ), τ (H.rt : E) = H.rt0 → FrameCover Y.t (genι Y) (genStr Y) V (HermitianCompactForm.chi c τ) D.p D.q := by
  intro E _ _ _ H D l Xo c O _ β Y V τ hτ z hz
  obtain ⟨U, hU, φ, f, hzU, hs, -⟩ := GlobalTheory.T.exists_affine_stable_lie_eigenspace_frame E H D l Xo c O β Y z
  obtain ⟨⟨v, w, hfr, -⟩, -⟩ := GlobalTheory.DetLine.EigParts.eigFrame_match E H D l Xo c O β Y τ hτ Set.univ
    Γ(gen Y, U) φ hU.fromSpec hs (Set.subset_univ _) f
  obtain ⟨r, hrV, hzr⟩ := hU.exists_basicOpen_le (V := V) ⟨z, hz⟩ hzU
  have hW := hU.basicOpen r
  have hle : (gen Y).basicOpen r ≤ U := (gen Y).basicOpen_le r
  let g : Γ(gen Y, U) →+* Γ(gen Y, (gen Y).basicOpen r) := ((gen Y).presheaf.map (homOfLE hle).op).hom
  have hx : (show Sp Γ(gen Y, (gen Y).basicOpen r) ⟶ gen Y from hW.fromSpec) = spMap g ≫ hU.fromSpec :=
    (hU.map_fromSpec hW (homOfLE hle).op).symm
  obtain ⟨v', w', h', -, -⟩ := exists_pull g hfr hx
  refine ⟨(gen Y).basicOpen r, hW, g.comp φ, v', w', hzr, h'.1, ?_, h'.2.2⟩
  rw [hW.range_fromSpec]
  exact hrV

end GlobalTheory.DetLine
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalGenericFibreAffineFrameCoverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toroidalGenericFibre_affineFrameCover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (V : (gen Y).Opens) (τ : E →+* ℂ), τ (H.rt : E) = H.rt0 → FrameCover Y.t (genι Y) (genStr Y) V (HermitianCompactForm.chi c τ) D.p D.q := by
  first | exact @GlobalTheory.DetLine.frameCover_gen | exact GlobalTheory.DetLine.frameCover_gen | (intros; apply GlobalTheory.DetLine.frameCover_gen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilIsRootLocal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilRootLocal

theorem exists_weilIs_root_local : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A],
    IsAbelianScheme A → ∀ (PP : RigLB A), CubicalStr A PP → ∀ (R : Type) [CommRing R] [IsLocalRing R]
    (t : Sp R ⟶ S) (n : ℕ) (g h : Over.mk t ⟶ A), g ^ n = 1 → h ^ n = 1 →
    ∃ u : Rˣ, u ^ n = 1 ∧ Out.WeilIs A PP.L (n : ℤ) g h (unitOn u) := by
  intro S A _ _ hA PP cub R _ _ t n g h hg hh
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have loc : ∀ z : Over.mk t ⟶ A, z ^ n = 1 → ∀ p : (Over.mk t).left, ∃ V : (Over.mk t).left.Opens, p ∈ V ∧
      ∃ θ : Out.ThetaGrp A PP.L (n : ℤ) (Out.overRes V), θ.pt = Out.overResι V ≫ z := fun z hz p => by
    obtain ⟨θ, hθ⟩ := TorsionThetaLocal.exists_theta_of_pow_eq_one S A PP cub R t n z hz
    obtain ⟨θ', hθ'⟩ := CommutatorPairing.exists_pull PP.isLB θ (Out.overResι ⊤)
    exact ⟨⊤, trivial, θ', by rw [hθ', hθ]⟩
  obtain ⟨c, hc⟩ := CommutatorPairing.exists_weilIs hG hA PP.isLB (loc g hg) (loc h hh)
  have pw : ∀ m : ℕ, Out.WeilIs A PP.L (n : ℤ) (g ^ (m + 1)) h (c ^ (m + 1)) := fun m => by
    induction m with
    | zero => rw [zero_add, pow_one, pow_one]; exact hc
    | succ m ih =>
      rw [pow_succ g (m + 1), pow_succ c (m + 1)]
      exact DiagPairing.weilIs_mul_left hG hA PP.isLB ih hc
  have e := pw n
  rw [pow_succ g, hg, _root_.one_mul] at e
  have hcn := CommutatorPairing.weilIs_unique hG hA PP.isLB e hc
  rw [pow_succ, mul_eq_right] at hcn
  obtain ⟨u, rfl⟩ : ∃ u : Rˣ, unitOn u = c :=
    (Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.toMulEquiv).surjective c
  refine ⟨u, unitOn_injective_of_commRing ?_, hc⟩
  show unitOn (u ^ n) = unitOn 1
  rw [unitOn, unitOn, map_pow, map_one]
  exact hcn

end GlobalTheory.WeilRootLocal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CarriesFramedPointOfUnitTriangularChart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CarriesFramedPointOfUnitTriangularChart
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FlagMod.Frames

theorem lies_of_chart_tri : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (F : Frames Y π), F.TopEigen → ∀ (S : Type) [CommRing S] [Algebra c.F S] (P : FrPt Xo c S) (z : Sp S ⟶ Z) (k : F.J) (hz : ⊤ ≤ z ⁻¹ᵁ F.U k) (hx : z ≫ π = frX P ≫ Y.j) (U : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S), (∀ σ, (U σ).BlockTriangular id) → (∀ σ i, IsUnit (U σ i i)) → (∀ σ i, frVec Y P rfl σ i = ∑ j, U σ j i • F.vecAt k z hz hx σ j) → F.Lies z P := by
  intro E _ _ _ H Dw l Xo c O _ β Y Z π F hT S _ _ P z k hz hx U hU hd hv
  obtain ⟨Q, hQ⟩ := hT.exists_chartFr (frX_snd P) hx k hz
  have hQx : frX Q ≫ Y.j = frX P ≫ Y.j := hQ.over.trans hx
  have hv' : ∀ σ i, frVec Y P rfl σ i = ∑ j, U σ j i • frVec Y Q hQx σ j := fun σ i => by
    rw [hQ.frVec_eq hx hQx]; exact hv σ i
  have e : P.x = Q.x := by
    rw [← frX_fst, ← frX_fst, xF_ext (Y := Y) (frX_snd P) (frX_snd Q) hQx.symm]
  have hB : ∃ t, FrBor t Q P := by
    have hM := F.inM hz hx
    clear hv hQ
    revert hv' hQx hM
    obtain ⟨x', xo', v', t1', t2', t3', s', t4'⟩ := P
    dsimp only at e
    subst e
    intro hQx hv' hM
    obtain ⟨u0, hu0⟩ := gen_unit Q.s s' Q.gen t4'
    exact ⟨_, frBor_of_frVec hM hQx rfl
      (fun ix => match ix with | none => u0 | some p => (hd p.1 p.2).unit) U hU (fun _ _ => rfl) hv' fun _ => hu0⟩
  obtain ⟨t, ht⟩ := hB
  exact hQ.lies.frBor ht

end GlobalTheory.FlagMod.Frames
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CarriesFramedPointOfUnitTriangularChartStatement
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carries_framedPoint_of_unitTriangular_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (F : Frames Y π), F.TopEigen → ∀ (S : Type) [CommRing S] [Algebra c.F S] (P : FrPt Xo c S) (z : Sp S ⟶ Z) (k : F.J) (hz : ⊤ ≤ z ⁻¹ᵁ F.U k) (hx : z ≫ π = frX P ≫ Y.j) (U : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S), (∀ σ, (U σ).BlockTriangular id) → (∀ σ i, IsUnit (U σ i i)) → (∀ σ i, frVec Y P rfl σ i = ∑ j, U σ j i • F.vecAt k z hz hx σ j) → F.Lies z P := by
  first | exact @GlobalTheory.FlagMod.Frames.lies_of_chart_tri | exact GlobalTheory.FlagMod.Frames.lies_of_chart_tri | (intros; apply GlobalTheory.FlagMod.Frames.lies_of_chart_tri <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitOfNormOneFractionRingDvr
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitOfNormOneFractionRingDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem GlobalTheory.KeyEven.fractionRing_norm_one_unit : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (C : Type) [NormedField C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ a : FractionRing V, ‖algebraMap (FractionRing V) C a‖ = 1 → ∃ u : Vˣ, a = algebraMap V (FractionRing V) u := by
  intro V _ _ _ C _ _ hC a ha
  have key : ∀ x : V, ‖algebraMap (FractionRing V) C (algebraMap V _ x)‖ = 1 → IsUnit x := by
    intro x hx
    by_contra hu
    have hm : x ∈ IsLocalRing.maximalIdeal V := (IsLocalRing.mem_maximalIdeal x).2 hu
    have := hC.2 x hm
    rw [hx] at this
    exact lt_irrefl _ this
  rcases ValuationRing.isInteger_or_isInteger V a with ⟨x, hx⟩ | ⟨x, hx⟩
  · have hu := key x (by rw [hx]; exact ha)
    exact ⟨hu.unit, by simp [hx]⟩
  · have hx' : ‖algebraMap (FractionRing V) C (algebraMap V _ x)‖ = 1 := by
      rw [hx, map_inv₀, norm_inv, ha, inv_one]
    have hu := key x hx'
    refine ⟨hu.unit⁻¹, ?_⟩
    have ha0 : a ≠ 0 := by
      rintro rfl
      simp at ha
    have h1 : algebraMap V (FractionRing V) (↑hu.unit⁻¹ : V) * algebraMap V (FractionRing V) x = 1 := by
      rw [← map_mul]
      have : (↑hu.unit⁻¹ : V) * x = 1 := by
        have := hu.unit.inv_mul
        simpa using this
      rw [this, map_one]
    rw [hx] at h1
    field_simp at h1
    exact h1.symm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitOfNormOneFractionRingDvrStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_of_norm_one_fractionRing_dvr : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (C : Type) [NormedField C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ a : FractionRing V, ‖algebraMap (FractionRing V) C a‖ = 1 → ∃ u : Vˣ, a = algebraMap V (FractionRing V) u := by
  first | exact @GlobalTheory.KeyEven.fractionRing_norm_one_unit | exact GlobalTheory.KeyEven.fractionRing_norm_one_unit | (intros; apply GlobalTheory.KeyEven.fractionRing_norm_one_unit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationDataValuesUltrametric
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationDataValuesUltrametric
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section
namespace GlobalTheory.IntGauge

theorem exists_ball (C : Type) [NormedField C] [IsUltrametricDist C] :
    ∃ S : ValuationSubring C, ∀ x, x ∈ S ↔ ‖x‖ ≤ 1 := by
  refine ⟨{ carrier := {x | ‖x‖ ≤ 1}
            mul_mem' := fun {a b} ha hb => by
              simp only [Set.mem_setOf_eq, norm_mul] at *
              exact mul_le_one₀ ha (norm_nonneg _) hb
            one_mem' := by simp
            add_mem' := fun {a b} ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
            zero_mem' := by simp
            neg_mem' := fun {a} ha => by simpa using ha
            mem_or_inv_mem' := fun x => by
              by_cases h : ‖x‖ ≤ 1
              · exact Or.inl h
              · right
                show ‖x⁻¹‖ ≤ 1
                rw [norm_inv]
                exact inv_le_one_of_one_le₀ (le_of_lt (not_le.1 h)) }, fun x => Iff.rfl⟩

theorem exists_intN : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V)), ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∃ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN := by
  intro V _ _ _ _ _ D C _ _ _ _ _ _ hC
  obtain ⟨S, hS⟩ := exists_ball C
  obtain ⟨N, ν, hν⟩ := GlobalTheory.ValuesExist.exists_integral_values GlobalTheory.firstFiveLaws.1 V D.toPre D.psi_even D.tau_bimult
    C S (fun r => (hS _).2 (hC.1 r))
  exact ⟨N, ν, S, hS, hν⟩

end GlobalTheory.IntGauge
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationDataValuesUltrametricStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_degenerationData_values_ultrametric : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V)), ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∃ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN := by
  first | exact @GlobalTheory.IntGauge.exists_intN | exact GlobalTheory.IntGauge.exists_intN | (intros; apply GlobalTheory.IntGauge.exists_intN <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseFlagBundlePreimageModuli
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseFlagBundlePreimageModuli
noncomputable section

namespace GlobalTheory.FlagMod.FieldFlag

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

theorem isOpenMap_scheme_comp {X₁ X₂ X₃ : Scheme.{0}} {f : X₁ ⟶ X₂} {g : X₂ ⟶ X₃} (hf : IsOpenMap f)
    (hg : IsOpenMap g) : IsOpenMap (f ≫ g) := hg.comp hf

theorem isOpenMap_cbase {X : Scheme.{0}} {T : Type} (m : T → ℕ) (U : X.affineOpens) : IsOpenMap (cbase m U) := by
  haveI : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
  exact isOpenMap_scheme_comp (MvPolynomial.isOpenMap_comap_C) U.2.fromSpec.isOpenEmbedding.isOpenMap

theorem dense_genMap_preimage : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)) (κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)) [∀ b w, IsOpenImmersion (κ b w)] (hZ : Cells A π g κ), Dense (genMap π ⁻¹' Set.range Y.jQ) := by
  intro E _ _ _ H Dw l Xo c Y p A Z π g κ _ hZ
  have hcell : ∀ b w, IsOpenMap (κ b w ≫ π) := fun b w => by
    rw [hZ.plk.base b w]; exact isOpenMap_cbase _ _
  have hπ : IsOpenMap π := by
    intro O hO
    rw [isOpen_iff_forall_mem_open]
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨b, w, y, rfl⟩ := hZ.cover z
    refine ⟨(κ b w ≫ π) '' (κ b w ⁻¹' O), ?_, hcell b w _ (hO.preimage (κ b w).continuous), y, hz, rfl⟩
    rintro _ ⟨y', hy', rfl⟩
    exact ⟨κ b w y', hy', rfl⟩
  have hid : IsIso (spMap (RingHom.id c.F)) := by
    rw [spMap, CommRingCat.ofHom_id, Spec.map_id]; infer_instance
  have he : genMap π = pullback.fst (π ≫ Y.s) (spMap (RingHom.id c.F)) ≫ π ≫
      inv (pullback.fst Y.s (spMap (RingHom.id c.F))) := by
    rw [← cancel_mono (pullback.fst Y.s (spMap (RingHom.id c.F)))]
    simp only [genMap, Category.assoc, IsIso.inv_hom_id, Category.comp_id, pullback.lift_fst]
  have hgen : IsOpenMap (genMap π) := by
    rw [he]
    exact isOpenMap_scheme_comp (pullback.fst (π ≫ Y.s) (spMap (RingHom.id c.F))).isOpenEmbedding.isOpenMap
      (isOpenMap_scheme_comp hπ (inv (pullback.fst Y.s (spMap (RingHom.id c.F)))).isOpenEmbedding.isOpenMap)
  exact Y.jQ_dense.preimage hgen

end GlobalTheory.FlagMod.FieldFlag
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseFlagBundlePreimageModuliStatement
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_flagBundle_preimage_moduli : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)) (κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)) [∀ b w, IsOpenImmersion (κ b w)] (hZ : Cells A π g κ), Dense (genMap π ⁻¹' Set.range Y.jQ) := by
  first | exact @GlobalTheory.FlagMod.FieldFlag.dense_genMap_preimage | exact GlobalTheory.FlagMod.FieldFlag.dense_genMap_preimage | (intros; apply GlobalTheory.FlagMod.FieldFlag.dense_genMap_preimage <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrOverHeightOne
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.HeightOneCompletion

open IsLocalRing


set_option autoImplicit false in
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open NumberField IsDedekindDomain in
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal in
attribute [local instance] Over.cartesianMonoidalCategory in
attribute [local instance] _root_.GlobalTheory.CompHt.algPadicInt _root_.GlobalTheory.CompHt.algPadicField
  _root_.GlobalTheory.CompHt.towerPadic _root_.GlobalTheory.CompHt.factPadic
  _root_.GlobalTheory.PadicComplexHost.isAdicComplete in
open IsLocalRing in
theorem _root_.GlobalTheory.HeightOneCompletion.exists_cdvr_of_height_eq_one :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A] [CharZero A]
      (𝔭 : PrimeSpectrum A), 𝔭.asIdeal.height = 1 →
      ∃ (T : _root_.Formalism.L2.Pj.CDVR) (iT : Localization.AtPrime 𝔭.asIdeal →+* T.V),
        Function.Injective iT ∧ IsLocalHom iT := by
  intro A _ _ _ _ _ 𝔭 h
  obtain ⟨hdom, hic⟩ :=
    _root_.GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_isDomain 𝔭.asIdeal (Localization.AtPrime 𝔭.asIdeal)
  haveI := hdom
  haveI := hic
  haveI : IsNoetherianRing (Localization.AtPrime 𝔭.asIdeal) :=
    IsLocalization.isNoetherianRing 𝔭.asIdeal.primeCompl _ inferInstance
  have hdim : ringKrullDim (Localization.AtPrime 𝔭.asIdeal) = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height 𝔭.asIdeal (Localization.AtPrime 𝔭.asIdeal), h]
    rfl
  haveI := _root_.GlobalTheory.CdvrExt.isDVR_of_ringKrullDim_eq_one hdim
  have hinj : Function.Injective (algebraMap A (Localization.AtPrime 𝔭.asIdeal)) :=
    IsLocalization.injective _ (Ideal.primeCompl_le_nonZeroDivisors 𝔭.asIdeal)
  obtain ⟨O, _, _, _, j, r, hc, hj, hl, -, -, -⟩ :=
    _root_.GlobalTheory.exists_complete_discreteValuationRing_with_residues (Localization.AtPrime 𝔭.asIdeal)
      (ResidueField (Localization.AtPrime 𝔭.asIdeal)) (residue _) ∅ (ker_residue)
  haveI : CharZero (Localization.AtPrime 𝔭.asIdeal) := ⟨fun m n hmn =>
    Nat.cast_injective (R := A) (hinj (by rw [map_natCast, map_natCast]; exact hmn))⟩
  haveI : CharZero O := ⟨fun m n hmn =>
    Nat.cast_injective (R := Localization.AtPrime 𝔭.asIdeal)
      (hj (by rw [map_natCast, map_natCast]; exact hmn))⟩
  exact ⟨@_root_.Formalism.L2.Pj.CDVR.mk O _ _ _ hc _, j, hj, hl⟩

end GlobalTheory.HeightOneCompletion
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHeckeProductOfLocalTestFunctionsSection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHeckeProductOfLocalTestFunctionsSection
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.GlobHecke

theorem isHecke_globFn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
    ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)),
    IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f →
    IsHecke (globLev S K') (globFn S f) := by
  intro E _ _ _ hU n _ S hS K' hK' f hf
  refine ⟨?_, globFn_inv S K' f fun w => (hf.1 w).2⟩
  have hC : ∀ᶠ w in cofinite, tsupport (f w) = (KL n w : Set (UL n w)) := by
    filter_upwards [hK'.2, hf.2] with w h1 h2
    have ho : IsOpen (KL n w : Set (UL n w)) := h1 ▸ (hK'.1 w).1
    have hc : IsClosed (KL n w : Set (UL n w)) := Subgroup.isClosed_of_isOpen _ ho
    rw [h2, tsupport, Set.support_indicator]
    have : Function.support (1 : UL n w → ℂ) = Set.univ := by
      ext x; simp
    rw [this, Set.inter_univ, hc.closure_eq]
  have hcpt := GlobalTheory.BCT.LocCpt.loc_cpt E hU n S hS (fun w => tsupport (f w)) (fun w => (hf.1 w).1) hC
  set_option synthInstance.maxHeartbeats 200000 in
  refine HasCompactSupport.intro hcpt fun x hx => ?_
  simp only [Set.mem_setOf_eq, not_forall] at hx
  obtain ⟨w, hw, hxw⟩ := hx
  have hfin : (S ∩ Function.mulSupport fun w : Pl E => f w (toSub (UL n w) (cLoc w (x : UA E n)))).Finite := by
    have h := (GlobalTheory.BCT.LocAE.eventually_mem_KL E hU n x).and hf.2
    rw [Filter.eventually_cofinite] at h
    refine h.subset ?_
    rintro u ⟨-, hu⟩ ⟨h1, h2⟩
    apply hu
    show f u _ = 1
    rw [h2, Set.indicator_of_mem (show _ ∈ (KL n u : Set (UL n u)) from h1)]
    rfl
  unfold globFn
  rw [finprod_mem_eq_prod _ hfin]
  have h0 : f w (toSub (UL n w) (cLoc w (x : UA E n))) = 0 := image_eq_zero_of_notMem_tsupport hxw
  refine Finset.prod_eq_zero (i := w) ?_ h0
  rw [Set.Finite.mem_toFinset]
  refine ⟨hw, ?_⟩
  show f w _ ≠ 1
  rw [h0]
  exact zero_ne_one

end GlobalTheory.BCT.GlobHecke
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHeckeProductOfLocalTestFunctionsSectionStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHecke_productOfLocalTestFunctions_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → IsHecke (globLev S K') (globFn S f) := by
  first | exact @GlobalTheory.BCT.GlobHecke.isHecke_globFn | exact GlobalTheory.BCT.GlobHecke.isHecke_globFn | (intros; apply GlobalTheory.BCT.GlobHecke.isHecke_globFn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTransportAlongGeneratingIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTransportAlongGeneratingIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.SecTransport

theorem main : ∀ {X : Scheme.{0}} {M L : LB X} (e : LB.Iso M L), e.IsGen → M.IsLB → L.IsLB →
    ∀ σ : L.Sec, ∃ σ' : M.Sec, GlobalTheory.Cartier.SecMaps e σ' σ ∧ Out.nonzeroLocus σ ≤ Out.nonzeroLocus σ' := by
  intro X M L e he hM hL σ
  refine ⟨DVR.secOfIso (u := e) σ he hM hL, ?_, DVR.nonzeroLocus_secOfIso e σ he hM hL⟩
  intro p
  apply GlobalTheory.Cartier.ext_germ
  intro x hx
  set σ' := DVR.secOfIso (u := e) σ he hM hL
  have hx' : x ∈ M.U p.2 ⊓ L.U p.1 := ⟨hx.2, hx.1⟩
  have h1 : (X.presheaf.germ _ x hx).hom (resG X (inf_le_left : L.U p.1 ⊓ M.U p.2 ≤ L.U p.1) (σ.f p.1)) =
      (X.presheaf.germ _ x hx.1).hom (σ.f p.1) := GlobalTheory.Cartier.germ_resG _ x hx _
  have h2 : (X.presheaf.germ _ x hx).hom (resG X (inf_le_right : L.U p.1 ⊓ M.U p.2 ≤ M.U p.2) (σ'.f p.2)) =
      (X.presheaf.germ _ x hx.2).hom (σ'.f p.2) := GlobalTheory.Cartier.germ_resG _ x hx _
  have h3 : (X.presheaf.germ _ x hx.2).hom (σ'.f p.2) =
      (X.presheaf.germ _ x hx').hom (DVR.isoCand e σ p.2 p.1) := by
    rw [← DVR.secOfIso_spec (u := e) σ he hM hL p.2 p.1]
    exact (GlobalTheory.Cartier.germ_resG (inf_le_left : M.U p.2 ⊓ L.U p.1 ≤ M.U p.2) x hx' _).symm
  have h4 : (X.presheaf.germ _ x hx').hom (DVR.isoCand e σ p.2 p.1) =
      (X.presheaf.germ _ x hx').hom (((res (DVR.divLe p.2 p.1) (e.s p))⁻¹ : Γ(X, M.U p.2 ⊓ L.U p.1)ˣ) : Γ(X, M.U p.2 ⊓ L.U p.1)) *
        (X.presheaf.germ _ x hx.1).hom (σ.f p.1) := by
    unfold DVR.isoCand
    rw [map_mul]
    congr 1
    exact GlobalTheory.Cartier.germ_resG (inf_le_right : M.U p.2 ⊓ L.U p.1 ≤ L.U p.1) x hx' _
  have h5 : (X.presheaf.germ _ x hx').hom (((res (DVR.divLe p.2 p.1) (e.s p)) : Γ(X, M.U p.2 ⊓ L.U p.1)ˣ) : Γ(X, M.U p.2 ⊓ L.U p.1)) =
      (X.presheaf.germ _ x hx).hom ((@id (Γ(X, L.U p.1 ⊓ M.U p.2)ˣ) (e.s p) : Γ(X, L.U p.1 ⊓ M.U p.2))) :=
    GlobalTheory.Cartier.germ_resG (DVR.divLe p.2 p.1) x hx' _
  have h6 : (X.presheaf.germ _ x hx').hom (((res (DVR.divLe p.2 p.1) (e.s p)) : Γ(X, M.U p.2 ⊓ L.U p.1)ˣ) : Γ(X, M.U p.2 ⊓ L.U p.1)) *
      (X.presheaf.germ _ x hx').hom (((res (DVR.divLe p.2 p.1) (e.s p))⁻¹ : Γ(X, M.U p.2 ⊓ L.U p.1)ˣ) : Γ(X, M.U p.2 ⊓ L.U p.1)) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  rw [map_mul, h1, h2, h3, h4, ← h5, ← _root_.mul_assoc, h6, _root_.one_mul]

end GlobalTheory.SecTransport
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTransportAlongGeneratingIsoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_transport_along_generating_iso : ∀ {X : Scheme.{0}} {M L : LB X} (e : LB.Iso M L), e.IsGen → M.IsLB → L.IsLB →
    ∀ σ : L.Sec, ∃ σ' : M.Sec, GlobalTheory.Cartier.SecMaps e σ' σ ∧ Out.nonzeroLocus σ ≤ Out.nonzeroLocus σ' := by
  first | exact @GlobalTheory.SecTransport.main | exact GlobalTheory.SecTransport.main | (intros; apply GlobalTheory.SecTransport.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfEntireMulEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl.FrameAut

theorem eq_zero_of_entire_mul_eq_zero {g : ℕ} {θ D : (Fin g → ℂ) → ℂ} (hθ : Differentiable ℂ θ) (h0 : θ ≠ 0)
    {S : Set (Fin g → ℂ)} (hS : IsOpen S) (hD : ContinuousOn D S) (h : ∀ w ∈ S, θ w * D w = 0)
    {z : Fin g → ℂ} (hz : z ∈ S) : D z = 0 := by
  by_contra hne
  have hc : ContinuousAt D z := hD.continuousAt (hS.mem_nhds hz)
  have he : θ =ᶠ[nhds z] 0 := by
    filter_upwards [hc.eventually_ne hne, hS.mem_nhds hz] with w hw hwS
    exact (mul_eq_zero.1 (h w hwS)).resolve_right hw
  have ha : AnalyticOnNhd ℂ θ Set.univ := SCV.analyticOnNhd_of_differentiable hθ Set.univ
  exact h0 (funext fun w =>
    ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ z) he (Set.mem_univ w))

end GlobalTheory.MBLow.Cl.FrameAut

namespace GlobalTheory.MBLow.Cl

theorem frame_eq_autV_mul : ∀ (g : ℕ) (x : KeyIn ℂ) (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (c : ℂ) (W : Fin g → Fin g → ℂ), NF x hg u τ a b c W → ∀ M N (i : x.P.L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ x.P.L.U i → u.fr i z = autV τ a b M N z * u.fr i (z + perV τ M N) := by
  intro g x hg u τ a b c W hNF M N i z hz
  obtain ⟨hs, hp, ha, hb, hc, hΛ, _, hth, _⟩ := hNF
  obtain ⟨hd, ⟨z₀, hz₀⟩, hlaw⟩ := GlobalTheory.T.thetaChar_differentiable_ne_zero_automorphy g τ a b hs hp ha hb
  have hdc : Differentiable ℂ (fun w => c * thetaChar τ a b w) := (differentiable_const c).mul hd
  have h0 : (fun w => c * thetaChar τ a b w) ≠ 0 := fun h => by
    have := congrFun h z₀
    simp only [Pi.zero_apply, mul_eq_zero] at this
    exact this.elim hc hz₀
  have hl : u.ex (perV τ M N) = 1 := (u.ker _).2 ((hΛ _).2 ⟨M, N, rfl⟩)
  have he : ∀ w, u.ex (w + perV τ M N) = u.ex w := fun w => by rw [u.ex_add, hl, _root_.mul_one]
  have hS : IsOpen {w | ⊤ ≤ (u.ex w).left ⁻¹ᵁ x.P.L.U i} := (u.hol _ 0).1
  have htr : ∀ w, ⊤ ≤ (u.ex w).left ⁻¹ᵁ x.P.L.U i → ⊤ ≤ (u.ex (w + perV τ M N)).left ⁻¹ᵁ x.P.L.U i :=
    fun w hw => by rw [he]; exact hw
  have hcf := (u.fr_hol i).continuousOn
  have haut : Continuous (autV τ a b M N) := by
    unfold autV dotProduct
    fun_prop
  have hD : ContinuousOn (fun w => u.fr i w - autV τ a b M N w * u.fr i (w + perV τ M N))
      {w | ⊤ ≤ (u.ex w).left ⁻¹ᵁ x.P.L.U i} :=
    hcf.sub (haut.continuousOn.mul (hcf.comp (continuous_add_const _).continuousOn fun w hw => htr w hw))
  refine sub_eq_zero.1 (FrameAut.eq_zero_of_entire_mul_eq_zero hdc h0 hS hD (fun w hw => ?_) hz)
  have h1 := hth i w hw
  have h2 := hth i _ (htr w hw)
  beta_reduce at h1 h2 ⊢
  rw [he, h1, hlaw] at h2
  linear_combination h2

end GlobalTheory.MBLow.Cl

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellPointImageAndFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellPointImageAndFrame
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FlagMod.FieldFlag

theorem spMap_comp_cellpt {R₁ R₂ R₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃] (f : R₁ →+* R₂)
    (g : R₂ →+* R₃) : spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem cellpt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)) (κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)) [∀ b w, IsOpenImmersion (κ b w)] (hZ : Cells A π g κ) (ht : FlagCellFrameChangeTriangular hZ) (b : A.B) (w : Pm Dw.mult) (S : Type) [CommRing S] (ψ₀ : Γ(Y.X, (A.V b).1) →+* S) (xc : CellVar Dw.mult → S) (z : Sp S ⟶ Z), z = spMap (MvPolynomial.eval₂Hom ψ₀ xc) ≫ κ b w → z ≫ π = spMap ψ₀ ≫ (A.V b).2.fromSpec ∧ ∃ hz : ⊤ ≤ z ⁻¹ᵁ (cellFrames hZ ht).U ((b, w) : A.B × Pm Dw.mult), ∀ σ, (cellFrames hZ ht).uAt ((b, w) : A.B × Pm Dw.mult) z hz σ = (((A.k b).u σ).map ψ₀).submatrix id (w σ) * Matrix.of (cell xc σ) := by
  intro E _ _ _ H Dw l Xo c Y p A Z π g κ _ hZ ht b w S _ ψ₀ xc z hzd
  refine ⟨?_, ?_⟩
  · rw [hzd, Category.assoc, hZ.plk.base b w, cbase, ← Category.assoc, spMap_comp_cellpt,
      MvPolynomial.eval₂Hom_comp_C]
  · have hz : ⊤ ≤ z ⁻¹ᵁ (cellFrames hZ ht).U ((b, w) : A.B × Pm Dw.mult) := by
      intro x _
      show z x ∈ Set.range (κ b w)
      rw [hzd, Scheme.Hom.comp_apply]
      exact ⟨_, rfl⟩
    refine ⟨hz, fun σ => ?_⟩
    have key : (ev z _ hz).comp (cellθ κ ((b, w) : A.B × Pm Dw.mult)).toRingHom = MvPolynomial.eval₂Hom ψ₀ xc := by
      have h1 := eq_spMap_ev (κ := κ) ((b, w) : A.B × Pm Dw.mult) z hz
      have h2 : spMap ((ev z _ hz).comp (cellθ κ ((b, w) : A.B × Pm Dw.mult)).toRingHom) =
          spMap (MvPolynomial.eval₂Hom ψ₀ xc) := by
        rw [← cancel_mono (κ b w)]
        exact h1.trans hzd
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective h2)
    show ((uC A b w σ).map (cellθ κ ((b, w) : A.B × Pm Dw.mult))).map (ev z _ hz) = _
    change (uC A b w σ).map ((ev z _ hz).comp (cellθ κ ((b, w) : A.B × Pm Dw.mult)).toRingHom) = _
    rw [key, uC, Matrix.map_mul, Matrix.submatrix_map, Matrix.map_map]
    congr 1
    · congr 1
      ext i j
      simp [cC]
    · ext i j
      simp only [cellMat, Matrix.map_apply, Matrix.of_apply, cell]
      split_ifs <;> simp

end GlobalTheory.FlagMod.FieldFlag
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellPointImageAndFrameStatement
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagCellPoint_image_and_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)) (κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)) [∀ b w, IsOpenImmersion (κ b w)] (hZ : Cells A π g κ) (ht : FlagCellFrameChangeTriangular hZ) (b : A.B) (w : Pm Dw.mult) (S : Type) [CommRing S] (ψ₀ : Γ(Y.X, (A.V b).1) →+* S) (xc : CellVar Dw.mult → S) (z : Sp S ⟶ Z), z = spMap (MvPolynomial.eval₂Hom ψ₀ xc) ≫ κ b w → z ≫ π = spMap ψ₀ ≫ (A.V b).2.fromSpec ∧ ∃ hz : ⊤ ≤ z ⁻¹ᵁ (cellFrames hZ ht).U ((b, w) : A.B × Pm Dw.mult), ∀ σ, (cellFrames hZ ht).uAt ((b, w) : A.B × Pm Dw.mult) z hz σ = (((A.k b).u σ).map ψ₀).submatrix id (w σ) * Matrix.of (cell xc σ) := by
  first | exact @GlobalTheory.FlagMod.FieldFlag.cellpt | exact GlobalTheory.FlagMod.FieldFlag.cellpt | (intros; apply GlobalTheory.FlagMod.FieldFlag.cellpt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanExistenceOfComplexIsomorphicField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanExistenceOfComplexIsomorphicField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow

theorem archF_of_arch : ∀ κ : Rule, Funct κ → Arch κ → ArchF κ := by
  intro κ hF hA R _ _ _ _ D hP hT F _ _ _ e N ν g r m k hg hm hk β ζ q hq s hs vB bX σ gm hAd k₀ hK
  letI : Algebra (FractionRing R) ℂ := ((e : F →+* ℂ).comp (algebraMap (FractionRing R) F)).toAlgebra
  have he : ∀ x, e (algebraMap (FractionRing R) F x) = algebraMap (FractionRing R) ℂ x := fun _ => rfl
  obtain ⟨N', ν', I, hb, hh, hl, heX, hth, hrg, hvE, hfam⟩ := GlobalTheory.T.degenerationValues_transport_fieldIso R D F ℂ e he N ν
  obtain ⟨hform, hlev⟩ := GlobalTheory.T.degenerationDataValuesIso_transport_formsLevelsFamilies F ℂ e N N' I hb hh hl
  obtain ⟨β', hβ⟩ := hform k β
  obtain ⟨q', hq', hev⟩ := hlev m g hm ζ q hq
  obtain ⟨hBK, hadp⟩ := GlobalTheory.T.abelianKeyValue_adaptedVectors_fieldIso κ hF R D F ℂ e he N ν N' ν' I hh hl heX hth hvE vB
  obtain ⟨gm', hpull, hAd'⟩ := hadp r g bX σ gm hAd
  choose s' hs1 hs2 using fun a => hfam (m ^ 2) (s a)
  have hs' : ∀ a, ∃ f, ν'.FamV (s' a) f ∧ IsEvFam N' m (q' a) f := by
    intro a
    obtain ⟨f, hf, hf2⟩ := hs a
    obtain ⟨f', hf', hff⟩ := hs1 a f hf
    exact ⟨f', hf', hev a f f' hf2 hff⟩
  obtain ⟨ε, hε, H⟩ := hA R D hP hT N' ν' g r m k hg hm hk β' _ q' hq' s' hs' vB _ σ gm' hAd' _ (hBK k₀ hK)
  have h1 : ∀ a j α, (jc ν' (s' a) (gm' j) (I.e α)).fst = e (jc ν (s a) (gm j) α).fst := by
    intro a j α
    rw [hs2 a _ _ (hpull j) α]
    simp [dualMap]
  have h2 : ∀ a j α, (jc ν' (s' a) (gm' j) (I.e α)).snd = e (jc ν (s a) (gm j) α).snd := by
    intro a j α
    rw [hs2 a _ _ (hpull j) α]
    simp [dualMap]
  refine ⟨ε, hε, fun u hu hu' => ?_⟩
  obtain ⟨hsum, x₀, hg₀, lev₀, ϑ, hϑ, hJ, hκ⟩ := H u hu hu'
  refine ⟨fun a j => ⟨?_, ?_⟩, x₀, hg₀, lev₀, ϑ, fun a j => ?_, ?_, hκ⟩
  · have := ((I.e.toEquiv.summable_iff.2 (hsum a j).1)).mul_left ‖(e (ν.rg ^ (m ^ 2)))⁻¹‖
    refine this.congr fun α => ?_
    simp only [Function.comp, AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe, h1, hβ]
    rw [← norm_mul, map_div₀, div_eq_inv_mul, _root_.mul_assoc]
  · have := ((I.e.toEquiv.summable_iff.2 (hsum a j).2)).mul_left ‖(e (ν.rg ^ (m ^ 2)))⁻¹‖
    refine this.congr fun α => ?_
    simp only [Function.comp, AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe, h2, hβ]
    rw [← norm_mul, map_div₀, div_eq_inv_mul, _root_.mul_assoc]
  · rw [hϑ a j, ← I.e.toEquiv.tsum_eq]
    refine tsum_congr fun α => ?_
    simp only [AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe, h1, hβ, hrg, map_div₀, map_pow]
  · convert hJ using 3 with a j
    rw [← I.e.toEquiv.tsum_eq]
    refine tsum_congr fun α => ?_
    simp only [AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe, h2, hβ, hrg, map_div₀, map_pow]

end GlobalTheory.MBLow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanExistenceOfComplexIsomorphicFieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanExistence_of_complex_isomorphic_field : ∀ κ : Rule, Funct κ → Arch κ → ArchF κ := by
  first | exact @GlobalTheory.MBLow.archF_of_arch | exact GlobalTheory.MBLow.archF_of_arch | (intros; apply GlobalTheory.MBLow.archF_of_arch <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EssFiniteTypeOfLocalizationFiniteTypeComplex
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EssFiniteTypeOfLocalizationFiniteTypeComplex
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

namespace GlobalTheory.EssFiniteDescent

theorem essFiniteType_of_eq_div : ∀ (K : Type) [Field K] (c : ℂ →+* K) (R : Subring K) (hcR : ∀ a, c a ∈ R) (E : ValuationSubring K) (hcE : ∀ a, c a ∈ E), R ≤ E.toSubring → (c.codRestrict R hcR).FiniteType → (∀ e ∈ E, ∃ a ∈ R, ∃ s ∈ R, s⁻¹ ∈ E ∧ e = a / s) → (c.codRestrict E hcE).EssFiniteType := by
  intro K _ c R hcR E hcE hRE hft hloc
  let f : R →+* E :=
    { toFun := fun r => ⟨(r : K), hRE r.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let M : Submonoid R :=
    { carrier := {s | (s : K) ≠ 0 ∧ (s : K)⁻¹ ∈ E}
      mul_mem' := by
        rintro a b ⟨ha0, ha⟩ ⟨hb0, hb⟩
        refine ⟨by simpa using mul_ne_zero ha0 hb0, ?_⟩
        have : ((a * b : R) : K)⁻¹ = (b : K)⁻¹ * (a : K)⁻¹ := by
          push_cast; exact mul_inv_rev _ _
        rw [this]; exact E.mul_mem _ _ hb ha
      one_mem' := ⟨by simp, by simpa using E.one_mem⟩ }
  letI : Algebra ℂ R := (c.codRestrict R hcR).toAlgebra
  letI : Algebra R E := f.toAlgebra
  letI : Algebra ℂ E := (c.codRestrict E hcE).toAlgebra
  haveI : IsScalarTower ℂ R E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.FiniteType ℂ R := hft
  haveI : IsLocalization M E := by
    rw [isLocalization_iff]
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨s, hs0, hs⟩
      refine isUnit_iff_exists_inv.mpr ⟨⟨_, hs⟩, ?_⟩
      apply Subtype.ext
      change (s : K) * (s : K)⁻¹ = 1
      exact mul_inv_cancel₀ hs0
    · rintro ⟨e, he⟩
      obtain ⟨a, ha, s, hs, hsE, rfl⟩ := hloc e he
      by_cases hs0 : s = 0
      · refine ⟨(0, 1), ?_⟩
        apply Subtype.ext
        change a / s * ((1 : M) : R) = (((0 : R)) : K)
        simp [hs0]
      · refine ⟨(⟨a, ha⟩, ⟨⟨s, hs⟩, by simpa using hs0, hsE⟩), ?_⟩
        apply Subtype.ext
        change a / s * s = a
        exact div_mul_cancel₀ a hs0
    · intro x y hxy
      refine ⟨1, ?_⟩
      have : (x : K) = y := congrArg (fun z : E => (z : K)) hxy
      simp [Subtype.ext this]
  haveI : Algebra.EssFiniteType R E := Algebra.EssFiniteType.of_isLocalization E M
  have h : Algebra.EssFiniteType ℂ E := Algebra.EssFiniteType.comp ℂ R E
  exact h

end GlobalTheory.EssFiniteDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EssFiniteTypeOfLocalizationFiniteTypeComplexStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.essFiniteType_of_localization_finiteType_complex : ∀ (K : Type) [Field K] (c : ℂ →+* K) (R : Subring K) (hcR : ∀ a, c a ∈ R) (E : ValuationSubring K) (hcE : ∀ a, c a ∈ E), R ≤ E.toSubring → (c.codRestrict R hcR).FiniteType → (∀ e ∈ E, ∃ a ∈ R, ∃ s ∈ R, s⁻¹ ∈ E ∧ e = a / s) → (c.codRestrict E hcE).EssFiniteType := by
  first | exact @GlobalTheory.EssFiniteDescent.essFiniteType_of_eq_div | exact GlobalTheory.EssFiniteDescent.essFiniteType_of_eq_div | (intros; apply GlobalTheory.EssFiniteDescent.essFiniteType_of_eq_div <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleComponentsClopenPartition
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleComponentsClopenPartition
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelTor

open TopologicalSpace

namespace GlobalTheory.CompPart

theorem isIrreducible_generizations {Z : Scheme.{0}} (hd : ∀ x : Z, IsDomain (Z.presheaf.stalk x)) (x : Z) :
    IsIrreducible {y : Z | y ⤳ x} := by
  haveI := hd x
  rw [← Scheme.range_fromSpecStalk, ← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ (Spec (Z.presheaf.stalk x))).image _
    (Z.fromSpecStalk x).continuous.continuousOn

theorem eq_closure_generizations {Z : Scheme.{0}} (hd : ∀ x : Z, IsDomain (Z.presheaf.stalk x))
    {C : Set Z} (hC : C ∈ irreducibleComponents Z) {x : Z} (hx : x ∈ C) :
    C = closure {y : Z | y ⤳ x} := by
  have hcl : IsClosed C := isClosed_of_mem_irreducibleComponents C hC
  obtain ⟨η, hη⟩ := QuasiSober.sober hC.1 hcl
  have hηx : η ⤳ x := by
    rw [specializes_iff_mem_closure, hη.def]; exact hx
  have hsub : C ⊆ closure {y : Z | y ⤳ x} := by
    rw [← hη.def]
    exact closure_mono (Set.singleton_subset_iff.2 hηx)
  exact hsub.antisymm (hC.2 (isIrreducible_generizations hd x).closure hsub)

theorem existsUnique_mem {Z : Scheme.{0}} (hd : ∀ x : Z, IsDomain (Z.presheaf.stalk x)) (x : Z) :
    ∃! C : irreducibleComponents Z, x ∈ (C : Set Z) :=
  ⟨⟨_, irreducibleComponent_mem_irreducibleComponents x⟩, mem_irreducibleComponent, fun C hC =>
    Subtype.ext ((eq_closure_generizations hd C.2 hC).trans
      (eq_closure_generizations hd (irreducibleComponent_mem_irreducibleComponents x)
        mem_irreducibleComponent).symm)⟩

theorem isOpen_of_mem {Z : Scheme.{0}} [NoetherianSpace Z] (hd : ∀ x : Z, IsDomain (Z.presheaf.stalk x))
    {C : Set Z} (hC : C ∈ irreducibleComponents Z) : IsOpen C := by
  have hfin : (irreducibleComponents Z).Finite := NoetherianSpace.finite_irreducibleComponents
  have hcompl : Cᶜ = ⋃ D ∈ {D ∈ irreducibleComponents Z | D ≠ C}, D := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · intro hy
      exact ⟨irreducibleComponent y, ⟨irreducibleComponent_mem_irreducibleComponents y,
        fun h => hy (h ▸ mem_irreducibleComponent)⟩, mem_irreducibleComponent⟩
    · rintro ⟨D, ⟨hD, hne⟩, hyD⟩ hyC
      exact hne (congrArg Subtype.val ((existsUnique_mem hd y).unique (y₁ := ⟨D, hD⟩) (y₂ := ⟨C, hC⟩) hyD hyC))
  rw [← isClosed_compl_iff, hcompl]
  exact (hfin.subset (by exact fun D hD => hD.1)).isClosed_biUnion fun D hD =>
    isClosed_of_mem_irreducibleComponents D hD.1

end GlobalTheory.CompPart

theorem GlobalTheory.irreducibleComponents_clopen_partition : ∀ (n : ℕ) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)),
    IsProjOver z → GlobalTheory.IsNormalScheme Z → ∃ (ι : Type) (_ : Fintype ι) (W : ι → Set Z),
      (∀ c, IsClopen (W c)) ∧ (∀ c, IsIrreducible (W c)) ∧ ∀ x, ∃! c, x ∈ W c := by
  intro n Z z hz hN
  haveI : IsNoetherianRing (cycAway n) :=
    is_noetherian_subring_closure _ (Set.toFinite _)
  haveI : AlgebraicGeometry.IsNoetherian Z := GlobalTheory.isNoetherian_of_isProjOver hz
  have hd : ∀ x : Z, IsDomain (Z.presheaf.stalk x) := fun x => hN.isDomain_stalk x
  have hfin : (irreducibleComponents Z).Finite := NoetherianSpace.finite_irreducibleComponents
  exact ⟨irreducibleComponents Z, hfin.fintype, fun C => (C : Set Z),
    fun C => ⟨isClosed_of_mem_irreducibleComponents _ C.2, GlobalTheory.CompPart.isOpen_of_mem hd C.2⟩,
    fun C => C.2.1, GlobalTheory.CompPart.existsUnique_mem hd⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleComponentsClopenPartitionStatement
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_clopen_irreducible_partition_of_normal_proj : ∀ (n : ℕ) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)), IsProjOver z → GlobalTheory.IsNormalScheme Z → ∃ (ι : Type) (_ : Fintype ι) (W : ι → Set Z), (∀ c, IsClopen (W c)) ∧ (∀ c, IsIrreducible (W c)) ∧ ∀ x, ∃! c, x ∈ W c := by
  first | exact @GlobalTheory.irreducibleComponents_clopen_partition | exact GlobalTheory.irreducibleComponents_clopen_partition | (intros; apply GlobalTheory.irreducibleComponents_clopen_partition <;> assumption)
end
end

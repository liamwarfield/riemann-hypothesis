module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilMatrixCoefficientVacuaUnramifiedPlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsStandardLocalisationWeilDatumInertPlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CayleyRuleOfBiInvariantVacuumCoefficient
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VacuumMatrixCoefficientSourceInertPlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisOFinsetSum
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentMulEntryEqZeroOfCutInverse
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticePrescribedSplitPlace

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitaryChartsAllFinitePlacesFrameLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitaryChartsAllFinitePlacesFrameLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChartsAll

open GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains

theorem exists_charts : ∀ (D : D7) (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), (IsSplit (E := D.host.E) v → ∃ e, IsSplitChart D.sp.cm.sig V.gram (frameLat V) h e) ∧ (¬ IsSplit (E := D.host.E) v → IsInertAt D.host.F D.host.E v w ∧ Odd (qV D.host.F v) ∧ ∀ c, IsConjAt D.sp.cm.sig h c → ∃ e, IsInertChart D.sp.cm.sig V.gram (frameLat V) h c e) := by
  intro D V v w h
  refine ⟨fun hs => (GlobalTheory.NoExcl.chart V h hs).1, fun hns => ?_⟩
  have hI := GlobalTheory.LFun.exists_isInertChart D.sp.cm.sig (isCMExt_host D) v
  obtain ⟨w₀, hw₀⟩ := (hI.1 (GlobalTheory.VacCoef.isUnram_host D v)).resolve_left hns
  have h₀ : w₀.under (𝓞 D.host.F) = v := GlobalTheory.LFun.under_eq_of_isInertAt hw₀
  obtain rfl : w = w₀ := ((hI.2 w₀ h₀ hw₀).2.2.1 w).1 h
  obtain ⟨-, ⟨c₀, hc₀, -⟩, -, -, H⟩ := hI.2 w h hw₀
  have hfix : Formalism.DivisionValues.conjPl w = w := GlobalTheory.WeilAtPlace.conjPl_eq_of_inert hw₀ h
  have h2 : ((2 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := fun h2 => GlobalTheory.CoreThree.conj_ne_of_two w h2 hfix
  have hv2 : Valued.v (2 : w.adicCompletion D.host.E) = 1 := by
    rw [← map_ofNat (algebraMap D.host.E (w.adicCompletion D.host.E)) 2, GlobalTheory.Idele.valued_algebraMap,
      ← map_ofNat (algebraMap (𝓞 D.host.E) D.host.E) 2, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 (by exact_mod_cast h2)
  obtain ⟨⟨ϖ, hU⟩, -⟩ := H c₀ hc₀
  refine ⟨hw₀, GlobalTheory.InertLoc.odd_of_v_two hU hv2, fun c hc => ?_⟩
  have hspan : Submodule.span D.host.E (frameLat V : Set (Fin V.rank → D.host.E)) = ⊤ := by
    have hfull : Submodule.span D.host.E (V.L0 : Set V.V) = ⊤ := by
      let W := Submodule.span D.host.E (V.L0 : Set V.V)
      change W = ⊤
      by_contra h
      let e : V.V ≃ₗ⋆[D.host.E] V.V :=
        (V.frame.equivFun.trans (starLinearEquiv D.host.E)).trans V.frame.equivFun.symm
      let g : V.V →ₗ[D.host.E] Module.Dual D.host.E W :=
        (LinearMap.domRestrict' W).comp (V.hT.comp e.toLinearMap)
      have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) < Module.finrank D.host.E V.V := by
        rw [Subspace.dual_finrank_eq]
        exact Submodule.finrank_lt h
      obtain ⟨x, hx, hx₀⟩ :=
        Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
      have hsmul (a : D.host.E) : a • e x ∈ V.L0 := by
        rw [← V.baseLattice_isUnimodular]
        rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
        intro y hy
        have hxy : V.hT (e x) y = 0 :=
          congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
        have hyx : V.hT y (e x) = 0 := by
          rw [(V.herm.eq (e x) y).symm, hxy, map_zero]
        simp [hyx]
      let i : D.host.E →ₗ[𝓞 D.host.E] V.L0 :=
        ((LinearMap.toSpanSingleton D.host.E _ (e x)).restrictScalars (𝓞 D.host.E)).codRestrict V.L0 hsmul
      let : Module.Finite (𝓞 D.host.E) V.L0 := Module.Finite.iff_fg.mpr V.standardTuple_isLattice.fg
      let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_injective i fun a b hab =>
        smul_left_injective D.host.E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
      exact RingOfIntegers.not_isField D.host.E
        (isField_of_isIntegral_of_isField (R := 𝓞 D.host.E) (S := D.host.E)
          (FaithfulSMul.algebraMap_injective _ _) (Field.toIsField _))
    have heq : (frameLat V : Set (Fin V.rank → D.host.E)) =
        V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V) :=
      (V.frame.equivFun.toEquiv.image_eq_preimage_symm _).symm
    rw [heq, ← Submodule.map_span, hfull, Submodule.map_top, LinearEquiv.range]
  obtain ⟨e, he, -⟩ := (H c hc).2 V.rank V.gram (frameLat V) (GlobalTheory.NoExcl.isHermND_gram V) (frameLat_fg V)
    hspan (SelfDual.isSelfDualAt_frameLat D V v)
  exact ⟨e, he⟩

end GlobalTheory.ChartsAll
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitaryChartsAllFinitePlacesFrameLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryCharts_allFinitePlaces_frameLattice : ∀ (D : D7) (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), (IsSplit (E := D.host.E) v → ∃ e, IsSplitChart D.sp.cm.sig V.gram (frameLat V) h e) ∧ (¬ IsSplit (E := D.host.E) v → IsInertAt D.host.F D.host.E v w ∧ Odd (qV D.host.F v) ∧ ∀ c, IsConjAt D.sp.cm.sig h c → ∃ e, IsInertChart D.sp.cm.sig V.gram (frameLat V) h c e) := by
  first | exact @GlobalTheory.ChartsAll.exists_charts | exact GlobalTheory.ChartsAll.exists_charts | (intros; apply GlobalTheory.ChartsAll.exists_charts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumInertPlaceStandardCayleyPair
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumInertPlaceStandardCayleyPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto

theorem eq_of_inert_under {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} (hin : IsInertAt F E v w)
    (w' : HeightOneSpectrum (𝓞 E)) (h' : w'.under (𝓞 F) = v) : w' = w := by
  have hle : w.asIdeal ≤ w'.asIdeal := by
    rw [← hin, Ideal.map_le_iff_le_comap, ← h', HeightOneSpectrum.under_asIdeal]
  exact (HeightOneSpectrum.ext (w.isMaximal.eq_of_le w'.isPrime.ne_top hle)).symm


set_option maxHeartbeats 2000000 in
theorem std_cayley_of_inert : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsInertAt D.host.F D.host.E v w → UnrAt χS w → UnrAt χT w → ∀ c ϖ eS eT, IsUnramInv ϖ c (qV D.host.F v) → IsInertChart D.sp.cm.sig S.gram (frameLat S) h c eS → IsInertChart D.sp.cm.sig T.gram (frameLat T) h c eT → ∀ f, VacFin ψ S T v f → f ≠ 0 → ∃ (δ : w.adicCompletion D.host.E) (ψ' : AddChar (w.adicCompletion D.host.E) ℂ) (M : Submodule ℂ (WO S T → ℂ)) (ρ : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E) → Module.End ℂ M) (ω : GU c S.rank × GU c T.rank →* Module.End ℂ M) (s : M), IsStd ϖ c (qV D.host.F v) δ ψ' ρ ω s ∧ (s : WO S T → ℂ) = f ∧ (∀ g g' (m : M), ((ω (g, g') m : M) : WO S T → ℂ) = om (embV S v (eS.symm g), embV T v (eT.symm g')) m) ∧ CayleyRule (qV D.host.F v) T.rank ρ (ω.comp (MonoidHom.inl _ _)) s ∧ CayleyRule (qV D.host.F v) S.rank ρ (ω.comp (MonoidHom.inr _ _)) s := by
  intro D ψ S T χS χT om hW v w h hin hS hT c ϖ eS eT hU heS heT f hf hf0
  obtain ⟨δ, ψ', M, ρ, ω, s, hstd, hsf, hω, hth, hρ⟩ :=
    GlobalTheory.T.exists_standardLocalisation_weilDatum_inertPlace D ψ S T χS χT om hW v w h hin hS hT c ϖ eS eT hU heS heT f hf hf0
  obtain ⟨μ, 𝓕, hμ⟩ := GlobalTheory.Size.exists_isCovolOne S T
  have hψ := hW.std
  have hthf : IsThetaFunO ψ S T f := hf.1
  let l : M →ₗ[ℂ] ℂ :=
    { toFun := fun m => Lift.pet μ 𝓕 (m : WO S T → ℂ) f
      map_add' := fun m m' => by
        show GlobalTheory.Ker.ipO μ 𝓕 ((m + m' : M) : WO S T → ℂ) f = GlobalTheory.Ker.ipO μ 𝓕 _ f + GlobalTheory.Ker.ipO μ 𝓕 _ f
        rw [Submodule.coe_add]
        exact GlobalTheory.Size.ipO_add_left hψ hμ.1 hμ.2.1 (hth m) (hth m') hthf
      map_smul' := fun a m => by
        show GlobalTheory.Ker.ipO μ 𝓕 ((a • m : M) : WO S T → ℂ) f = a * GlobalTheory.Ker.ipO μ 𝓕 _ f
        rw [Submodule.coe_smul]
        exact GlobalTheory.Size.ipO_smul_left μ 𝓕 a _ _ }
  have hl : ∀ m : M, l m = Lift.pet μ 𝓕 (m : WO S T → ℂ) f := fun _ => rfl
  have hls : l s ≠ 0 := by
    rw [hl, hsf]
    exact fun h0 => hf0 ((GlobalTheory.Size.ipO_self_eq_zero_iff hψ hμ.1 hμ.2.1 hthf).1 h0)
  have hinv : ∀ u ∈ intMat (w.adicCompletion D.host.E) (Fin T.rank) (Fin S.rank), ∀ m : M, l (ρ u m) = l m := by
    intro u hu m
    obtain ⟨u0, hu0⟩ := hρ u
    have hfix : heisO ψ S T u0 f = f := by
      have e := hu0 s
      rw [hstd.fixes u hu, hsf] at e
      exact e.symm
    rw [hl, hl, hu0 m]
    conv_lhs => rw [← hfix]
    exact GlobalTheory.Size.ipO_heisO hψ hμ.1 hμ.2.1 (hth m) hthf u0
  have hcay := GlobalTheory.T.cayleyRule_of_biInvariantVacuumCoefficient _ ϖ c (qV D.host.F v) δ ψ' S.rank T.rank M ρ ω s hstd l hls hinv
  obtain ⟨φ1, hk1, hc1⟩ := GlobalTheory.T.vacuum_matrixCoefficient_source_inert_place_alt D ψ S T χS χT om hW μ 𝓕 hμ v w h hin hS hT c ϖ eS hU heS
  have hunr : ∀ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = v → UnrAt χS w' ∧ UnrAt χT w' :=
    fun w' h' => by
      rw [eq_of_inert_under hin w' h']
      exact ⟨hS, hT⟩
  obtain ⟨φ2, hk2, hc2⟩ := GlobalTheory.T.weilMatrixCoefficient_vacua_unramifiedPlace D ψ S T χS χT om hW μ 𝓕 hμ v hunr
  have hval := (GlobalTheory.T.heckeChar_value_inert_place_and_segment D χS S.rank hW.hecS hW.resS v w h hin hS).1
  have hk2' := (hk2 w h).2 hin c ϖ eT hU heT
  rw [hval] at hk2'
  refine ⟨δ, ψ', M, ρ, ω, s, hstd, hsf, hω, hcay.1 φ1 hk1 fun g => ?_, hcay.2 (φ2 ∘ eT.symm) hk2' fun g => ?_⟩
  · exact (congrArg (fun x => Lift.pet μ 𝓕 x f) ((hω g 1 s).trans (by rw [map_one eT.symm, map_one (embV T v), hsf]))).trans
      ((hc1 g f f hf hf).trans (by rw [hl, hsf]))
  · exact (congrArg (fun x => Lift.pet μ 𝓕 x f) ((hω 1 g s).trans (by rw [map_one eS.symm, map_one (embV S v), hsf]))).trans
      ((hc2 (eT.symm g) f f hf hf).trans (by rw [hl, hsf]; rfl))

end GlobalTheory.ChainOnto

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumInertPlaceStandardCayleyPairStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDatum_inertPlace_standard_cayley_pair : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsInertAt D.host.F D.host.E v w → UnrAt χS w → UnrAt χT w → ∀ c ϖ eS eT, IsUnramInv ϖ c (qV D.host.F v) → IsInertChart D.sp.cm.sig S.gram (frameLat S) h c eS → IsInertChart D.sp.cm.sig T.gram (frameLat T) h c eT → ∀ f, VacFin ψ S T v f → f ≠ 0 → ∃ (δ : w.adicCompletion D.host.E) (ψ' : AddChar (w.adicCompletion D.host.E) ℂ) (M : Submodule ℂ (WO S T → ℂ)) (ρ : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E) → Module.End ℂ M) (ω : GU c S.rank × GU c T.rank →* Module.End ℂ M) (s : M), IsStd ϖ c (qV D.host.F v) δ ψ' ρ ω s ∧ (s : WO S T → ℂ) = f ∧ (∀ g g' (m : M), ((ω (g, g') m : M) : WO S T → ℂ) = om (embV S v (eS.symm g), embV T v (eT.symm g')) m) ∧ CayleyRule (qV D.host.F v) T.rank ρ (ω.comp (MonoidHom.inl _ _)) s ∧ CayleyRule (qV D.host.F v) S.rank ρ (ω.comp (MonoidHom.inr _ _)) s := by
  first | exact @GlobalTheory.ChainOnto.std_cayley_of_inert | exact GlobalTheory.ChainOnto.std_cayley_of_inert | (intros; apply GlobalTheory.ChainOnto.std_cayley_of_inert <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalLevelZeroStabilizerMem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevZeroRead

theorem matrix_in_frame {k n Y A : Type} [CommRing k] [Fintype n] [DecidableEq n] [Fintype Y] [DecidableEq Y] [Fintype A]
    [DecidableEq A] (β : Matrix n Y k) (γ : Matrix Y n k) (h : γ * β = 1) (b : GL Y k) (σ : A ≃ Y) (e : A ≃ n)
    (X : Matrix A A k) (m : Matrix n n k)
    (hm : ((β * b.val).submatrix id fun i => σ (e.symm i)) * m =
      β * (b.val * X.submatrix σ.symm σ.symm * (b⁻¹).val) * γ * (β * b.val).submatrix id fun i => σ (e.symm i)) :
    m = X.submatrix e.symm e.symm := by
  let ρ : n ≃ Y := e.symm.trans σ
  have h1 : ((b⁻¹).val * γ) * (β * b.val) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc γ, h, Matrix.one_mul, Units.inv_mul]
  have h2 : β * (b.val * X.submatrix σ.symm σ.symm * (b⁻¹).val) * γ * (β * b.val) =
      β * b.val * X.submatrix σ.symm σ.symm := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc (b.val * _), ← Matrix.mul_assoc (b⁻¹).val, h1, Matrix.mul_one,
      Matrix.mul_assoc]
  have h3 : ∀ (P : Matrix n n k) (Q : Matrix n Y k), P * Q.submatrix id ρ = (P * Q).submatrix id ρ := fun _ _ => rfl
  have h4 : ∀ (P : Matrix Y n k) (Q : Matrix n Y k), P.submatrix ρ id * Q.submatrix id ρ = (P * Q).submatrix ρ ρ :=
    fun _ _ => rfl
  change (β * b.val).submatrix id ρ * m = _ * (β * b.val).submatrix id ρ at hm
  rw [h3, h2] at hm
  have h5 := congrArg (fun Z => ((b⁻¹).val * γ).submatrix ρ id * Z) hm
  try simp only at h5
  rw [← Matrix.mul_assoc, h4, h4, h1, ← Matrix.mul_assoc, h1, Matrix.submatrix_one_equiv, Matrix.one_mul, Matrix.one_mul] at h5
  rw [h5]
  ext i j
  simp [ρ]

theorem toEAf_onto (D : D7) : Function.Surjective (toEAf D) := by
  refine (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).surjective.comp ?_
  exact Algebra.TensorProduct.map_surjective _ _ (fun α => ⟨pairA _ 0 α, rfl⟩) Function.surjective_id

theorem finE_val {D : D7} (V : HSp D) (g : GA D V) : (Lev.finE V g).val = (Formalism.L2.Theta.mt V g).map (toEAf D) := rfl

theorem upperLeftBlock_apply_of_eq {κ : Type} [CommRing κ] {r n : ℕ} (hr : r ≤ n) (hn : n ≤ r) (g : GL (Fin n) κ) (i j : Fin r) :
    (upperLeftBlock hr g).val i j = g.val (Fin.castLE hr i) (Fin.castLE hr j) := by
  have hg : g ∈ blockTri (κ := κ) (blk2 r) := fun i j h => by
    have hi : i.val < r := lt_of_lt_of_le i.2 hn
    have hj : j.val < r := lt_of_lt_of_le j.2 hn
    simp [blk2, hi, hj] at h
  rw [upper_block_val_submatrix hr hg]
  rfl


set_option maxHeartbeats 1000000 in
theorem red_of_isLoc : ∀ (D : D7) (u : D.what₂.Word) (d : GlobalTheory.SeeSaw.Dat D u) (τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E) (PP : Pl D.host.E) (G : GlobalTheory.LocMod.GAt d τ PP), d.Base → ∀ (hr : D.R.r ≤ (d.st 0).V.rank) (g : GA D (d.st 0).V) (x : G.S.P.J), (GlobalTheory.LocMod.ofSplit G.q).IsLoc (G.FY 0 (G.s + 1) (Nat.zero_add _)) g (GlobalTheory.LevZeroGen.upZero G.S (Fin D.R.t) x.1) → finE (d.st 0).V ((d.t 0)⁻¹ * g * d.t 0) ∈ St (d.st 0).β → G.Red x (upperLeftBlock hr (redFn (d.st 0).β PP (finE (d.st 0).V ((d.t 0)⁻¹ * g * d.t 0)))) := by
  intro D u d τ PP G hB hr g x hg hS
  obtain ⟨π', h1, h2, -⟩ := GlobalTheory.FinPl.SplitPt.exists_lift_isRed D G.k G.q PP G.idem
  obtain ⟨e, he, hM⟩ := G.frame 0 (G.s + 1) (Nat.zero_add _)
  obtain ⟨m, hm⟩ := hS
  choose f hf using toEAf_onto D
  have hπ : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) (Formalism.L2.Theta.AE D)), (Z.map (toEAf D)).map π' = Z.map (GlobalTheory.LocMod.ofSplit G.q).π := fun Z => by
    ext i j; exact h1 _
  have hb : (((d.st 0).β.val.map f).map (toEAf D)) = (d.st 0).β.val := by ext i j; exact hf _
  have hM' := hM _ hb
  rw [← hπ, Matrix.map_mul (f := toEAf D), hb, ← finE_val] at hM'
  have hg2 := hg.2
  rw [← hπ, ← finE_val] at hg2
  have hmul : Lev.finE (d.st 0).V (d.t 0) * (d.st 0).β * intGL _ _ _ m =
      Lev.finE (d.st 0).V g * (Lev.finE (d.st 0).V (d.t 0) * (d.st 0).β) := by
    have : (d.st 0).β * intGL _ _ _ m * (d.st 0).β⁻¹ = _ := hm
    rw [map_mul, map_mul, map_inv] at this
    rw [mul_assoc, eq_mul_of_mul_inv_eq this]
    group
  have hmul' := congrArg (fun Z : GL (Fin (d.st 0).V.rank) (Lev.EAf D) => Z.val.map π') hmul
  simp only [Units.val_mul] at hmul'
  rw [Matrix.map_mul (L := _ * _), Matrix.map_mul (M := _ * _), hM', hg2] at hmul'
  have key := matrix_in_frame _ _ (G.FY 0 (G.s + 1) (Nat.zero_add _)).γβ _ _ e
    (x.1.val.submatrix (GlobalTheory.StepData.ixZero _ (Fin D.R.t)).symm (GlobalTheory.StepData.ixZero _ (Fin D.R.t)).symm) _ hmul'
  have hn : (d.st 0).V.rank ≤ D.R.r := by
    have := (hB.st 0 (by have := G.hs; omega)).rank
    rw [this]; simp [Formalism.BasicNotions.Ranks.rankY]
  intro a b a' b' ha hb' z hz
  rw [upperLeftBlock_apply_of_eq hr hn, ← hm, redFn_frGL] at hz
  have ea : e.symm (Fin.castLE hr a') = Sum.inl a := by
    rw [Equiv.symm_apply_eq]; apply Fin.ext; rw [he]; rcases a with a | a <;> exact ha
  have eb : e.symm (Fin.castLE hr b') = Sum.inl b := by
    rw [Equiv.symm_apply_eq]; apply Fin.ext; rw [he]; rcases b with b | b <;> exact hb'
  have k2 := congrFun (congrFun key (Fin.castLE hr a')) (Fin.castLE hr b')
  rw [Matrix.submatrix_apply, ea, eb] at k2
  have k3 : resS D.host.F PP (m.val (Fin.castLE hr a') (Fin.castLE hr b') - oToS D.host.F D.host.E z) = 0 := by
    rw [map_sub, resS_oToS, hz]; exact sub_self _
  have k4 := (h2.ker _).1 k3
  rw [map_sub] at k4
  have k5 : π' (oToS D.host.F D.host.E z).1 = (GlobalTheory.LocMod.ofSplit G.q).pr (z : D.host.E) := by
    refine Eq.trans (congrArg π' ?_) (h1 (incA D (z : D.host.E)))
    rfl
  convert k4 using 3
  · exact k2.symm
  · exact k5.symm

end GlobalTheory.LevZeroRead
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ProdLocalParts
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel

noncomputable section

namespace GlobalTheory.LevelCut

open GlobalTheory.SplitCut

variable {D : D7}

theorem entry_idAt (V : HSp D) (P : Pl D → Prop) (g : GA D V) (hg : g ∈ grpAt V P) (i j : Fin V.rank) :
    (mt V g - 1) i j ∈ idAt D P := by
  have h := congrArg (fun x : GL (Fin V.rank) (AE D ⧸ idAt D P) => x.1 i j) (show _ = (1 : GL _ _) from hg)
  change Ideal.Quotient.mk (idAt D P) (mt V g i j) = _ at h
  have h2 : Ideal.Quotient.mk (idAt D P) (mt V g i j) =
      Ideal.Quotient.mk (idAt D P) ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) := by
    rw [h, Units.val_one]; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  rw [Matrix.sub_apply]; exact Ideal.Quotient.eq.mp h2


open GlobalTheory.LocWeil.PlaceIdem in
theorem sum_act {W : Type} [Fintype W] (v : W → Pl D) (hv : Function.Injective v)
    (y : AE D) (hy : y ∈ idAt D (fun u => u ∈ Set.range v)) :
    (1 - ∑ w, algebraMap (AF D.host.F) (AE D) (eFin D.host.F (v w))) * y = 0 := by
  unfold idAt at hy
  obtain ⟨h1, h2⟩ := hy
  have h1' : infPart D y = 0 := h1
  have h2' : ∀ u, u ∉ Set.range v → compAt D u y = 0 := fun u hu => by
    have := (Ideal.mem_iInf.1 h2) ⟨u, hu⟩
    exact (RingHom.mem_ker).mp this
  have h3 := key v hv y h2'
  have h0 : finPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0)) = 0 := by
    rw [finPart_algebraMap]
    exact TensorProduct.zero_tmul _ _
  have h4 : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0) * y = 0 :=
    GlobalTheory.SplitScalar.adele_ext (by rw [RingHom.map_mul, h1', mul_zero, RingHom.map_zero])
      (by rw [RingHom.map_mul, h0, zero_mul, RingHom.map_zero])
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, map_sub, map_one, map_sum] at h3
  linear_combination h3 + h4

theorem pr_sum {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k) :
    q.pr (q.e + cA D q.e) = 1 := by
  have h2 := q.split.2.1
  have ho : q.sec 1 = q.e := by rw [← q.pr.map_one, q.sec_pr, mul_one]
  have p1 : q.pr q.e = 1 := by rw [← ho, q.pr_sec]
  have p2 : q.pr (cA D q.e) = 0 := by rw [← one_mul (q.pr _), ← p1, ← RingHom.map_mul, h2, RingHom.map_zero]
  rw [RingHom.map_add (f := _), p1, p2, add_zero]

theorem exists_coord {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k N Y)
    (A B : Matrix (Fin N) (Fin N) k) (h1 : A * B = 1) (h2 : B * A = 1) : ∃ x : GL Y k, A = F.β * x.val * F.γ := by
  have key : ∀ A B : Matrix (Fin N) (Fin N) k, A * B = 1 → (F.γ * A * F.β) * (F.γ * B * F.β) = 1 := fun A B h => by
    calc (F.γ * A * F.β) * (F.γ * B * F.β) = F.γ * (A * (F.β * F.γ) * B) * F.β := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [F.βγ, Matrix.mul_one, h, Matrix.mul_one, F.γβ]
  refine ⟨⟨F.γ * A * F.β, F.γ * B * F.β, key A B h1, key B A h2⟩, ?_⟩
  calc A = (F.β * F.γ) * A * (F.β * F.γ) := by rw [F.βγ, Matrix.mul_one, Matrix.one_mul]
    _ = F.β * (F.γ * A * F.β) * F.γ := by simp only [Matrix.mul_assoc]


open GlobalTheory.LocWeil.PlaceIdem in
theorem exists_parts (V : HSp D) {n : ℕ} (v : Fin n → Pl D) (e : Fin n → AE D) (hv : Function.Injective v)
    (he : ∀ w, ∃ ε, IsPlaceIdem D (v w) ε ∧ e w + cA D (e w) = algebraMap (AF D.host.F) (AE D) ε)
    (g : GA D V) (hg : g ∈ grpAt V (fun u => u ∈ Set.range v)) :
    ∃ h : Fin n → GA D V, (∀ w, SuppAt (e w) V (h w)) ∧
      (∀ w, mt V (h w) = (e w + cA D (e w)) • mt V g + (1 - (e w + cA D (e w))) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) ∧
      g = ((List.finRange n).map h).prod := by
  set E : Fin n → AE D := fun w => algebraMap (AF D.host.F) (AE D) (eFin D.host.F (v w)) with hEdef
  have hE : ∀ w, e w + cA D (e w) = E w := fun w => by
    obtain ⟨ε, hε, h⟩ := he w
    rw [h, eFin_of_placeIdem hε]
  have hEE : ∀ w, E w * E w = E w := fun w => by
    simp only [hEdef, ← map_mul, eFin_idem]
  have hEc : ∀ w, cA D (E w) = E w := fun w => cA_algebraMap _
  have hEo : ∀ w w', w ≠ w' → E w * E w' = 0 := fun w w' hww => by
    simp only [hEdef, ← map_mul]
    rw [eFin_mul_eFin _ (fun h => hww (hv h)), map_zero]
  choose h hh using fun w => cut_exists V g (E w) (hEE w) (hEc w)
  refine ⟨h, fun w i j => ?_, fun w => ?_, ?_⟩
  · rw [hE w, hh w]
    exact idempotent_mul_cut_sub_one_entry _ (hEE w) _ i j
  · rw [hE w, hh w]
  · apply GlobalTheory.SplitCut.mt_injective
    rw [mt_list_prod V h E _ hh hEo _ (List.nodup_finRange n), ← Fin.sum_univ_def]
    exact exists_widePullback_of_iteratedLine _ _ fun i j => sum_act v hv _ (entry_idAt V _ g hg i j)

theorem prod_local_parts : ∀ (D : D7) (c : Comm D) (v : VCom c) (n : ℕ) (G : Fin n → GLoc v), GPin G →
    ∀ (j : ℕ) (k : GA D (c.V j)), k ∈ grpAt (c.V j) (· ∈ v.gP) → ∃ h : Fin n → GA D (c.V j),
      (∀ i b hb, ∃ x, (G i).Mat j b hb k x ∧ (ofSplit (G i).q).IsLoc ((G i).FY j b hb) (h i) x) ∧
        k = ((List.finRange n).map h).prod := by
  intro D c v n G hG j g hg
  have hP : (fun u => u ∈ v.gP) = fun u => u ∈ Set.range (fun i => (G i).q.v) := by
    funext u
    rw [hG.places u]
    exact propext ⟨fun ⟨i, h⟩ => ⟨i, h.symm⟩, fun ⟨i, h⟩ => ⟨i, h.symm⟩⟩
  rw [hP] at hg
  obtain ⟨h, h1, h2, h3⟩ := exists_parts (c.V j) (fun i => (G i).q.v) (fun i => (G i).q.e) hG.inj
    (fun i => (G i).q.above) g hg
  refine ⟨h, fun i b hb => ?_, h3⟩
  have hm : ∀ a a' : GA D (c.V j), a * a' = 1 →
      (mt (c.V j) a).map (G i).q.pr * (mt (c.V j) a').map (G i).q.pr = 1 := fun a a' ha => by
    rw [← Matrix.map_mul, ← GlobalTheory.SplitCut.mt_mul, ha, GlobalTheory.SplitCut.mt_one, Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _)]
  obtain ⟨x, hx⟩ := exists_coord ((G i).FY j b hb) _ _ (hm g g⁻¹ (mul_inv_cancel g)) (hm g⁻¹ g (inv_mul_cancel g))
  refine ⟨x, hx, h1 i, ?_⟩
  change (mt (c.V j) (h i)).map (G i).q.pr = _
  rw [h2 i, GlobalTheory.GfCut.map_idem, pr_sum, one_smul, sub_self, zero_smul, add_zero]
  exact hx

end GlobalTheory.LevelCut
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalModelSliceFirstSummand
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalModelSliceFirstSummand
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SliceLeft

open GlobalTheory.MixModel.OrthDec GlobalTheory.LocFlat.CFac GlobalTheory.SliceLine

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

def boxL (c : SB (Matrix n Unit k)) : SB (Matrix n n' k) →ₗ[ℂ] SB (Matrix n (n' ⊕ Unit) k) where
  toFun Ξ := box Ξ c
  map_add' Ξ Ξ' := Subtype.ext (funext fun x => by simp [box, splitCols, add_mul])
  map_smul' a Ξ := Subtype.ext (funext fun x => by simp [box, splitCols]; ring)

theorem heis_slice_left {S A L T : HSp D} (d : OrthDec S A L) (ψ : AddChar (AF D.host.F) ℂ) (f : WO S T → ℂ)
    (u u' : WO A T) (w : WO L T) :
    heisO ψ S T ((d.resS T).symm (u', 0)) f ((d.resS T).symm (u, w)) =
      heisO ψ A T u' (fun u => f ((d.resS T).symm (u, w))) u := by
  simp only [heisO]
  rw [d.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, GlobalTheory.MixModel.symplOH_zero_right, add_zero,
    ← map_add, Prod.mk_add_mk, add_zero]

theorem isHalf_slice_left {S A L T : HSp D} (d : OrthDec S A L) {a : AE D} {y : WO A T} (hy : IsHalf a y) :
    IsHalf a ((d.resS T).symm (y, 0)) := by
  intro i j
  rw [resS_symm_apply, Matrix.zero_mul, add_zero, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← mul_assoc, hy i l]

end GlobalTheory.SliceLeft

namespace GlobalTheory.SliceLeft

open GlobalTheory.MixModel.OrthDec GlobalTheory.LocFlat.CFac GlobalTheory.SliceLine

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
variable {ρ : ℕ} {B : BesLev D ρ} {s : k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {FA : Frame k B.A.rank n'} {F₀ : Frame k B.V₀.rank (n' ⊕ Unit)} {FL : Frame k B.L.rank Unit}

theorem up_fromCols_left (h : p.IsCoreFrame B s FA F₀) (hL : ∀ r, FL.β r () = s * p.pr (B.ζ r)) {S : HSp D}
    (FS : Frame k S.rank n) (x : Matrix n n' k) :
    p.up F₀ FS (fromCols x 0) = (B.o.resS S).symm (p.up FA FS x, 0) := by
  have k1 : x * FA.γ * B.o.qA.map (p.π.comp (incA D)) * F₀.β = fromCols x (0 : Matrix n Unit k) := by
    rw [beta_eq p h hL, Matrix.mul_fromCols]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (B.o.qA.map _) (B.o.iA.map _), ← Matrix.map_mul, B.o.qA_iA,
      ← Matrix.mul_assoc (B.o.qA.map _) (B.o.iB.map _), ← Matrix.map_mul, B.o.qA_iB]
    simp [FA.γβ]
  have k2 : fromCols x (0 : Matrix n Unit k) * F₀.γ = x * FA.γ * B.o.qA.map (p.π.comp (incA D)) := by
    rw [← k1, Matrix.mul_assoc (x * FA.γ * B.o.qA.map (p.π.comp (incA D))) F₀.β F₀.γ, F₀.βγ, Matrix.mul_one]
  rw [resS_symm_apply, Matrix.zero_mul, add_zero]
  unfold Place.up
  rw [pA, map_ι_mul, rat_map_π]
  congr 1
  rw [Matrix.mul_assoc FS.β (fromCols x 0) F₀.γ, k2]
  simp only [Matrix.mul_assoc]

theorem resS_up_fst (h : p.IsCoreFrame B s FA F₀) (hL : ∀ r, FL.β r () = s * p.pr (B.ζ r)) {S : HSp D}
    (FS : Frame k S.rank n) (t : Matrix n (n' ⊕ Unit) k) :
    (B.o.resS S (p.up F₀ FS t)).1 = p.up FA FS t.toCols₁ := by
  have k1 : t * F₀.γ * B.o.iA.map (p.π.comp (incA D)) * FA.β = t.toCols₁ := by
    calc t * F₀.γ * B.o.iA.map (p.π.comp (incA D)) * FA.β
        = ((t * F₀.γ) * fromCols (B.o.iA.map (p.π.comp (incA D)) * FA.β)
            (B.o.iB.map (p.π.comp (incA D)) * FL.β)).toCols₁ := by
          rw [Matrix.mul_fromCols, toCols₁_fromCols, Matrix.mul_assoc (t * F₀.γ)]
      _ = ((t * F₀.γ) * F₀.β).toCols₁ := by rw [← beta_eq p h hL]
      _ = t.toCols₁ := by rw [Matrix.mul_assoc, F₀.γβ, Matrix.mul_one]
  have k2 : t * F₀.γ * B.o.iA.map (p.π.comp (incA D)) = t.toCols₁ * FA.γ := by
    rw [← k1, Matrix.mul_assoc (t * F₀.γ * B.o.iA.map (p.π.comp (incA D))) FA.β FA.γ, FA.βγ, Matrix.mul_one]
  rw [resS_apply]
  dsimp only
  unfold Place.up
  rw [jA, map_ι_mul, rat_map_π]
  simp only [Matrix.mul_assoc] at k2 ⊢
  rw [k2]

end GlobalTheory.SliceLeft

namespace GlobalTheory.SliceLeft

open GlobalTheory.MixModel.OrthDec GlobalTheory.LocFlat.CFac GlobalTheory.SliceLine

theorem toCols_add_left {k n n' : Type} [Field k] (t : Matrix n (n' ⊕ Unit) k) (x : Matrix n n' k) :
    (t + fromCols x (0 : Matrix n Unit k)).toCols₁ = t.toCols₁ + x ∧
      (t + fromCols x (0 : Matrix n Unit k)).toCols₂ = t.toCols₂ :=
  ⟨by ext i j; simp, by ext i j; simp⟩

theorem slice_left : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (s : k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n), p.IsCoreFrame B s FA F₀ → ∀ T₀, p.IsModel ψ F₀ FS T₀ → ∀ (c : SB (Matrix n Unit k)) (w₀ : WO B.L S), ∃ T', p.IsModel ψ FA FS T' ∧ ∀ (Ξ : SB (Matrix n n' k)) (Ψ : SB (Matrix n (n' ⊕ Unit) k)), (∀ x, Ψ.1 x = Ξ.1 x.toCols₁ * c.1 (Matrix.of fun r _ => x r (Sum.inr ()))) → ∀ u, T' Ξ u = T₀ Ψ ((B.o.resS S).symm (u, w₀)) := by
  intro D k _ _ _ _ p ψ ρ B S s n n' _ _ _ _ FA F₀ FS h T₀ hT c w₀
  obtain ⟨FL, hFL, -⟩ := slice_line D k p ψ ρ B S s n n' FA F₀ FS h T₀ hT
  let T' : SB (Matrix n n' k) →ₗ[ℂ] (WO B.A S → ℂ) :=
    (LinearMap.funLeft ℂ ℂ (fun u : WO B.A S => (B.o.resS S).symm (u, w₀))).comp (T₀.comp (boxL c))
  have hT' : ∀ Ξ u, T' Ξ u = T₀ (box Ξ c) ((B.o.resS S).symm (u, w₀)) := fun _ _ => rfl
  refine ⟨T', ⟨fun Φ => ?_, fun x Φ Φ' hΦ => ?_, fun y hy Φ Φ' hΦ => ?_⟩, fun Ξ Ψ hΨ u => ?_⟩
  · exact GlobalTheory.BoxSlice.isThetaFunO_slice_left B.o (hT.theta (box Φ c)) w₀
  · have e := hT.trans (fromCols x 0) (box Φ c) (box Φ' c) (fun t => by
      rw [box_apply, box_apply, hΦ, (toCols_add_left t x).1, (toCols_add_left t x).2])
    funext u
    rw [hT', e, up_fromCols_left p h hFL, heis_slice_left]
    rfl
  · have e := hT.modul ((B.o.resS S).symm (y, 0)) (isHalf_slice_left B.o hy) (box Φ c) (box Φ' c) (fun t => by
      simp only [box_apply, hΦ, B.o.symplO_resS, AddEquiv.apply_symm_apply, resS_up_fst p h hFL, symplO_zero_right',
        add_zero]
      ring)
    funext u
    rw [hT', e, heis_slice_left]
    rfl
  · have e : Ψ = box Ξ c := Subtype.ext (funext fun x => by rw [hΨ, box_apply]; rfl)
    rw [hT', e]

end GlobalTheory.SliceLeft
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalModelSliceFirstSummandStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localModel_slice_firstSummand : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (s : k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n), p.IsCoreFrame B s FA F₀ → ∀ T₀, p.IsModel ψ F₀ FS T₀ → ∀ (c : SB (Matrix n Unit k)) (w₀ : WO B.L S), ∃ T', p.IsModel ψ FA FS T' ∧ ∀ (Ξ : SB (Matrix n n' k)) (Ψ : SB (Matrix n (n' ⊕ Unit) k)), (∀ x, Ψ.1 x = Ξ.1 x.toCols₁ * c.1 (Matrix.of fun r _ => x r (Sum.inr ()))) → ∀ u, T' Ξ u = T₀ Ψ ((B.o.resS S).symm (u, w₀)) := by
  first | exact @GlobalTheory.SliceLeft.slice_left | exact GlobalTheory.SliceLeft.slice_left | (intros; apply GlobalTheory.SliceLeft.slice_left <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawProdLocalCellsDistinctPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawProdLocalCellsDistinctPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.CellProd

theorem prod_ofFn_mul {M : Type} [Monoid M] : ∀ {n : ℕ} (r u : Fin n → M), (∀ i i', i ≠ i' → Commute (u i) (r i')) →
    (List.ofFn fun i => r i * u i).prod = (List.ofFn r).prod * (List.ofFn u).prod
  | 0, _, _, _ => by simp
  | n + 1, r, u, h => by
    have ih := prod_ofFn_mul (fun i => r i.succ) (fun i => u i.succ)
      (fun i i' hi => h _ _ fun e => hi (Fin.succ_injective _ e))
    have hc : Commute (u 0) (List.ofFn fun i : Fin n => r i.succ).prod := by
      refine Commute.list_prod_right _ _ ?_
      rw [List.forall_mem_ofFn_iff]
      intro i
      exact h _ _ (Fin.succ_ne_zero i).symm
    simp only [List.ofFn_succ, List.prod_cons]
    rw [ih, mul_assoc, mul_assoc, ← mul_assoc (u 0), hc.eq, mul_assoc]

theorem prod_ofFn_single {M : Type} [Monoid M] : ∀ {n : ℕ} (f : Fin n → M) (i : Fin n), (∀ i', i' ≠ i → f i' = 1) →
    (List.ofFn f).prod = f i
  | 0, _, i, _ => i.elim0
  | n + 1, f, i, h => by
    simp only [List.ofFn_succ, List.prod_cons]
    induction i using Fin.cases with
    | zero =>
      rw [List.prod_eq_one, mul_one]
      rw [List.forall_mem_ofFn_iff]
      intro i
      exact h _ (Fin.succ_ne_zero i)
    | succ i =>
      rw [h 0 (Fin.succ_ne_zero i).symm, one_mul]
      exact prod_ofFn_single (fun i => f i.succ) i fun i' hi => h _ fun e => hi (Fin.succ_injective _ e)

variable {D : D7} {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

theorem idAt_le {P P' : Pl D → Prop} (h : ∀ v, P v → P' v) : idAt D P ≤ idAt D P' :=
  inf_le_inf_left _ (le_iInf fun w => iInf_le_of_le ⟨w.1, fun hw => w.2 (h _ hw)⟩ le_rfl)

theorem mem_idAt (q : SplitPt D k) {a : AE D} (h : (q.e + cA D q.e) * a = a) : a ∈ idAt D (· = q.v) := by
  obtain ⟨ε, hε, hs⟩ := q.above
  exact ((placeIdem_acts D q.v ε hε).1 a).2 (hs ▸ h)

theorem idem_mul_eq_zero (q : SplitPt D k) (q' : SplitPt D k') (hv : q'.v ≠ q.v) {a : AE D}
    (h : (q'.e + cA D q'.e) * a = a) : (q.e + cA D q.e) * a = 0 := by
  obtain ⟨ε, hε, hs⟩ := q.above
  rw [hs]
  exact (placeIdem_acts D q.v ε hε).2 a (idAt_le (fun v (e : v = q'.v) => e ▸ hv) (mem_idAt q' h))

theorem pr_eq_zero (q : SplitPt D k) (q' : SplitPt D k') (hv : q'.v ≠ q.v) {a : AE D}
    (h : (q'.e + cA D q'.e) * a = a) : q.pr a = 0 := by
  have h0 := idem_mul_eq_zero q q' hv h
  obtain ⟨h1, h2, -⟩ := q.split
  have : q.e * a = 0 := by
    have := congrArg (q.e * ·) h0
    simpa only [← mul_assoc, mul_add, h1, h2, add_zero, mul_zero] using this
  rw [← q.pr_sec (q.pr a), q.sec_pr, this, map_zero]

theorem mem_grpAt (q : SplitPt D k) {V : HSp D} {g : GA D V} (hg : SuppAt q.e V g) {P : Pl D → Prop} (hP : P q.v) :
    g ∈ grpAt V P := by
  rw [grpAt, congGrp, MonoidHom.mem_ker]
  ext i j
  change Ideal.Quotient.mk _ (mt V g i j) = (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j
  rw [← Matrix.map_one (Ideal.Quotient.mk (idAt D P)) (map_zero _) (map_one _), Matrix.map_apply, Ideal.Quotient.eq]
  exact idAt_le (fun v (e : v = q.v) => e ▸ hP) (mem_idAt q (hg i j))

theorem mt_mul' (V : HSp D) (g h : GA D V) : mt V (g * h) = mt V g * mt V h := by
  simp [Formalism.L2.Theta.mt]

theorem sub_mul_sub (q : SplitPt D k) (q' : SplitPt D k') (hv : q'.v ≠ q.v) {V : HSp D} {g h : GA D V}
    (hg : SuppAt q.e V g) (hh : SuppAt q'.e V h) :
    (mt V g - 1) * (mt V h - 1) = 0 ∧ (mt V h - 1) * (mt V g - 1) = 0 := by
  have key : ∀ a b c d, (mt V g - 1) a b * (mt V h - 1) c d = 0 := fun a b c d => by
    rw [← hg a b, mul_comm (q.e + _), mul_assoc, idem_mul_eq_zero q q' hv (hh c d), mul_zero]
  constructor
  · ext a b
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun c _ => key _ _ _ _
  · ext a b
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun c _ => by rw [mul_comm]; exact key _ _ _ _

theorem commute_of_suppAt (q : SplitPt D k) (q' : SplitPt D k') (hv : q'.v ≠ q.v) {V : HSp D} {g h : GA D V}
    (hg : SuppAt q.e V g) (hh : SuppAt q'.e V h) : Commute g h := by
  obtain ⟨h1, h2⟩ := sub_mul_sub q q' hv hg hh
  have : mt V (g * h) = mt V (h * g) := by
    rw [mt_mul', mt_mul', ← sub_eq_zero]
    have e : mt V g * mt V h - mt V h * mt V g = (mt V g - 1) * (mt V h - 1) - (mt V h - 1) * (mt V g - 1) := by
      noncomm_ring
    rw [e, h1, h2, sub_zero]
  exact Subtype.ext (Units.ext this)

theorem map_eq_one (q : SplitPt D k) (q' : SplitPt D k') (hv : q'.v ≠ q.v) {V : HSp D} {g : GA D V}
    (hg : SuppAt q'.e V g) : (mt V g).map q.pr = 1 := by
  ext i j
  have := pr_eq_zero q q' hv (hg i j)
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
  rw [Matrix.map_apply, this, ← Matrix.map_one q.pr (map_zero _) (map_one _), Matrix.map_apply]

def matAt (q : SplitPt D k) (V : HSp D) : GA D V →* Matrix (Fin V.rank) (Fin V.rank) k :=
  (q.pr.mapMatrix.toMonoidHom.comp (Units.coeHom _)).comp (matHom V)

end GlobalTheory.SeeSaw.CellProd


open GlobalTheory.SeeSaw.CellProd in
theorem GlobalTheory.SeeSaw.prod_local_cells : ∀ {D : D7} {c : Comm D} {v : VCom c} {n : ℕ} (G : Fin n → GLoc v), GPin G → ∀ (j' : ℕ), j' < D.R.m → ∀ (R : Subgroup (GA D (c.V j'))) (b : Fin n → ℕ) (hb : ∀ i, j' + b i = (G i).s + 1) (xs : Fin n → GA D (c.V j')), (∀ i, ∃ r ∈ R, SuppAt (G i).q.e (c.V j') r ∧ ∃ u uk, (GlobalTheory.LocMod.ofSplit (G i).q).IsLoc ((G i).FY j' (b i) (hb i)) u uk ∧ uk ∈ (((G i).S.T (Fin D.R.t)).lev j' (b i) (hb i)).J ∧ xs i = r * u) → ∃ r ∈ R, r ∈ grpAt (c.V j') (· ∈ v.gP) ∧ ∃ k ∈ v.JG j', (List.ofFn xs).prod = r * k := by
  intro D c v n G hG j' hj R b hb xs H
  choose r hr hrs u uk hu huk hx using H
  have hne : ∀ i i', i ≠ i' → (G i).q.v ≠ (G i').q.v := fun i i' h e => h (hG.inj e)
  have hP : ∀ i, (G i).q.v ∈ v.gP := fun i => (hG.places _).2 ⟨i, rfl⟩
  have hus : ∀ i, SuppAt (G i).q.e (c.V j') (u i) := fun i => (hu i).1
  refine ⟨(List.ofFn r).prod, R.list_prod_mem ?_, Subgroup.list_prod_mem _ ?_, (List.ofFn u).prod,
    (hG.lev j' hj _).2 ⟨Subgroup.list_prod_mem _ ?_, ?_⟩, ?_⟩
  · rw [List.forall_mem_ofFn_iff]
    intro i
    exact hr i
  · rw [List.forall_mem_ofFn_iff]
    intro i
    exact mem_grpAt (G i).q (hrs i) (hP i)
  · rw [List.forall_mem_ofFn_iff]
    intro i
    exact mem_grpAt (G i).q (hus i) (hP i)
  · intro i a ha y hy
    obtain rfl : a = b i := by have := hb i; omega
    have e : matAt (G i).q (c.V j') (List.ofFn u).prod = matAt (G i).q (c.V j') (u i) := by
      rw [map_list_prod, List.map_ofFn]
      exact prod_ofFn_single _ i fun i' hi => map_eq_one (G i).q (G i').q (hne _ _ hi) (hus i')
    have e2 : ((G i).FY j' (b i) ha).β * y.val * ((G i).FY j' (b i) ha).γ =
        ((G i).FY j' (b i) ha).β * (uk i).val * ((G i).FY j' (b i) ha).γ := hy.symm.trans (e.trans (hu i).2)
    have e3 := congrArg (fun x => ((G i).FY j' (b i) ha).γ * x * ((G i).FY j' (b i) ha).β) e2
    simp only [← Matrix.mul_assoc, GlobalTheory.LocMod.Frame.γβ, Matrix.one_mul] at e3
    simp only [Matrix.mul_assoc, GlobalTheory.LocMod.Frame.γβ, Matrix.mul_one] at e3
    rw [Units.ext e3]
    exact huk i
  · rw [show xs = fun i => r i * u i from funext hx]
    exact prod_ofFn_mul r u fun i i' h => commute_of_suppAt (G i).q (G i').q (hne _ _ h.symm) (hus i) (hrs i')

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawProdLocalCellsDistinctPlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSaw_prod_local_cells_distinct_places : ∀ {D : D7} {c : Comm D} {v : VCom c} {n : ℕ} (G : Fin n → GLoc v), GPin G → ∀ (j' : ℕ), j' < D.R.m → ∀ (R : Subgroup (GA D (c.V j'))) (b : Fin n → ℕ) (hb : ∀ i, j' + b i = (G i).s + 1) (xs : Fin n → GA D (c.V j')), (∀ i, ∃ r ∈ R, SuppAt (G i).q.e (c.V j') r ∧ ∃ u uk, (GlobalTheory.LocMod.ofSplit (G i).q).IsLoc ((G i).FY j' (b i) (hb i)) u uk ∧ uk ∈ (((G i).S.T (Fin D.R.t)).lev j' (b i) (hb i)).J ∧ xs i = r * u) → ∃ r ∈ R, r ∈ grpAt (c.V j') (· ∈ v.gP) ∧ ∃ k ∈ v.JG j', (List.ofFn xs).prod = r * k := by
  first | exact @GlobalTheory.SeeSaw.prod_local_cells | exact GlobalTheory.SeeSaw.prod_local_cells | (intros; apply GlobalTheory.SeeSaw.prod_local_cells <;> assumption)
end
end

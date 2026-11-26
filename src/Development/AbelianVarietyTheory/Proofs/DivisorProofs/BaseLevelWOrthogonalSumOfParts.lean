module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianInvariantFormsProportionalFinitePlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagMemDoubledVacuumLatticeStabilizer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharHalfTraceTensorLatticeHeisenbergCocycle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementDet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingExistsDoublingConfiguration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentCoprimeAtGoodPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePlaceComponentAdeleNormEqLocalNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagUnipotentRadicalLeStandardParabolicUnipotent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxChangeRealisedCompAndReindex

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLevelWOrthogonalSumOfParts
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WFormsPartsOfDistinctTypesOrthogonal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WFormsPartsOfDistinctTypesOrthogonal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram evC dualC)
namespace GlobalTheory.OrthW

theorem evC_single {D : D7} {V : HSp D} {P : Pl D.host.E} {a : List ℤ → ℂ} {d : List ℤ} (hd : IsLab V P d) :
    evC V P a (Finsupp.single d 1) = a d := by
  unfold evC
  rw [Finsupp.sum_single_index] <;> simp [hd]

theorem dualC_single (d : List ℤ) :
    dualC (Finsupp.mapRange star (star_zero ℂ) (Finsupp.single d (1 : ℂ))) = Finsupp.single (dualLab d) 1 := by
  simp [dualC, Finsupp.mapRange_single, Finsupp.mapDomain_single]

theorem inner_eq_zero_of_eig {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (T S : H →ₗ[ℂ] H) (hadj : LinearMap.adjoint T = S) {a b b' : ℂ} {x y : H} (hx : T x = a • x) (hy : T y = b • y)
    (hy' : S y = b' • y) (hne : a ≠ b) : ⟪x, y⟫_ℂ = 0 := by
  have hxy : ⟪T x, y⟫_ℂ = ⟪x, S y⟫_ℂ := by rw [← hadj, LinearMap.adjoint_inner_right]
  have hyy : ⟪T y, y⟫_ℂ = ⟪y, S y⟫_ℂ := by rw [← hadj, LinearMap.adjoint_inner_right]
  rw [hx, hy'] at hxy
  rw [hy, hy'] at hyy
  rw [inner_smul_left, inner_smul_right] at hxy hyy
  by_cases hy0 : y = 0
  · simp [hy0]
  have hyy0 : ⟪y, y⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hy0
  have hconj : (starRingEnd ℂ) b = b' := mul_right_cancel₀ hyy0 hyy
  rw [← hconj] at hxy
  have hne' : (starRingEnd ℂ) a ≠ (starRingEnd ℂ) b := fun h => hne ((starRingEnd ℂ).injective h)
  have := sub_eq_zero.mpr hxy
  rw [← sub_mul] at this
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne')

theorem inner_wp3_eq_zero_of_ne : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → ∀ i p q, p ≠ q → ∀ w ∈ R.Wp3 i p, ∀ w' ∈ R.Wp3 i q, ⟪w, w'⟫_ℂ = 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hW hEx hSch hOkH hPos hB i p q hpq
  obtain ⟨hCore, hSF, hE, hWc⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hW hEx
  have hX : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hOk.ok2.irr
  obtain ⟨hE', hOpsE, hNE, -, hEig, hMem⟩ := GlobalTheory.T.exists_sphericalOperators_rows_normal_eigenspaces R.toRealDat F.lv2 hCore hSch R.SF hSF
  obtain ⟨hw, -, hNW, -, -, -, hWEig, -⟩ := GlobalTheory.T.sphericalOperators_forms_on_rank_space_normal R.toRealDat F.lv2 hCore hSch hX R.SF hSF i
  have hLab := fun P d hP => GlobalTheory.T.isLabel_thetaLiftSpace_iff_dual (s := s) R.toRealDat F.lv2 hCore i P d hP
  have horthE := GlobalTheory.T.orthogonal_rowParts_of_distinct_types R F hOk hW hOkH hPos hB p q hpq
  have key : ∀ c c', R.Carries p c → R.Carries q c' → ∀ x ∈ R.Wc' i c, ∀ y ∈ R.Wc' i c', ⟪x, y⟫_ℂ = 0 := by
    intro c c' hc hc' x hx y hy
    rw [hWc] at hx hy
    rcases Classical.em (∃ P d, Good R.toRealDat A3.A.μ0 P ∧ IsLab (Wc D i) P d ∧ c P d ≠ c' P d) with hdiff | hdiff
    · obtain ⟨P, d, hP, hd, hne⟩ := hdiff
      have hd' : IsLab (Wc D i) P (dualLab d) := (hLab P (dualLab d) hP).2.mpr ((hLab P d hP).1.mp hd)
      have hadj := hNW.2 P hP (Finsupp.single d 1)
      rw [dualC_single] at hadj
      have ex := hWEig c P hP (Finsupp.single d 1) x hx
      have ey := hWEig c' P hP (Finsupp.single d 1) y hy
      have ey' := hWEig c' P hP (Finsupp.single (dualLab d) 1) y hy
      rw [evC_single hd] at ex ey
      rw [evC_single hd'] at ey'
      exact inner_eq_zero_of_eig _ _ hadj ex ey ey' hne
    · have hagree : ∀ P d, Good R.toRealDat A3.A.μ0 P → IsLab (Wc D i) P d → c P d = c' P d :=
        fun P d hP hd => Classical.byContradiction fun h => hdiff ⟨P, d, hP, hd, h⟩
      exfalso
      have hle : EEc R.toRealDat R.SF c ≤ EEc R.toRealDat R.SF c' := by
        intro e he
        apply hMem c' e
        intro P d hP hd
        rw [hEig c P hP _ e he, evC_single hd]
        congr 1
        apply hagree P (dualLab d) hP
        exact (hLab P (dualLab d) hP).2.mpr ((hLab P d hP).1.mp ((hLab P d hP).2.mpr hd))
      obtain ⟨e, he, he0⟩ := (Submodule.ne_bot_iff _).mp hc.1
      have hep : e ∈ R.EEp3 p := (le_iSup₂ (f := fun c (_ : R.Carries p c) => R.EEc c) c hc) he
      have he' : e ∈ R.EEc c' := by
        rw [hE] at he ⊢
        exact hle he
      have heq : e ∈ R.EEp3 q := (le_iSup₂ (f := fun c (_ : R.Carries q c) => R.EEc c) c' hc') he'
      exact he0 (inner_self_eq_zero.mp (horthE e hep e heq))
  have hort : R.Wp3 i p ⟂ R.Wp3 i q := by
    unfold RealDat3.Wp3
    refine Submodule.isOrtho_iSup_left.mpr fun c => Submodule.isOrtho_iSup_left.mpr fun hc => ?_
    refine Submodule.isOrtho_iSup_right.mpr fun c' => Submodule.isOrtho_iSup_right.mpr fun hc' => ?_
    exact Submodule.isOrtho_iff_inner_eq.mpr (key c c' hc hc')
  intro w hw' w' hw''
  exact Submodule.isOrtho_iff_inner_eq.mp hort w hw' w' hw''

end GlobalTheory.OrthW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WFormsPartsOfDistinctTypesOrthogonalStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.W_forms_parts_of_distinct_types_orthogonal : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → ∀ i p q, p ≠ q → ∀ w ∈ R.Wp3 i p, ∀ w' ∈ R.Wp3 i q, ⟪w, w'⟫_ℂ = 0 := by
  first | exact @GlobalTheory.OrthW.inner_wp3_eq_zero_of_ne | exact GlobalTheory.OrthW.inner_wp3_eq_zero_of_ne | (intros; apply GlobalTheory.OrthW.inner_wp3_eq_zero_of_ne <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLevelWOrthogonalSumOfParts
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.SumW

theorem tw_sub_eq_map {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (c : Bool) (V : Submodule ℂ E) :
    Tw.sub c V = V.map (Tw.mkL c E) := by
  ext x
  constructor
  · intro hx; exact ⟨Tw.out x, hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩; exact hy

theorem tw_sub_iSup {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (c : Bool) (U : ι → Submodule ℂ E) :
    Tw.sub c (⨆ p, U p) = ⨆ p, Tw.sub c (U p) := by
  simp only [tw_sub_eq_map, Submodule.map_iSup]

theorem inner_tw_eq_zero {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (c : Bool) (x y : Tw c E)
    (h : inner ℂ (Tw.out x) (Tw.out y) = 0) : inner ℂ x y = 0 := by
  rw [Tw.inner_eq, h, map_zero]

theorem iSup_inf_typeSp {G E C K : Type} [Group G] [Fintype G] [Field K] [AddCommGroup E] [Module ℂ E] (σ : K →+* ℂ)
    (ρ : Representation ℂ G E) (P : Subgroup G) (ψ : P →* Kˣ) (U : C → Submodule ℂ E)
    (hU : ∀ c g, (U c).map (ρ g) ≤ U c) :
    (⨆ c, U c) ⊓ (⨅ h : P, LinearMap.ker (ρ (h : G) - (σ ((ψ h : Kˣ) : K)) • LinearMap.id)) =
      ⨆ c, U c ⊓ (⨅ h : P, LinearMap.ker (ρ (h : G) - (σ ((ψ h : Kˣ) : K)) • LinearMap.id)) := by
  have := GlobalTheory.iSup_stable_inf_typeSpace ρ P ((Units.map σ.toMonoidHom).comp ψ) U (fun _ => True) hU
  simpa only [iSup_pos trivial, MonoidHom.comp_apply, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] using this

theorem iSup_inf_inf_typeSp {G E C K : Type} [Group G] [Fintype G] [Field K] [AddCommGroup E] [Module ℂ E] (σ : K →+* ℂ)
    (ρ : Representation ℂ G E) (P : Subgroup G) (ψ : P →* Kˣ) (U : C → Submodule ℂ E) (R0 : Submodule ℂ E)
    (hU : ∀ c g, (U c).map (ρ g) ≤ U c) (hsum : (⨆ c, U c) = R0) :
    (⨆ c, U c ⊓ (R0 ⊓ ⨅ h : P, LinearMap.ker (ρ (h : G) - (σ ((ψ h : Kˣ) : K)) • LinearMap.id))) =
      R0 ⊓ ⨅ h : P, LinearMap.ker (ρ (h : G) - (σ ((ψ h : Kˣ) : K)) • LinearMap.id) := by
  have hle : ∀ c, U c ≤ R0 := fun c => hsum ▸ le_iSup U c
  have h1 := iSup_inf_typeSp σ ρ P ψ U hU
  set Kt := ⨅ h : P, LinearMap.ker (ρ (h : G) - (σ ((ψ h : Kˣ) : K)) • LinearMap.id) with hKt
  calc (⨆ c, U c ⊓ (R0 ⊓ Kt)) = ⨆ c, U c ⊓ Kt :=
        iSup_congr fun c => by rw [← inf_assoc, inf_of_le_left (hle c)]
    _ = (⨆ c, U c) ⊓ Kt := h1.symm
    _ = R0 ⊓ Kt := by rw [hsum]

theorem partsW_base : GlobalTheory.Published.CuspRapidDecay → HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → GoodStable A3.A.X → GlobalTheory.CuspMult.CuspDecomp D → GlobalTheory.CuspMult.MultEq R.toRealDat → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) → R.PGEquiv F → (∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → R.toRealDat.LUnif → (R.toCx3 F).PartsW false := by
  intro hCRD hHowe D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hLI hOk hW hEx hInert hGS hCD hME hOkH hPG hPos hkap hB hU
  have hS : SchurAll R.toRealDat := GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCRD R.toRealDat
  obtain ⟨hCore, hSF, -, hWc⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hW hEx
  have hirr : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hOk.ok2.irr
  have hcar := GlobalTheory.T.thetaLift_carrying_of_base_tuple_rows hCRD hHowe R F hLI hOk hW hEx hInert hPG hPos
  have hspan := GlobalTheory.T.cuspidal_multiplicity_carriers R F hOk hW hEx hS hGS hCD hME hcar
  have horth := GlobalTheory.T.W_forms_parts_of_distinct_types_orthogonal R F hOk hW hEx hS hOkH hkap hB
  intro j
  have htype := GlobalTheory.T.range_goodProjector_baseLevel_twistedModel R F hOk hW hEx hU j
  refine ⟨fun p q hpq w hw w' hw' => ?_, ?_⟩
  · exact inner_tw_eq_zero (E := (R.HW j (sg0 D A3.A)).H) (twAt D.what₂.embLL A3.A.v0) w w' (horth j p q hpq _ hw.1 _ hw'.1)
  · obtain ⟨-, -, -, -, -, hst, -⟩ := GlobalTheory.T.sphericalOperators_forms_on_rank_space_normal R.toRealDat F.lv2 hCore hS hirr R.SF hSF j
    have hstab : ∀ p g, (R.Wp3 j p).map (R.gW j (sg0 D A3.A) g) ≤ R.Wp3 j p := by
      intro p g
      unfold RealDat3.Wp3
      simp only [Submodule.map_iSup]
      exact iSup₂_mono fun c _ => by rw [hWc]; exact hst c g
    have hstabX : ∀ p g, ((R.toCx3 F).Wp j p).map (R.gWx F j g) ≤ (R.toCx3 F).Wp j p := by
      rintro p g _ ⟨y, hy, rfl⟩
      exact hstab p g (Submodule.mem_map_of_mem hy)
    have hsumX : (⨆ p, (R.toCx3 F).Wp j p) =
        Tw.sub (twAt D.what₂.embLL A3.A.v0) (LinearMap.range (eH R.toRealDat j)) :=
      (tw_sub_iSup (twAt D.what₂.embLL A3.A.v0) (R.Wp3 j)).symm.trans
        (congrArg (Tw.sub (twAt D.what₂.embLL A3.A.v0)) (hspan j))
    rw [htype]
    unfold typeSubspace
    exact iSup_inf_inf_typeSp _ (R.gWx F j) F.P0 F.ψ0⁻¹ ((R.toCx3 F).Wp j) _ hstabX hsumX

end GlobalTheory.SumW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLevelWOrthogonalSumOfPartsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseLevelW_orthogonalSum_of_parts : GlobalTheory.Published.CuspRapidDecay → HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → GoodStable A3.A.X → GlobalTheory.CuspMult.CuspDecomp D → GlobalTheory.CuspMult.MultEq R.toRealDat → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) → R.PGEquiv F → (∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → R.toRealDat.LUnif → (R.toCx3 F).PartsW false := by
  first | exact @GlobalTheory.SumW.partsW_base | exact GlobalTheory.SumW.partsW_base | (intros; apply GlobalTheory.SumW.partsW_base <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergInvariantFormVanishesLagrangianTest
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.InertLagUniq

open GlobalTheory.LatVac GlobalTheory.InertVacLag

theorem finrank_le_of_isotropic {K : Type} [Field K] {κ : Type} [Fintype κ] (Λ : Submodule K ((κ → K) × (κ → K)))
    (h : ∀ a ∈ Λ, ∀ b ∈ Λ, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) : Module.finrank K Λ ≤ Fintype.card κ := by
  classical
  let B : LinearMap.BilinForm K ((κ → K) × (κ → K)) :=
    LinearMap.mk₂ K (fun a b => a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2)
      (fun a a' b => by simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]; ring)
      (fun c a b => by simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring)
      (fun a b b' => by simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]; ring)
      (fun c a b => by simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring)
  have hB : ∀ a b, B a b = a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2 := fun _ _ => rfl
  have hker : LinearMap.ker B = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    have ha' : ∀ b, B a b = 0 := fun b => by rw [LinearMap.mem_ker.1 ha]; rfl
    refine (Submodule.mem_bot _).2 (Prod.ext (funext fun k => ?_) (funext fun k => ?_))
    · have := ha' (0, Pi.single k 1)
      simpa [hB] using this
    · have := ha' (Pi.single k 1, 0)
      simpa [hB] using this
  have h1 := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := B) Λ
  rw [hker, inf_bot_eq, finrank_bot, add_zero, Module.finrank_prod, Module.finrank_fintype_fun_eq_card] at h1
  have h2 : Λ ≤ B.orthogonal Λ := fun b hb a ha => by
    show B a b = 0
    rw [hB, h a ha b hb, sub_self]
  have h3 := Submodule.finrank_mono h2
  omega

theorem finrank_eq_of_isotropic {K : Type} [Field K] {κ : Type} [Fintype κ] (Λ Λ' : Submodule K ((κ → K) × (κ → K)))
    (h : ∀ a ∈ Λ, ∀ b ∈ Λ, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) (h' : ∀ a ∈ Λ', ∀ b ∈ Λ', a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2)
    (hs : Λ ⊔ Λ' = ⊤) : Module.finrank K Λ = Fintype.card κ := by
  have h1 := finrank_le_of_isotropic Λ h
  have h2 := finrank_le_of_isotropic Λ' h'
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq Λ Λ'
  rw [hs, finrank_top, Module.finrank_prod, Module.finrank_fintype_fun_eq_card] at h3
  omega

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem continuous_psiAt (ψ : AddChar (AF F) ℂ) (v : Pl (F := F)) (h : PsiUnr ψ v) : Continuous (psiAt ψ v) := by
  have hker : ∀ y ∈ v.adicCompletionIntegers F, psiAt ψ v y = 1 := fun y hy => by
    have := (h 1).2 (one_mem _) y hy
    rwa [one_mul] at this
  have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  refine IsLocallyConstant.continuous ?_
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  rw [← map_add_left_nhds_zero, Filter.eventually_map]
  filter_upwards [hO.mem_nhds (zero_mem _)] with s hs
  rw [AddChar.map_add_eq_mul, hker s hs, mul_one]

theorem psiAt_ne_one (ψ : AddChar (AF F) ℂ) (v : Pl (F := F)) (h : PsiUnr ψ v) : psiAt ψ v ≠ 1 := by
  intro h1
  have hall : ∀ x : Fv F v, x ∈ v.adicCompletionIntegers F := fun x => (h x).1 fun y _ => by
    rw [← psiAt_apply, h1]; rfl
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have h2 := hall (algebraMap F (Fv F v) π⁻¹)
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h2
  erw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h2
  rw [map_inv₀, map_inv₀, Algebra.algebraMap_self_apply, hπ, ← WithZero.exp_neg, ← WithZero.exp_zero, WithZero.exp_le_exp] at h2
  omega

theorem liftV_one_smul {M : Type} [AddCommGroup M] [Module (AF F) M] (v : Pl (F := F)) (u : M) (hu : At (evFin F v) u) :
    liftV v (1 : Fv F v) • u = u := by
  have h := hu (1 - liftV v 1) (by rw [map_sub, map_one, evFin_liftV, sub_self])
  rw [sub_smul, one_smul] at h
  exact (sub_eq_zero.1 h).symm

theorem liftV_one_mul (v : Pl (F := F)) (x : AF F) : liftV v (1 : Fv F v) * x = liftV v (evFin F v x) := by
  have h := at_liftV v (1 : Fv F v) (x - liftV v (evFin F v x)) (by rw [map_sub, evFin_liftV, sub_self])
  have h2 := liftV_one_smul v _ (at_liftV v (evFin F v x))
  rw [smul_eq_mul] at h h2
  linear_combination h + h2

theorem liftV_one_smul_eq_zero (v : Pl (F := F)) (a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (ha : compFin F E v a = 0) : liftV v (1 : Fv F v) • a = 0 := by
  have key : ∀ a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), liftV v (1 : Fv F v) • a = (liftV v).rTensor E (compFin F E v a) := by
    intro a
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul x e =>
      rw [TensorProduct.smul_tmul', smul_eq_mul, liftV_one_mul]
      simp [compFin]
    | add x y hx hy => rw [smul_add, hx, hy, map_add (f := _), map_add (f := _)]
  rw [key, ha, map_zero]

theorem exists_map_compFin (v : Pl (F := F)) {α β : Type} (A : Matrix α β (Fv F v ⊗[F] E)) :
    ∃ C : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), C.map (compFin F E v) = A := by
  refine ⟨A.map ((liftV v).rTensor E), ?_⟩
  ext i j
  simp only [Matrix.map_apply]
  induction A i j using TensorProduct.induction_on with
  | zero => simp
  | tmul x e => simp [compFin, evFin_liftV]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem mul_eq_self {n d : ℕ} (v : Pl (F := F)) (u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (hu : At (evFin F v) u)
    (N : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (hN : N.map (compFin F E v) = 1) : u * N = u := by
  have h0 : liftV v (1 : Fv F v) • (N - 1) = 0 := by
    ext i j
    refine liftV_one_smul_eq_zero v _ ?_
    have := congrFun (congrFun hN i) j
    rw [Matrix.map_apply] at this
    rw [Matrix.sub_apply, map_sub, this]
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  have h1 : u * (N - 1) = 0 := by
    rw [← liftV_one_smul v u hu, Matrix.smul_mul, ← Matrix.mul_smul, h0, Matrix.mul_zero]
  rwa [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h1

theorem at_mul {α β γ : Type} [Fintype β] (v : Pl (F := F)) (u : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (hu : At (evFin F v) u)
    (A : Matrix β γ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : At (evFin F v) (u * A) := fun t ht => by
  rw [← Matrix.smul_mul, hu t ht, Matrix.zero_mul]

theorem exists_compl (σ : E →ₐ[F] E) {d m : ℕ} (W : Spc F E d) (v : Pl (F := F)) (C : Matrix (Fin d) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (hC : IsLagrAt σ W v C) (n : ℕ) : ∃ C' : Matrix (Fin d) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), IsLagrAt σ W v C' ∧
      ∀ u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) u → ∃ x ∈ lagAt v C, ∃ y ∈ lagAt v C', u = x + y := by
  obtain ⟨h0, Cx, M, hx, h1, h2⟩ := hC
  obtain ⟨C', hC'⟩ := exists_map_compFin v Cx
  obtain ⟨M₁, hM₁⟩ := exists_map_compFin v M.toRows₁
  obtain ⟨M₂, hM₂⟩ := exists_map_compFin v M.toRows₂
  rw [← Matrix.fromRows_toRows M] at h1 h2
  rw [Matrix.fromCols_mul_fromRows] at h1
  rw [Matrix.fromRows_mul_fromCols, ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj] at h2
  refine ⟨C', ⟨by rw [hC']; exact hx, _, Matrix.fromRows M.toRows₂ M.toRows₁, h0, ?_, ?_⟩, fun u hu => ?_⟩
  · rw [hC', Matrix.fromCols_mul_fromRows, add_comm, h1]
  · rw [hC', Matrix.fromRows_mul_fromCols, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2, Matrix.fromBlocks_one]
  · have hN : ((C * M₁ + C' * M₂)ᵀ).map (compFin F E v) = 1 := by
      rw [Matrix.transpose_map, Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul, hC', hM₁, hM₂, h1,
        Matrix.transpose_one]
    refine ⟨u * M₁ᵀ * Cᵀ, ⟨at_mul v _ (at_mul v u hu _) _, _, rfl⟩, u * M₂ᵀ * C'ᵀ,
      ⟨at_mul v _ (at_mul v u hu _) _, _, rfl⟩, ?_⟩
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_add, ← Matrix.transpose_mul, ← Matrix.transpose_mul,
      ← Matrix.transpose_add, mul_eq_self v u hu _ hN]

theorem exists_at_locCo {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} {κ : Type} [Fintype κ] (co : Darboux B κ) (v : Pl (F := F)) (p : (κ → Fv F v) × (κ → Fv F v)) :
    ∃ u : W, At (evFin F v) u ∧ locCo co v u = p := by
  refine ⟨co.e.symm (fun k => liftV v (p.1 k), fun k => liftV v (p.2 k)), ?_, ?_⟩
  · intro r hr
    rw [← LinearEquiv.map_smul]
    have h0 : r • ((fun k => liftV v (p.1 k), fun k => liftV v (p.2 k)) : (κ → AF F) × (κ → AF F)) = 0 :=
      Prod.ext (funext fun k => at_liftV v (p.1 k) r hr) (funext fun k => at_liftV v (p.2 k) r hr)
    rw [h0, map_zero]
  · show ((fun k => evFin F v ((co.e _).1 k)), fun k => evFin F v ((co.e _).2 k)) = p
    rw [LinearEquiv.apply_symm_apply]
    exact Prod.ext (funext fun k => evFin_liftV v _) (funext fun k => evFin_liftV v _)

variable {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

def lagCo (M : Model σ X W) (v : Pl (F := F)) {m : ℕ} (C : Matrix (Fin d) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    Submodule (Fv F v) ((Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) where
  carrier := locCo M.co v '' lagAt v C
  zero_mem' := ⟨0, ⟨fun u _ => smul_zero u, 0, by simp⟩, map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨_, ⟨hx, z, rfl⟩, rfl⟩ ⟨_, ⟨hy, z', rfl⟩, rfl⟩
    exact ⟨_, ⟨fun u hu => by rw [smul_add, hx u hu, hy u hu, add_zero], z + z', by rw [Matrix.add_mul]⟩, map_add _ _ _⟩
  smul_mem' := by
    rintro a _ ⟨_, ⟨hx, z, rfl⟩, rfl⟩
    refine ⟨liftV v a • (z * Cᵀ), ⟨fun u hu => by rw [smul_comm, hx u hu, smul_zero], liftV v a • z,
      by rw [Matrix.smul_mul]⟩, ?_⟩
    ext k <;> simp [locCo, evFin_liftV, -Matrix.smul_mul]

theorem lagCo_isotropic (M : Model σ X W) (v : Pl (F := F)) {m : ℕ} (C : Matrix (Fin d) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (hC : IsLagrAt σ W v C) : ∀ a ∈ lagCo M v C, ∀ b ∈ lagCo M v C, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2 := by
  rintro _ ⟨u, hu, rfl⟩ _ ⟨u', hu', rfl⟩
  have h0 := GlobalTheory.T.symplecticForm_eq_zero_of_lagrangianAtPlace σ X.J W v C hC (-1) u u' hu hu'
  change symp (cA σ) (-1) (incM F X.J) (incM F W.J) u u' = 0 at h0
  rw [M.co.form] at h0
  have h1 := congrArg (evFin F v) h0
  rw [← sub_eq_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    simpa [locCo, dotProduct, map_sum, map_mul, map_sub] using h1

theorem finrank_lagCo (M : Model σ X W) (v : Pl (F := F)) {m : ℕ} (C : Matrix (Fin d) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (hC : IsLagrAt σ W v C) : Module.finrank (Fv F v) (lagCo M v C) = Fintype.card (Fin n × Fin d) := by
  obtain ⟨C', hC', hdec⟩ := exists_compl σ W v C hC n
  refine finrank_eq_of_isotropic _ (lagCo M v C') (lagCo_isotropic M v C hC) (lagCo_isotropic M v C' hC') ?_
  rw [eq_top_iff]
  intro p _
  obtain ⟨u, hu, rfl⟩ := exists_at_locCo M.co v p
  obtain ⟨x, hx, y, hy, rfl⟩ := hdec u hu
  rw [map_add (f := _)]
  exact Submodule.add_mem_sup ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩

theorem exists_test : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (v : Pl (F := F)), PsiUnr ψ v →
    ∀ (m : ℕ) (C : Matrix (Fin d) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), GlobalTheory.InertVacLag.IsLagrAt σ W v C →
    ∃ φ₀ ∈ SB (Fin n × Fin d → Fv F v), ∀ l : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] ℂ,
      GlobalTheory.InertVacLag.HeisInv M ψ v C l → l φ₀ = 0 → ∀ φ ∈ SB (Fin n × Fin d → Fv F v), l φ = 0 := by
  intro F E _ _ _ _ _ σ n d X W M ψ v hψ m C hC
  have hc := continuous_psiAt ψ v hψ
  have hinv : ∀ l, HeisInv M ψ v C l → ∀ w ∈ lagCo M v C, ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      l (schr (psiAt ψ v) w φ) = l φ := by
    rintro l hl _ ⟨u, hu, rfl⟩ φ hφ
    exact hl u hu φ hφ _ (GlobalTheory.SchrSBFin.schr_mem_SB v _ hc _ φ hφ) (GlobalTheory.VacBridge.rho_acts_locCo M.co ψ v u hu.1 φ)
  by_cases hex : ∃ l₂, HeisInv M ψ v C l₂ ∧ ∃ φ ∈ SB (Fin n × Fin d → Fv F v), l₂ φ ≠ 0
  · obtain ⟨l₂, hl₂, φ₀, hφ₀, hne⟩ := hex
    refine ⟨φ₀, hφ₀, fun l hl h0 φ hφ => ?_⟩
    obtain ⟨c, hcl⟩ := GlobalTheory.T.lagrangian_invariant_forms_proportional_finitePlace F v (psiAt ψ v) hc (psiAt_ne_one ψ v hψ) _ (lagCo M v C) (lagCo_isotropic M v C hC)
      (finrank_lagCo M v C hC) l l₂ (hinv l hl) (hinv l₂ hl₂) ⟨φ₀, hφ₀, hne⟩
    have hc0 : c = 0 := (mul_eq_zero.1 ((hcl φ₀ hφ₀).symm.trans h0)).resolve_right hne
    rw [hcl φ hφ, hc0, zero_mul]
  · refine ⟨0, zero_mem _, fun l hl _ φ hφ => ?_⟩
    by_contra hne
    exact hex ⟨l, hl, φ, hφ, hne⟩

end GlobalTheory.InertLagUniq

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlipAtEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.SquareFlipReach

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def rowE (t : T) (w : Pl D.host.E) (i j : Fin D.R.m) :
    Fin ((locGrid G t w).rank (i + 1, j + 1)) ≃ Fin (spW G i j).rank :=
  finCongr (rank_vertex G t w (X := ((i : ℕ) + 1, (j : ℕ) + 1)) ⟨i.2, j.2⟩)

def colE (t : T) (w : Pl D.host.E) {i j : Fin D.R.m} (e : Num G i j) :
    (locGrid G t w).Cols i j ≃ Fin ((spW G i j).rank + (spW₁ G i j).rank) :=
  (Equiv.sumCongr (finCongr (rank_vertex G t w (X := ((i : ℕ), (j : ℕ) + 1)) ⟨i.2.le, j.2⟩))
    (finCongr (rank_vertex G t w (X := ((i : ℕ) + 1, (j : ℕ))) ⟨i.2, j.2.le⟩))).trans e

def trA (t : T) {w : Pl D.host.E} {v : Pl D.host.F} (hv : w.under (𝓞 D.host.F) = v) {i j : Fin D.R.m} (e : Num G i j)
    (Z : Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Fv D.host.F v)) :
    Matrix (Fin ((locGrid G t w).rank (i + 1, j + 1))) ((locGrid G t w).Cols i j) (Kw w) :=
  Matrix.of fun r c => GlobalTheory.LFun.complMap hv (Z (rowE t w i j r) (colE t w e c))

def sqCore (W : G.Weil) (t : T) (i j : ℕ) (w : Pl D.host.E) (n : ℕ)
    (Φ : Matrix (Fin ((locGrid G t w).rank (i, j))) ((locGrid G t w).Cols i j) (Kw w) → ℂ) :
    Matrix (Fin ((locGrid G t w).rank (i + 1, j + 1))) ((locGrid G t w).Cols i j) (Kw w) → ℂ :=
  phiA (haarVol ((givenLevel G t w (i, j)).map invT)) (stdSplit ((locGrid G t w).rank_square i j)) ((locGrid G t w).nu i j)
    (unifAt w) n (blockLat (unifAt w) n (Assignment.one.block _ _))
    (fourierSum (psiAt W w) (unifAt w) n (Assignment.one.block _ _) Φ)

theorem flipAt_eq (W : G.Weil) (t : T) (i j : ℕ) (w : Pl D.host.E) (n : ℕ)
    (Φ : Matrix (Fin ((locGrid G t w).rank (i, j))) ((locGrid G t w).Cols i j) (Kw w) → ℂ) :
    flipAt W t i j w n Φ = invFourierSum (psiAt W w)⁻¹ (unifAt w) n (Assignment.one.block _ _)ᶜ (sqCore W t i j w n Φ) := rfl

end GlobalTheory.SquareFlipReach

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyLocalCompactSmall
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.IdTorus GlobalTheory.GLTwoHecke
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut (IsMaxCpt)
open GlobalTheory.StdPar

namespace GlobalTheory.GLTwoHecke

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem isOpen_adicCompletionIntegers_loc (w : HeightOneSpectrum (𝓞 E)) :
    IsOpen (w.adicCompletionIntegers E : Set (w.adicCompletion E)) := by
  have h : (w.adicCompletionIntegers E : Set (w.adicCompletion E)) =
      ((Valued.v : Valuation (w.adicCompletion E) _).integer : Set (w.adicCompletion E)) := by
    ext x
    simp only [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.mem_integer_iff]
  rw [h]
  exact Valued.isOpen_integer _

theorem eventually_singleNU_mem {N : Set (FiniteAdeleRing (𝓞 E) E)} (hN : N ∈ 𝓝 0) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∀ y ∈ w.adicCompletionIntegers E, singleNU w y ∈ N := by
  classical
  let s : (∀ w : HeightOneSpectrum (𝓞 E), w.adicCompletionIntegers E) → FiniteAdeleRing (𝓞 E) E :=
    RestrictedProduct.structureMap (fun w : HeightOneSpectrum (𝓞 E) => w.adicCompletion E)
      (fun w => (w.adicCompletionIntegers E : Set (w.adicCompletion E))) cofinite
  have hs : Continuous s :=
    (RestrictedProduct.isOpenEmbedding_structureMap isOpen_adicCompletionIntegers_loc).continuous
  have hs0 : s 0 = 0 := rfl
  have h1 : s ⁻¹' N ∈ 𝓝 (0 : ∀ w : HeightOneSpectrum (𝓞 E), w.adicCompletionIntegers E) :=
    hs.continuousAt.preimage_mem_nhds (by rw [hs0]; exact hN)
  rw [nhds_pi, Filter.mem_pi'] at h1
  obtain ⟨I, t, ht, hIt⟩ := h1
  refine Filter.mem_of_superset I.finite_toSet.compl_mem_cofinite fun w hw y hy => ?_
  have hx : s (Pi.single w ⟨y, hy⟩) = singleNU w y := by
    refine Subtype.ext (funext fun u => ?_)
    change ((Pi.single w (⟨y, hy⟩ : w.adicCompletionIntegers E) : ∀ w : HeightOneSpectrum (𝓞 E), w.adicCompletionIntegers E) u : u.adicCompletion E) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV E u (GlobalTheory.AdelicU.singleFin w y)
    by_cases h : u = w
    · subst h
      rw [GlobalTheory.AdelicU.evalV_singleFin_self, Pi.single_eq_same]
    · rw [GlobalTheory.AdelicU.evalV_singleFin_ne h, Pi.single_eq_of_ne h]
      rfl
  rw [← hx]
  refine hIt fun u hu => ?_
  have hne : u ≠ w := fun e => hw (e ▸ hu : w ∈ (I : Set _))
  rw [Pi.single_eq_of_ne hne]
  exact mem_of_mem_nhds (ht u)

end GlobalTheory.GLTwoHecke
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewPlaneModularCharacter
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB

noncomputable section

namespace GlobalTheory.LeviSplit

open Matrix

section Ring

variable {R : Type} [CommRing R] {n n₁ k : ℕ}

end Ring

theorem exists_prod_equiv {G B : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group B] [TopologicalSpace B]
    (A T : Subgroup G) (m : B → A) (π : A → B) (hm : Continuous m) (hπ : Continuous π) (hmm : ∀ a b, m (a * b) = m a * m b)
    (hππ : ∀ a b, π (a * b) = π a * π b) (hπm : ∀ b, π (m b) = b) (hTA : T ≤ A) (hT : ∀ a : A, a.1 ∈ T ↔ π a = 1)
    (hc : ∀ τ ∈ T, ∀ b, τ * (m b : G) = m b * τ) : ∃ φ : T × B ≃ₜ* A, ∀ p, (φ p : G) = p.1 * m p.2 := by
  let π' := MonoidHom.mk' π hππ
  have h1 : ∀ τ : T, π' ⟨τ, hTA τ.2⟩ = 1 := fun τ => (hT ⟨τ, hTA τ.2⟩).1 τ.2
  have h2 : ∀ b, π' (m b) = b := hπm
  have h3 : ∀ (τ : T) b, π' (⟨τ, hTA τ.2⟩ * m b) = b := fun τ b => by rw [map_mul, h1, h2, one_mul]
  refine ⟨{ toFun := fun p => ⟨p.1, hTA p.1.2⟩ * m p.2
            invFun := fun a => (⟨(a * (m (π' a))⁻¹ : A), (hT _).2 (show π' _ = 1 by rw [map_mul, map_inv, h2, mul_inv_cancel])⟩, π' a)
            left_inv := fun p => Prod.ext (Subtype.ext ?_) (h3 _ _)
            right_inv := fun a => Subtype.ext ?_
            map_mul' := fun p q => Subtype.ext ?_
            continuous_toFun := ?_
            continuous_invFun := ?_ }, fun p => rfl⟩
  · simp only [h3]
    simp
  · simp
  · simp only [Prod.fst_mul, Prod.snd_mul, hmm, Subgroup.coe_mul]
    rw [mul_assoc, mul_assoc, ← mul_assoc (q.1 : G), hc _ q.1.2, mul_assoc]
  · exact ((continuous_subtype_val.comp continuous_fst).subtype_mk _).mul (hm.comp continuous_snd)
  · exact ((continuous_subtype_val.comp (continuous_id.mul (hm.comp hπ).inv)).subtype_mk _).prodMk hπ

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}





open GlobalTheory.StdPar GlobalTheory.SiegelSet in
theorem mem_leviOne {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E} {S : Finset (Fin r)}
    {g : GAd σ J} : g ∈ leviOne σ J X Y S ↔ ∀ k ∈ S,
      g ∈ frameStab σ J (initCols X k) ((⊤ : Subgroup (AE F E)ˣ).comap Matrix.GeneralLinearGroup.det) ∧
      g ∈ frameStab σ J (initCols Y k) ((⊤ : Subgroup (AE F E)ˣ).comap Matrix.GeneralLinearGroup.det) ∧
      g ∈ frameStab σ J (initCols X k) ((GlobalTheory.Doubling.absE F E).ker.comap Matrix.GeneralLinearGroup.det) := by
  simp only [leviOne, levi, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.comap_top, MonoidHom.comap_ker]
  exact ⟨fun h k hk => ⟨(h.1 k hk).1, (h.1 k hk).2, h.2 k hk⟩, fun h => ⟨fun k hk => ⟨(h k hk).1, (h k hk).2.1⟩,
    fun k hk => (h k hk).2.2⟩⟩


end GlobalTheory.LeviSplit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyNrmLTwConj
open NumberField IsDedekindDomain Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open scoped Classical TensorProduct
open GlobalTheory.BCT

noncomputable section

namespace GlobalTheory.BCT.StTw2Add

section Generic

variable {G : Type} [Group G]

theorem twRel_equiv (θ : G →* G) : Equivalence fun x y : G => ∃ g, y = g⁻¹ * x * θ g := by
  refine ⟨fun x => ⟨1, by simp⟩, ?_, ?_⟩
  · rintro x y ⟨g, rfl⟩
    exact ⟨g⁻¹, by simp only [map_inv, inv_inv]; group⟩
  · rintro x y z ⟨g, rfl⟩ ⟨h, rfl⟩
    exact ⟨g * h, by simp only [map_mul, mul_inv_rev]; group⟩

theorem twCl_eq_iff (θ : G →* G) (x y : G) :
    (Quot.mk _ x : TwCl θ) = Quot.mk _ y ↔ ∃ g, y = g⁻¹ * x * θ g :=
  ⟨fun h => (twRel_equiv θ).eqvGen_iff.1 (Quot.eqvGen_exact h), fun h => Quot.sound h⟩

theorem mk_rep (θ : G →* G) (c : TwCl θ) : (Quot.mk _ c.rep : TwCl θ) = c := Quot.out_eq c

theorem rep_mk_iff (θ : G →* G) (P : G → Prop) (hP : ∀ x g, P (g⁻¹ * x * θ g) ↔ P x) (x : G) :
    P (TwCl.rep (θ := θ) (Quot.mk _ x)) ↔ P x := by
  obtain ⟨g, hg⟩ := (twCl_eq_iff θ _ _).1 (mk_rep θ (Quot.mk _ x : TwCl θ))
  have h := hP (TwCl.rep (θ := θ) (Quot.mk _ x)) g
  rw [← hg] at h
  exact h.symm

variable [TopologicalSpace G]

variable {G₁ G₂ : Type} [Group G₁] [Group G₂]

theorem finite_prod (θ₁ : G₁ →* G₁) (θ₂ : G₂ →* G₂) (P₁ : G₁ → Prop) (P₂ : G₂ → Prop)
    (h₁ : ∀ x g, P₁ (g⁻¹ * x * θ₁ g) ↔ P₁ x) (h₂ : ∀ x g, P₂ (g⁻¹ * x * θ₂ g) ↔ P₂ x)
    (f₁ : {c : TwCl θ₁ | P₁ c.rep}.Finite) (f₂ : {c : TwCl θ₂ | P₂ c.rep}.Finite) :
    {c : TwCl (θ₁.prodMap θ₂) | P₁ c.rep.1 ∧ P₂ c.rep.2}.Finite := by
  refine Set.Finite.of_finite_image (f := fun c : TwCl (θ₁.prodMap θ₂) =>
    ((Quot.mk _ c.rep.1 : TwCl θ₁), (Quot.mk _ c.rep.2 : TwCl θ₂))) ((f₁.prod f₂).subset ?_) ?_
  · rintro _ ⟨c, hc, rfl⟩
    exact ⟨(rep_mk_iff θ₁ P₁ h₁ _).2 hc.1, (rep_mk_iff θ₂ P₂ h₂ _).2 hc.2⟩
  · intro c _ d _ hcd
    obtain ⟨g₁, hg₁⟩ := (twCl_eq_iff θ₁ _ _).1 (congrArg Prod.fst hcd)
    obtain ⟨g₂, hg₂⟩ := (twCl_eq_iff θ₂ _ _).1 (congrArg Prod.snd hcd)
    rw [← mk_rep _ c, ← mk_rep _ d]
    exact Quot.sound ⟨(g₁, g₂), Prod.ext hg₁ hg₂⟩

end Generic

section Local

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isOpen_isCompact_KK (a b : ℕ) (w : Pl E) :
    IsOpen (((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b)) : Subgroup (GLw a w × GLw b w)) : Set (GLw a w × GLw b w)) ∧
    IsCompact (((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b)) : Subgroup (GLw a w × GLw b w)) : Set (GLw a w × GLw b w)) := by
  rw [Subgroup.coe_prod]
  exact ⟨(GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).1.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).1,
    (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).2⟩

end Local

end GlobalTheory.BCT.StTw2Add
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalArchimedeanSchwartzFockOperator
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalArchimedeanSchwartzFockOperator
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

noncomputable section
namespace GlobalTheory.FockKFinStep
open GlobalTheory.ThK.EvAt0.PolD LineDeriv

theorem lin_expand {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ι : Type} [Fintype ι]
    (B : Module.Basis ι ℝ (κ → mixedEmbedding.mixedSpace F)) (b x : κ → mixedEmbedding.mixedSpace F) :
    lin b x = ∑ j, (B.repr b j : ℂ) * lin (B j) x := by
  conv_lhs => rw [← B.sum_repr b]
  simp only [lin, Finset.sum_apply, Pi.smul_apply, Finset.mul_sum, mul_smul_comm]
  rw [Finset.sum_comm]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, map_smul, Finset.mul_sum]

theorem fderiv_expand {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ι : Type} [Fintype ι]
    (B : Module.Basis ι ℝ (κ → mixedEmbedding.mixedSpace F)) (a : κ → mixedEmbedding.mixedSpace F) (f : SInf F κ) (x) :
    fderiv ℝ f x a = ∑ j, (B.repr a j : ℂ) * fderiv ℝ f x (B j) := by
  conv_lhs => rw [← B.sum_repr a]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [map_smul, Complex.real_smul]

theorem sumAt {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ι : Type} (s : Finset ι) (g : ι → SInf F κ) (x) :
    (∑ j ∈ s, g j) x = ∑ j ∈ s, g j x := by simp

theorem dOp_expand {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ι : Type} [Fintype ι]
    (B : Module.Basis ι ℝ (κ → mixedEmbedding.mixedSpace F)) (a b : κ → mixedEmbedding.mixedSpace F) (f : SInf F κ) :
    dOp a b f = ∑ j, (B.repr a j : ℂ) • ∂_{B j} f -
      (2 * Real.pi * Complex.I : ℂ) • ∑ j, (B.repr b j : ℂ) • mulOp (B j) f := by
  refine DFunLike.ext _ _ fun x => ?_
  rw [dOp_apply, fderiv_expand B a f x, lin_expand B b x]
  simp only [SchwartzMap.sub_apply, SchwartzMap.smul_apply, sumAt, smul_eq_mul,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, mulOp_apply, Finset.mul_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => by ring

theorem dStep_finiteDimensional : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (P : Submodule ℂ (SInf F κ)),
    FiniteDimensional ℂ P → FiniteDimensional ℂ (GlobalTheory.FockKFin.dStep P) := by
  intro F _ _ κ _ P hP
  let B := Module.finBasis ℝ (κ → mixedEmbedding.mixedSpace F)
  let T : Submodule ℂ (SInf F κ) :=
    (⨆ j, P.map (lineDerivOpCLM ℂ (SInf F κ) (B j)).toLinearMap) ⊔ ⨆ j, P.map (mulOp (B j)).toLinearMap
  haveI : FiniteDimensional ℂ T := by
    haveI := Submodule.finiteDimensional_iSup (fun j => P.map (lineDerivOpCLM ℂ (SInf F κ) (B j)).toLinearMap)
    haveI := Submodule.finiteDimensional_iSup (fun j => P.map (mulOp (B j)).toLinearMap)
    exact Submodule.finiteDimensional_sup _ _
  refine Submodule.finiteDimensional_of_le (S₂ := T) ?_
  rw [GlobalTheory.FockKFin.dStep, Submodule.span_le]
  rintro _ ⟨a, b, f, hf, rfl⟩
  rw [dOp_expand B]
  refine Submodule.sub_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
  · exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.mem_iSup_of_mem j ⟨f, hf, rfl⟩)
  · exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.mem_iSup_of_mem (p := fun j => P.map (mulOp (B j)).toLinearMap) j ⟨f, hf, rfl⟩))

end GlobalTheory.FockKFinStep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalArchimedeanSchwartzFockOperatorStatement
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_archimedeanSchwartzFockOperatorSpan : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (P : Submodule ℂ (SInf F κ)),
    FiniteDimensional ℂ P → FiniteDimensional ℂ (GlobalTheory.FockKFin.dStep P) := by
  first | exact @GlobalTheory.FockKFinStep.dStep_finiteDimensional | exact GlobalTheory.FockKFinStep.dStep_finiteDimensional | (intros; apply GlobalTheory.FockKFinStep.dStep_finiteDimensional <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerExtension
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.EvNeZero

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem pure_ne_zero {κ : Type} [Fintype κ] (g : SInf F κ) (hg : g ≠ 0) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ)
    (h0 : ∀ v, φ v ≠ 0)
    (hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ ≠ 0 := by
  classical
  obtain ⟨a, ha⟩ : ∃ a, g a ≠ 0 := by
    by_contra! h
    exact hg (SchwartzMap.ext h)
  have hfin : {v | ¬ φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1}.Finite := hstd
  set T := hfin.toFinset with hT
  have hy : ∀ v, ∃ y : κ → Fv F v, φ v y ≠ 0 := fun v => by
    by_contra! h
    exact h0 v (funext h)
  choose y hy using hy
  let xf : κ → Af F := fun i => ⟨fun v => if v ∈ T then y v i else 0, by
    filter_upwards [T.eventually_cofinite_notMem] with v hv
    simp only [if_neg hv]
    exact zero_mem _⟩
  let x : κ → AF F := fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (a i), xf i)
  intro hz
  have hx := congrFun hz x
  have e1 : (fun i => evI F (x i)) = a := funext fun i => by
    change InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (a i)) = a i
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (a i)
  have e2 : ∀ v, (fun i => evFin F v (x i)) = fun i => if v ∈ T then y v i else 0 := fun v => funext fun i => rfl
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.zero_apply, e1, e2] at hx
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := T) ?_] at hx
  · rcases mul_eq_zero.1 hx with h | h
    · exact ha h
    · obtain ⟨v, hv, h⟩ := Finset.prod_eq_zero_iff.1 h
      simp only [hv, if_true] at h
      exact hy v h
  · intro v hv
    by_contra hvT
    apply hv
    have hφ : φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
      by_contra hc
      exact hvT (hfin.mem_toFinset.2 hc)
    have hvT' : v ∉ T := hvT
    simp only [hvT', if_false, hφ]
    rw [Set.indicator_of_mem (s := {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F}) (a := fun _ => 0)
      (fun i => zero_mem _)]
    rfl

theorem exists_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ)
    (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X₁ W₁)
    (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E) (I : Set (Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))))
    (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁), M.IsGood B.ψ → M₁.IsGood B.ψ → IsEv B M M₁ ι ι' I e →
      ∃ Φ ∈ schA F (Fin n × Fin d), e Φ ≠ 0 := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ ι ι' I e hM hM₁ he
  obtain ⟨ei, ev, hei, hev, hpure⟩ := he.loc
  obtain ⟨f, hf⟩ : ∃ f, ei f ≠ 0 := by
    by_contra! h
    exact hei (ContinuousLinearMap.ext h)
  have hfam : GlobalTheory.BigNZ.Fam M M.vac := ⟨fun v => (hM.vac v).1, Filter.Eventually.of_forall fun _ => rfl⟩
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac, hfam.mem hM f, ?_⟩
  rw [hpure f M.vac hfam.1 hfam.2]
  have hv : (fun v => ev v (M.vac v)) = M₁.vac := funext fun v => (hev v).1
  rw [hv]
  exact pure_ne_zero (ei f) hf M₁.vac (fun v => (hM₁.vac v).2.1) hM₁.std

end GlobalTheory.ThK.EvNeZero
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KroneckerCharacterFrameSecond
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.LamMuMax

theorem slopeMax_le : GlobalTheory.UCls.MassBound → GlobalTheory.UCls.TorusBound → ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → GoodW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) → latW U (wtZ a n) ≠ ⊥ → slopeMax_sq (normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n)) (latW U (wtZ a n)) ≤ 2 * lamSup D.host.E D.R.r Dw.q D.host.d l.M (GlobalTheory.CM.logOm D.host.E χ).re ((absA Dw a : ℕ) : ℝ) ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) + 2 * Real.log (supConst D.host.E D.R.r D.host.d l.M (((absA Dw a : ℕ) : ℝ) + ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) + 1)) + Real.log |(discr c.F : ℝ)| / (Module.finrank ℚ c.F : ℝ) := by
  intro hMass hTor D j H Dw l Xo c U dict hL _ χ hχ a n hD hG h0
  have hTC : IsTotallyComplex c.F := ⟨fun v => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    exact fun e => GlobalTheory.CompHt.conj_comp_ne (c := c) v.embedding (RingHom.ext fun a => RingHom.congr_fun e a)⟩
  have hj : ∀ (σ : c.F →+* ℂ) (f : cuspW Xo c U (wtZ a n)),
      normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) ((starRingEnd ℂ).comp σ) f =
        normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) σ f := fun σ f => by
    rw [normW, normW, petW, petW, GlobalTheory.CompHt.goodOf_conj σ]
  have hP := GlobalTheory.T.kronecker_character_frame_first hMass hTor D j H Dw l Xo c U dict hL χ hχ a n hD
  have hR := GlobalTheory.LevGeo.RankBd.finrank_cuspW_le hMass hTor D j H Dw l Xo c U dict hL a n hD
  have hS := GlobalTheory.T.maxSlope_sq_le_of_no_short_vector c.F (cuspW Xo c U (wtZ a n)) (normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n))
    (latW U (wtZ a n)) _ hG.1 hj hG.2.1 h0 (fun F hF hF0 => (hP F hF hF0).2)
  haveI := hR.1
  obtain ⟨F, hF, hF0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  haveI : Nontrivial (cuspW Xo c U (wtZ a n)) := ⟨⟨F, 0, hF0⟩⟩
  have hpos : (0 : ℝ) < (Module.finrank c.F (cuspW Xo c U (wtZ a n)) : ℝ) := by
    exact_mod_cast Module.finrank_pos
  have hlog := Real.log_le_log hpos hR.2
  refine hS.trans ?_
  rw [lamPet]
  linarith

end GlobalTheory.LamMuMax
end

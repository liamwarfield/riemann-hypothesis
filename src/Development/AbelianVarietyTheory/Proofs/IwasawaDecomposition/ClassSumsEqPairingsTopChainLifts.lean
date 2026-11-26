module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnfoldingSchurOrthogonalityDefiniteCoefficients
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowLevelFormsSpanDefiniteMultiplicitySpace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CasselmanWallachExtensionBanachTarget
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemRangeSrcForm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanLiftFormsBaseLevelEqHilbertImage
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseLevelAdelicTypeImpliesLiftLaw
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseLevelAdelicTypeImpliesLiftLaw
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.LevToQ
end GlobalTheory.LevToQ

namespace GlobalTheory.LevToQ
theorem units_map_inv_val {K : Type} [Field K] (σ : K →+* ℂ) (u : Kˣ) :
    (((Units.map σ.toMonoidHom u)⁻¹ : ℂˣ) : ℂ) = σ ((u⁻¹ : Kˣ) : K) := by
  simp
end GlobalTheory.LevToQ


set_option maxHeartbeats 800000 in
theorem GlobalTheory.LevToQ.levtoq : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.models_cV → R.grp_red_L → ∀ (i : Fin D.R.m) (t : T) (Φ : Bridge.Gf (Vc D i) → (R.cV i).W), (R.cV i).ext Φ ∈ levSubV (Vc D i) (R.cV i).W (levS _ (R.βV i) (datVP R i t (R.levR F false))) (levChi _ (R.βV i) (datVP R i t (R.levR F false))) → ∀ (κ : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q) (hu : (R.B.L i t).act_tie.red κ ∈ F.P0) (h : Bridge.Gf (Vc D i)), Φ (h * κ) = (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch κ : ℂˣ) : ℂ) • D.what₂.embLL ((F.ψ0⁻¹ ⟨_, hu⟩ : D.what₂.LLˣ) : D.what₂.LL) • Φ h := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hcV hred i t Φ hΦ κ hu h
  have hl := GlobalTheory.DefiniteMult.exists_fin_lift (Vc D i) (κ : Bridge.Gf (Vc D i))
  obtain ⟨k, hkG, hk⟩ := hl
  have hl' := GlobalTheory.DefiniteMult.exists_fin_lift (Vc D i) h
  obtain ⟨g, hgG, hg⟩ := hl'
  have hfk : finE (Vc D i) k = Formalism.UG.bc (swapAE D) (((κ : Bridge.Gf (Vc D i)) : GL _ _)) := by
    rw [finE_eq, ← hk]
    rfl
  have hκQ := κ.2
  have hpar : finE (Vc D i) k ∈ Formalism.L2.DIV.parLev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t) := by
    rw [hfk]; exact hκQ.1
  have hrt : Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) k) = R.eG ((R.B.L i t).act_tie.red κ) := by
    exact (congrArg (Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t)) hfk).trans (hred i t κ).symm
  have hmem : Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) k) ∈ (R.levR F false).conj.H := by
    rw [hrt]
    show R.eG.symm (R.eG ((R.B.L i t).act_tie.red κ)) ∈ F.P0
    simpa using hu
  have hkS : k ∈ levS (Vc D i) (R.βV i) (datVP R i t (R.levR F false)) :=
    ⟨hkG, hpar, hmem⟩
  have hlaw := hΦ k hkS g
  have e1 : (R.cV i).ext Φ (g * k) = Φ (h * κ) := by
    show (R.cV i).ρ (g * k)⁻¹ (Φ ((finHom (Vc D i)).rangeRestrict (g * k))) = _
    have hrr : (finHom (Vc D i)).rangeRestrict (g * k) = h * (κ : Bridge.Gf (Vc D i)) := by
      rw [map_mul, hg]
      exact congrArg (h * ·) hk
    exact (LinearMap.congr_fun ((hcV i).1 _ ((GfC _).inv_mem ((GfC _).mul_mem hgG hkG))) _).trans
      ((Module.End.one_apply _).trans (congrArg Φ hrr))
  have e2 : (R.cV i).ext Φ g = Φ h := by
    show (R.cV i).ρ g⁻¹ (Φ ((finHom (Vc D i)).rangeRestrict g)) = _
    exact (LinearMap.congr_fun ((hcV i).1 _ ((GfC _).inv_mem hgG)) _).trans
      ((Module.End.one_apply _).trans (congrArg Φ hg))
  have hchi : levChi (Vc D i) (R.βV i) (datVP R i t (R.levR F false)) k =
      (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch κ : ℂˣ) : ℂ) *
        D.what₂.embLL ((F.ψ0⁻¹ ⟨_, hu⟩ : D.what₂.LLˣ) : D.what₂.LL) := by
    have hw : (⟨R.eG.symm (Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) k)), hmem⟩ : F.P0) = ⟨_, hu⟩ :=
      Subtype.ext ((congrArg R.eG.symm hrt).trans (R.eG.symm_apply_apply _))
    have c1 : levChi (Vc D i) (R.βV i) (datVP R i t (R.levR F false)) k =
        ((Formalism.L2.DIV.levFn (R.βV i) (withP (R.datVt i t) (R.levR F false).conj) (finE (Vc D i) k) : ℂˣ) : ℂ) := rfl
    have c2 := levFn_withP (V := Vc D i) (β := R.βV i) (L := R.datVt i t) (R.levR F false).conj (finE (Vc D i) k)
    have c3 := Formalism.L2.DIV.extendOne_of_mem (R.levR F false).conj.chi hmem
    have c4 : Formalism.L2.DIV.levFn (R.βV i) (flagL (R.datVt i t)) (finE (Vc D i) k) = (levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch κ :=
      congrArg (Formalism.L2.DIV.levFn (R.βV i) (flagL (R.datVt i t))) hfk
    have c5 : (((R.levR F false).conj.chi ⟨_, hmem⟩ : ℂˣ) : ℂ) =
        D.what₂.embLL ((F.ψ0⁻¹ ⟨_, hu⟩ : D.what₂.LLˣ) : D.what₂.LL) := by
      have d1 : (R.levR F false).conj.chi ⟨_, hmem⟩ = ((R.levR F false).chi ⟨_, hmem⟩)⁻¹ := rfl
      have d2 : (R.levR F false).chi ⟨_, hmem⟩ = Units.map D.what₂.embLL.toMonoidHom
          (F.ψ0 ⟨R.eG.symm (Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) k)), hmem⟩) := rfl
      have d3 : (((Units.map D.what₂.embLL.toMonoidHom (F.ψ0 ⟨_, hu⟩))⁻¹ : ℂˣ) : ℂ) =
          D.what₂.embLL ((F.ψ0⁻¹ ⟨_, hu⟩ : D.what₂.LLˣ) : D.what₂.LL) :=
        (GlobalTheory.LevToQ.units_map_inv_val D.what₂.embLL (F.ψ0 ⟨_, hu⟩)).trans
          (congrArg (fun u : D.what₂.LLˣ => D.what₂.embLL (u : D.what₂.LL)) (MonoidHom.inv_apply F.ψ0 _).symm)
      exact (congrArg (fun u : ℂˣ => (u : ℂ)) (d1.trans (congrArg (·⁻¹) (d2.trans (congrArg (Units.map D.what₂.embLL.toMonoidHom) (congrArg F.ψ0 hw)))))).trans d3
    have c6 := congrArg (fun u : ℂˣ => (u : ℂ)) (c2.trans (congrArg₂ (· * ·) c3 c4))
    refine c1.trans (c6.trans ?_)
    exact (Units.val_mul _ _).trans ((congrArg (· * (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch κ : ℂˣ) : ℂ)) c5).trans (mul_comm _ _))
  calc Φ (h * κ) = (R.cV i).ext Φ (g * k) := e1.symm
    _ = levChi (Vc D i) (R.βV i) (datVP R i t (R.levR F false)) k • (R.cV i).ext Φ g := hlaw
    _ = levChi (Vc D i) (R.βV i) (datVP R i t (R.levR F false)) k • Φ h := congrArg _ e2
    _ = ((((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch κ : ℂˣ) : ℂ) *
        D.what₂.embLL ((F.ψ0⁻¹ ⟨_, hu⟩ : D.what₂.LLˣ) : D.what₂.LL)) • Φ h := congrArg (· • Φ h) hchi
    _ = _ := mul_smul _ _ _
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseLevelAdelicTypeImpliesLiftLawStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_level_adelic_type_implies_lift_law : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.models_cV → R.grp_red_L → ∀ (i : Fin D.R.m) (t : T) (Φ : Bridge.Gf (Vc D i) → (R.cV i).W), (R.cV i).ext Φ ∈ levSubV (Vc D i) (R.cV i).W (levS _ (R.βV i) (datVP R i t (R.levR F false))) (levChi _ (R.βV i) (datVP R i t (R.levR F false))) → ∀ (κ : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q) (hu : (R.B.L i t).act_tie.red κ ∈ F.P0) (h : Bridge.Gf (Vc D i)), Φ (h * κ) = (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch κ : ℂˣ) : ℂ) • D.what₂.embLL ((F.ψ0⁻¹ ⟨_, hu⟩ : D.what₂.LLˣ) : D.what₂.LL) • Φ h := by
  first | exact @GlobalTheory.LevToQ.levtoq | exact GlobalTheory.LevToQ.levtoq | (intros; apply GlobalTheory.LevToQ.levtoq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanEigenformsAdelicFormsIffClassPresentation
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanEigenformsAdelicFormsIffClassPresentation
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.LiftSpanEig

theorem eigen_span_iff : ∀ {G Γ W K G0 : Type} [Group G] [Group Γ] (ι : Γ →* G) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K] [NumberField K] [StarRing K] (S : CSD K) (σ : K →+* ℂ) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) [Group G0] [Fintype G0] (Q : Subgroup G) (ch : Q →* ℂˣ) (act : Representation K G0 S.Forms) (P : Bridge.ClassPres ι S σ ρ J χ) (Tt : Bridge.ActTie ι P Q ch act), P.ExtBij → ∀ (U : Subgroup G0) (ψ : U →* Kˣ) (Φ : G → W), Φ ∈ Submodule.span ℂ (P.extL '' {f | ∀ u : U, act (u : G0) f = ((ψ u : Kˣ) : K) • f}) ↔ (Φ ∈ Bridge.AdForms ι ρ J χ ∧ ∀ (κ : Q) (hu : Tt.red κ ∈ U) (h : G), Φ (h * κ) = ((ch κ : ℂˣ) : ℂ) • σ ((ψ ⟨_, hu⟩ : Kˣ) : K) • Φ h) := by
  classical
  intro G Γ W K G0 _ _ ι _ _ _ _ _ S σ ρ J χ _ _ Q ch act P Tt hB U ψ Φ

  let gA : Q → (G → W) →ₗ[ℂ] (G → W) := fun κ =>
    { toFun := Bridge.g0Act ch κ
      map_add' := fun F F' => by
        funext h
        simp only [Bridge.g0Act, Pi.add_apply, smul_add]
      map_smul' := fun a F => by
        funext h
        simp only [Bridge.g0Act, Pi.smul_apply, RingHom.id_apply]
        rw [smul_comm] }
  have gA_apply : ∀ κ F h, gA κ F h = (((ch κ)⁻¹ : ℂˣ) : ℂ) • F (h * (κ : G)) := fun _ _ _ => rfl
  have hsemi : ∀ (a : K) (f : S.Forms), P.extL (a • f) = σ a • P.extL f := fun a f => map_smulₛₗ P.extL a f
  have hact : ∀ (g : G0) (κ : Q), Tt.red κ = g → ∀ f : S.Forms, P.extL (act g f) = gA κ (P.extL f) :=
    fun g κ hk f => Tt.act_eq g κ hk f

  let N : Submodule ℂ (G → W) :=
    { carrier := {Φ | Φ ∈ Bridge.AdForms ι ρ J χ ∧ ∀ (κ : Q) (hu : Tt.red κ ∈ U) (h : G),
        Φ (h * κ) = ((ch κ : ℂˣ) : ℂ) • σ ((ψ ⟨_, hu⟩ : Kˣ) : K) • Φ h}
      add_mem' := fun {a b} ha hb => ⟨add_mem ha.1 hb.1, fun κ hu h => by
        simp only [Pi.add_apply, ha.2 κ hu h, hb.2 κ hu h, smul_add]⟩
      zero_mem' := ⟨zero_mem _, fun κ hu h => by simp⟩
      smul_mem' := fun c a ha => ⟨Submodule.smul_mem _ c ha.1, fun κ hu h => by
        simp only [Pi.smul_apply, ha.2 κ hu h]
        rw [smul_comm c, smul_comm c]⟩ }
  constructor
  · intro hΦ
    have : Submodule.span ℂ (P.extL '' {f | ∀ u : U, act (u : G0) f = ((ψ u : Kˣ) : K) • f}) ≤ N := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨f, hf, rfl⟩
      refine ⟨hB.2 ▸ Submodule.subset_span ⟨f, rfl⟩, fun κ hu h => ?_⟩
      have e := congrFun (hact (Tt.red κ) κ rfl f) h
      have e2 : act (Tt.red κ) f = ((ψ ⟨_, hu⟩ : Kˣ) : K) • f := hf ⟨_, hu⟩
      rw [e2, hsemi, gA_apply] at e
      rw [Pi.smul_apply] at e
      rw [e, smul_smul, Units.mul_inv, one_smul]
    exact this hΦ
  · rintro ⟨hA, hc⟩
    choose κ hκ using Tt.red_surj
    let L : (G → W) →ₗ[ℂ] (G → W) := ∑ g : G0, σ (GlobalTheory.TraceIncl.invChar U ψ g) • gA (κ g)
    have L_apply : ∀ F, L F = ∑ g : G0, σ (GlobalTheory.TraceIncl.invChar U ψ g) • gA (κ g) F := fun F => by
      simp [L, LinearMap.sum_apply]
    have hLext : ∀ f : S.Forms, L (P.extL f) = P.extL (GlobalTheory.TraceIncl.trU act U ψ f) := fun f => by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [L_apply, GlobalTheory.TraceIncl.trU_apply, map_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [hsemi, hact g (κ g) (hκ g)]
    let E := P.extL '' {f | ∀ u : U, act (u : G0) f = ((ψ u : Kˣ) : K) • f}
    have hspan : Submodule.span ℂ (Set.range P.extL) ≤ (Submodule.span ℂ E).comap L := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨f, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, hLext]
      exact Submodule.subset_span ⟨_, fun u => GlobalTheory.TraceIncl.trU_eigen act U ψ f u, rfl⟩
    have hLΦ : L Φ = (Nat.card U : ℂ) • Φ := by
      have term : ∀ g : G0, σ (GlobalTheory.TraceIncl.invChar U ψ g) • gA (κ g) Φ = if g ∈ U then Φ else 0 := fun g => by
        unfold GlobalTheory.TraceIncl.invChar
        split_ifs with hg
        · have hs : ψ ⟨Tt.red (κ g), (hκ g).symm ▸ hg⟩ = ψ ⟨g, hg⟩ := congrArg ψ (Subtype.ext (hκ g))
          funext h
          rw [Pi.smul_apply, gA_apply, hc (κ g) ((hκ g).symm ▸ hg) h, hs, smul_smul, smul_smul, smul_smul]
          convert one_smul ℂ (Φ h) using 2
          rw [mul_assoc (σ _), Units.inv_mul, mul_one, ← map_mul, Units.inv_mul, map_one]
        · rw [map_zero, zero_smul]
      rw [L_apply, Finset.sum_congr rfl fun g _ => term g, ← Finset.sum_filter, Finset.sum_const,
        ← Nat.cast_smul_eq_nsmul ℂ, Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hmem : L Φ ∈ Submodule.span ℂ E := hspan (hB.2.symm ▸ hA)
    rw [hLΦ] at hmem
    have hne : (Nat.card U : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
    exact (Submodule.smul_mem_iff _ hne).1 hmem

end GlobalTheory.LiftSpanEig
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanEigenformsAdelicFormsIffClassPresentationStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_eigenforms_adelic_forms_iff_class_presentation : ∀ {G Γ W K G0 : Type} [Group G] [Group Γ] (ι : Γ →* G) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K] [NumberField K] [StarRing K] (S : CSD K) (σ : K →+* ℂ) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) [Group G0] [Fintype G0] (Q : Subgroup G) (ch : Q →* ℂˣ) (act : Representation K G0 S.Forms) (P : Bridge.ClassPres ι S σ ρ J χ) (Tt : Bridge.ActTie ι P Q ch act), P.ExtBij → ∀ (U : Subgroup G0) (ψ : U →* Kˣ) (Φ : G → W), Φ ∈ Submodule.span ℂ (P.extL '' {f | ∀ u : U, act (u : G0) f = ((ψ u : Kˣ) : K) • f}) ↔ (Φ ∈ Bridge.AdForms ι ρ J χ ∧ ∀ (κ : Q) (hu : Tt.red κ ∈ U) (h : G), Φ (h * κ) = ((ch κ : ℂˣ) : ℂ) • σ ((ψ ⟨_, hu⟩ : Kˣ) : K) • Φ h) := by
  first | exact @GlobalTheory.LiftSpanEig.eigen_span_iff | exact GlobalTheory.LiftSpanEig.eigen_span_iff | (intros; apply GlobalTheory.LiftSpanEig.eigen_span_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftLawImpliesAdelicExtensionBaseLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftLawImpliesAdelicExtensionBaseLevel
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.LiftSpan

theorem end_smul_smul {W : Type} [AddCommGroup W] [Module ℂ W] (L : Module.End ℂ W) (a b : ℂ) (x : W) :
    L (a • b • x) = (a * b) • L x := by
  rw [map_smul, map_smul, smul_smul]


set_option maxHeartbeats 16000000 in
theorem ext_mem_levSubV_of_lift : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.models_cV → R.grp_red_L → ∀ (i : Fin D.R.m) (t : T) (Φ : Bridge.Gf (Vc D i) → (R.cV i).W), (∀ (κ : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q) (hu : (R.B.L i t).act_tie.red κ ∈ F.P0) (h : Bridge.Gf (Vc D i)), Φ (h * κ) = (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch κ : ℂˣ) : ℂ) • D.what₂.embLL ((F.ψ0⁻¹ ⟨_, hu⟩ : D.what₂.LLˣ) : D.what₂.LL) • Φ h) → (R.cV i).ext Φ ∈ levSubV (Vc D i) (R.cV i).W (levS _ (R.βV i) (datVP R i t (R.levR F false))) (levChi _ (R.βV i) (datVP R i t (R.levR F false))) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hcV hred i t Φ hΦ
  intro k hk g
  have hkG : k ∈ GfC (Vc D i) := hk.1
  have hpar : finE (Vc D i) k ∈ Formalism.L2.DIV.parLev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t) := hk.2.1
  have hH : Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) k) ∈ (R.levR F false).H := hk.2.2
  have hq : (finHom (Vc D i)).rangeRestrict k ∈ (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q := by
    show Formalism.UG.bc (swapAE D) (finHom (Vc D i) k) ∈
      Formalism.L2.DIV.lev D.sp.cm (Vc D i).gram (R.βV i) (flagL (R.datVt i t))
    rw [← finE_eq]
    exact ⟨hpar, Subgroup.mem_top _⟩
  set κ : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q := ⟨_, hq⟩ with hκdef
  have hred' : R.eG ((R.B.L i t).act_tie.red κ) = Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) k) :=
    hred i t κ
  have hu : (R.B.L i t).act_tie.red κ ∈ F.P0 := by
    have h2 : R.eG.symm (Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) k)) ∈ F.P0 := hH
    rw [← hred', MulEquiv.symm_apply_apply] at h2
    exact h2
  have hlaw := hΦ κ hu ((finHom (Vc D i)).rangeRestrict g)
  have hchi : levChi _ (R.βV i) (datVP R i t (R.levR F false)) k =
      (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch κ : ℂˣ) : ℂ) •
        D.what₂.embLL ((F.ψ0⁻¹ ⟨_, hu⟩ : D.what₂.LLˣ) : D.what₂.LL) := by
    have hH' : Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) k) ∈ (R.levR F false).conj.H := hH
    have hP : (⟨R.eG.symm (Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) k)), hH⟩ : F.P0) =
        ⟨(R.B.L i t).act_tie.red κ, hu⟩ := Subtype.ext (by
          show R.eG.symm (Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) k)) = (R.B.L i t).act_tie.red κ
          rw [← hred', MulEquiv.symm_apply_apply])
    have hw := levFn_withP (V := Vc D i) (β := R.βV i) (L := R.datVt i t) (R.levR F false).conj (finE (Vc D i) k)
    have he := Formalism.L2.DIV.extendOne_of_mem (R.levR F false).conj.chi hH'
    have hw2 : Formalism.L2.DIV.levFn (R.βV i) (withP (R.datVt i t) (R.levR F false).conj) (finE (Vc D i) k) =
        (R.levR F false).conj.chi ⟨_, hH'⟩ * Formalism.L2.DIV.levFn (R.βV i) (flagL (R.datVt i t)) (finE (Vc D i) k) :=
      hw.trans (congrArg (fun u => u * Formalism.L2.DIV.levFn (R.βV i) (flagL (R.datVt i t)) (finE (Vc D i) k)) he)
    show ((Formalism.L2.DIV.levFn (R.βV i) (withP (R.datVt i t) (R.levR F false).conj) (finE (Vc D i) k) : ℂˣ) : ℂ) = _
    rw [hw2, Units.val_mul, mul_comm, smul_eq_mul]
    congr 1
    · show (((Units.map D.what₂.embLL.toMonoidHom (F.ψ0 ⟨R.eG.symm _, hH⟩))⁻¹ : ℂˣ) : ℂ) = _
      rw [hP]
      rfl
  have e1 := Formalism.IndefR.Eqv.Act.coefExt_mul (R.cV i) (hcV i) Φ g k hkG
  have e3 : (R.cV i).ext Φ g = (R.cV i).ρ g⁻¹ (Φ ((finHom (Vc D i)).rangeRestrict g)) := rfl
  rewrite [e1, hchi, hlaw, e3, smul_eq_mul]
  exact @end_smul_smul _ _ _ _ _ _ _

end GlobalTheory.LiftSpan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftLawImpliesAdelicExtensionBaseLevelStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_law_implies_adelic_extension_base_level : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.models_cV → R.grp_red_L → ∀ (i : Fin D.R.m) (t : T) (Φ : Bridge.Gf (Vc D i) → (R.cV i).W), (∀ (κ : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q) (hu : (R.B.L i t).act_tie.red κ ∈ F.P0) (h : Bridge.Gf (Vc D i)), Φ (h * κ) = (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch κ : ℂˣ) : ℂ) • D.what₂.embLL ((F.ψ0⁻¹ ⟨_, hu⟩ : D.what₂.LLˣ) : D.what₂.LL) • Φ h) → (R.cV i).ext Φ ∈ levSubV (Vc D i) (R.cV i).W (levS _ (R.βV i) (datVP R i t (R.levR F false))) (levChi _ (R.βV i) (datVP R i t (R.levR F false))) := by
  first | exact @GlobalTheory.LiftSpan.ext_mem_levSubV_of_lift | exact GlobalTheory.LiftSpan.ext_mem_levSubV_of_lift | (intros; apply GlobalTheory.LiftSpan.ext_mem_levSubV_of_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanLiftFormsBaseLevelEqHilbertImage
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.LiftSpan


set_option maxHeartbeats 10000000 in
theorem span_liftForm_eq : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → A.fam.Ok 1 → (∀ i t, Function.Injective (R.extV i t)) → ∀ (i : Fin D.R.m) (t : T), Submodule.span ℂ (Set.range fun x => R.extV i t (R.jV i t (liftForm A F.P0 F.ψ0 i t x))) = LinearMap.range (R.extV i t) ⊓ levSubV (Vc D i) (R.cV i).W (levS _ (R.βV i) (datVP R i t (R.levR F false))) (levChi _ (R.βV i) (datVP R i t (R.levR F false))) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hB _ _ i t
  classical
  have hHV := hB.models.HV i t
  have hjV := hB.models.jV
  have hExt : (R.B.L i t).pres.ExtBij :=
    (GlobalTheory.classPres_extMem_extBij_isom _ _ _ _ _ _ _ _ _ _ (R.B.L i t).pres).2.1
  have key : (fun x => R.extV i t (R.jV i t (liftForm A F.P0 F.ψ0 i t x))) =
      fun x => (R.cV i).ext ((R.B.L i t).pres.extL (GlobalTheory.OnTies.srcForm A i t F.P0 F.ψ0⁻¹ x)) := by
    funext x
    exact congrArg (R.cV i).ext (hjV i t _)
  have hR : Set.range (fun x => R.extV i t (R.jV i t (liftForm A F.P0 F.ψ0 i t x))) =
      (R.cV i).ext '' ((R.B.L i t).pres.extL ''
        {f | ∀ u : F.P0, A.leftGroupActionLift i t (u : G) f = ((F.ψ0⁻¹ u : D.what₂.LLˣ) : D.what₂.LL) • f}) := by
    rw [key]
    ext Y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨_, ⟨_, (GlobalTheory.TraceIncl.mem_range_srcForm i t F.P0 F.ψ0⁻¹ _).1 ⟨x, rfl⟩, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
      obtain ⟨x, rfl⟩ := (GlobalTheory.TraceIncl.mem_range_srcForm i t F.P0 F.ψ0⁻¹ f).2 hf
      exact ⟨x, rfl⟩
  rw [hR, Submodule.span_image]
  ext Y
  simp only [Submodule.mem_map, Submodule.mem_inf, LinearMap.mem_range]
  have hs1 := GlobalTheory.T.span_eigenforms_adelic_forms_iff_class_presentation (W := (R.cV i).W) (Bridge.ratF (Vc D i)) (A.MtCSD i t) D.what₂.embLL (R.cV i).coef.ρ
    (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J (levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ
    (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q (levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch (A.leftGroupActionLift i t)
    (R.B.L i t).pres (R.B.L i t).act_tie hExt F.P0 F.ψ0⁻¹
  have hs2a := GlobalTheory.T.base_level_adelic_type_implies_lift_law D G Pl0 T A Ks R F hB.models.cV hB.grp.red_L i t
  have hs2b := GlobalTheory.T.lift_law_implies_adelic_extension_base_level D G Pl0 T A Ks R F hB.models.cV hB.grp.red_L i t
  constructor
  · rintro ⟨Φ, hΦ, rfl⟩
    obtain ⟨hAd, hq⟩ := (hs1 Φ).1 hΦ
    refine ⟨?_, hs2b Φ hq⟩
    have h1 : Φ ∈ LinearMap.range (R.HV i t).e := by rw [hHV.2.1]; exact hAd
    obtain ⟨y, hy⟩ := h1
    exact ⟨y, by rw [← hy]; rfl⟩
  · rintro ⟨⟨y, rfl⟩, hlev⟩
    have h1 : (R.HV i t).e y ∈ LinearMap.range (R.HV i t).e := LinearMap.mem_range_self _ y
    rw [hHV.2.1] at h1
    exact ⟨(R.HV i t).e y, (hs1 _).2 ⟨h1, hs2a _ hlev⟩, rfl⟩

end GlobalTheory.LiftSpan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanLiftFormsBaseLevelEqHilbertImageStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_liftForms_baseLevel_eq_hilbertImage : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → A.fam.Ok 1 → (∀ i t, Function.Injective (R.extV i t)) → ∀ (i : Fin D.R.m) (t : T), Submodule.span ℂ (Set.range fun x => R.extV i t (R.jV i t (liftForm A F.P0 F.ψ0 i t x))) = LinearMap.range (R.extV i t) ⊓ levSubV (Vc D i) (R.cV i).W (levS _ (R.βV i) (datVP R i t (R.levR F false))) (levChi _ (R.βV i) (datVP R i t (R.levR F false))) := by
  first | exact @GlobalTheory.LiftSpan.span_liftForm_eq | exact GlobalTheory.LiftSpan.span_liftForm_eq | (intros; apply GlobalTheory.LiftSpan.span_liftForm_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurOrthogonalityDimPairingEqInner
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankCoefficientSpaceEqProdRealModels
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankCoefficientSpaceEqProdRealModels
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
namespace GlobalTheory.CoefDim


open Classical in
theorem finrank_piTensorProduct {ι : Type} [Fintype ι] (E : ι → Type) [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)]
    [∀ i, FiniteDimensional ℂ (E i)] : Module.finrank ℂ (⨂[ℂ] i, E i) = ∏ i, Module.finrank ℂ (E i) := by
  let b := Basis.piTensorProduct (fun i => Module.finBasis ℂ (E i))
  rw [Module.finrank_eq_card_basis b, Fintype.card_pi]
  simp [Fintype.card_fin]

theorem finrank_coef_eq_prod : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → Module.finrank ℂ R.cX.W = ∏ τ, Module.finrank ℂ (R.MX.H τ) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hB
  have hp := GlobalTheory.DefiniteMult.allPlus_parB _ (Nat.sub_le _ _) R.MX
  have hb := GlobalTheory.DefiniteMult.pair_bijective hB.models.inf hp hB.models.cX hB.models.prX
  have m := GlobalTheory.DefLift.AllPlus.finite_smooth_irreducible D _ _ R.MX hp
  haveI : ∀ τ, FiniteDimensional ℂ (R.MX.H τ) := fun τ => (m τ).1
  haveI : ∀ τ, FiniteDimensional ℂ (R.MX.sm τ) := fun τ => inferInstance
  have hsm : ∀ τ, Module.finrank ℂ (R.MX.sm τ) = Module.finrank ℂ (R.MX.H τ) := fun τ => by
    rw [(m τ).2.1, finrank_top]
  have e : R.cX.W ≃ₗ[ℂ] Module.Dual ℂ (SmT R.MX) := LinearEquiv.ofBijective R.prX hb
  have hT : Module.finrank ℂ (SmT R.MX) = ∏ τ, Module.finrank ℂ (R.MX.H τ) :=
    (finrank_piTensorProduct (fun τ => R.MX.sm τ)).trans (Finset.prod_congr rfl fun τ _ => hsm τ)
  haveI : FiniteDimensional ℂ (SmT R.MX) :=
    Module.Finite.of_basis (Basis.piTensorProduct (fun τ => Module.finBasis ℂ (R.MX.sm τ)))
  rw [e.finrank_eq, Subspace.dual_finrank_eq, hT]

end GlobalTheory.CoefDim
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankCoefficientSpaceEqProdRealModelsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_coefficient_space_eq_prod_real_models : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → Module.finrank ℂ R.cX.W = ∏ τ, Module.finrank ℂ (R.MX.H τ) := by
  first | exact @GlobalTheory.CoefDim.finrank_coef_eq_prod | exact GlobalTheory.CoefDim.finrank_coef_eq_prod | (intros; apply GlobalTheory.CoefDim.finrank_coef_eq_prod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RieszVectorsPureTensorsInnerEqProd
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RieszVectorsPureTensorsInnerEqProd
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem

theorem rieszProd_inner : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → Seed.PrIso R.MX R.cX R.prX → ∀ (v v' : R.MX.Vec) (a a' : R.cX.W), (∀ w, R.prX w (PiTensorProduct.tprod ℂ v) = ⟪a, w⟫_ℂ) → (∀ w, R.prX w (PiTensorProduct.tprod ℂ v') = ⟪a', w⟫_ℂ) → ⟪a', a⟫_ℂ = ∏ τ, ⟪(v τ : R.MX.H τ), (v' τ : R.MX.H τ)⟫_ℂ := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hB hI v v' a a' ha ha'
  classical
  have hp : GlobalTheory.DefLift.AllPlus R.MX := GlobalTheory.DefiniteMult.allPlus_parB _ (Nat.sub_le _ _) R.MX
  have hbij := GlobalTheory.DefiniteMult.pair_bijective hB.models.inf hp hB.models.cX hB.models.prX
  have m := GlobalTheory.DefLift.AllPlus.finite_smooth_irreducible D _ _ R.MX hp
  haveI : ∀ τ, FiniteDimensional ℂ (R.MX.sm τ) := fun τ => by haveI := (m τ).1; infer_instance
  let b := fun τ => stdOrthonormalBasis ℂ (R.MX.sm τ)
  let c : R.MX.Vec → (∀ τ, Fin (Module.finrank ℂ (R.MX.sm τ))) → ℂ := fun u f => ∏ τ, ⟪(b τ (f τ)), u τ⟫_ℂ
  have hexp : ∀ u : R.MX.Vec, PiTensorProduct.tprod ℂ u =
      ∑ f, c u f • PiTensorProduct.tprod ℂ (fun τ => b τ (f τ)) := by
    intro u
    conv_lhs => rw [show u = fun τ => ∑ i, ⟪b τ i, u τ⟫_ℂ • b τ i from funext fun τ => ((b τ).sum_repr' (u τ)).symm]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [MultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    exact MultilinearMap.map_smul_univ _ (fun τ => ⟪b τ (f τ), u τ⟫_ℂ) (fun τ => b τ (f τ))
  let B := Basis.piTensorProduct (fun τ => (b τ).toBasis)
  have hB' : ∀ f, B f = PiTensorProduct.tprod ℂ (fun τ => b τ (f τ)) := fun f => by
    simp [B, Basis.piTensorProduct_apply]

  have hw : ∀ g : (∀ τ, Fin (Module.finrank ℂ (R.MX.sm τ))), ∃ w, ∀ f : (∀ τ, Fin (Module.finrank ℂ (R.MX.sm τ))), R.prX w (PiTensorProduct.tprod ℂ (fun τ => b τ (f τ))) = if f = g then 1 else 0 := by
    intro g
    obtain ⟨w, hw⟩ := hbij.2 (B.coord g)
    refine ⟨w, fun f => ?_⟩
    rw [hw, ← hB', Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  have hcoef : ∀ g : (∀ τ, Fin (Module.finrank ℂ (R.MX.sm τ))), R.prX a (PiTensorProduct.tprod ℂ (fun τ => b τ (g τ))) = starRingEnd ℂ (c v g) := by
    intro g
    obtain ⟨w, hw⟩ := hw g
    have h1 := hI (fun τ => Fin (Module.finrank ℂ (R.MX.sm τ))) b w a
    rw [Finset.sum_eq_single g (fun f _ hf => by rw [hw f, if_neg hf]; simp) (by simp), hw g, if_pos rfl,
      map_one, one_mul] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← h1, ← inner_conj_symm, ← ha w, hexp v, map_sum]
    rw [Finset.sum_eq_single g (fun f _ hf => by rw [map_smul, hw f, if_neg hf]; simp) (by simp)]
    rw [map_smul, hw g, if_pos rfl, smul_eq_mul, mul_one]
  have h2 := ha' a
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← h2, hexp v', map_sum]
  have hr : ∀ τ, ⟪((v τ : R.MX.sm τ) : R.MX.H τ), ((v' τ : R.MX.sm τ) : R.MX.H τ)⟫_ℂ =
      ∑ i, ⟪v τ, b τ i⟫_ℂ * ⟪b τ i, v' τ⟫_ℂ := fun τ =>
    (Submodule.coe_inner (R.MX.sm τ) (v τ) (v' τ)).symm.trans ((b τ).sum_inner_mul_inner (v τ) (v' τ)).symm
  have hprod : ∏ τ, ⟪((v τ : R.MX.sm τ) : R.MX.H τ), ((v' τ : R.MX.sm τ) : R.MX.H τ)⟫_ℂ =
      ∑ f : (∀ τ, Fin (Module.finrank ℂ (R.MX.sm τ))), ∏ τ, (⟪v τ, b τ (f τ)⟫_ℂ * ⟪b τ (f τ), v' τ⟫_ℂ) := by
    exact (Finset.prod_congr rfl fun τ _ => hr τ).trans
      (Fintype.prod_sum (fun τ (i : Fin (Module.finrank ℂ (R.MX.sm τ))) => ⟪v τ, b τ i⟫_ℂ * ⟪b τ i, v' τ⟫_ℂ))
  refine Eq.trans ?_ hprod.symm
  refine Finset.sum_congr rfl fun f _ => ?_
  have e1 : R.prX a (c v' f • PiTensorProduct.tprod ℂ (fun τ => b τ (f τ))) = c v' f * starRingEnd ℂ (c v f) :=
    ((R.prX a).map_smul _ _).trans ((congrArg (c v' f • ·) (hcoef f)).trans (smul_eq_mul _ _))
  refine e1.trans ?_
  have e2 : starRingEnd ℂ (c v f) = ∏ τ, ⟪v τ, b τ (f τ)⟫_ℂ :=
    (map_prod (starRingEnd ℂ) _ _).trans (Finset.prod_congr rfl fun τ _ => inner_conj_symm _ _)
  refine (congrArg (c v' f * ·) e2).trans ?_
  refine (Finset.prod_mul_distrib).symm.trans ?_
  exact Finset.prod_congr rfl fun τ _ => mul_comm _ _

end GlobalTheory.Mem
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RieszVectorsPureTensorsInnerEqProdStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riesz_vectors_pure_tensors_inner_eq_prod : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → Seed.PrIso R.MX R.cX R.prX → ∀ (v v' : R.MX.Vec) (a a' : R.cX.W), (∀ w, R.prX w (PiTensorProduct.tprod ℂ v) = ⟪a, w⟫_ℂ) → (∀ w, R.prX w (PiTensorProduct.tprod ℂ v') = ⟪a', w⟫_ℂ) → ⟪a', a⟫_ℂ = ∏ τ, ⟪(v τ : R.MX.H τ), (v' τ : R.MX.H τ)⟫_ℂ := by
  first | exact @GlobalTheory.Mem.rieszProd_inner | exact GlobalTheory.Mem.rieszProd_inner | (intros; apply GlobalTheory.Mem.rieszProd_inner <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurOrthogonalityDimPairingEqInner
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.TopSchur

theorem riesz {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (ℓ : W →ₗ[ℂ] ℂ) : ∃ a : W, ∀ w, ℓ w = ⟪a, w⟫_ℂ :=
  ⟨(InnerProductSpace.toDual ℂ W).symm (LinearMap.toContinuousLinearMap ℓ), fun w => by
    rw [InnerProductSpace.toDual_symm_apply]; rfl⟩

theorem exists_vec_prod_ne {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) {W : Type}
    [AddCommGroup W] [Module ℂ W] (pr : W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ) (hpr : pr ≠ 0) :
    ∃ v : M.Vec, ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ ≠ 0 := by
  classical
  have hτ : ∀ τ, ∃ x : M.sm τ, x ≠ 0 := by
    intro τ
    by_contra hz
    push_neg at hz
    apply hpr
    have hs : ∀ s : SmT M, s = 0 := by
      intro s
      induction s using PiTensorProduct.induction_on with
      | smul_tprod r f =>
        rw [(PiTensorProduct.tprod ℂ).map_coord_zero τ (hz (f τ)), smul_zero]
      | add x y hx hy => rw [hx, hy, add_zero]
    refine LinearMap.ext fun w => LinearMap.ext fun s => ?_
    rw [hs s]
    simp
  choose v hv using hτ
  refine ⟨v, Finset.prod_ne_zero_iff.mpr fun τ _ => inner_self_ne_zero.mpr ?_⟩
  intro h0
  exact hv τ (Subtype.ext h0)

theorem alg_step {d I p q x : ℂ} (hd : d ≠ 0) (hI : d * I = q * x) (hq : q = p) : I = x / d * p := by
  subst hq
  field_simp
  linear_combination hI

theorem dualNumber_unit_mul_decomposition {P c d x : ℂ} (hP : P = d) (hc : c = x / d) (hd : d ≠ 0) : P * c = x := by
  subst hP hc
  field_simp


set_option maxHeartbeats 400000 in
theorem topSchur : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → Seed.PrIso R.MX R.cX R.prX → ∀ (t : T) (h h' : (R.HX t).H), (((∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)) : ℝ) : ℂ) * ipMT R.MX (R.νX t) (R.fdX t) (R.cX.toMap R.prX ((R.HX t).e h)) (R.cX.toMap R.prX ((R.HX t).e h')) = ⟪h, h'⟫_ℂ := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hB hP t h h'
  classical
  have hC := GlobalTheory.T.finrank_coefficient_space_eq_prod_real_models D G Pl0 T A Ks R F hB
  haveI hWnt : Nontrivial R.cX.W := hB.models.cX.2.2.2.1
  have hd0 : (Module.finrank ℂ R.cX.W : ℂ) ≠ 0 := by
    have := Module.finrank_pos (R := ℂ) (M := R.cX.W)
    exact_mod_cast this.ne'
  have hcast : (((∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)) : ℝ) : ℂ) = (Module.finrank ℂ R.cX.W : ℂ) := by
    rw [hC]; push_cast; rfl
  have key : ∀ v v' : R.MX.Vec,
      IntegrableOn (fun g => star (R.prX (R.cX.ext ((R.HX t).e h) g) (PiTensorProduct.tprod ℂ v)) *
        R.prX (R.cX.ext ((R.HX t).e h') g) (PiTensorProduct.tprod ℂ v')) (R.fdX t) (R.νX t) ∧
      ∫ g in R.fdX t, star (R.prX (R.cX.ext ((R.HX t).e h) g) (PiTensorProduct.tprod ℂ v)) *
        R.prX (R.cX.ext ((R.HX t).e h') g) (PiTensorProduct.tprod ℂ v') ∂(R.νX t) =
      ⟪h, h'⟫_ℂ / (Module.finrank ℂ R.cX.W : ℂ) * ∏ τ, ⟪(v τ : R.MX.H τ), (v' τ : R.MX.H τ)⟫_ℂ := by
    intro v v'
    have hr : ∃ a : R.cX.W, ∀ w, R.prX w (PiTensorProduct.tprod ℂ v) = ⟪a, w⟫_ℂ := riesz (R.prX.flip _)
    have hr' : ∃ a : R.cX.W, ∀ w, R.prX w (PiTensorProduct.tprod ℂ v') = ⟪a, w⟫_ℂ := riesz (R.prX.flip _)
    obtain ⟨a, ha⟩ := hr
    obtain ⟨a', ha'⟩ := hr'
    have hA := GlobalTheory.T.unfolding_schur_orthogonality_definite_coefficients D G Pl0 T A Ks R F hB t h h' a a'
    obtain ⟨hint, hval⟩ := hA
    have hab := GlobalTheory.T.riesz_vectors_pure_tensors_inner_eq_prod D G Pl0 T A Ks R F hB hP v v' a a' ha ha'
    simp only [ha, ha']
    refine ⟨hint, ?_⟩
    exact alg_step hd0 hval hab
  have hv := exists_vec_prod_ne R.MX R.prX hB.models.prX.1
  obtain ⟨v0, hv0⟩ := hv
  unfold ipMT Mult.ipM
  split_ifs with hex
  · have e1 := (hex.choose_spec v0 v0).2
    have hch : hex.choose * _ = _ * _ := e1.symm.trans (key v0 v0).2
    have hch' := mul_right_cancel₀ hv0 hch
    exact dualNumber_unit_mul_decomposition hcast hch' hd0
  · exfalso
    exact hex ⟨_, fun v v' => key v v'⟩

end GlobalTheory.Mem.TopSchur
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurOrthogonalityDimPairingEqInnerStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schur_orthogonality_dim_pairing_eq_inner : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → Seed.PrIso R.MX R.cX R.prX → ∀ (t : T) (h h' : (R.HX t).H), (((∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)) : ℝ) : ℂ) * ipMT R.MX (R.νX t) (R.fdX t) (R.cX.toMap R.prX ((R.HX t).e h)) (R.cX.toMap R.prX ((R.HX t).e h')) = ⟪h, h'⟫_ℂ := by
  first | exact @GlobalTheory.Mem.TopSchur.topSchur | exact GlobalTheory.Mem.TopSchur.topSchur | (intros; apply GlobalTheory.Mem.TopSchur.topSchur <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertInnerLiftFormsEqBaseLevelHermitian
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertInnerLiftFormsEqBaseLevelHermitian
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
noncomputable section
namespace GlobalTheory.Mem.R3

theorem liftForm_inner_eq_hform : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → ∀ (i : Fin D.R.m) (t : T) (x y : Fin (lDim D A F.P0 F.ψ0 i t) → D.what₂.LL), (((RealDat.nP F false)⁻¹ : ℝ) : ℂ) * ⟪R.jV i t (liftForm A F.P0 F.ψ0 i t x), R.jV i t (liftForm A F.P0 F.ψ0 i t y)⟫_ℂ = D.what₂.embLL (Formalism.DivisionValues.hform (lH D A F.P0 F.ψ0 i t) x y) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hB i t x y
  have h1 : ∀ f g : (A.MtCSD i t).Forms, ⟪R.jV i t f, R.jV i t g⟫_ℂ = D.what₂.embLL ((A.MtCSD i t).csum f g) := by
    intro f g
    refine ((hB.models.HV i t).2.2 _ _).trans ?_
    refine (congrArg₂ _ (hB.models.jV i t f) (hB.models.jV i t g)).trans ?_
    exact (GlobalTheory.classPres_extMem_extBij_isom _ _ _ _ _ _ _ _ _ _ (R.B.L i t).pres).2.2 f g
  have h2 := GlobalTheory.Mem.LiftForms.csum_lvlForm (A.fam.L i t).S (A.fam.L i t).r (A.fam.lvlA F.P0 F.ψ0).P (A.fam.lvlA F.P0 F.ψ0).ψ x y
  have h3 : ⟪R.jV i t (liftForm A F.P0 F.ψ0 i t x), R.jV i t (liftForm A F.P0 F.ψ0 i t y)⟫_ℂ =
      D.what₂.embLL ((Nat.card (A.fam.lvlA F.P0 F.ψ0).P : D.what₂.LL) * Formalism.DivisionValues.hform (lH D A F.P0 F.ψ0 i t) x y) :=
    (h1 (liftForm A F.P0 F.ψ0 i t x) (liftForm A F.P0 F.ψ0 i t y)).trans (congrArg D.what₂.embLL h2)
  have hP : RealDat.nP F false = (Nat.card F.P0 : ℝ) := rfl
  have hc : (Nat.card F.P0 : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := F.P0)).ne'
  rw [h3, map_mul, map_natCast, hP, ← mul_assoc]
  change ((((Nat.card F.P0 : ℝ))⁻¹ : ℝ) : ℂ) * (Nat.card F.P0 : ℂ) * _ = _
  rw [Complex.ofReal_inv, Complex.ofReal_natCast, inv_mul_cancel₀ hc, one_mul]

end GlobalTheory.Mem.R3
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertInnerLiftFormsEqBaseLevelHermitianStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbert_inner_liftForms_eq_base_level_hermitian : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → ∀ (i : Fin D.R.m) (t : T) (x y : Fin (lDim D A F.P0 F.ψ0 i t) → D.what₂.LL), (((RealDat.nP F false)⁻¹ : ℝ) : ℂ) * ⟪R.jV i t (liftForm A F.P0 F.ψ0 i t x), R.jV i t (liftForm A F.P0 F.ψ0 i t y)⟫_ℂ = D.what₂.embLL (Formalism.DivisionValues.hform (lH D A F.P0 F.ψ0 i t) x y) := by
  first | exact @GlobalTheory.Mem.R3.liftForm_inner_eq_hform | exact GlobalTheory.Mem.R3.liftForm_inner_eq_hform | (intros; apply GlobalTheory.Mem.R3.liftForm_inner_eq_hform <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassSumsEqPairingsTopChainLifts
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.TopNorm

theorem ipVia_self {H N : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [AddCommGroup N] [Module ℂ N]
    (e : H →ₗ[ℂ] N) (he : Function.Injective e) (u v : H) : ipVia e (e u) (e v) = ⟪u, v⟫_ℂ := by
  unfold ipVia
  split_ifs with h
  · have h1 : h.1.choose = u := he h.1.choose_spec
    have h2 : h.2.choose = v := he h.2.choose_spec
    rw [h1, h2]
  · exact absurd ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩ h


set_option maxHeartbeats 2000000 in
theorem classSums_topNorm : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R) (hinj : ∀ i t, Function.Injective (R.extV i t)), R.BaseW F → Seed.PrIso R.MX R.cX R.prX → A.fam.Ok 1 → let C := toChainReal R F tupT hm hTop; let L := toLiftReal R F tupT hm hTop hinj; ∀ μ : D.what₂.Tup, (let a := fun x => R.cX.toMap R.prX ((R.HX (tupT μ)).e (R.jX (tupT μ) (rowForm A F.P1 F.ψ1 (tupT μ) x))); Submodule.span ℂ (Set.range a) = C.CCXP true μ ∧ ∀ x y, C.ipXP true μ (a x) (a y) = D.what₂.embLL (Formalism.DivisionValues.hform (rH D A F.P1 F.ψ1 (tupT μ)) x y)) ∧ (let a := fun x => R.cX.toMap R.prX ((R.HX (tupT μ)).e (R.jX (tupT μ) (rowForm A F.P0 F.ψ0 (tupT μ) x))); Submodule.span ℂ (Set.range a) = C.CCXP false μ ∧ ∀ x y, C.ipXP false μ (a x) (a y) = D.what₂.embLL (Formalism.DivisionValues.hform (rH D A F.P0 F.ψ0 (tupT μ)) x y)) ∧ ∀ i : Fin D.R.m, (let a := fun x => R.extV i (tupT μ) (R.jV i (tupT μ) (liftForm A F.P0 F.ψ0 i (tupT μ) x)); Submodule.span ℂ (Set.range a) = L.Amt μ i ∧ ∀ x y, L.ipA μ i (a x) (a y) = D.what₂.embLL (Formalism.DivisionValues.hform (lH D A F.P0 F.ψ0 i (tupT μ)) x y)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F tupT hm hTop hinj hB hPr hOk C L μ
  refine ⟨⟨GlobalTheory.T.rowLevelForms_span_definiteMultiplicitySpace D G Pl0 T A Ks R F hB hPr hOk hTop true (tupT μ), fun x y => ?_⟩,
    ⟨GlobalTheory.T.rowLevelForms_span_definiteMultiplicitySpace D G Pl0 T A Ks R F hB hPr hOk hTop false (tupT μ), fun x y => ?_⟩,
    fun i => ⟨GlobalTheory.T.span_liftForms_baseLevel_eq_hilbertImage D G Pl0 T A Ks R F hB hOk hinj i (tupT μ), fun x y => ?_⟩⟩
  · have h1 := GlobalTheory.T.schur_orthogonality_dim_pairing_eq_inner D G Pl0 T A Ks R F hB hPr (tupT μ) (R.jX (tupT μ) (rowForm A F.P1 F.ψ1 (tupT μ) x))
      (R.jX (tupT μ) (rowForm A F.P1 F.ψ1 (tupT μ) y))
    have h3 := GlobalTheory.T.hilbert_inner_rowForms_eq_level_class_sum D G Pl0 T A Ks R F hB true (tupT μ) x y
    have e1 : ((((∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)) / (1 : ℝ) : ℝ) : ℂ)) =
        (((∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)) : ℝ) : ℂ) :=
      congrArg (fun r : ℝ => (r : ℂ)) (div_one (∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)))
    refine Eq.trans ?_ h3
    show (((RealDat.nP F true)⁻¹ : ℝ) : ℂ) * ((((∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)) / (1 : ℝ) : ℝ) : ℂ) *
        ipMT R.MX (R.νX (tupT μ)) (R.fdX (tupT μ))
          (R.cX.toMap R.prX ((R.HX (tupT μ)).e (R.jX (tupT μ) (rowForm A F.P1 F.ψ1 (tupT μ) x))))
          (R.cX.toMap R.prX ((R.HX (tupT μ)).e (R.jX (tupT μ) (rowForm A F.P1 F.ψ1 (tupT μ) y))))) = _
    exact congrArg (fun z : ℂ => (((RealDat.nP F true)⁻¹ : ℝ) : ℂ) * z) ((congrArg (· * _) e1).trans h1)
  · have h1 := GlobalTheory.T.schur_orthogonality_dim_pairing_eq_inner D G Pl0 T A Ks R F hB hPr (tupT μ) (R.jX (tupT μ) (rowForm A F.P0 F.ψ0 (tupT μ) x))
      (R.jX (tupT μ) (rowForm A F.P0 F.ψ0 (tupT μ) y))
    have h3 := GlobalTheory.T.hilbert_inner_rowForms_eq_level_class_sum D G Pl0 T A Ks R F hB false (tupT μ) x y
    have e1 : ((((∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)) / (1 : ℝ) : ℝ) : ℂ)) =
        (((∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)) : ℝ) : ℂ) :=
      congrArg (fun r : ℝ => (r : ℂ)) (div_one (∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)))
    refine Eq.trans ?_ h3
    show (((RealDat.nP F false)⁻¹ : ℝ) : ℂ) * ((((∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)) / (1 : ℝ) : ℝ) : ℂ) *
        ipMT R.MX (R.νX (tupT μ)) (R.fdX (tupT μ))
          (R.cX.toMap R.prX ((R.HX (tupT μ)).e (R.jX (tupT μ) (rowForm A F.P0 F.ψ0 (tupT μ) x))))
          (R.cX.toMap R.prX ((R.HX (tupT μ)).e (R.jX (tupT μ) (rowForm A F.P0 F.ψ0 (tupT μ) y))))) = _
    exact congrArg (fun z : ℂ => (((RealDat.nP F false)⁻¹ : ℝ) : ℂ) * z) ((congrArg (· * _) e1).trans h1)
  · have h5 := GlobalTheory.T.hilbert_inner_liftForms_eq_base_level_hermitian D G Pl0 T A Ks R F hB i (tupT μ) x y
    refine Eq.trans ?_ h5
    show (((RealDat.nP F false)⁻¹ : ℝ) : ℂ) * ipVia (R.extV i (tupT μ))
      (R.extV i (tupT μ) (R.jV i (tupT μ) (liftForm A F.P0 F.ψ0 i (tupT μ) x)))
      (R.extV i (tupT μ) (R.jV i (tupT μ) (liftForm A F.P0 F.ψ0 i (tupT μ) y))) = _
    exact congrArg (fun z : ℂ => (((RealDat.nP F false)⁻¹ : ℝ) : ℂ) * z) (ipVia_self _ (hinj i (tupT μ)) _ _)

end GlobalTheory.TopNorm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassSumsEqPairingsTopChainLiftsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classSums_eq_pairings_topChain_lifts : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R) (hinj : ∀ i t, Function.Injective (R.extV i t)), R.BaseW F → Seed.PrIso R.MX R.cX R.prX → A.fam.Ok 1 → let C := toChainReal R F tupT hm hTop; let L := toLiftReal R F tupT hm hTop hinj; ∀ μ : D.what₂.Tup, (let a := fun x => R.cX.toMap R.prX ((R.HX (tupT μ)).e (R.jX (tupT μ) (rowForm A F.P1 F.ψ1 (tupT μ) x))); Submodule.span ℂ (Set.range a) = C.CCXP true μ ∧ ∀ x y, C.ipXP true μ (a x) (a y) = D.what₂.embLL (Formalism.DivisionValues.hform (rH D A F.P1 F.ψ1 (tupT μ)) x y)) ∧ (let a := fun x => R.cX.toMap R.prX ((R.HX (tupT μ)).e (R.jX (tupT μ) (rowForm A F.P0 F.ψ0 (tupT μ) x))); Submodule.span ℂ (Set.range a) = C.CCXP false μ ∧ ∀ x y, C.ipXP false μ (a x) (a y) = D.what₂.embLL (Formalism.DivisionValues.hform (rH D A F.P0 F.ψ0 (tupT μ)) x y)) ∧ ∀ i : Fin D.R.m, (let a := fun x => R.extV i (tupT μ) (R.jV i (tupT μ) (liftForm A F.P0 F.ψ0 i (tupT μ) x)); Submodule.span ℂ (Set.range a) = L.Amt μ i ∧ ∀ x y, L.ipA μ i (a x) (a y) = D.what₂.embLL (Formalism.DivisionValues.hform (lH D A F.P0 F.ψ0 i (tupT μ)) x y)) := by
  first | exact @GlobalTheory.TopNorm.classSums_topNorm | exact GlobalTheory.TopNorm.classSums_topNorm | (intros; apply GlobalTheory.TopNorm.classSums_topNorm <;> assumption)
end

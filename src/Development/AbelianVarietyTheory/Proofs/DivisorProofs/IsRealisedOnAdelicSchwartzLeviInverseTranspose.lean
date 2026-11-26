module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EOpEqAsAlgebraHom
public import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OneMeasureSizes
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyAdicIntegralSpanClosedMulStar

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRealisedOnAdelicSchwartzLeviInverseTranspose
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRealisedOnAdelicSchwartzLeviInverseTranspose
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicSvN
open scoped Matrix

namespace GlobalTheory.AdelicSvNLevi

open scoped Classical

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] [DecidableEq κ]

def qI (F : Type) [Field F] [NumberField F] : F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp
    ((RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).comp (algebraMap F (AdeleRing (𝓞 F) F)))

def qF (F : Type) [Field F] [NumberField F] : F →+* FiniteAdeleRing (𝓞 F) F :=
  (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).comp (algebraMap F (AdeleRing (𝓞 F) F))

def compM (P : Matrix κ κ F) : ((κ → AdeleRing (𝓞 F) F) → ℂ) →ₗ[ℂ] ((κ → AdeleRing (𝓞 F) F) → ℂ) :=
  LinearMap.funLeft ℂ ℂ (fun x => P.map (algebraMap F (AdeleRing (𝓞 F) F)) *ᵥ x)

theorem compM_apply (P : Matrix κ κ F) (φ : (κ → AdeleRing (𝓞 F) F) → ℂ) (x : κ → AdeleRing (𝓞 F) F) :
    compM P φ x = φ (P.map (algebraMap F (AdeleRing (𝓞 F) F)) *ᵥ x) := rfl

def archEquiv (P Q : Matrix κ κ F) (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    (κ → mixedEmbedding.mixedSpace F) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F) where
  toFun y := P.map (qI F) *ᵥ y
  invFun y := Q.map (qI F) *ᵥ y
  map_add' y y' := Matrix.mulVec_add _ _ _
  map_smul' r y := by rw [RingHom.id_apply, Matrix.mulVec_smul]
  left_inv y := by
    simp only [Matrix.mulVec_mulVec, ← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  right_inv y := by
    simp only [Matrix.mulVec_mulVec, ← Matrix.map_mul, hPQ, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

def finHomeo (P Q : Matrix κ κ F) (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    (κ → FiniteAdeleRing (𝓞 F) F) ≃ₜ (κ → FiniteAdeleRing (𝓞 F) F) where
  toFun z := P.map (qF F) *ᵥ z
  invFun z := Q.map (qF F) *ᵥ z
  left_inv z := by
    simp only [Matrix.mulVec_mulVec, ← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  right_inv z := by
    simp only [Matrix.mulVec_mulVec, ← Matrix.map_mul, hPQ, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

theorem comp_pureA (P Q : Matrix κ κ F) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    compM P (pureA F f g) =
      pureA F (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (archEquiv P Q hPQ hQP) f) (g ∘ finHomeo P Q hPQ hQP) := by
  funext x
  let q : AdeleRing (𝓞 F) F →+* mixedEmbedding.mixedSpace F :=
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
  let p : AdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 F) F := RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
  have h1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F
      ((P.map (algebraMap F (AdeleRing (𝓞 F) F)) *ᵥ x) i).1) =
      P.map (qI F) *ᵥ (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) := by
    funext i
    change q ((P.map (algebraMap F (AdeleRing (𝓞 F) F)) *ᵥ x) i) = _
    rw [RingHom.map_mulVec, Matrix.map_map]
    rfl
  have h2 : (fun i => ((P.map (algebraMap F (AdeleRing (𝓞 F) F)) *ᵥ x) i).2) =
      P.map (qF F) *ᵥ (fun i => (x i).2) := by
    funext i
    change p ((P.map (algebraMap F (AdeleRing (𝓞 F) F)) *ᵥ x) i) = _
    rw [RingHom.map_mulVec, Matrix.map_map]
    rfl
  simp only [compM_apply, pureA, Function.comp_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  rw [h1, h2]
  rfl

theorem comp_mem (P Q : Matrix κ κ F) (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    ∀ φ ∈ schA F κ, compM P φ ∈ schA F κ := by
  have hle : schA F κ ≤ (schA F κ).comap (compM P) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, g, hg, rfl⟩
    refine Submodule.subset_span ⟨_, _, ⟨hg.1.comp_continuous (finHomeo P Q hPQ hQP).continuous,
      hg.2.comp_homeomorph (finHomeo P Q hPQ hQP)⟩, comp_pureA P Q hPQ hQP f g⟩
  exact fun φ hφ => hle hφ

theorem act_levi {K R ι : Type} [Field K] [CommRing R] [Algebra K R] [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι K)
    (w : (ι → R) × (ι → R)) :
    AdelicSvN.act (Matrix.fromBlocks A 0 0 B) w = (A.map (algebraMap K R) *ᵥ w.1, B.map (algebraMap K R) *ᵥ w.2) := by
  have h0 : (0 : Matrix ι ι K).map (algebraMap K R) = 0 := Matrix.map_zero _ (map_zero _)
  simp only [AdelicSvN.act, Matrix.fromBlocks_map, h0, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
    Matrix.zero_mulVec, add_zero, zero_add]

theorem dot_transpose {R ι : Type} [CommRing R] [Fintype ι] (M : Matrix ι ι R) (x v : ι → R) :
    x ⬝ᵥ (Mᵀ *ᵥ v) = (M *ᵥ x) ⬝ᵥ v := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem realised_levi : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (κ : Type) [Fintype κ]
    [DecidableEq κ] (A : Matrix κ κ F), IsUnit A.det → Realised ψ (Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ) := by
  intro F _ _ ψ κ _ _ A hA
  have h1 : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hA
  have h2 : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hA
  let Am : Matrix κ κ (AdeleRing (𝓞 F) F) := A.map (algebraMap F (AdeleRing (𝓞 F) F))
  let Aim : Matrix κ κ (AdeleRing (𝓞 F) F) := A⁻¹.map (algebraMap F (AdeleRing (𝓞 F) F))
  have e1 : Am * Aim = 1 := by
    rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  have e2 : Aim * Am = 1 := by
    rw [← Matrix.map_mul, h2, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨compM A⁻¹, comp_mem A⁻¹ A h2 h1, fun φ hφ => ⟨compM A φ, comp_mem A A⁻¹ h1 h2 φ hφ, ?_⟩,
    fun l hl => ⟨l ∘ₗ compM A⁻¹, fun g hg => ?_, fun _ _ => rfl⟩, fun w φ _ => funext fun x => ?_⟩
  · funext x
    change φ (Am *ᵥ (Aim *ᵥ x)) = φ x
    rw [Matrix.mulVec_mulVec, e1, Matrix.one_mulVec]
  · obtain ⟨T, hT⟩ := hl _ ⟨hg.1.comp_continuous (finHomeo A⁻¹ A h2 h1).continuous,
      hg.2.comp_homeomorph (finHomeo A⁻¹ A h2 h1)⟩
    refine ⟨T.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (archEquiv A⁻¹ A h2 h1)), fun f => ?_⟩
    rw [LinearMap.comp_apply, comp_pureA A⁻¹ A h2 h1, hT]
    rfl
  · rw [act_levi, Matrix.transpose_map]
    change ψ ((Aim *ᵥ x) ⬝ᵥ w.2 + ⅟(2 : AdeleRing (𝓞 F) F) * (w.1 ⬝ᵥ w.2)) * φ (Aim *ᵥ x + w.1) =
      ψ (x ⬝ᵥ (Aimᵀ *ᵥ w.2) + ⅟(2 : AdeleRing (𝓞 F) F) * ((Am *ᵥ w.1) ⬝ᵥ (Aimᵀ *ᵥ w.2))) *
        φ (Aim *ᵥ (x + Am *ᵥ w.1))
    rw [dot_transpose, dot_transpose, Matrix.mulVec_add, Matrix.mulVec_mulVec, e2, Matrix.one_mulVec]

end GlobalTheory.AdelicSvNLevi

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRealisedOnAdelicSchwartzLeviInverseTransposeStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicSvN
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRealisedOnAdelicSchwartz_levi_inverseTranspose : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (κ : Type) [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ F), IsUnit A.det → Realised ψ (Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ) := by
  first | exact @GlobalTheory.AdelicSvNLevi.realised_levi | exact GlobalTheory.AdelicSvNLevi.realised_levi | (intros; apply GlobalTheory.AdelicSvNLevi.realised_levi <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyFiniteTypeIndexOfRowsPos
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyFiniteTypeIndexOfRowsPos
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

noncomputable section

namespace GlobalTheory.Div

theorem nonempty_ix_of_pos : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m s : ℕ} (A3 : FamIn3 K G Pl0 I0 Ty T m) (P : Subgroup G) (ψ : P →* Kˣ) (Zs : DefSub A3.fam3.amb3), A3.fam3.Ok3 s → Zs.InBlock → (A3.side3 P ψ Zs).Pos → Nonempty A3.fam3.base3.Ix := by
  intro K _ _ _ G _ _ Pl0 I0 Ty T m s A3 P ψ Zs hOk hin hpos
  by_contra hne
  have hfalse : ∀ x, ¬ A3.fam3.IsType3 (A3.fam3.RI A3.fam3.F.μ0) id x := by
    rintro x ⟨p, hp, -⟩
    exact hne ⟨⟨p, hp⟩⟩
  have hsame := A3.fam3.sameTypes_base3 hOk P ψ hin
  have hbot : Formalism.L2.Col.eigSum (A3.fam3.RI A3.fam3.F.μ0).opAll
      (A3.fam3.IsType3 (A3.fam3.RI A3.fam3.F.μ0) id) = ⊥ := by
    unfold Formalism.L2.Col.eigSum
    simp [hfalse]
  rw [hbot, BlockDat.good_part_coordinates_bot, le_bot_iff] at hsame
  unfold FamIn3.side3 DefFam3.side3 DefSide.Pos at hpos
  simp only [BlockDat.dZ, subDim] at hpos
  rw [hsame] at hpos
  simp at hpos

end GlobalTheory.Div
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyFiniteTypeIndexOfRowsPosStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_finite_type_index_of_rows_pos : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m s : ℕ} (A3 : FamIn3 K G Pl0 I0 Ty T m) (P : Subgroup G) (ψ : P →* Kˣ) (Zs : DefSub A3.fam3.amb3), A3.fam3.Ok3 s → Zs.InBlock → (A3.side3 P ψ Zs).Pos → Nonempty A3.fam3.base3.Ix := by
  first | exact @GlobalTheory.Div.nonempty_ix_of_pos | exact GlobalTheory.Div.nonempty_ix_of_pos | (intros; apply GlobalTheory.Div.nonempty_ix_of_pos <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeComplexPointsLevelFormsEqGoodForms
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeComplexPointsLevelFormsEqGoodForms
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

noncomputable section

namespace GlobalTheory.LevelRange

theorem range_w0C_eq : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.LUnif → ∀ b i, LinearMap.range ((R.toCx3 F).w0C b i) = Tw.sub (twAt D.what₂.embLL A3.A.v0) ((R.toRealDat.Wat i (sg0 D A3.A) (R.toRealDat.levL F.lv2 b (sg0 D A3.A))).comap (R.HW i (sg0 D A3.A)).e) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hC hU b i
  have hL := GlobalTheory.LevelForms.levelW_of_irr R.toRealDat F.lv2 hOk.ok2.irr hU hC.base.models.HW
  rw [← hL b i (sg0 D A3.A)]
  have h3 : Submodule.span ℂ (Set.range fun k => (⟨R.toRealDat.bC F.lv2 b i (sg0 D A3.A) k, Submodule.subset_span ⟨k, rfl⟩⟩ :
      R.toRealDat.WS F.lv2 b i (sg0 D A3.A))) = ⊤ := Submodule.span_range_subtype_eq_top_iff _ _ |>.2 rfl
  have h4 : LinearMap.range ((R.toCx3 F).wC b i A3.A.v0) = ⊤ :=
    (Fintype.range_linearCombination _ _).trans (Tw.span_top (E := R.toRealDat.WS F.lv2 b i (sg0 D A3.A)) _ h3)
  have hc : ((Real.sqrt (RealDat.nP F.lv2 b) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (RealDat.nP_pos (F := F.lv2) b)).ne'
  refine (LinearMap.range_comp_of_range_eq_top _ h4).trans (le_antisymm ?_ fun x hx => ?_)
  · rintro _ ⟨y, rfl⟩
    exact (R.toRealDat.WS F.lv2 b i (sg0 D A3.A)).smul_mem _ (Tw.out y : R.toRealDat.WS F.lv2 b i (sg0 D A3.A)).2
  · let y : (R.HW i (sg0 D A3.A)).H := x
    exact ⟨(⟨((Real.sqrt (RealDat.nP F.lv2 b) : ℝ) : ℂ)⁻¹ • y, (R.toRealDat.WS F.lv2 b i (sg0 D A3.A)).smul_mem _ hx⟩ :
      R.toRealDat.WS F.lv2 b i (sg0 D A3.A)), smul_inv_smul₀ hc y⟩

end GlobalTheory.LevelRange
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeComplexPointsLevelFormsEqGoodFormsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.range_complex_points_level_forms_eq_good_forms : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.LUnif → ∀ b i, LinearMap.range ((R.toCx3 F).w0C b i) = Tw.sub (twAt D.what₂.embLL A3.A.v0) ((R.toRealDat.Wat i (sg0 D A3.A) (R.toRealDat.levL F.lv2 b (sg0 D A3.A))).comap (R.HW i (sg0 D A3.A)).e) := by
  first | exact @GlobalTheory.LevelRange.range_w0C_eq | exact GlobalTheory.LevelRange.range_w0C_eq | (intros; apply GlobalTheory.LevelRange.range_w0C_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCoordinateWedgeLinearIndependentSpanEqTop
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCoordinateWedgeLinearIndependentSpanEqTop
open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory.LogDR

theorem ofCard_symm_apply_eq_sort {n : ℕ} (s : Finset (Fin n)) (k : ℕ) (hk : k < s.card) :
    Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard (rfl : s.card = s.card)) ⟨k, hk⟩ =
      (s.sort (· ≤ ·))[k]'(by rw [Finset.length_sort]; exact hk) := by
  show s.orderEmbOfFin rfl ⟨k, hk⟩ = _
  rw [Finset.orderEmbOfFin_apply]
  rfl

noncomputable def dlogBasis {K : Type} [Field K] {n : ℕ} (x : Fin n → Kˣ) (hx : IsCoord x) :
    Module.Basis (Fin n) K Ω[K⁄ℤ] :=
  (Module.Basis.mk hx.1 (by rw [hx.2])).unitsSMul fun i => (x i)⁻¹

theorem dlogBasis_apply {K : Type} [Field K] {n : ℕ} (x : Fin n → Kˣ) (hx : IsCoord x) (i : Fin n) :
    dlogBasis x hx i = dlog (x i) := by
  rw [dlogBasis, Module.Basis.unitsSMul_apply, Module.Basis.mk_apply, Units.smul_def]
  rfl

theorem logWedge_eq_basis {K : Type} [Field K] {n : ℕ} (x : Fin n → Kˣ) (hx : IsCoord x) :
    logWedge x = ⇑(dlogBasis x hx).ExteriorAlgebra := by
  funext s
  rw [ExteriorAlgebra.basis_apply_ofCard _ rfl, ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_apply,
    logWedge]
  congr 1
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    simp only [List.getElem_map, List.getElem_ofFn, Function.comp_apply, dlogBasis_apply]
    rw [ofCard_symm_apply_eq_sort]

theorem logWedge_basis : ∀ (K : Type) [Field K] (n : ℕ) (x : Fin n → Kˣ), IsCoord x →
    LinearIndependent K (logWedge x) ∧ Submodule.span K (Set.range (logWedge x)) = ⊤ := by
  intro K _ n x hx
  rw [logWedge_eq_basis x hx]
  exact ⟨(dlogBasis x hx).ExteriorAlgebra.linearIndependent, (dlogBasis x hx).ExteriorAlgebra.span_eq⟩

end GlobalTheory.LogDR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCoordinateWedgeLinearIndependentSpanEqTopStatement
open GlobalTheory GlobalTheory.LogDR

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logCoordinateWedge_linearIndependent_span_eq_top : ∀ (K : Type) [Field K] (n : ℕ) (x : Fin n → Kˣ), IsCoord x → LinearIndependent K (logWedge x) ∧ Submodule.span K (Set.range (logWedge x)) = ⊤ := by
  first | exact @GlobalTheory.LogDR.logWedge_basis | exact GlobalTheory.LogDR.logWedge_basis | (intros; apply GlobalTheory.LogDR.logWedge_basis <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaAtOfIsEtaConj
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open Formalism.L2.JoinChr
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EtaConjLocal

section Field

variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))

theorem val_unif : P.valuation E ((Formalism.L2.Host.unif P : Eˣ) : E) = WithZero.exp (-1 : ℤ) := by
  have h := Formalism.L2.Host.unif_spec P
  rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact h

theorem mk_unit {u : E} (hu : P.valuation E u = 1) : FinitePlace.mk P u = 1 := by
  rw [FinitePlace.mk_apply, FinitePlace.norm_embedding, NumberField.HeightOneSpectrum.adicAbv_def, hu]
  simp

theorem mk_unif : FinitePlace.mk P ((Formalism.L2.Host.unif P : Eˣ) : E) = ((Ideal.absNorm P.asIdeal : ℕ) : ℝ)⁻¹ := by
  rw [FinitePlace.mk_apply, FinitePlace.norm_embedding, NumberField.HeightOneSpectrum.adicAbv_def, val_unif,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  simp

end Field

variable {D : D7}

noncomputable def locHom {e : AE D} (he : e * e = e) : D.host.Eˣ →* (AE D)ˣ where
  toFun := locU he
  map_one' := Units.ext (by rw [locU_val]; simp [locE])
  map_mul' k l := Units.ext (by rw [Units.val_mul, locU_val, locU_val, locU_val, locE_mul_locE he, Units.val_mul])

theorem locE_parts {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)} (he : IsPlIdem D e P) (u : D.host.E)
    (hu : P.valuation D.host.E u ≤ 1) : infPart D (locE D e u) = 1 ∧ finPart D (locE D e u) ∈ intAE D := by
  obtain ⟨ι, hι, hint, -⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.HeckeTensorRead.isPlIdem_parts D ι hι hint he
  refine ⟨(GlobalTheory.HeckeTensorRead.map_loc (infPart D) e _).trans (by rw [h1, zero_mul, add_zero]), ?_⟩
  rw [hint]
  intro Q
  have h4 : ι (finPart D (incA D u)) = algebraMap D.host.E _ u := hι u
  have h5 : ι (finPart D (locE D e u)) = 1 + ι (finPart D e) * (ι (finPart D (incA D u)) - 1) :=
    GlobalTheory.HeckeTensorRead.map_loc (ι.toRingHom.comp (finPart D)) e _
  rw [h5, h4]
  change Valued.v (1 + ι (finPart D e) Q * (algebraMap D.host.E (Q.adicCompletion D.host.E) u - 1)) ≤ 1
  by_cases hQ : Q = P
  · subst hQ
    rw [h2, one_mul, add_sub_cancel]
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' Q u).trans_le hu
  · rw [h3 Q hQ]
    simp

end GlobalTheory.EtaConjLocal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockSphereMeanEqOfFrameNormEq
set_option autoImplicit false

noncomputable section

open MvPolynomial NumberField Module GlobalTheory.ChowHt GlobalTheory.CompHt MeasureTheory

namespace GlobalTheory.SphereMeanFrame

set_option autoImplicit false in
open MvPolynomial NumberField Module MeasureTheory in
theorem _root_.GlobalTheory.SphereMeanFrame.eval_linSubst {B N n : ℕ} (M : Matrix (Fin N) (Fin n) ℂ)
    (f : MvPolynomial (Fin B × Fin N) ℂ) (u : Fin B × Fin n → ℂ) :
    eval u (_root_.GlobalTheory.ChowHt.linSubst M f) =
      eval (fun p : Fin B × Fin N => ∑ k, M p.2 k * u (p.1, k)) f := by
  unfold _root_.GlobalTheory.ChowHt.linSubst
  rw [_root_.ReciprocityTheory.MultiplicativeHeights.eval_aeval_alt]
  simp


set_option autoImplicit false in
open MvPolynomial NumberField Module MeasureTheory in
theorem _root_.GlobalTheory.SphereMeanFrame.blockSphereMean_linSubst {B N : ℕ} (Q : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (hQ : ∀ x : EuclideanSpace ℂ (Fin (N + 1)), ‖Matrix.toEuclideanLin Q x‖ = ‖x‖)
    (f : MvPolynomial (Fin B × Fin (N + 1)) ℂ) :
    _root_.ReciprocityTheory.MultiplicativeHeights.blockSphereMean B (N + 1) (_root_.GlobalTheory.ChowHt.linSubst Q f) = _root_.ReciprocityTheory.MultiplicativeHeights.blockSphereMean B (N + 1) f := by
  let T : EuclideanSpace ℂ (Fin (N + 1)) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (N + 1)) :=
    { toLinearMap := Matrix.toEuclideanLin Q, norm_map' := hQ }
  let U := T.toLinearIsometryEquiv rfl
  let V : EuclideanSpace ℂ (Fin (N + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin (N + 1)) :=
    { toLinearEquiv := U.toLinearEquiv.restrictScalars ℝ, norm_map' := U.norm_map }
  set μ : Measure (Fin B → _root_.ReciprocityTheory.MultiplicativeHeights.UnitSphereC (N + 1)) := Measure.pi fun _ => _root_.ReciprocityTheory.MultiplicativeHeights.sphereProb (N + 1) with hμ
  set Φ : (Fin B → _root_.ReciprocityTheory.MultiplicativeHeights.UnitSphereC (N + 1)) → (Fin B → _root_.ReciprocityTheory.MultiplicativeHeights.UnitSphereC (N + 1)) :=
    fun z b => _root_.ReciprocityTheory.MultiplicativeHeights.sphereMap V (z b) with hΦdef
  have hΦ : MeasurePreserving Φ μ μ := measurePreserving_pi _ _ (fun _ => _root_.ReciprocityTheory.MultiplicativeHeights.measurePreserving_sphereMap V)
  set g : (Fin B → _root_.ReciprocityTheory.MultiplicativeHeights.UnitSphereC (N + 1)) → ℝ := fun z => Real.log ‖eval (_root_.ReciprocityTheory.MultiplicativeHeights.blockPoint z) f‖ with hg
  have hcont : Continuous (fun z : Fin B → _root_.ReciprocityTheory.MultiplicativeHeights.UnitSphereC (N + 1) => _root_.ReciprocityTheory.MultiplicativeHeights.blockPoint z) := by
    unfold _root_.ReciprocityTheory.MultiplicativeHeights.blockPoint
    exact continuous_pi fun p => (continuous_apply p.2).comp
      ((_root_.ReciprocityTheory.MultiplicativeHeights.continuous_spherePoint (N + 1)).comp (continuous_apply p.1))
  have hgm : Measurable g :=
    Real.measurable_log.comp (((MvPolynomial.continuous_eval f).comp hcont).norm.measurable)
  have hpt : ∀ z, eval (_root_.ReciprocityTheory.MultiplicativeHeights.blockPoint z) (_root_.GlobalTheory.ChowHt.linSubst Q f) = eval (_root_.ReciprocityTheory.MultiplicativeHeights.blockPoint (Φ z)) f := by
    intro z
    rw [_root_.GlobalTheory.SphereMeanFrame.eval_linSubst]
    congr 1
  change ∫ z, Real.log ‖eval (_root_.ReciprocityTheory.MultiplicativeHeights.blockPoint z) (_root_.GlobalTheory.ChowHt.linSubst Q f)‖ ∂μ = ∫ z, g z ∂μ
  simp_rw [hpt]
  change ∫ z, g (Φ z) ∂μ = ∫ z, g z ∂μ
  rw [← integral_map hΦ.measurable.aemeasurable hgm.aestronglyMeasurable, hΦ.map_eq]


set_option autoImplicit false in
open MvPolynomial NumberField Module MeasureTheory in
theorem _root_.GlobalTheory.SphereMeanFrame.blockSphereMean_eq_of_frameNorm_eq : ∀ (B N : ℕ) (A A' : Matrix (Fin N) (Fin N) ℂ),
    A.det ≠ 0 → A'.det ≠ 0 → (∀ z, _root_.GlobalTheory.ChowHt.frameNorm A z = _root_.GlobalTheory.ChowHt.frameNorm A' z) →
    ∀ f : MvPolynomial (Fin B × Fin N) ℂ,
      _root_.ReciprocityTheory.MultiplicativeHeights.blockSphereMean B N (_root_.GlobalTheory.ChowHt.linSubst A f) = _root_.ReciprocityTheory.MultiplicativeHeights.blockSphereMean B N (_root_.GlobalTheory.ChowHt.linSubst A' f) := by
  intro B N A A' hA hA' hn f
  cases N with
  | zero =>
    have hAA : A = A' := Subsingleton.elim _ _
    rw [hAA]
  | succ N =>
    have hAu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
    have hA'u : IsUnit A'.det := isUnit_iff_ne_zero.mpr hA'
    have hAQ : A * (A⁻¹ * A') = A' := by
      rw [← mul_assoc, Matrix.mul_nonsing_inv _ hAu, one_mul]
    have key : _root_.GlobalTheory.ChowHt.linSubst A' f =
        _root_.GlobalTheory.ChowHt.linSubst (A⁻¹ * A') (_root_.GlobalTheory.ChowHt.linSubst A f) := by
      rw [_root_.GlobalTheory.HeightUnique.linSubst_linSubst, hAQ]
    rw [key, _root_.GlobalTheory.SphereMeanFrame.blockSphereMean_linSubst (A⁻¹ * A')]
    intro x
    have h1 := hn (A'.mulVec x.ofLp)
    simp only [_root_.GlobalTheory.ChowHt.frameNorm, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA'u,
      Matrix.one_mulVec] at h1
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    convert h1 using 4 with i
    rfl

end GlobalTheory.SphereMeanFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedAutomorphicHasRepresentative
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedAutomorphicHasRepresentative
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict.RepresentativeL2

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  {Γ : Subgroup G} [Countable Γ] {μ : Measure G} {𝓕 : Set G}

theorem meas_mk : Measurable (Quotient.mk (QuotientGroup.rightRel Γ)) := measurable_quotient_mk''

theorem ae_up [μ.IsMulLeftInvariant] (h : IsFundamentalDomain Γ 𝓕 μ) {p : Quotient (QuotientGroup.rightRel Γ) → Prop}
    (hp : ∀ᵐ q ∂((μ.restrict 𝓕).map (Quotient.mk (QuotientGroup.rightRel Γ))), p q) :
    ∀ᵐ x ∂μ, p (Quotient.mk _ x) := by
  have h1 := ae_of_ae_map (meas_mk (Γ := Γ)).aemeasurable hp
  rw [ae_iff, Measure.restrict_apply₀' h.nullMeasurableSet] at h1
  rw [ae_iff]
  refine h.measure_zero_of_invariant _ (fun g => ?_) h1
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  have : (Quotient.mk (QuotientGroup.rightRel Γ) (g⁻¹ • x)) = Quotient.mk _ x := by
    refine Quotient.sound (QuotientGroup.rightRel_apply.2 ?_)
    simp [Subgroup.smul_def]
  simp only [Set.mem_setOf_eq, this]

end General

theorem repr_properties : ∀ (D : D7) (V : HSp D), ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (ρ : GA D V →* (Lp ℂ 2 (nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (nuQ V μ 𝓕))), FinPair V μ 𝓕 → IsReg V μ 𝓕 ρ → (∀ φ : GA D V → ℂ, Continuous φ → (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) → (∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C) → ∃ F, Repr V μ 𝓕 F φ) ∧ (∀ F ψ ψ', Continuous ψ → Continuous ψ' → Repr V μ 𝓕 F ψ → Repr V μ 𝓕 F ψ' → ψ = ψ') ∧ (∀ F F' ψ, Repr V μ 𝓕 F ψ → Repr V μ 𝓕 F' ψ → F = F') ∧ (∀ F ψ g, Repr V μ 𝓕 F ψ → Repr V μ 𝓕 (ρ g F) (rTr V g ψ)) ∧ (∀ F F' ψ ψ' (a : ℂ), Repr V μ 𝓕 F ψ → Repr V μ 𝓕 F' ψ' → Repr V μ 𝓕 (a • F + F') (a • ψ + ψ')) ∧ ∀ F F' ψ ψ', Repr V μ 𝓕 F ψ → Repr V μ 𝓕 F' ψ' → IntegrableOn (fun x => star (ψ x) * ψ' x) 𝓕 μ ∧ ⟪F, F'⟫_ℂ = ∫ x in 𝓕, star (ψ x) * ψ' x ∂μ := by
  intro D V μ 𝓕 ρ hp hr
  obtain ⟨-, -, -, hB, hT, -, hC⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hp.haar
  haveI := hp.right
  have hm : Measurable (autMk V) := meas_mk
  haveI : IsFiniteMeasure (nuQ V μ 𝓕) := ⟨by
    rw [nuQ, Measure.map_apply hm MeasurableSet.univ]
    simpa [lt_top_iff_ne_top] using hp.fin⟩
  have up : ∀ {p : AutQ V → Prop}, (∀ᵐ q ∂(nuQ V μ 𝓕), p q) → ∀ᵐ x ∂μ, p (autMk V x) := fun h => ae_up hp.fd h
  refine ⟨fun φ hφ hinv ⟨C, hC⟩ => ?_, fun F ψ ψ' h h' e e' => ?_, fun F F' ψ e e' => ?_, fun F ψ g e => ?_,
    fun F F' ψ ψ' a e e' => ?_, fun F F' ψ ψ' e e' => ?_⟩
  · let f : AutQ V → ℂ := Quotient.lift φ fun a b hab => by
      have := hinv _ (QuotientGroup.rightRel_apply.1 hab) a
      rw [inv_mul_cancel_right] at this
      exact this.symm
    have hf : Measurable f := measurable_from_quotient.2 hφ.measurable
    have hL : MemLp f 2 (nuQ V μ 𝓕) :=
      MemLp.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall fun q => by
        induction q using Quotient.inductionOn with
        | h x => exact hC x)
    exact ⟨hL.toLp f, up hL.coeFn_toLp⟩
  · refine (h.ae_eq_iff_eq μ h').1 ?_
    filter_upwards [e, e'] with x h1 h2
    rw [← h1, h2]
  · refine Lp.ext ?_
    refine (ae_map_iff hm.aemeasurable
      ((Lp.stronglyMeasurable F).measurableSet_eq_fun (Lp.stronglyMeasurable F'))).2 (ae_restrict_of_ae ?_)
    filter_upwards [e, e'] with x h1 h2
    rw [h1, h2]
  · have e2 := (measurePreserving_mul_right μ g).quasiMeasurePreserving.ae e
    filter_upwards [hr.val g F, e2] with x h1 h2
    rw [h1, h2]; rfl
  · filter_upwards [up (Lp.coeFn_add (a • F) F'), up (Lp.coeFn_smul a F), e, e'] with x h1 h2 h3 h4
    rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4]; rfl
  · have hI : Integrable (fun q => ⟪F q, F' q⟫_ℂ) (nuQ V μ 𝓕) := L2.integrable_inner F F'
    have hae : (fun x => ⟪F (autMk V x), F' (autMk V x)⟫_ℂ) =ᵐ[μ.restrict 𝓕] fun x => star (ψ x) * ψ' x := by
      refine ae_restrict_of_ae ?_
      filter_upwards [e, e'] with x h1 h2
      rw [h1, h2]
      simp [mul_comm]
    refine ⟨((integrable_map_measure hI.aestronglyMeasurable hm.aemeasurable).1 hI).congr hae, ?_⟩
    rw [L2.inner_def, ← integral_congr_ae hae]
    exact integral_map hm.aemeasurable hI.aestronglyMeasurable

end GlobalTheory.HolDict.RepresentativeL2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedAutomorphicHasRepresentativeStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_automorphic_has_representative : ∀ (D : D7) (V : HSp D), ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (ρ : GA D V →* (Lp ℂ 2 (nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (nuQ V μ 𝓕))), FinPair V μ 𝓕 → IsReg V μ 𝓕 ρ → (∀ φ : GA D V → ℂ, Continuous φ → (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) → (∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C) → ∃ F, Repr V μ 𝓕 F φ) ∧ (∀ F ψ ψ', Continuous ψ → Continuous ψ' → Repr V μ 𝓕 F ψ → Repr V μ 𝓕 F ψ' → ψ = ψ') ∧ (∀ F F' ψ, Repr V μ 𝓕 F ψ → Repr V μ 𝓕 F' ψ → F = F') ∧ (∀ F ψ g, Repr V μ 𝓕 F ψ → Repr V μ 𝓕 (ρ g F) (rTr V g ψ)) ∧ (∀ F F' ψ ψ' (a : ℂ), Repr V μ 𝓕 F ψ → Repr V μ 𝓕 F' ψ' → Repr V μ 𝓕 (a • F + F') (a • ψ + ψ')) ∧ ∀ F F' ψ ψ', Repr V μ 𝓕 F ψ → Repr V μ 𝓕 F' ψ' → IntegrableOn (fun x => star (ψ x) * ψ' x) 𝓕 μ ∧ ⟪F, F'⟫_ℂ = ∫ x in 𝓕, star (ψ x) * ψ' x ∂μ := by
  first | exact @GlobalTheory.HolDict.RepresentativeL2.repr_properties | exact GlobalTheory.HolDict.RepresentativeL2.repr_properties | (intros; apply GlobalTheory.HolDict.RepresentativeL2.repr_properties <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramSchmidtFlagDomainOrthonormalFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramSchmidtFlagDomainOrthonormalFrames
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical

namespace GlobalTheory.FlagGS

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sgn_mul_self (p a : ℕ) : ((sgn p a : ℝ) : ℂ) * ((sgn p a : ℝ) : ℂ) = 1 := by
  unfold sgn
  split_ifs <;> simp

theorem diag_of_upper {r : ℕ} (s : Fin r → ℂ) (hs : ∀ a, s a * s a = 1) (b : Matrix (Fin r) (Fin r) ℂ)
    (hb : b.BlockTriangular id) (h : bᵀ * diagonal s * b.map (starRingEnd ℂ) = diagonal s) :
    ∃ t : Fin r → ℝ, b = diagonal fun a => Complex.exp ((t a : ℂ) * Complex.I) := by
  have hs0 : ∀ a, s a ≠ 0 := fun a h0 => by simpa [h0] using hs a
  have hss : diagonal s * diagonal s = (1 : Matrix (Fin r) (Fin r) ℂ) := by
    rw [diagonal_mul_diagonal]; simp [hs]
  have h1 : (diagonal s * bᵀ * diagonal s) * b.map (starRingEnd ℂ) = 1 := by
    rw [Matrix.mul_assoc (diagonal s), Matrix.mul_assoc (diagonal s), h, hss]
  have hc : (b.map (starRingEnd ℂ)).BlockTriangular id := fun a c hca => by
    rw [Matrix.map_apply, hb hca, map_zero]
  letI : Invertible (b.map (starRingEnd ℂ)) := invertibleOfLeftInverse _ _ h1
  have hinv := Matrix.blockTriangular_inv_of_blockTriangular hc
  rw [Matrix.inv_eq_left_inv h1] at hinv
  have hoff : ∀ a c, a ≠ c → b a c = 0 := by
    intro a c hac
    rcases lt_or_gt_of_ne hac with hlt | hlt
    · have := hinv (i := c) (j := a) hlt
      rw [mul_diagonal, diagonal_mul, transpose_apply] at this
      simpa [hs0] using this
    · exact hb hlt
  have hd : b = diagonal fun a => b a a := by
    ext a c
    by_cases hac : a = c
    · subst hac; simp
    · rw [diagonal_apply_ne _ hac, hoff a c hac]
  have hn : ∀ a, ‖b a a‖ = 1 := by
    intro a
    have h2 := congrFun (congrFun h a) a
    rw [hd, diagonal_transpose, diagonal_map (map_zero _), diagonal_mul_diagonal, diagonal_mul_diagonal] at h2
    simp only [diagonal_apply_eq] at h2
    have h3 : b a a * starRingEnd ℂ (b a a) = 1 := by
      apply mul_left_cancel₀ (hs0 a)
      linear_combination h2
    have h4 := congrArg norm h3
    rw [norm_mul, Complex.norm_conj, norm_one] at h4
    nlinarith [norm_nonneg (b a a)]
  refine ⟨fun a => Complex.arg (b a a), ?_⟩
  calc
    b = diagonal (fun a => b a a) := hd
    _ = diagonal (fun a => Complex.exp ((Complex.arg (b a a) : ℂ) * Complex.I)) := by
      congr 1
      funext a
      have harg := Complex.norm_mul_exp_arg_mul_I (b a a)
      rw [hn a] at harg
      simpa using harg.symm

theorem exp_keeps {r : ℕ} {H Z : Matrix (Fin r) (Fin r) ℂ} (hH : H * H = 1) (hZ : Zᴴ * H + H * Z = 0) :
    (NormedSpace.exp Z)ᴴ * H * NormedSpace.exp Z = H := by
  have hu : IsUnit H.det := Matrix.isUnit_det_of_left_inverse hH
  have hu' : IsUnit H := (isUnit_iff_isUnit_det H).2 hu
  have e : Zᴴ = H * (-Z) * H⁻¹ := by
    have h1 : Zᴴ * H = -(H * Z) := eq_neg_of_add_eq_zero_left hZ
    rw [mul_neg, ← h1, mul_assoc, mul_nonsing_inv _ hu, mul_one]
  rw [← Matrix.exp_conjTranspose, e, Matrix.exp_conj _ _ hu', mul_assoc _ H⁻¹, nonsing_inv_mul _ hu, mul_one, mul_assoc,
    ← Matrix.exp_add_of_commute _ _ (Commute.refl Z).neg_left, neg_add_cancel, NormedSpace.exp_zero, mul_one]

theorem conj_keeps {r : ℕ} (s : Fin r → ℝ) (g : Matrix (Fin r) (Fin r) ℂ)
    (h : gᴴ * diagonal (fun a => (s a : ℂ)) * g = diagonal fun a => (s a : ℂ)) :
    gᵀ * diagonal (fun a => (s a : ℂ)) * g.map (starRingEnd ℂ) = diagonal fun a => (s a : ℂ) := by
  have h2 := congrArg (fun M : Matrix (Fin r) (Fin r) ℂ => M.map (starRingEnd ℂ)) h
  simp only [Matrix.map_mul, diagonal_map (map_zero (starRingEnd ℂ)), Complex.conj_ofReal] at h2
  have e : gᴴ.map (starRingEnd ℂ) = gᵀ := by
    ext a c; simp [conjTranspose_apply]
  rwa [e] at h2

theorem gram_schmidt_frames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), (∀ y, IsUnitFr X y → y ∈ X.dom) ∧ (∀ x ∈ X.dom, ∃ y, IsUnitFr X y ∧ ∃ b ∈ Bor X.Ψ r, x = rmul y b) ∧ (∀ y, IsUnitFr X y → ∀ b ∈ Bor X.Ψ r, IsUnitFr X (rmul y b) → ∃ t : X.Ψ → Fin r → ℝ, b = (fun τ => (Matrix.diagonal fun a => Complex.exp ((t τ a : ℂ) * Complex.I) : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r)) ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, rmul x b ∈ X.dom) ∧ (∀ y, IsUnitFr X y → ∀ γ ∈ X.Γ, IsUnitFr X (lact γ y)) ∧ (∀ y, IsUnitFr X y → ∀ Z ∈ unitLie X, IsUnitFr X (rmul y (expFr Z))) ∧ ∀ (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) y, IsUnitFr X y → ∀ b ∈ Bor X.Ψ r, P (rmul y b) = bchar la b * P y → X.pnorm la P (rmul y b) = ‖P y‖ := by
  intro E _ _ _ r X
  have hdom : ∀ y, IsUnitFr X y → y ∈ X.dom := fun y hy => ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.orth_mem_dom X hy
  refine ⟨hdom, fun x hx => ?_, fun y hy b hb hyb => ?_,
    fun x hx b hb => ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS.dom_rmul X hx hb, fun y hy γ hγ τ => ?_, fun y hy Z hZ τ => ?_,
    fun la P y hy b hb hP => ?_⟩
  · have hb := FrameDegreeData.bOf_mem X hx
    refine ⟨rmul x (FrameDegreeData.bOf X x), FrameDegreeData.ortho_bOf X hx, fun τ => ((mat (FrameDegreeData.bOf X x) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ),
      fun τ => ?_, ?_⟩
    · have hu : IsUnit (mat (FrameDegreeData.bOf X x) τ).det := isUnit_iff_ne_zero.2 (hb τ).1
      letI := Matrix.invertibleOfIsUnitDet _ hu
      refine ⟨?_, fun a c hca => Matrix.blockTriangular_inv_of_blockTriangular (FrameDegreeData.upper_of_bor X hb τ) hca⟩
      exact (Matrix.isUnit_nonsing_inv_det _ hu).ne_zero
    · funext τ
      have hu : IsUnit (mat (FrameDegreeData.bOf X x) τ).det := isUnit_iff_ne_zero.2 (hb τ).1
      exact (Matrix.mul_nonsing_inv_cancel_right _ (mat x τ) hu).symm
  · have h : ∀ τ : X.Ψ, ∃ t : Fin r → ℝ, mat b τ = diagonal fun a => Complex.exp ((t a : ℂ) * Complex.I) := by
      intro τ
      have h1 := hyb τ
      rw [show mat (rmul y b) τ = mat y τ * mat b τ from rfl, FrameDegreeData.gram_mul, hy τ] at h1
      exact diag_of_upper _ (fun a => sgn_mul_self _ _) _ (FrameDegreeData.upper_of_bor X hb τ) h1
    choose t ht using h
    exact ⟨t, funext fun τ => ht τ⟩
  · rw [ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS.gram_lact X hγ]
    exact hy τ
  · rw [show mat (rmul y (expFr Z)) τ = mat y τ * NormedSpace.exp (mat Z τ) from rfl, FrameDegreeData.gram_mul, hy τ]
    refine conj_keeps _ _ (exp_keeps ?_ (hZ τ))
    rw [diagonal_mul_diagonal]
    simp only [sgn_mul_self]
    exact diagonal_one
  · have hx := hdom y hy
    unfold Data.pnorm
    rw [hP, norm_mul]
    have hbc : ‖bchar la b‖ = ∏ τ, ∏ i, ‖b τ i i‖ ^ la τ i := by
      unfold bchar
      simp only [norm_prod, norm_zpow]
    rw [hbc, mul_comm (∏ τ, ∏ i, ‖b τ i i‖ ^ la τ i) ‖P y‖, mul_assoc, ← Finset.prod_mul_distrib]
    conv_rhs => rw [← mul_one ‖P y‖]
    congr 1
    refine Finset.prod_eq_one fun τ _ => ?_
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [FrameDegreeData.ratio_rmul X y hx hb τ i,
      FrameDegreeData.factor_eq _ _ (norm_pos_iff.2 (FrameDegreeData.bdiag_ne X hb τ i)) (norm_nonneg _), norm_div,
      ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.norm_dmin_orth' X hy, ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.norm_dmin_orth' X hy,
      div_one, Real.one_rpow]

end GlobalTheory.FlagGS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramSchmidtFlagDomainOrthonormalFramesStatement
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gramSchmidt_flagDomain_orthonormalFrames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), (∀ y, IsUnitFr X y → y ∈ X.dom) ∧ (∀ x ∈ X.dom, ∃ y, IsUnitFr X y ∧ ∃ b ∈ Bor X.Ψ r, x = rmul y b) ∧ (∀ y, IsUnitFr X y → ∀ b ∈ Bor X.Ψ r, IsUnitFr X (rmul y b) → ∃ t : X.Ψ → Fin r → ℝ, b = (fun τ => (Matrix.diagonal fun a => Complex.exp ((t τ a : ℂ) * Complex.I) : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r)) ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, rmul x b ∈ X.dom) ∧ (∀ y, IsUnitFr X y → ∀ γ ∈ X.Γ, IsUnitFr X (lact γ y)) ∧ (∀ y, IsUnitFr X y → ∀ Z ∈ unitLie X, IsUnitFr X (rmul y (expFr Z))) ∧ ∀ (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) y, IsUnitFr X y → ∀ b ∈ Bor X.Ψ r, P (rmul y b) = bchar la b * P y → X.pnorm la P (rmul y b) = ‖P y‖ := by
  first | exact @GlobalTheory.FlagGS.gram_schmidt_frames | exact GlobalTheory.FlagGS.gram_schmidt_frames | (intros; apply GlobalTheory.FlagGS.gram_schmidt_frames <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapCentralizerRegularTwistedCentraliser
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapCentralizerRegularTwistedCentraliser
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.CarryCent

theorem commute_of_commute_sep {K : Type} [Field K] {n : ℕ} (N A B : Matrix (Fin n) (Fin n) K)
    (hN : N.charpoly.Separable) (hA : Commute A N) (hB : Commute B N) : Commute A B := by
  obtain ⟨q, rfl⟩ := GlobalTheory.CentralizerSeparable.matrix_eq_aeval_of_commute n N A hN hA
  obtain ⟨q', rfl⟩ := GlobalTheory.CentralizerSeparable.matrix_eq_aeval_of_commute n N B hN hB
  change _ * _ = _ * _
  rw [← map_mul, ← map_mul, mul_comm]

theorem map_coord_commute {K R : Type} [Field K] [CommRing R] [Algebra K R] {n : ℕ}
    (N : Matrix (Fin n) (Fin n) K) (X : Matrix (Fin n) (Fin n) R)
    (hX : Commute X (N.map (algebraMap K R))) (f : R →ₗ[K] K) : Commute (X.map f) N := by
  have k1 : (X * N.map (algebraMap K R)).map f = X.map f * N := by
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.map_apply, Matrix.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  have k2 : (N.map (algebraMap K R) * X).map f = N * X.map f := by
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.map_apply, Matrix.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  have h := congrArg (fun Y => Y.map f) hX.eq
  simp only [k1, k2] at h
  exact h

theorem commute_of_commute_map {K R : Type} [Field K] [CommRing R] [Algebra K R] [Module.Finite K R] {n : ℕ}
    (N : Matrix (Fin n) (Fin n) K) (hN : N.charpoly.Separable) (X Y : Matrix (Fin n) (Fin n) R)
    (hX : Commute X (N.map (algebraMap K R))) (hY : Commute Y (N.map (algebraMap K R))) : Commute X Y := by
  let b := Module.Free.chooseBasis K R
  have dec : ∀ Z : Matrix (Fin n) (Fin n) R, Z = ∑ k, b k • (Z.map (b.coord k)).map (algebraMap K R) := by
    intro Z
    ext i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, Module.Basis.coord_apply, smul_eq_mul]
    conv_lhs => rw [← b.sum_repr (Z i j)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, mul_comm]
  rw [dec X, dec Y]
  refine Commute.sum_left _ _ _ fun k _ => Commute.sum_right _ _ _ fun l _ => ?_
  refine ((Commute.map ?_ (algebraMap K R).mapMatrix).smul_left _).smul_right _
  exact commute_of_commute_sep N _ _ hN (map_coord_commute N X hX _) (map_coord_commute N Y hY _)

variable {p : ℕ} [Fact p.Prime]

theorem commute_of_commute_reg (G : HTGroup p) (r : ℕ) (hr : 0 < r) (γ : Gp G) (hγ : regular₂ G γ) (a b : Gr G r)
    (ha : Commute a (inclG G r γ)) (hb : Commute b (inclG G r γ)) : Commute a b := by
  refine Prod.ext ?_ (funext fun w => ?_)
  · change a.1 * b.1 = b.1 * a.1
    apply Units.ext
    ext i j
    obtain rfl : i = 0 := Subsingleton.elim _ _
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp [Matrix.mul_apply, mul_comm]
  · change a.2 w * b.2 w = b.2 w * a.2 w
    letI : Algebra (G.Fw w) (KQ p (G.Fw w) r) := Algebra.TensorProduct.leftAlgebra
    haveI : FiniteDimensional ℚ_[p] (Qr p r) :=
      ReciprocityTheory.DiscreteGroups.LocalClassField.finiteDimensional_Kn p (Q0 p) inferInstance hr
    haveI : Module.Finite (G.Fw w) (KQ p (G.Fw w) r) :=
      inferInstanceAs (Module.Finite (G.Fw w) ((G.Fw w) ⊗[ℚ_[p]] Qr p r))
    have hw : ∀ x : Gr G r, Commute x (inclG G r γ) →
        Commute (x.2 w : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) r))
          (((γ.2 w : GL (Fin G.n) (G.Fw w)) : Matrix (Fin G.n) (Fin G.n) (G.Fw w)).map
            (algebraMap (G.Fw w) (KQ p (G.Fw w) r))) := by
      intro x hx
      have := congrArg (fun y : Gr G r => ((y.2 w : GL (Fin G.n) (KQ p (G.Fw w) r)) :
        Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) r))) hx.eq
      exact this
    exact Units.ext (commute_of_commute_map _ (hγ w) _ _ (hw a ha) (hw b hb)).eq

end GlobalTheory.CarryCent

namespace GlobalTheory.CarryCent

variable {p : ℕ} [Fact p.Prime]

theorem map_centralizer_carry : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ) (γ : Gp G) (δ z : Gr G r),
    0 < r → regular₂ G γ → IsNrm G r γ δ z →
    (Subgroup.centralizer {γ}).map (carry G r z) = GlobalTheory.BCT.twCent (sigG G r) δ := by
  intro p _ G r γ δ z hr hγ hN
  set δ' := z * δ * (sigG G r z)⁻¹ with hδ'
  have hN' : nrmG (sigG G r) r δ' = inclG G r γ := by
    have h := (GlobalTheory.T.twistedNormConj_normalize_and_degree_one p G).1 r γ δ z hr hN
    simpa [IsNrm] using h
  obtain ⟨hit, hfix, hinj, hrange⟩ := GlobalTheory.T.hermitianTripleFrobeniusTwist_order_fixed_points p G r hr
  have hδc : Commute δ' (inclG G r γ) := by
    have h2 := (GlobalTheory.T.twistedNormProductIterate_twistedConj (sigG G r) r δ' 1).2
    rw [hN', hfix, hit] at h2
    exact h2
  have memT : ∀ h, h ∈ GlobalTheory.BCT.twCent (sigG G r) δ' ↔ ∃ g ∈ Subgroup.centralizer {γ}, inclG G r g = h := by
    intro h
    constructor
    · intro hh
      change h * δ' = δ' * sigG G r h at hh
      have hc : Commute h (inclG G r γ) := by
        have h1 := (GlobalTheory.T.twistedNormProductIterate_twistedConj (sigG G r) r δ' h).1
        have e : h⁻¹ * δ' * sigG G r h = δ' := by rw [mul_assoc, ← hh, inv_mul_cancel_left]
        rw [e, hN', hit] at h1
        change h * inclG G r γ = inclG G r γ * h
        calc h * inclG G r γ = h * (h⁻¹ * inclG G r γ * h) := by rw [← h1]
          _ = inclG G r γ * h := by group
      have hcd : Commute h δ' := commute_of_commute_reg G r hr γ hγ h δ' hc hδc
      have hs : sigG G r h = h := mul_left_cancel (hh.symm.trans hcd.eq)
      obtain ⟨g, rfl⟩ := hrange h hs
      refine ⟨g, ?_, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply hinj
      rw [map_mul, map_mul]
      exact hc.eq
    · rintro ⟨g, hg, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hg
      have hc : Commute (inclG G r g) (inclG G r γ) := by
        change inclG G r g * inclG G r γ = inclG G r γ * inclG G r g
        rw [← map_mul, ← map_mul, hg]
      have hcd := commute_of_commute_reg G r hr γ hγ _ δ' hc hδc
      change inclG G r g * δ' = δ' * sigG G r (inclG G r g)
      rw [hfix]
      exact hcd.eq
  have conjT : ∀ x, x ∈ GlobalTheory.BCT.twCent (sigG G r) δ ↔ z * x * z⁻¹ ∈ GlobalTheory.BCT.twCent (sigG G r) δ' := by
    intro x
    change x * δ = δ * sigG G r x ↔ z * x * z⁻¹ * δ' = δ' * sigG G r (z * x * z⁻¹)
    rw [hδ', map_mul, map_mul, map_inv]
    have e1 : z * x * z⁻¹ * (z * δ * (sigG G r z)⁻¹) = z * (x * δ) * (sigG G r z)⁻¹ := by group
    have e2 : z * δ * (sigG G r z)⁻¹ * (sigG G r z * sigG G r x * (sigG G r z)⁻¹) =
        z * (δ * sigG G r x) * (sigG G r z)⁻¹ := by group
    rw [e1, e2, mul_left_inj, mul_right_inj]
  ext x
  rw [conjT, memT, Subgroup.mem_map]
  refine exists_congr fun g => and_congr_right fun _ => ?_
  change z⁻¹ * inclG G r g * z⁻¹⁻¹ = x ↔ inclG G r g = z * x * z⁻¹
  constructor
  · rintro rfl; group
  · intro e; rw [e]; group

end GlobalTheory.CarryCent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapCentralizerRegularTwistedCentraliserStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_centralizer_regular_twistedCentraliser : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ) (γ : Gp G) (δ z : Gr G r), 0 < r → regular₂ G γ → IsNrm G r γ δ z → (Subgroup.centralizer {γ}).map (carry G r z) = GlobalTheory.BCT.twCent (sigG G r) δ := by
  first | (exact @GlobalTheory.CarryCent.map_centralizer_carry) | (exact GlobalTheory.CarryCent.map_centralizer_carry) | (intros; apply GlobalTheory.CarryCent.map_centralizer_carry  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterTrivialOnSubgroup
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead.PrincLevelSub

private lemma ext1_bot_one_apply {G : Type} [Group G] (x : G) :
    Formalism.L2.DIV.ext1 (⊥ : Subgroup G) (⇑(1 : (⊥ : Subgroup G) →* ℂˣ)) x = 1 := by
  unfold Formalism.L2.DIV.ext1
  split <;> rfl

theorem levChi_triv {D : D7} {T0 : Type} (L : LevCh D T0) (i : Fin D.R.m) (k : GA D (Wc D i)) :
    Lev.levChi (Wc D i) (L.βW i) (L.datWp i L.triv) k = 1 := by
  simp [Lev.levChi, Formalism.L2.DIV.levFn, LevCh.datWp, LevCh.triv, Lev.datY, Formalism.L2.DIV.LevelP.triv,
    ext1_bot_one_apply]
  exact ext1_bot_one_apply _

end GlobalTheory.HolRead.PrincLevelSub
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinPair
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict

theorem exists_finPair : GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ (D : D7) (V : HSp D), ∃ μ 𝓕, FinPair V μ 𝓕 := by
  intro hV D V
  obtain ⟨_, _, _, _⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable V
  have : IsTopologicalGroup (GA D V) :=
    inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  have hμ : (Measure.haar : Measure (GA D V)).IsHaarMeasure := inferInstance
  obtain ⟨hr, 𝓕, h𝓕⟩ := GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V _ hμ
  exact ⟨_, 𝓕, hμ, hr, h𝓕, (GlobalTheory.CuspDecay.measure_lt_top hV V _ 𝓕 hμ h𝓕).ne⟩

end GlobalTheory.HolDict
end

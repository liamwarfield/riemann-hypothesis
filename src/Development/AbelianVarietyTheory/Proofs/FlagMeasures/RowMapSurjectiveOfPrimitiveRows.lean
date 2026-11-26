module

public import Formalism.LocalToGlobal.IndefiniteReal.PrimitivePackageFullHecke
public import Formalism.LocalToGlobal.GroupLattices.JointServices.LevelOperatorFixesImage
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAllTiedPerTied
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TorusNormaliserBessel
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MomentPieriNumericsOfSizeHyps

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowMapSurjectiveOfPrimitiveRows
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimitiveRowsMapBijectiveColumnLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimitiveRowsMapBijectiveColumnLevel
open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Cx NumberField

namespace GlobalTheory

theorem prim_rows_surjective : ∀ (D : D7) [_root_.NumberField.IsTotallyComplex D.what₂.LL] (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (s : ℕ), A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation F → PrimRows3 R F → ∀ (Zs : DefSub A3.fam3.amb3) (S1 : IndefData (A3.side3 F.P1 F.ψ1 Zs)), (R.toCx3 F).zs = Zs → HEq ((R.toCx3 F).data F.cr true) S1 → Function.Surjective ((A3.side3 F.P1 F.ψ1 Zs).Pq A3.A.μ0).mulVec ∧ Function.Surjective (S1.ι A3.A.μ0).mulVec := by
  intro D _ G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hok hsep hW hP Zs S1 hz hS
  subst hz
  have hS' := eq_of_heq hS
  subst hS'
  have hR := complex_data_conditions_base_level_of_primitive_links hok hsep hW hP
  exact ⟨(hR.wf true).Pq_surj _, (CxData.rowMat_bij _ _ true (hR.what₂ true).1 (hR.ratMu true) _).2⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimitiveRowsMapBijectiveColumnLevelStatement
open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Cx NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitiveRows_map_bijective_columnLevel : ∀ (D : D7) [_root_.NumberField.IsTotallyComplex D.what₂.LL] (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (s : ℕ), A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation F → PrimRows3 R F → ∀ (Zs : DefSub A3.fam3.amb3) (S1 : IndefData (A3.side3 F.P1 F.ψ1 Zs)), (R.toCx3 F).zs = Zs → HEq ((R.toCx3 F).data F.cr true) S1 → Function.Surjective ((A3.side3 F.P1 F.ψ1 Zs).Pq A3.A.μ0).mulVec ∧ Function.Surjective (S1.ι A3.A.μ0).mulVec := by
  first | exact @GlobalTheory.prim_rows_surjective | exact GlobalTheory.prim_rows_surjective | (intros; apply GlobalTheory.prim_rows_surjective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.V0MapIotaEqTopDefinite
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowSideIotaMapsFixedColumnsOntoOfMatrices
open Formalism.BasicNotions Formalism.MainNotions

theorem GlobalTheory.rowSide_iota_maps_fixedColumns_onto_of_matrices : ∀ (D : D7) (μ : D.what₂.Tup) (n nV dQ d : ℕ) (jA : (Fin n → D.what₂.LL) →ₛₗ[D.what₂.embLL] (RowSide.sharp D).Amb μ) (E : Matrix (Fin n) (Fin n) D.what₂.LL) (V : Matrix (Fin n) (Fin nV) D.what₂.LL) (Pq : Matrix (Fin dQ) (Fin nV) D.what₂.LL) (ι : Matrix (Fin d) (Fin dQ) D.what₂.LL) (eRR : (Fin d → D.what₂.LL) ≃ₗ[D.what₂.LL] (RowSide.sharp D).RR.V), (∀ x, (RowSide.sharp D).eOp μ (jA x) = jA (E.mulVec x)) → (∀ F, E.mulVec (V.mulVec F) = V.mulVec F) → Function.Surjective Pq.mulVec → Function.Surjective ι.mulVec → (∀ F, (RowSide.sharp D).iota μ (jA (V.mulVec F)) = (RowSide.sharp D).jEE (eRR (ι.mulVec (Pq.mulVec F)))) → (D.what₂.V0 μ).map (D.what₂.iota μ) = ⊤ := by
  intro D μ n nV dQ d jA E V Pq ι eRR hE hV hP hι hio
  have hi : (RowSide.sharp D).iota μ = D.what₂.iota μ := by
    unfold RowSide.iota Rows.Data.iota
    rw [PrimeDegreeVariant.sharp_downTo]
    rfl
  have hV0 : (RowSide.sharp D).V0 μ = D.what₂.V0 μ := rfl
  rw [eq_top_iff, ← (RowSide.sharp D).jEE_basis.2, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  obtain ⟨y, hy⟩ := hι (eRR.symm ((RowSide.sharp D).RR.b i))
  obtain ⟨F, hF⟩ := hP y
  have h1 := hio F
  rw [hF, hy, LinearEquiv.apply_symm_apply, hi] at h1
  refine ⟨jA (V.mulVec F), ?_, h1⟩
  rw [← hV0]
  exact ⟨jA (V.mulVec F), by rw [hE, hV]⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.V0MapIotaEqTopDefinite
open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef NumberField

theorem GlobalTheory.V0_map_iota_eq_top_of_definite : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 Ty T : Type) (m : ℕ) (A3 : FamIn3 D.what₂.LL G Pl0 I0 Ty T m) (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (Ps : Subgroup G) (ψs : Ps →* D.what₂.LLˣ) (Zs : DefSub A3.fam3.amb3) (S0 : IndefData (A3.side3 P0 ψ0 Zs)) (S1 : IndefData (A3.side3 Ps ψs Zs)) (X0 : BaseLevelRowSide D) (Dc : DefCols (A3.side3 Ps ψs Zs)) (Sp : SPer Dc) (C : ColData Dc Sp S1) (NuC : ∀ u, Submodule (𝓞 D.what₂.LL) (Fin (Dc.a u) → D.what₂.LL)) (I : DivisionCompatibilityDataThreeSided D A3 P0 ψ0 Ps ψs Zs S0 S1 X0 Dc), DivDef3 D A3 P0 ψ0 Ps ψs Zs S0 S1 X0 C NuC I → (∃ s, A3.A.fam.Ok s) → Function.Surjective ((A3.side3 Ps ψs Zs).Pq A3.A.μ0).mulVec → Function.Surjective (S1.ι A3.A.μ0).mulVec → (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ := by
  intro D G _ _ Pl0 I0 Ty T m A3 P0 ψ0 Ps ψs Zs S0 S1 X0 Dc Sp C NuC I hD hOk hPq hι
  obtain ⟨s, hs⟩ := hOk

  have key := GlobalTheory.rowSide_iota_maps_fixedColumns_onto_of_matrices D (I.tup A3.A.μ0) _ _ _ _
    (I.jA A3.A.μ0) (rE D A3.A Ps ψs A3.A.μ0) (rV0 D A3.A Ps ψs A3.A.μ0)
    ((A3.side3 Ps ψs Zs).Pq A3.A.μ0) (S1.ι A3.A.μ0) I.eRR
    (fun x => (hD.sharp.forms A3.A.μ0).op_eq x)
    (fun F => Formalism.L2.G.ServJoint.level_operator_fixes_image hs Ps ψs (A3.fam3.toSub2 Zs) A3.A.μ0 F)
    hPq hι (fun F => hD.sharp.iota A3.A.μ0 F)
  rw [hD.tup.mu0] at key
  exact key
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.V0MapIotaEqTopDefiniteStatement
open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.V0_map_iota_eq_top_definite : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 Ty T : Type) (m : ℕ) (A3 : FamIn3 D.what₂.LL G Pl0 I0 Ty T m) (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (Ps : Subgroup G) (ψs : Ps →* D.what₂.LLˣ) (Zs : DefSub A3.fam3.amb3) (S0 : IndefData (A3.side3 P0 ψ0 Zs)) (S1 : IndefData (A3.side3 Ps ψs Zs)) (X0 : BaseLevelRowSide D) (Dc : DefCols (A3.side3 Ps ψs Zs)) (Sp : SPer Dc) (C : ColData Dc Sp S1) (NuC : ∀ u, Submodule (𝓞 D.what₂.LL) (Fin (Dc.a u) → D.what₂.LL)) (I : DivisionCompatibilityDataThreeSided D A3 P0 ψ0 Ps ψs Zs S0 S1 X0 Dc), DivDef3 D A3 P0 ψ0 Ps ψs Zs S0 S1 X0 C NuC I → (∃ s, A3.A.fam.Ok s) → Function.Surjective ((A3.side3 Ps ψs Zs).Pq A3.A.μ0).mulVec → Function.Surjective (S1.ι A3.A.μ0).mulVec → (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ := by
  first | exact @GlobalTheory.V0_map_iota_eq_top_of_definite | exact GlobalTheory.V0_map_iota_eq_top_of_definite | (intros; apply GlobalTheory.V0_map_iota_eq_top_of_definite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowMapSurjectiveOfPrimitiveRows
open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Cx NumberField

namespace GlobalTheory

theorem rowMap_surjective_of_primitiveRows_alt : ∀ (D : D7) [_root_.NumberField.IsTotallyComplex D.what₂.LL] (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (Ps : Subgroup G) (ψs : Ps →* D.what₂.LLˣ) (Zs : DefSub A3.fam3.amb3) (S0 : IndefData (A3.side3 P0 ψ0 Zs)) (S1 : IndefData (A3.side3 Ps ψs Zs)) (X0 : BaseLevelRowSide D) (Dc : DefCols (A3.side3 Ps ψs Zs)) (Sp : SPer Dc) (C : ColData Dc Sp S1) (NuC : ∀ u, Submodule (𝓞 D.what₂.LL) (Fin (Dc.a u) → D.what₂.LL)) (I : DivisionCompatibilityDataThreeSided D A3 P0 ψ0 Ps ψs Zs S0 S1 X0 Dc) (Dcf : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 Ps ψs Zs)) (Spf : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (s : ℕ), DivDef3 D A3 P0 ψ0 Ps ψs Zs S0 S1 X0 C NuC I → A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation (⟨P0, ψ0, Ps, ψs, Dcf, Spf, Zscf⟩ : Face3 D A3) → PrimRows3 R (⟨P0, ψ0, Ps, ψs, Dcf, Spf, Zscf⟩ : Face3 D A3) → (R.toCx3 (⟨P0, ψ0, Ps, ψs, Dcf, Spf, Zscf⟩ : Face3 D A3)).zs = Zs → HEq ((R.toCx3 (⟨P0, ψ0, Ps, ψs, Dcf, Spf, Zscf⟩ : Face3 D A3)).data (⟨P0, ψ0, Ps, ψs, Dcf, Spf, Zscf⟩ : Face3 D A3).cr true) S1 → (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ := by
  intro D _ G _ _ Pl0 I0 T A3 Ks _ _ _ R P0 ψ0 Ps ψs Zs S0 S1 X0 Dc Sp C NuC I Dcf Spf Zscf s hD hOk hSep hW hP hzs hS1
  obtain ⟨h1, h2⟩ := GlobalTheory.T.primitiveRows_map_bijective_columnLevel D G Pl0 I0 T A3 Ks R ⟨P0, ψ0, Ps, ψs, Dcf, Spf, Zscf⟩ s hOk hSep hW hP Zs S1 hzs hS1
  exact GlobalTheory.T.V0_map_iota_eq_top_definite D G Pl0 I0 (List ℕ) T D.R.m A3 P0 ψ0 Ps ψs Zs S0 S1 X0 Dc Sp C NuC I hD ⟨s, hOk.ok2⟩ h1 h2

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowMapSurjectiveOfPrimitiveRowsStatement
open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Cx NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowMap_surjective_of_primitiveRows : ∀ (D : D7) [_root_.NumberField.IsTotallyComplex D.what₂.LL] (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (Ps : Subgroup G) (ψs : Ps →* D.what₂.LLˣ) (Zs : DefSub A3.fam3.amb3) (S0 : IndefData (A3.side3 P0 ψ0 Zs)) (S1 : IndefData (A3.side3 Ps ψs Zs)) (X0 : BaseLevelRowSide D) (Dc : DefCols (A3.side3 Ps ψs Zs)) (Sp : SPer Dc) (C : ColData Dc Sp S1) (NuC : ∀ u, Submodule (𝓞 D.what₂.LL) (Fin (Dc.a u) → D.what₂.LL)) (I : DivisionCompatibilityDataThreeSided D A3 P0 ψ0 Ps ψs Zs S0 S1 X0 Dc) (Dcf : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 Ps ψs Zs)) (Spf : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (s : ℕ), DivDef3 D A3 P0 ψ0 Ps ψs Zs S0 S1 X0 C NuC I → A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation (⟨P0, ψ0, Ps, ψs, Dcf, Spf, Zscf⟩ : Face3 D A3) → PrimRows3 R (⟨P0, ψ0, Ps, ψs, Dcf, Spf, Zscf⟩ : Face3 D A3) → (R.toCx3 (⟨P0, ψ0, Ps, ψs, Dcf, Spf, Zscf⟩ : Face3 D A3)).zs = Zs → HEq ((R.toCx3 (⟨P0, ψ0, Ps, ψs, Dcf, Spf, Zscf⟩ : Face3 D A3)).data (⟨P0, ψ0, Ps, ψs, Dcf, Spf, Zscf⟩ : Face3 D A3).cr true) S1 → (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ := by
  first | exact @GlobalTheory.rowMap_surjective_of_primitiveRows_alt | exact GlobalTheory.rowMap_surjective_of_primitiveRows_alt | (intros; apply GlobalTheory.rowMap_surjective_of_primitiveRows_alt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TorusCommutesWithUnipotent
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TorusCommutesWithUnipotent
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.LocalSetup

theorem exists_seq {k : ℕ} (u : Fin k → ℝ) : ∃ U : ℕ → ℝ, ∀ i : Fin k, U (i.val + 1) = u i :=
  ⟨fun n => if h : n - 1 < k then u ⟨n - 1, h⟩ else 0, fun i => by simp⟩

theorem exists_setup (hH : Hyps) {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [CompleteSpace Wp] [FiniteDimensional ℂ Wp] {lam : Fin (2 * r + k + 1) → ℝ} {u : ℕ → ℝ} {b bv ga h : ℝ} {q0 : ℕ}
    {z : Fin (2 * r + k + 1) → ℂ} {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)}
    {μW μN μG νq : Measure (Mt k r)} {R : (Fin (2 * r + k + 1) → ℤ) → Rep k r}
    (hN : Num k r lam u b bv ga h q0) (hF : IsFam lam q0 R) (hS : SideG k r z π u μW μN μG νq) {c : ℝ} (hc : 0 < c)
    (hd : ∀ (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS (PI.BesselPeriodGGP.eps48 k r) mu →
      ∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH μG R.σ w = c * fdegHC mu) :
    ∃ l : ∀ ν, (R ν).H → Wp,
      Setup lam u b bv ga h q0 z π μW μN μG νq R l (fun ν => c * fdegHC (fun a => lam a + (ν a : ℝ))) := by
  obtain ⟨⟨-, -, -, -, hG⟩, hν⟩ := GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hN
  have h1 : ∀ ν, ∃ l : (R ν).H → Wp, n1 ν ≤ q0 → IsBeL (R ν) z π μW μN l := by
    intro ν
    by_cases hq : n1 ν ≤ q0
    · obtain ⟨l, hl⟩ := GlobalTheory.exists_normalised_bessel_map hH k r _ _ (h / 2) (R ν) Wp _ _ _ _ _ _ _ (hF ν hq)
        (hν ν hq).2.2.1 hG hS
      exact ⟨l, fun _ => hl⟩
    · exact ⟨0, fun h' => absurd h' hq⟩
  choose l hl using h1
  exact ⟨l, hN, hF, hS, fun ν hq => ⟨hl ν hq,
    mul_pos hc (GlobalTheory.FamilyDegreeRatio.degree_ratios k r lam u b bv ga h q0 hN ν hq).1, hd _ _ (hF ν hq)⟩⟩

theorem exists_setup_both : Hyps → ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → 1000 ≤ Cl → ∀ τ w w' θ (W : LocW D.R.k D.R.rS), HypTT D w w' → 0 < θ → GoodW D τ w w' θ W → ∀ t ∈ GG D.R.k D.R.rS, (∀ n, n ∈ Nset D.R.k D.R.rS ↔ t * n * t⁻¹ ∈ Nset D.R.k D.R.rS) → (∀ z, inWb D.R.k D.R.rS z → (∀ h ∈ UWset D.R.k D.R.rS z, t * h = h * t) ∧ ∀ n ∈ Nset D.R.k D.R.rS, psi D.R.k D.R.rS z cStd n = psiS D z (t * n * t⁻¹)) → ∀ R : (Fin (2 * D.R.rS + D.R.k + 1) → ℤ) → Rep D.R.k D.R.rS, IsFam (lamD D τ) (D.R.k * D.R.m ^ 5) R → haveI := FiniteDimensional.complete ℂ W.Wp; haveI := FiniteDimensional.complete ℂ W.Wq; ∃ (U U' : ℕ → ℝ) (l : ∀ ν, (R ν).H → W.Wp) (l' : ∀ ν, (R ν).H → W.Wq) (dg : (Fin (2 * D.R.rS + D.R.k + 1) → ℤ) → ℝ), Setup (lamD D τ) U (large₂.sc.b ^ max 2 Cu) (bOne D τ 1) ((D.R.r : ℝ) * (D.R.m : ℝ) ^ 10) ((D.R.r : ℝ) ^ 19) (D.R.k * D.R.m ^ 5) W.z W.π W.μW (W.μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) W.μG (W.νS.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j) R l dg ∧ Setup (lamD D τ) U' (large₂.sc.b ^ max 2 Cu) (bOne D τ 1) ((D.R.r : ℝ) * (D.R.m : ℝ) ^ 10) ((D.R.r : ℝ) ^ 19) (D.R.k * D.R.m ^ 5) W.z' W.π' W.μW' (W.μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) W.μG (W.νS'.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j) R l' dg := by
  intro hH D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl τ w w' θ W hTT hθ hW t ht hNt hψ R hF
  haveI := FiniteDimensional.complete ℂ W.Wp
  haveI := FiniteDimensional.complete ℂ W.Wq
  obtain ⟨c1, c2, z1, z2, t1, t2, hG, w1, -, w2, -, hN, q1, q2⟩ := hW
  have hv : 1 ≤ D.host.v := hZ.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hNH : IsHaarOn (Nset D.R.k D.R.rS) W.μN := by
    rw [hN]
    exact GlobalTheory.T.haarLie_isHaarOn_unipotentRadical _ _ _ (ENNReal.ofReal_pos.2 (by positivity)) ENNReal.ofReal_lt_top
  have hT1 : 0 < Tz D.R.k D.R.rS W.z := by
    rw [t1]; unfold Tr; exact_mod_cast hTT.1.pos
  have hT2 : 0 < Tz D.R.k D.R.rS W.z' := by
    rw [t2]; unfold Tr; exact_mod_cast hTT.2.1.pos
  obtain ⟨U, hU⟩ := exists_seq (uS D w τ)
  obtain ⟨U', hU'⟩ := exists_seq (uS D w' τ)
  have s1 : SideG D.R.k D.R.rS W.z W.π U W.μW W.μN W.μG W.νS :=
    ⟨z1, hT1, ⟨_, c1⟩, GlobalTheory.ThA.capParam_of_isHCTypeW _ _ _ _ U _ _ z1 hT1 c1 hU, w1, hNH, hG, q1⟩
  have s2 : SideG D.R.k D.R.rS W.z' W.π' U' W.μW' W.μN W.μG W.νS' :=
    ⟨z2, hT2, ⟨_, c2⟩, GlobalTheory.ThA.capParam_of_isHCTypeW _ _ _ _ U' _ _ z2 hT2 c2 hU', w2, hNH, hG, q2⟩
  have m1 := (GlobalTheory.T.torus_normaliser_bessel hH _ _ _ _ _ _ _ _ _ _ _ t ht hNt (hψ _ z1).1 (hψ _ z1).2 s1).1
  have m2 := (GlobalTheory.T.torus_normaliser_bessel hH _ _ _ _ _ _ _ _ _ _ _ t ht hNt (hψ _ z2).1 (hψ _ z2).2 s2).1
  obtain ⟨c, hc, hd⟩ := GlobalTheory.BesselDegree.schur_fdeg hH D.R.k D.R.rS (PI.BesselPeriodGGP.eps48 _ _) W.μG hG
  obtain ⟨l, hl⟩ := exists_setup hH (GlobalTheory.T.momentPieriNumerics_of_sizeHyps D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl τ w U hU).1 hF m1 hc
    fun mu R h => (hd mu R h).1
  obtain ⟨l', hl'⟩ := exists_setup hH (GlobalTheory.T.momentPieriNumerics_of_sizeHyps D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl τ w' U' hU').1 hF m2 hc
    fun mu R h => (hd mu R h).1
  exact ⟨U, U', l, l', _, hl, hl'⟩

end GlobalTheory.Amp.LocalSetup
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TorusCommutesWithUnipotentStatement
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_commutes_with_unipotent : Hyps → ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → 1000 ≤ Cl → ∀ τ w w' θ (W : LocW D.R.k D.R.rS), HypTT D w w' → 0 < θ → GoodW D τ w w' θ W → ∀ t ∈ GG D.R.k D.R.rS, (∀ n, n ∈ Nset D.R.k D.R.rS ↔ t * n * t⁻¹ ∈ Nset D.R.k D.R.rS) → (∀ z, inWb D.R.k D.R.rS z → (∀ h ∈ UWset D.R.k D.R.rS z, t * h = h * t) ∧ ∀ n ∈ Nset D.R.k D.R.rS, psi D.R.k D.R.rS z cStd n = psiS D z (t * n * t⁻¹)) → ∀ R : (Fin (2 * D.R.rS + D.R.k + 1) → ℤ) → Rep D.R.k D.R.rS, IsFam (lamD D τ) (D.R.k * D.R.m ^ 5) R → haveI := FiniteDimensional.complete ℂ W.Wp; haveI := FiniteDimensional.complete ℂ W.Wq; ∃ (U U' : ℕ → ℝ) (l : ∀ ν, (R ν).H → W.Wp) (l' : ∀ ν, (R ν).H → W.Wq) (dg : (Fin (2 * D.R.rS + D.R.k + 1) → ℤ) → ℝ), Setup (lamD D τ) U (large₂.sc.b ^ max 2 Cu) (bOne D τ 1) ((D.R.r : ℝ) * (D.R.m : ℝ) ^ 10) ((D.R.r : ℝ) ^ 19) (D.R.k * D.R.m ^ 5) W.z W.π W.μW (W.μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) W.μG (W.νS.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j) R l dg ∧ Setup (lamD D τ) U' (large₂.sc.b ^ max 2 Cu) (bOne D τ 1) ((D.R.r : ℝ) * (D.R.m : ℝ) ^ 10) ((D.R.r : ℝ) ^ 19) (D.R.k * D.R.m ^ 5) W.z' W.π' W.μW' (W.μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) W.μG (W.νS'.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j) R l' dg := by
  first | exact @GlobalTheory.Amp.LocalSetup.exists_setup_both | exact GlobalTheory.Amp.LocalSetup.exists_setup_both | (intros; apply GlobalTheory.Amp.LocalSetup.exists_setup_both <;> assumption)
end
end

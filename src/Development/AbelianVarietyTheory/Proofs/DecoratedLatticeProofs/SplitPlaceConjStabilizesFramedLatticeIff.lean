module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdAtToEAfEqZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColNone
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RepresentativeImagePointOfLift
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelsRepsRepresentUnitaryDoubleCosets
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapHandedFunctionVanishingPeriodInvariant

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceConjStabilizesFramedLatticeIff
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceConjFrameMatrixReindex
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceConjFrameMatrixReindex
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel

theorem GlobalTheory.Lev.conj_frameMatrix_submatrix_equiv {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]
    (βF : Matrix (Fin N) Y k) (γF : Matrix Y (Fin N) k) (hβγ : βF * γF = 1) (hγβ : γF * βF = 1) (σ : Fin N ≃ Y)
    (gk : GL Y k) (Pi Bi B P G X Xi : Matrix (Fin N) (Fin N) k) (hG : G = βF * gk.val * γF) (hX : X = Pi * (Bi * G * B) * P)
    (hBP : B * P = βF.submatrix id σ) (hBB : Bi * B = 1) (hPP : Pi * P = 1) (hXi : Xi * X = 1) :
    X = gk.val.submatrix σ σ ∧ Xi = (gk⁻¹).val.submatrix σ σ := by
  subst hG
  have hMM : βF.submatrix id σ * γF.submatrix σ id = 1 := by
    rw [Matrix.submatrix_mul_equiv βF γF id σ id, hβγ, Matrix.submatrix_id_id]
  have hN : Pi * Bi = γF.submatrix σ id := by
    have h1 : (Pi * Bi) * βF.submatrix id σ = 1 := by
      rw [← hBP]
      calc Pi * Bi * (B * P) = Pi * ((Bi * B) * P) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hBB, Matrix.one_mul, hPP]
    calc Pi * Bi = (Pi * Bi) * (βF.submatrix id σ * γF.submatrix σ id) := by rw [hMM, Matrix.mul_one]
      _ = γF.submatrix σ id := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hX' : X = gk.val.submatrix σ σ := by
    have e0 : X = (Pi * Bi) * (βF * gk.val * γF) * (B * P) := by rw [hX]; simp only [Matrix.mul_assoc]
    rw [e0, hN, hBP]
    have e1 : γF.submatrix σ id * (βF * gk.val * γF) = (γF * (βF * gk.val * γF)).submatrix σ id := by
      rw [Matrix.submatrix_mul γF _ σ id id Function.bijective_id, Matrix.submatrix_id_id]
    rw [e1, ← Matrix.submatrix_mul _ βF σ id σ Function.bijective_id]
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hγβ, Matrix.one_mul, Matrix.mul_assoc, hγβ, Matrix.mul_one]
  refine ⟨hX', ?_⟩
  have hR : gk.val.submatrix σ σ * (gk⁻¹).val.submatrix σ σ = 1 := by
    rw [Matrix.submatrix_mul_equiv _ _ σ σ σ, Units.mul_inv, Matrix.submatrix_one_equiv]
  calc Xi = Xi * (gk.val.submatrix σ σ * (gk⁻¹).val.submatrix σ σ) := by rw [hR, Matrix.mul_one]
    _ = (gk⁻¹).val.submatrix σ σ := by rw [← Matrix.mul_assoc, ← hX', hXi, Matrix.one_mul]

set_option maxHeartbeats 400000 in
theorem GlobalTheory.Lev.conj_frame_matrix : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt q.e PP) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k V.rank Y) (σ : Fin V.rank ≃ Y) (b : GA D V), MovedTo (ofSplit q) V b β (F.β.submatrix id σ) → ∀ (g : GA D V) (gk : GL Y k), (ofSplit q).IsLoc F g gk → (∀ i j, q.prF he ((β⁻¹ * Lev.finE V (b⁻¹ * g * b) * β : GL (Fin V.rank) (Lev.EAf D)).val i j) = gk.val (σ i) (σ j)) ∧ ∀ i j, q.prF he (((β⁻¹ * Lev.finE V (b⁻¹ * g * b) * β : GL (Fin V.rank) (Lev.EAf D))⁻¹).val i j) = (gk⁻¹).val (σ i) (σ j) := by
  intro D k _ _ _ _ q PP he V β Y _ _ F σ b hmov g gk hloc
  have hm : (mt V (b⁻¹ * g * b)).map q.pr = (mt V b⁻¹).map q.pr * (mt V g).map q.pr * (mt V b).map q.pr := by
    rw [mt_mul, mt_mul, Matrix.map_mul, Matrix.map_mul]
  have hc : ∀ A : Matrix (Fin V.rank) (Fin V.rank) (AE D), (A.map (toEAf D)).map (q.prF he) = A.map q.pr := by
    intro A; ext i j; simp [Matrix.map_apply, GlobalTheory.FinPl.SplitPt.prF_toEAf]
  have hX : (β⁻¹ * Lev.finE V (b⁻¹ * g * b) * β : GL (Fin V.rank) (Lev.EAf D)).val.map (q.prF he) =
      (β⁻¹).val.map (q.prF he) * (mt V (b⁻¹ * g * b)).map q.pr * β.val.map (q.prF he) := by
    rw [Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul, ← hc]
    rfl
  rw [hm] at hX
  obtain ⟨bt, hbt⟩ : ∃ bt : Matrix (Fin V.rank) (Fin V.rank) (AE D), bt.map (toEAf D) = β.val := by
    choose s hs using fun i j => GlobalTheory.ResLoc.toEAf_surj (D := D) (β.val i j)
    exact ⟨Matrix.of s, by ext i j; simp [hs]⟩
  have hM : ((mt V b * bt).map q.pr) = F.β.submatrix id σ := hmov bt hbt
  have hBP : (mt V b).map q.pr * β.val.map (q.prF he) = F.β.submatrix id σ := by
    rw [← hM, ← hbt, hc, Matrix.map_mul]
  have hBB : (mt V b⁻¹).map q.pr * (mt V b).map q.pr = 1 := by
    have h := mt_mul_inv V b⁻¹
    rw [inv_inv] at h
    rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]
  have hPP : (β⁻¹).val.map (q.prF he) * β.val.map (q.prF he) = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have hG : (mt V g).map q.pr = F.β * gk.val * F.γ := hloc.2
  have hXi : ((β⁻¹ * Lev.finE V (b⁻¹ * g * b) * β : GL (Fin V.rank) (Lev.EAf D))⁻¹).val.map (q.prF he) *
      (β⁻¹ * Lev.finE V (b⁻¹ * g * b) * β : GL (Fin V.rank) (Lev.EAf D)).val.map (q.prF he) = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨h1, h2⟩ := GlobalTheory.Lev.conj_frameMatrix_submatrix_equiv F.β F.γ F.βγ F.γβ σ gk _ _ _ _ _ _ _ hG hX hBP hBB hPP hXi
  exact ⟨fun i j => congrArg (fun M => M i j) h1, fun i j => congrArg (fun M => M i j) h2⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceConjFrameMatrixReindexStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_conj_frameMatrix_reindex : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt q.e PP) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k V.rank Y) (σ : Fin V.rank ≃ Y) (b : GA D V), MovedTo (ofSplit q) V b β (F.β.submatrix id σ) → ∀ (g : GA D V) (gk : GL Y k), (ofSplit q).IsLoc F g gk → (∀ i j, q.prF he ((β⁻¹ * Lev.finE V (b⁻¹ * g * b) * β : GL (Fin V.rank) (Lev.EAf D)).val i j) = gk.val (σ i) (σ j)) ∧ ∀ i j, q.prF he (((β⁻¹ * Lev.finE V (b⁻¹ * g * b) * β : GL (Fin V.rank) (Lev.EAf D))⁻¹).val i j) = (gk⁻¹).val (σ i) (σ j) := by
  first | exact @GlobalTheory.Lev.conj_frame_matrix | exact GlobalTheory.Lev.conj_frame_matrix | (intros; apply GlobalTheory.Lev.conj_frame_matrix <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceConjStabilizesFramedLatticeIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.SplitStabConj

theorem eq_idempotent_mul_add_of_mul_sub_eq {R : Type*} [CommRing R] (ε m o : R) (h : ε * (m - o) = m - o) : m = ε * m + (1 - ε) * o := by
  linear_combination -h

theorem suppAt_conj {D : D7} {e : AE D} {V : HSp D} {g : GA D V} (h : Formalism.L2.Theta.SuppAt e V g) (b : GA D V) :
    Formalism.L2.Theta.SuppAt e V (b⁻¹ * g * b) := by
  have hmul : ∀ x y : GA D V, Formalism.L2.Theta.mt V (x * y) = Formalism.L2.Theta.mt V x * Formalism.L2.Theta.mt V y := fun x y => by
    simp [Formalism.L2.Theta.mt, map_mul]
  have hAB : Formalism.L2.Theta.mt V b⁻¹ * Formalism.L2.Theta.mt V b = 1 := by
    rw [← hmul, inv_mul_cancel]; simp [Formalism.L2.Theta.mt]
  have hm : Formalism.L2.Theta.mt V (b⁻¹ * g * b) - 1 =
      Formalism.L2.Theta.mt V b⁻¹ * (Formalism.L2.Theta.mt V g - 1) * Formalism.L2.Theta.mt V b := by
    rw [hmul, hmul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hAB]
  have hg : Formalism.L2.Theta.mt V g - 1 = (e + cA D e) • (Formalism.L2.Theta.mt V g - 1) := by
    ext i j; exact (h i j).symm
  intro i j
  rw [hm]
  conv_rhs => rw [hg, Matrix.mul_smul, Matrix.smul_mul]
  rfl

end GlobalTheory.SplitStabConj


set_option maxHeartbeats 1000000 in
open GlobalTheory.SplitStabConj in
theorem GlobalTheory.splitStab_conj_iff : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsSDFrame V β Λ N → ∀ (Y : Type) [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k V.rank Y) (σ : Fin V.rank ≃ Y) (b : GA D V), MovedTo (ofSplit q) V b β (F.β.submatrix id σ) → ∀ (g : GA D V) (gk : GL Y k), (ofSplit q).IsLoc F g gk → b⁻¹ * g * b ∈ GfC V ∧ (Lev.finE V (b⁻¹ * g * b) ∈ Formalism.L2.DIV.St β ↔ gk ∈ KO k Y) ∧ ∀ PP' : Formalism.L2.DIV.Pl D.host.E, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') ≠ (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) → Lev.finE V (b⁻¹ * g * b) ∈ Formalism.L2.DIV.St β → Formalism.L2.DIV.redFn β PP' (Lev.finE V (b⁻¹ * g * b)) = 1 := by
  intro D k _ _ _ _ q PP he V β Λ N hSD Y _ _ F σ b hM g gk hL
  have hsd := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D V β Λ N hSD
  obtain ⟨c, hfr, -⟩ := hSD
  have hsg : Formalism.L2.Theta.SuppAt q.e V g := hL.1
  have hsκ : Formalism.L2.Theta.SuppAt q.e V (b⁻¹ * g * b) := suppAt_conj hsg b
  refine ⟨?_, ?_, ?_⟩
  · have hg := GlobalTheory.SplitHecke.Stab.mem_GfC q.split hsg
    rw [GfC, MonoidHom.mem_ker] at hg ⊢
    rw [map_mul, map_mul, hg, mul_one, ← map_mul, inv_mul_cancel, map_one]
  · obtain ⟨hX, hXi⟩ := GlobalTheory.T.splitPlace_conj_frameMatrix_reindex q he V β F σ b hM g gk hL
    obtain ⟨hint, -⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D q.e PP he
    rw [GlobalTheory.LocGl.mem_KO_iff]
    constructor
    · rintro ⟨y, hy⟩
      have hyX : Formalism.L2.DIV.intGL D.host.F D.host.E _ y = β⁻¹ * Lev.finE V (b⁻¹ * g * b) * β := by
        rw [← hy]; simp [Formalism.L2.DIV.frGL, MulAut.conj_apply, mul_assoc]
      refine ⟨fun a a' => ?_, fun a a' => ?_⟩
      · obtain ⟨i, rfl⟩ := σ.surjective a
        obtain ⟨j, rfl⟩ := σ.surjective a'
        rw [← hX i j, q.prF_mem_iff he, ← hyX]
        exact mul_mem hint (y.val i j).2
      · obtain ⟨i, rfl⟩ := σ.surjective a
        obtain ⟨j, rfl⟩ := σ.surjective a'
        rw [← hXi i j, q.prF_mem_iff he, ← hyX, ← map_inv]
        exact mul_mem hint ((y⁻¹).val i j).2
    · rintro ⟨h1, h2⟩
      have hA : IsIntM (toEAf D q.e • (β⁻¹ * Lev.finE V (b⁻¹ * g * b) * β : GL (Fin V.rank) (Lev.EAf D)).1) := fun i j => by
        rw [Matrix.smul_apply, smul_eq_mul, ← q.prF_mem_iff he, hX]; exact h1 _ _
      have hB : IsIntM (toEAf D q.e • ((β⁻¹ * Lev.finE V (b⁻¹ * g * b) * β : GL (Fin V.rank) (Lev.EAf D))⁻¹ : GL (Fin V.rank) (Lev.EAf D)).1) := fun i j => by
        rw [Matrix.smul_apply, smul_eq_mul, ← q.prF_mem_iff he, hXi]; exact h2 _ _
      obtain ⟨hC, hD⟩ := GlobalTheory.T.selfDualFrame_conj_integral_smul_of_integral V Λ β hsd hfr _ (GlobalTheory.LevSplit.finE_mem_UA V (b⁻¹ * g * b)) _ rfl q.e hA hB
      have hsum : IsIdemSum q.e {PP} := ⟨⟨fun _ => q.e, by simpa using he, by simp⟩, q.split.2.1⟩
      have hmt : Formalism.L2.Theta.mt V (b⁻¹ * g * b) = (q.e + cA D q.e) • Formalism.L2.Theta.mt V (b⁻¹ * g * b) +
          (1 - (q.e + cA D q.e)) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
        ext i j
        have := hsκ i j
        simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at this ⊢
        exact eq_idempotent_mul_add_of_mul_sub_eq _ _ _ this
      have hy := GlobalTheory.T.finiteEmbedding_idempotent_patch_in_frame V β (b⁻¹ * g * b) (b⁻¹ * g * b) (q.e + cA D q.e) hmt
      exact (GlobalTheory.T.frameIdempotentCutMatrix_mem_stabiliser_reduction V.rank β _ _ {PP} q.e hsum hA hB hC hD hy).1
  · intro PP' hne hS
    exact GlobalTheory.T.reduction_eq_one_off_splitPlace q he V β _ hsκ hS PP' hne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceConjStabilizesFramedLatticeIffStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_conj_stabilizes_framedLattice_iff : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsSDFrame V β Λ N → ∀ (Y : Type) [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k V.rank Y) (σ : Fin V.rank ≃ Y) (b : GA D V), MovedTo (ofSplit q) V b β (F.β.submatrix id σ) → ∀ (g : GA D V) (gk : GL Y k), (ofSplit q).IsLoc F g gk → b⁻¹ * g * b ∈ GfC V ∧ (Lev.finE V (b⁻¹ * g * b) ∈ Formalism.L2.DIV.St β ↔ gk ∈ KO k Y) ∧ ∀ PP' : Formalism.L2.DIV.Pl D.host.E, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') ≠ (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) → Lev.finE V (b⁻¹ * g * b) ∈ Formalism.L2.DIV.St β → Formalism.L2.DIV.redFn β PP' (Lev.finE V (b⁻¹ * g * b)) = 1 := by
  first | exact @GlobalTheory.splitStab_conj_iff | exact GlobalTheory.splitStab_conj_iff | (intros; apply GlobalTheory.splitStab_conj_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeConjugate
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil

noncomputable section
namespace GlobalTheory.LevProd.Bwd

section Dense
open Formalism.HermitianLatticesTheory _root_.Formalism.L2.Col GlobalTheory.RootEx GlobalTheory.TwBridge ValuativeRel

theorem prX_le_of_prCat (X : Formalism.L2.Col.Fields) (Pr : Formalism.L2.Col.Primes X) (R : Ranks) (Ch : Formalism.L2.Col.Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Formalism.L2.DIV.Tup X.F X.E X.K S₀)
    (cst : Formalism.L2.Col.LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k]
    [BorelSpace k] (ν : Measure k) (hν : IsUnitVol ν) (hok : cst.Ok) (hat : AtTwist (R := R) sel mu cst σ₀ P ι s W)
    (j c : ℕ) (h : j + (c + 1) = s + 1) (γ : AutY X R j) (g : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) k)
    (hg : IsGL ι γ g) (K : Subgroup (GL (XIx (Fin R.k) (Fin R.t) j) k))
    (hKo : IsOpen (K : Set (GL (XIx (Fin R.k) (Fin R.t) j) k)))
    (hle : ∀ e' : XIx (Fin R.k) (Fin R.t) j ≃ Fin (R.N j), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e' →
      ∀ y ∈ prCat (Pr := Pr) cst.sharp j P.1 γ, GlobalTheory.VolBridge.locHom ι e' y ∈ K) :
    GlobalTheory.StepData.prX (Cgrp ((W.T s R).lev j (c + 1) h).J g) ≤ K := by
  have hLev := GlobalTheory.TwBridge.Lev.levelAgree X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hν hok hat
  obtain ⟨e, he, hge⟩ := hg
  have hcc : cOf R j = c + 1 := by unfold cOf; have := hat.steps; omega
  have heR : ∀ i : Fin (c + 1), (e (Sum.inr i)).val = R.N j + i.val := fun i => he (Sum.inr i)
  have hgφ : g = GlobalTheory.VolBridge.locHom ι e γ := Units.ext hge
  have hreg : (W.T s R).Regular := Chain.ofTwist_regular _ _ _ _ _
  obtain ⟨hJo, -, -⟩ := hreg.2.2 j (c + 1) h
  set J := ((W.T s R).lev j (c + 1) h).J with hJdef
  set φ := GlobalTheory.VolBridge.locHom ι e with hφ
  have hcompl := hat.compl
  have hIsGL : ∀ x : AutY X R j, IsGL ι (γ⁻¹ * x * γ) (g⁻¹ * φ x * g) := by
    intro x
    refine ⟨e, he, ?_⟩
    rw [hgφ, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hC : ∀ x : AutY X R j, x ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) γ ↔ φ x ∈ Cgrp J g := by
    intro x
    rw [mem_Cgrp, ← GlobalTheory.RankOneMatrix.mem_rationalFirstParabolic_iff_localGL_mem_rootExchange ι e hcc heR x, (hLev j (c + 1) h _ _ (hIsGL x)).1]
    simp [Loc.Cbe, Subgroup.mem_comap, MulAut.conj_apply]
  have hN1 := GlobalTheory.UnipRead.mem_N1_iff_local_hom ι e hcc heR
  have hdN := GlobalTheory.VolBridge.exists_N1_local_hom_mem_open ι hcompl.dense e hcc heR
  have hord : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos (GlobalTheory.VolBridge.eX e hcc heR) := fun a => he (Sum.inl a)
  set e' := GlobalTheory.VolBridge.eX e hcc heR with he'
  set φ' := GlobalTheory.VolBridge.locHom ι e' with hφ'
  have hOo : IsOpen {w : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) k | g⁻¹ * w * g ∈ J} :=
    hJo.preimage (by fun_prop)
  have hOR : ∀ z ∈ GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1,
      z ∈ Cgrp J g ↔ z ∈ {w | g⁻¹ * w * g ∈ J} := fun z hz => by
    simp [mem_Cgrp, hz]
  have hCR : Cgrp J g ≤ GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1 := fun z hz => (mem_Cgrp.1 hz).1
  have hP : ∀ y, y ∈ prCat (Pr := Pr) cst.sharp j P.1 γ ↔ φ' y ∈ GlobalTheory.StepData.prX (Cgrp J g) :=
    GlobalTheory.VolBridge.prX_iff_locHom ι e hcc heR hN1 hdN _ _ _ hOo hOR hCR hC
  have hpo : IsOpen (GlobalTheory.StepData.prX (Cgrp J g) : Set (GL (XIx (Fin R.k) (Fin R.t) j) k)) :=
    GlobalTheory.OpenPr.isOpen_prX _ _ hOo (by simp [J.one_mem]) (fun z hz hzO => (hOR z hz).2 hzO)
  intro z hz
  have hV : IsOpen {v : GL (XIx (Fin R.k) (Fin R.t) j) k |
      v⁻¹ * z ∈ ((GlobalTheory.StepData.prX (Cgrp J g) ⊓ K : Subgroup _) : Set _)} :=
    (hpo.inter hKo).preimage (by fun_prop)
  obtain ⟨y, hy⟩ := GlobalTheory.denseGL_completion ι hcompl.dense e' z _ hV (by simp [one_mem, hz])
  have hy1 : (φ' y)⁻¹ * z ∈ GlobalTheory.StepData.prX (Cgrp J g) := hy.1
  have hy2 : (φ' y)⁻¹ * z ∈ K := hy.2
  have hyC : φ' y ∈ GlobalTheory.StepData.prX (Cgrp J g) := by
    have := mul_mem hz (inv_mem hy1); simpa using this
  have hyK : φ' y ∈ K := hle e' hord y ((hP y).2 hyC)
  have := mul_mem hyK hy2; simpa using this

end Dense

theorem adAt_eq_of_pr {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (PP : HeightOneSpectrum (𝓞 D.host.E)) (he : Formalism.L2.NTheta.IsIdemAt q.e PP)
    (z : Formalism.L2.Theta.AE D) (x : D.host.E) (h : q.pr z = q.pr (incA D x)) :
    adAt D.host.F PP (toEAf D z) = algebraMap D.host.E (PP.adicCompletion D.host.E) x := by
  have h1 : q.e * z = q.e * incA D x := by rw [← q.sec_pr, ← q.sec_pr, h]
  have h2 := congrArg (fun w => GlobalTheory.StdFrames.cpt PP (toEAf D w)) h1
  simp only [RingHom.map_mul, (GlobalTheory.StdFrames.cpt_of_isIdemAt he).1, one_mul] at h2
  rw [← GlobalTheory.SplitProj.cpt_eq_adAt, h2]
  exact (GlobalTheory.SplitProj.cpt_eq_adAt PP _).trans (GlobalTheory.Mem.Col2.adAt_inclE D.host.F PP x)

section Rat
open _root_.Formalism.L2.Col Formalism.UG
attribute [local instance] GlobalTheory.Mem.Col2.starE


set_option maxHeartbeats 1000000 in
theorem mem_lev_of_rat {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (a : I.ι) {Ch : ℕ → Type} (A : TwDat I l Z u a Ch) (hA : A.Is) (j : ℕ) (hj : j + 2 ≤ B.R.m) (β : Ch j)
    (hβ : A.kb j β = TC.kStd X u (B.R.N j)) (P : rowSG (B.primes X) I.sel (I.tup a)) (hP : P.1 ∉ (B.primes X).vGs)
    (x : TC.GA B (B.R.N j)) (hx : x ∈ UAd B.sp.cm (B.R.N j))
    (hoff : ∀ v', v' ≠ P.1.under (𝓞 B.host.F) → bc (prV (E := B.host.E) v') x = 1)
    (g : Sp B.fields.E (B.R.N j) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N j))
    (hg : g ∈ prCat (Pr := B.primes X) (I.cst a).sharp j P.1 ((I.idx a).h j ((A.b0 j β).get (by omega)) P))
    (hpt : ∀ r s, adAt B.host.F P.1 (x.1 r s) = algebraMap B.fields.E (P.1.adicCompletion B.fields.E) (g (Pi.single s 1) r)) :
    x ∈ (A.K j (by omega) β).lev.U := by
  have hj' : j ≤ B.R.m := by omega
  have hjm : j < B.R.m := by omega
  have hL := hI.idx_ok a
  have hR := hA.reads j hj'
  obtain ⟨c, rfl⟩ := hA.chOf_onto j hj' β
  have hc := (hA.rep j hj' c).1
  rw [← hc] at hg
  have hPQ : P.1 ∈ I.Q a := (@Finset.mem_union _ (Classical.decEq _) _ _ _).1 P.2 |>.resolve_left hP
  obtain ⟨hLev, hdisj, -⟩ := GlobalTheory.Mem.LevTwist.levOk_twists B X I hI
  have hd : Disjoint (B.primes X).vGs (I.Q a) := Finset.disjoint_of_subset_right (ColIn.Q_subset_SQ I a) hdisj
  have hp := IsPtOf.of_extTo (ColIn.Q_subset_SQ I a) hd (hR.pt c)
  obtain ⟨pk, hpk, -⟩ := hR.k_std (A.chOf j c)
  have hv : Formalism.L2.Col.IsOver (P.1.under (𝓞 B.host.F)) P.1 := rfl
  have hgI : g ∈ GLint B.fields.E (B.R.N j) P.1 := hL.int j _ P hg
  have hT := (GlobalTheory.Mem.Col2.TC.underQ_prime_to_bad I hI l u a (P.1.under (𝓞 B.host.F)) ⟨P.1, hPQ, rfl⟩).1
  have hk1 : bc (prV (E := B.host.E) (P.1.under (𝓞 B.host.F))) (A.kb j (A.chOf j c)) = 1 := by
    rw [hβ]; exact (GlobalTheory.Mem.Col2.MemChart.kStd_spec (X := X) l.pr u (B.R.N j)).2.1 _ hT
  let cc : GLQ B.fields.E (B.R.N j) (I.Q a) := Pi.mulSingle (⟨P.1, hPQ⟩ : I.Q a) (⟨g, hgI⟩⁻¹ : GLint B.fields.E (B.R.N j) P.1)
  have hccP : cc ⟨P.1, hPQ⟩ = (⟨g, hgI⟩⁻¹ : GLint B.fields.E (B.R.N j) P.1) := Pi.mulSingle_eq_same _ _
  have hccO : ∀ P'' : I.Q a, P''.1 ≠ P.1 → cc P'' = 1 := fun P'' h => Pi.mulSingle_eq_of_ne (fun e => h (congrArg Subtype.val e)) _
  have hb : c.1 = Idx.of (c.1.get hjm) hjm := (Idx.of_get c.1 hjm _).symm
  have hcc : cc ∈ (levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) j c.1).grp := by
    rw [hb]
    intro P'' _
    by_cases h : P''.1 = P.1
    · obtain rfl : P'' = ⟨P.1, hPQ⟩ := Subtype.ext h
      show cc ⟨P.1, hPQ⟩ ∈ ((I.idx a).levQ j (c.1.get hjm) ⟨P.1, hPQ⟩).H
      rw [hccP, hL.grpQ]
      exact inv_mem (Subgroup.mem_subgroupOf.2 hg)
    · show cc P'' ∈ ((I.idx a).levQ j (c.1.get hjm) P'').H
      rw [hccO P'' h]
      exact one_mem _
  let κ : (I.stp u a j).G c.1 := (1, 1, ⟨cc, hcc⟩)
  have hPu : P.1 ∈ uSG (B.primes X).vGs I.SQ := by
    simp only [uSG, Finset.mem_union]
    exact Or.inr (ColIn.Q_subset_SQ I a hPQ)
  have key := GlobalTheory.Mem.Col2.LevLiftPt.core B.sp.cm hp hx hpk.uni _ P.1 hv hoff g hgI (fun r s => by
      have e : bc (prV (E := B.host.E) (P.1.under (𝓞 B.host.F))) ((A.kb j (A.chOf j c))⁻¹ * x * A.kb j (A.chOf j c)) =
          bc (prV (E := B.host.E) (P.1.under (𝓞 B.host.F))) x := by
        rw [map_mul, map_mul, map_inv, hk1, inv_one, one_mul, mul_one]
      exact (GlobalTheory.Mem.Col2.ChTwRead.adAt_congr_prV P.1 (congrArg (fun m => m.1 r s) e)).trans (hpt r s))
    (GlobalTheory.Mem.Col2.LevLiftPt.vT_notOver I hI a P _ hv u) (fun w hw hwv => by
      have hw' : w ∈ uSG (B.primes X).vGs I.SQ := by
        simp only [uSG, Finset.mem_union]
        rcases hw with h | h
        · exact Or.inl h
        · exact Or.inr (ColIn.Q_subset_SQ I a h)
      rcases rll_over_cases B.sp.cm hv hwv with h | h
      · exact h
      · exact absurd (h ▸ hw') (hLev.split P.1 hPu))
    1 cc (fun h => absurd h hP) (fun w _ y _ => by simp) (fun _ => by rw [hccP, inv_inv])
    (fun P'' h => by rw [hccO P'' h, inv_one]; rfl)
  have e := GlobalTheory.Mem.Col2.LevLiftPt.mul_conj (G := TC.GA B (B.R.N j)) ((A.K j hj' (A.chOf j c)).y ⟨c, rfl⟩).1 x (A.kb j (A.chOf j c))
  have hq : TC.PtOf ((show TC.GA B (B.R.N j) from ((A.K j hj' (A.chOf j c)).y ⟨c, rfl⟩).1) * x * A.kb j (A.chOf j c))
      ((I.stp u a j).act c.1 κ ((I.stp u a j).rep c)).1.1 := e ▸ key
  refine (hR.lev c x _ hq).2 ⟨κ, map_one (ufGL B.fields.E (B.R.N j)), rfl, ?_⟩
  have h0 : ∀ p : PtAt B.R I.sel (I.tup a) (I.cst a) u j, p.1.2 = ∅ := fun p => by
    have := p.2
    rw [ysAt_ys_of_ne I.sel (I.tup a) (I.cst a) (by omega)] at this
    exact this
  funext P'
  simp only [cosetIn, h0, Set.mem_empty_iff_false, false_and, exists_false]

end Rat

theorem entry_of_std {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k N Y) (e : Y ≃ Fin N)
    (he : F.β = (1 : Matrix (Fin N) (Fin N) k).submatrix id e) (M : Matrix (Fin N) (Fin N) k) (g : Matrix Y Y k)
    (h : M = F.β * g * F.γ) (a b : Y) : M (e a) (e b) = g a b := by
  have h1 : M * F.β = F.β * g := by rw [h, Matrix.mul_assoc, F.γβ, Matrix.mul_one]
  have h2 := congrFun (congrFun h1 (e a)) b
  rw [he] at h2
  simpa [Matrix.mul_apply, Matrix.one_apply] using h2



open GlobalTheory.FinPl in
theorem grpAt_empty {D : D7} (V : HSp D) {P : Pl D → Prop} (hP : ∀ w, ¬ P w) (n : GA D V) (hn : n ∈ grpAt V P) : n = 1 := by
  rw [GlobalTheory.FinPl.SetCut.mem_grpAt_iff_parts] at hn
  apply GlobalTheory.FinPlLoc.mt_inj
  rw [GlobalTheory.FinPlLoc.mt_one]
  ext i j
  have := GlobalTheory.FinPlLoc.eq_zero_of_comp _ (hn i j).1 (fun w => (hn i j).2 w (hP w))
  rw [Matrix.sub_apply, sub_eq_zero] at this
  exact this


open GlobalTheory.FinPl in
theorem locHom_one_of_off {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {Y : Type} [Fintype Y] [DecidableEq Y] (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (F : GlobalTheory.LocMod.Frame k S.rank Y)
    {x : GA D S} (h1 : x ∈ grpOff S (· = q.v)) : GlobalTheory.LevIdx.locHom q S F x = 1 := by
  have h2 := GlobalTheory.LocMod.PinInhab.map_mt_eq_one_of_off q (P := (· = q.v)) rfl h1
  symm
  rw [← GlobalTheory.LevIdx.eq_locHom_iff, h2]
  simp [F.βγ]


open GlobalTheory.FinPl in
theorem grpAt_le_of {D : D7} (V : HSp D) {P P' : Pl D → Prop} (h : ∀ w, P w → P' w) {n : GA D V} (hn : n ∈ grpAt V P) :
    n ∈ grpAt V P' := by
  rw [GlobalTheory.FinPl.SetCut.mem_grpAt_iff_parts] at hn ⊢
  exact fun i j => ⟨(hn i j).1, fun w hw => (hn i j).2 w (fun hp => hw (h w hp))⟩

end GlobalTheory.LevProd.Bwd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeMeasureValue
noncomputable section
namespace GlobalTheory.LevProd.Fwd

section Columns
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col _root_.Formalism.L2.DIV _root_.Formalism.L2.Ker Formalism.UG _root_.Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open GlobalTheory.Mem.ColAd GlobalTheory.Mem.Col2.PtExist
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem ratM_inj {E : Type} [Field E] [NumberField E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) {f g : Sp E n ≃ₗ[E] Sp E n}
    (h : ratM P f = ratM P g) : f = g := by
  refine LinearEquiv.ext fun x => funext fun i => (algebraMap E (P.adicCompletion E)).injective ?_
  have h1 := congrFun (ratM_mulVec (P := P) f x) i
  have h2 := congrFun (ratM_mulVec (P := P) g x) i
  rw [← h1, ← h2, h]

theorem exists_gl_mat {E : Type} [Field E] [NumberField E] {n : ℕ} (f : Sp E n ≃ₗ[E] Sp E n) : ∃ γ : GL (Fin n) E, γ.1 = mat f := by
  have h1 : mat (1 : Sp E n ≃ₗ[E] Sp E n) = 1 := by
    ext i j
    show (Pi.single j 1 : Sp E n) i = _
    rw [Matrix.one_apply, Pi.single_apply]
  exact ⟨⟨mat f, mat f⁻¹, by rw [← mat_mul, mul_inv_cancel, h1], by rw [← mat_mul, inv_mul_cancel, h1]⟩, rfl⟩

theorem mem_levQ {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) {u : B.Word} {a : I.ι} {i : ℕ} {Ch : Type}
    {chOf : (I.stp u a i).Cl → Ch}
    {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)} {U : Ch → Subgroup (GA B (B.R.N i))} {chi : ∀ β, U β →* ℂˣ}
    {y : (I.stp u a i).Cl → GA B (B.R.N i)} {st : ∀ c, (I.stp u a i).Stab c → GL (Fin (B.R.N i)) B.host.E}
    {k : Ch → GA B (B.R.N i)} (hR : I.Reads u a i chOf Lb U chi y st k) (c : (I.stp u a i).Cl) (x : GA B (B.R.N i))
    (hx : x ∈ Formalism.L2.Herm.UstdAf B.sp.cm (B.R.N i)) (hxU : x ∈ U (chOf c))
    (hk1 : ∀ P : I.Q a, locM P.1 (k (chOf c)) = 1)
    (γ : I.Q a → (Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)))
    (hγ : ∀ P : I.Q a, locM P.1 x = ratM P.1 (γ P)) (P : I.Q a) :
    ∃ κ ∈ (levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) i c.1 P).H, κ.1 = γ P := by
  haveI : NeZero (B.R.N i) := ⟨(B.R.N_pos i).ne'⟩
  have hd : Disjoint (B.primes X).vGs (I.Q a) :=
    Finset.disjoint_of_subset_right (ColIn.Q_subset_SQ I a) (GlobalTheory.Mem.LevTwist.levOk_twists B X I hI).2.1
  have hp : PtOf (y c * k (chOf c)) ((I.stp u a i).rep c).1.1 :=
    IsPtOf.of_extTo (ColIn.Q_subset_SQ I a) hd (hR.pt c)
  obtain ⟨pk, hpk, -⟩ := hR.k_std (chOf c)
  have hk : k (chOf c) ∈ UAd B.sp.cm (B.R.N i) := hpk.uni
  have hg' : y c * x * k (chOf c) ∈ UAd B.sp.cm (B.R.N i) := by
    have e : y c * x * k (chOf c) = y c * k (chOf c) * ((k (chOf c))⁻¹ * x * k (chOf c)) := by group
    rw [e]
    exact mul_mem hp.uni (mul_mem (mul_mem (inv_mem hk) hx) hk)
  have hy : ∀ P : I.Q a, locM P.1 (y c * x * k (chOf c)) = ratM P.1 (((I.stp u a i).rep c).1.1.fr P * γ P) := by
    intro P
    have h1 : locM P.1 (y c * k (chOf c)) = ratM P.1 (((I.stp u a i).rep c).1.1.fr P) := Matrix.ext fun r s => hp.fr P r s
    rw [locM_mul, hk1, Matrix.mul_one] at h1
    rw [locM_mul, locM_mul, hk1, Matrix.mul_one, ratM_mul, h1, hγ]
  obtain ⟨q, hq⟩ := GlobalTheory.Mem.Col2.RatFrPt.exists_isPtOf_of_rat B.sp.cm ((B.primes X).vT u) (B.primes X).vGs (I.Q a) _ hg' fun P hP => by
    obtain ⟨δ, hδ⟩ := exists_gl_mat (((I.stp u a i).rep c).1.1.fr ⟨P, hP⟩ * γ ⟨P, hP⟩)
    refine ⟨δ, fun r s => ?_⟩
    rw [hδ]
    exact congrFun (congrFun (hy ⟨P, hP⟩) r) s
  obtain ⟨κ, hκ1, hκq, -⟩ := (hR.lev c x q hq).1 hxU
  have hκ : κ.1 = 1 := by
    have h1 : toGLm B.fields.E (B.R.N i) κ.1.1 = toGLm B.fields.E (B.R.N i) 1 := by
      rw [map_one]
      exact hκ1
    exact Subtype.ext ((toGLm B.fields.E (B.R.N i)).injective h1)
  have h2 : locM P.1 (y c * x * k (chOf c)) = ratM P.1 (q.fr P) := Matrix.ext fun r s => hq.fr P r s
  have h3 : q.fr P = κ.1.1 * ((I.stp u a i).rep c).1.1.fr P * ((κ.2.2.1 P)⁻¹).1 := by
    rw [← hκq]
    rfl
  rw [hy, h3, hκ] at h2
  have h4 := ratM_inj P.1 h2
  refine ⟨(κ.2.2.1 P)⁻¹, inv_mem (κ.2.2.2 P (Set.mem_univ _)), ?_⟩
  have h5 : ((1 : UF B.fields.E (B.R.N i)).1 : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) = 1 := rfl
  rw [h5, one_mul] at h4
  exact (mul_left_cancel h4).symm

end Columns

section Local
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory _root_.Formalism.L2.DIV _root_.Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

theorem prCat_iff (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀)
    (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k]
    [BorelSpace k] (ν : Measure k) (hν : IsUnitVol ν) (hok : cst.Ok) (hat : AtTwist (R := R) sel mu cst σ₀ P ι s W)
    (j c : ℕ) (h : j + (c + 1) = s + 1) (γ : AutY X R j) (g : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) k)
    (hg : IsGL ι γ g) (e₀ : XIx (Fin R.k) (Fin R.t) j ≃ Fin (R.N j)) (he₀ : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e₀) :
    IsOpen (prX (Cgrp ((W.T s R).lev j (c + 1) h).J g) : Set (GL (XIx (Fin R.k) (Fin R.t) j) k)) ∧
    ∀ y, y ∈ prCat (Pr := Pr) cst.sharp j P.1 γ ↔ GlobalTheory.VolBridge.locHom ι e₀ y ∈ prX (Cgrp ((W.T s R).lev j (c + 1) h).J g) := by
  have hLev := GlobalTheory.TwBridge.Lev.levelAgree X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hν hok hat
  obtain ⟨e, he, hge⟩ := hg
  have hcc : cOf R j = c + 1 := by unfold cOf; have := hat.steps; omega
  have heR : ∀ i : Fin (c + 1), (e (Sum.inr i)).val = R.N j + i.val := fun i => he (Sum.inr i)
  have hgφ : g = GlobalTheory.VolBridge.locHom ι e γ := Units.ext hge
  have hreg : (W.T s R).Regular := Chain.ofTwist_regular _ _ _ _ _
  obtain ⟨hJo, -, -⟩ := hreg.2.2 j (c + 1) h
  set J := ((W.T s R).lev j (c + 1) h).J with hJdef
  set φ := GlobalTheory.VolBridge.locHom ι e with hφ
  have hcompl := hat.compl
  have hIsGL : ∀ x : AutY X R j, IsGL ι (γ⁻¹ * x * γ) (g⁻¹ * φ x * g) := by
    intro x
    refine ⟨e, he, ?_⟩
    rw [hgφ, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hC : ∀ x : AutY X R j, x ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) γ ↔ φ x ∈ Cgrp J g := by
    intro x
    rw [mem_Cgrp, ← GlobalTheory.RankOneMatrix.mem_rationalFirstParabolic_iff_localGL_mem_rootExchange ι e hcc heR x, (hLev j (c + 1) h _ _ (hIsGL x)).1]
    simp [Loc.Cbe, Subgroup.mem_comap, MulAut.conj_apply]
  have hN1 := GlobalTheory.UnipRead.mem_N1_iff_local_hom ι e hcc heR
  have hdN := GlobalTheory.VolBridge.exists_N1_local_hom_mem_open ι hcompl.dense e hcc heR
  have hee : e₀ = GlobalTheory.VolBridge.eX e hcc heR := Equiv.ext fun a => Fin.ext ((he₀ a).trans (he (Sum.inl a)).symm)
  have hOo : IsOpen {w : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) k | g⁻¹ * w * g ∈ J} :=
    hJo.preimage (by fun_prop)
  have hOR : ∀ z ∈ GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1,
      z ∈ Cgrp J g ↔ z ∈ {w | g⁻¹ * w * g ∈ J} := fun z hz => by
    simp [mem_Cgrp, hz]
  have hCR : Cgrp J g ≤ GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1 := fun z hz => (mem_Cgrp.1 hz).1
  refine ⟨GlobalTheory.OpenPr.isOpen_prX _ _ hOo (by simp [J.one_mem]) (fun z hz hzO => (hOR z hz).2 hzO), ?_⟩
  rw [hee]
  exact GlobalTheory.VolBridge.prX_iff_locHom ι e hcc heR hN1 hdN _ _ _ hOo hOR hCR hC

end Local

section Split
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice _root_.Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum _root_.Formalism.L2.Forms IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.AdForm GlobalTheory.Mem.Col2
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem adAt_of_pr (q : GlobalTheory.FinPl.SplitPt D k) (PP : HeightOneSpectrum (𝓞 D.host.E)) (he : Formalism.L2.NTheta.IsIdemAt q.e PP)
    (z : AE D) (x : D.host.E) (h : q.pr z = q.pr (incA D x)) :
    adAt D.host.F PP (toEAf D z) = algebraMap D.host.E (PP.adicCompletion D.host.E) x := by
  have h1 : q.e * z = q.e * incA D x := by rw [← q.sec_pr, ← q.sec_pr, h]
  have h2 := congrArg (fun w => adAt D.host.F PP (toEAf D w)) h1
  simp only [map_mul, GlobalTheory.AdForm.CongAtIdem.adAt_toEAf_of_isIdemAt he, one_mul] at h2
  exact h2.trans (adAt_inclE D.host.F PP x)

theorem locM_of_pr (q : GlobalTheory.FinPl.SplitPt D k) (PP : HeightOneSpectrum (𝓞 D.host.E)) (he : Formalism.L2.NTheta.IsIdemAt q.e PP)
    (V : HSp D) {n : ℕ} (hn : V.rank = n) (g : GA D V) (x : GL (Fin n) (Formalism.L2.DIV.AfE D.host.F D.host.E)) (hx : x.1 = finM V hn g)
    (y : Formalism.L2.Col.Sp D.host.E n ≃ₗ[D.host.E] Formalism.L2.Col.Sp D.host.E n)
    (hy : ∀ r s, q.pr (mt V g (Fin.cast hn.symm r) (Fin.cast hn.symm s)) = q.pr (incA D (y (Pi.single s 1) r))) :
    GlobalTheory.Mem.ColAd.locM PP x = GlobalTheory.Mem.ColAd.ratM PP y :=
  Matrix.ext fun r s => (congrArg (adAt D.host.F PP) (congrFun (congrFun hx r) s)).trans (adAt_of_pr q PP he _ _ (hy r s))

theorem locHom_std (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k S.rank Y)
    (e : Y ≃ Fin S.rank) (hF : F.β = (1 : Matrix (Fin S.rank) (Fin S.rank) k).submatrix id e) (g : GA D S) (r b : Y) :
    (GlobalTheory.LevIdx.locHom q S F g).val r b = q.pr (mt S g (e r) (e b)) := by
  have h := (GlobalTheory.LevIdx.eq_locHom_iff q S F g _).2 rfl
  have h2 := congrFun (congrFun h (e r)) (e b)
  rw [GlobalTheory.Fam.MovedJoin.mul_frameγ_std F e hF, GlobalTheory.Fam.MovedJoin.frameβ_mul_std F e hF] at h2
  exact h2.symm

theorem locHom_eq_one {k' : Type} [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']
    {Y : Type} [Fintype Y] [DecidableEq Y] (q' : GlobalTheory.FinPl.SplitPt D k') (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (F : Frame k S.rank Y)
    (hv : q.v ≠ q'.v) {x : GA D S} (hx : x ∈ GlobalTheory.FinPl.grpAt S (· = q'.v)) : GlobalTheory.LevIdx.locHom q S F x = 1 := by
  have h1 : x ∈ GlobalTheory.FinPl.grpOff S (· = q.v) :=
    GlobalTheory.FinPl.SetCut.grpAt_le_grpOff S (· = q'.v) (· = q.v) (fun p hp e => hv (e.symm.trans hp)) hx
  have h2 := GlobalTheory.LocMod.PinInhab.map_mt_eq_one_of_off q (P := (· = q.v)) rfl h1
  symm
  rw [← GlobalTheory.LevIdx.eq_locHom_iff, h2]
  simp [F.βγ]

end Split

theorem list_prod_map_mulSingle {n : ℕ} {G : Fin n → Type*} [∀ i, Monoid (G i)] (x : ∀ i, G i) (k : Fin n) :
    ∀ l : List (Fin n), l.Nodup → ((l.map fun i => Pi.mulSingle i (x i) k).prod = if k ∈ l then x k else 1)
  | [], _ => by simp
  | b :: l, hl => by
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.prod_cons, list_prod_map_mulSingle x k l hl.2]
    by_cases hb : b = k
    · subst hb
      simp [hl.1]
    · rw [Pi.mulSingle_eq_of_ne (Ne.symm hb), one_mul]
      simp [List.mem_cons, Ne.symm hb]

theorem list_prod_mulSingle {n : ℕ} {G : Fin n → Type*} [∀ i, Monoid (G i)] (x : ∀ i, G i) :
    ((List.finRange n).map fun i => Pi.mulSingle i (x i)).prod = x := by
  funext k
  rw [Pi.list_prod_apply, List.map_map]
  have := list_prod_map_mulSingle x k (List.finRange n) (List.nodup_finRange n)
  simpa [Function.comp_def] using this

end GlobalTheory.LevProd.Fwd

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil

namespace GlobalTheory.LevProd.Fwd

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word} {a : GeoAll W u} {t : W.P.T}


end GlobalTheory.LevProd.Fwd

namespace GlobalTheory.LevProd
open GlobalTheory.LevProd.Fwd


end GlobalTheory.LevProd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualCoreComponentGluedAlongPair
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualCoreComponentGluedAlongPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch


open GlobalTheory.LatPair in
theorem exists_pair_of_line {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type}
    (Λ : Submodule 𝒪[k] (n ⊕ Fin 1 → k)) (hΛ : Λ.IsFullLattice k) (q : Unif k) (m : k)
    (h1 : ∀ t : k, (Sum.elim 0 (fun _ => t) : n ⊕ Fin 1 → k) ∈ Λ ↔ m * t ∈ 𝒪[k])
    (h2 : ∀ s : k, (∀ x ∈ Λ, s * ((q.1 : k) * (m * x (Sum.inr 0))) ∈ 𝒪[k]) ↔ s ∈ 𝒪[k]) :
    ∃ P : Pair k n, ∀ x : n ⊕ Fin 1 → k, x ∈ Λ ↔
      Sum.elim (fun a => x (Sum.inl a)) (fun j => m * x (Sum.inr j)) ∈ gluedS q 1 P.ker P.vec := by
  have hq := GlobalTheory.LevelUnfold.mul_inv_q q
  have hint : ∀ x ∈ Λ, (q.1 : k) * (m * x (Sum.inr 0)) ∈ 𝒪[k] := fun x hx => by
    simpa using (h2 1).2 (one_mem _) x hx
  have hqi : q.inv ∉ 𝒪[k] := fun h => q.2.not_isUnit (IsUnit.of_mul_eq_one ⟨_, h⟩ (Subtype.ext hq))
  obtain ⟨e, he, he1⟩ : ∃ e ∈ Λ, (q.1 : k) * (m * e (Sum.inr 0)) = 1 := by
    have h := mt (h2 q.inv).1 hqi
    push Not at h
    obtain ⟨x, hx, hx'⟩ := h
    have hu : IsUnit (⟨_, hint x hx⟩ : 𝒪[k]) := by
      rw [← IsLocalRing.notMem_maximalIdeal, q.mem_max_iff]
      rintro ⟨c, hc⟩
      have hc' : (q.1 : k) * (m * x (Sum.inr 0)) = (q.1 : k) * c := congrArg Subtype.val hc
      apply hx'
      rw [hc', ← mul_assoc, mul_comm q.inv, hq, one_mul]
      exact c.2
    obtain ⟨c, hc⟩ := hu.exists_left_inv
    have hc' : (c : k) * ((q.1 : k) * (m * x (Sum.inr 0))) = 1 := congrArg Subtype.val hc
    refine ⟨c • x, Λ.smul_mem c hx, ?_⟩
    rw [← hc']
    change _ * (m * ((c : k) * _)) = _
    ring
  have hsplit : ∀ x : n ⊕ Fin 1 → k, x = inX k n 1 (x ∘ Sum.inl) + (Sum.elim 0 (fun _ => x (Sum.inr 0)) : n ⊕ Fin 1 → k) := fun x => by
    ext (j | j)
    · simp [inX]
    · obtain rfl : j = 0 := Subsingleton.elim _ _
      simp [inX]
  let L : Submodule 𝒪[k] (n → k) := Λ.comap (inX k n 1)
  have hL : ∀ x : n ⊕ Fin 1 → k, m * x (Sum.inr 0) ∈ 𝒪[k] → (x ∈ Λ ↔ x ∘ Sum.inl ∈ L) := fun x hx => by
    conv_lhs => rw [hsplit x]
    exact Λ.add_mem_iff_left ((h1 _).2 hx)
  have key : ∀ (x : n ⊕ Fin 1 → k) (s : 𝒪[k]), (q.1 : k) * (m * x (Sum.inr 0)) = s →
      (x ∈ Λ ↔ x ∘ Sum.inl - s • (e ∘ Sum.inl) ∈ L) := fun x s hs => by
    rw [← Λ.sub_mem_iff_left (Λ.smul_mem s he)]
    refine hL (x - s • e) ?_
    have h0 : (q.1 : k) * (m * (x - s • e) (Sum.inr 0)) = 0 := by
      change (q.1 : k) * (m * (x _ - (s : k) * e _)) = 0
      linear_combination hs - (s : k) * he1
    rw [(mul_eq_zero.1 h0).resolve_left q.ne_zero]
    exact zero_mem _
  have hqe : q.1 • (e ∘ Sum.inl) ∈ L := by
    refine (hL (q.1 • e) ?_).1 (Λ.smul_mem _ he)
    change m * ((q.1 : k) * e _) ∈ _
    rw [mul_left_comm, he1]
    exact one_mem _
  have hlat : L.IsLattice k := by
    refine ⟨?_, ?_⟩
    · refine Submodule.fg_of_fg_map_injective (inX k n 1) (fun x y h => ?_) (hΛ.fg.of_le (Submodule.map_comap_le _ _))
      funext j
      exact congrFun h (Sum.inl j)
    · intro s hs hli
      exact (LinearIndependent.iff_fractionRing _ _).mp hli
  have hfull : L.IsFullLattice k := by
    refine { toIsLattice := hlat, span_eq_top := ?_ }
    rw [eq_top_iff]
    intro y _
    have hy : inX k n 1 y ∈ Submodule.span k (Λ : Set (n ⊕ Fin 1 → k)) := by
      rw [hΛ.span_eq_top]
      trivial
    have hproj : ∀ x ∈ Submodule.span k (Λ : Set (n ⊕ Fin 1 → k)),
        x ∘ Sum.inl ∈ Submodule.span k (L : Set (n → k)) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        have hm : q.1 • (x ∘ Sum.inl) ∈ L := by
          refine (hL (q.1 • x) ?_).1 (Λ.smul_mem _ hx)
          change m * ((q.1 : k) * x (Sum.inr 0)) ∈ 𝒪[k]
          simpa [mul_comm, mul_left_comm, mul_assoc] using hint x hx
        have := Submodule.smul_mem (Submodule.span k (L : Set (n → k))) q.inv (Submodule.subset_span hm)
        simpa using this
      | zero => simp
      | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
      | smul a x _ hx => exact Submodule.smul_mem _ a hx
    simpa [inX] using hproj _ hy
  have hglue : IsGlue L (e ∘ Sum.inl) := by
    refine (isGlue_iff q).2 ⟨hfull, fun h => hqi ?_, hqe⟩
    have h3 : (Sum.elim 0 (fun _ => e (Sum.inr 0)) : n ⊕ Fin 1 → k) ∈ Λ := by
      rw [← Λ.add_mem_iff_right (show inX k n 1 (e ∘ Sum.inl) ∈ Λ from h), ← hsplit]
      exact he
    have h4 : q.inv = m * e (Sum.inr 0) := by
      rw [← mul_one q.inv, ← he1, ← mul_assoc, mul_comm q.inv, hq, one_mul]
    rw [h4]
    exact (h1 _).1 h3
  obtain ⟨P, hk, hv⟩ := hglue.exists_pair
  have hd : e ∘ Sum.inl - P.vec ∈ L := hk ▸ Pair.sub_vec_mem hv
  have hvec : ∀ (y : n → k) (s : 𝒪[k]), y - s • (e ∘ Sum.inl) ∈ L ↔ y - s • P.vec ∈ L := fun y s => by
    rw [← L.add_mem_iff_left (L.smul_mem s hd), smul_sub, sub_add_sub_cancel]
  refine ⟨P, fun x => ?_⟩
  rw [GlobalTheory.LevelUnfold.mem_gluedS, hk]
  constructor
  · intro hx
    refine ⟨⟨_, hint x hx⟩, (hvec _ _).1 ((key x _ rfl).1 hx), fun i => ⟨fun _ => ?_, fun hi => absurd hi (by omega)⟩⟩
    obtain rfl : i = 0 := Subsingleton.elim _ _
    change m * x _ = q.inv * ((q.1 : k) * _)
    rw [← mul_assoc, mul_comm q.inv, hq, one_mul]
  · rintro ⟨s, hs, hs'⟩
    have h3 : m * x (Sum.inr 0) = q.inv * s := (hs' 0).1 rfl
    refine (key x s ?_).2 ((hvec _ _).2 hs)
    rw [h3, ← mul_assoc, hq, one_mul]

section Place

open GlobalTheory.FinPl.FrameLat GlobalTheory.SeeSaw.CoreGlue

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)

theorem pr_cA_sec (c : k) : p.pr (cA D (p.sec c)) = 0 := by
  have he : p.pr p.e = 1 := by rw [← sec_one, p.pr_sec]
  have h0 : p.e * cA D (p.sec c) = 0 := by
    rw [← cA_cA p.e, ← map_mul, ← e_mul_sec p c, ← mul_assoc, cAe_mul_e, zero_mul, map_zero]
  have h1 := congrArg p.pr h0
  rwa [RingHom.map_mul, he, one_mul, RingHom.map_zero] at h1

theorem mul_sec_mem_intAt_iff (a : AE D) (t : k) : a * p.sec t ∈ intAt D (· = p.v) ↔ p.pr a * t ∈ 𝒪[k] := by
  rw [mul_comm, sec_mul_right, mem_intAt_iff p (sec_mem_idAt p _), pr_cA_sec, p.pr_sec, and_iff_left (zero_mem _), mul_comm]

theorem cA_sec_mul (a : AE D) (t : k) : cA D (p.sec t) * a = cA D (p.sec (t * p.pr (cA D a))) := by
  rw [← sec_mul_right, RingHom.map_mul, cA_cA]

theorem mul_cA_sec_mem_intAt_iff (a : AE D) (t : k) :
    a * cA D (p.sec t) ∈ intAt D (· = p.v) ↔ p.pr (cA D a) * t ∈ 𝒪[k] := by
  rw [mul_comm, cA_sec_mul, mem_intAt_iff p (csec_mem_idAt _), pr_cA_sec, cA_cA, p.pr_sec, and_iff_right (zero_mem _), mul_comm]

theorem exists_gluedW : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (n : Type) [Fintype n] [DecidableEq n] (β : GlobalTheory.FinPl.Frame p A n) (β₀ : GlobalTheory.FinPl.Frame p S (n ⊕ Fin 1)) (M : Lat S) (μ : D.host.E) (T : ℕ) (q : GlobalTheory.LatPair.Unif k), IsSumFrame o ζ β β₀ → IsSelfDualC S M → μ ≠ 0 → LineAt (vecB o ζ) μ M p.v → star ζ ⬝ᵥ L.gram *ᵥ ζ = -(μ * star μ * (T : D.host.E)) → valuation k (p.pr (incA D (T : D.host.E))) = valuation k ((q.1 : 𝒪[k]) : k) → ∃ P : GlobalTheory.LatPair.Pair k n, GluedW β₀ M q (p.pr (incA D μ)) P := by
  intro D k _ _ _ _ p S A L o ζ n _ _ β β₀ M μ T q hs hM hμ hline hnorm hT
  have hb : p.pr (incA D (star μ)) ≠ 0 := (map_ne_zero (p.pr.comp (incA D))).2 (star_ne_zero.2 hμ)
  refine exists_pair_of_line (latW β₀ hM) ?_ q (p.pr (incA D μ)) (fun t => ?_) (fun s => ?_)
  · obtain ⟨Λ, h1, h2, -⟩ := exists_lat D k p S _ β₀ M hM
    have hlat : (latW β₀ hM).IsLattice k := by
      rwa [show latW β₀ hM = Λ from Submodule.ext fun x => (h2 x).symm]
    refine { toIsLattice := hlat, span_eq_top := ?_ }
    obtain ⟨m, s, c, hs, hc, -⟩ := exists_gen (p := p) hM
    rw [eq_top_iff]
    intro x _
    have hexp : x = ∑ l, c l (β₀.b *ᵥ x) • (β₀.b' *ᵥ fun a => p.pr (incA D (s l a))) := by
      have h := congrArg (β₀.b' *ᵥ ·) (hc (β₀.b *ᵥ x))
      simp only [Matrix.mulVec_sum, Matrix.mulVec_smul] at h
      rwa [Matrix.mulVec_mulVec, β₀.b'b, Matrix.one_mulVec] at h
    rw [hexp]
    refine Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    change (fun i => p.sec ((β₀.b *ᵥ (β₀.b' *ᵥ fun a => p.pr (incA D (s l a)))) i)) ∈ latV S M (· = p.v)
    rw [Matrix.mulVec_mulVec, β₀.bb', Matrix.one_mulVec]
    exact sec_inc_mem (hs l)
  · refine Iff.trans ?_ ((hline _ (sec_mem_idAt p t)).trans (mul_sec_mem_intAt_iff p _ t))
    have h2 : (fun i => p.sec ((β₀.b *ᵥ (Sum.elim 0 (fun _ => t) : n ⊕ Fin 1 → k)) i)) = p.sec t • ratV (vecB o ζ) := by
      funext i
      rw [Pi.smul_apply, smul_eq_mul, sec_mul_right, hs]
      congr 1
      simp [mulVec, dotProduct, Fintype.sum_sum_type, mul_comm]
    rw [← h2]
    rfl
  · obtain ⟨s', rfl⟩ : ∃ s', s = p.pr (incA D (star μ)) * s' := ⟨_, (mul_inv_cancel_left₀ hb s).symm⟩
    refine Iff.trans ?_ ((hline _ (csec_mem_idAt (p := p) s')).trans (mul_cA_sec_mem_intAt_iff p _ s'))
    have h2 : cA D (p.sec s') • ratV (vecB o ζ) =
        fun i => cA D (p.sec (s' * p.pr (incA D (star (vecB o ζ i))))) := funext fun i => cA_sec_mul p _ s'
    rw [h2]
    refine Iff.trans ?_ (csec_mem_iff hM _).symm
    have h3 : ∀ x : n ⊕ Fin 1 → k, s' * (p.pr (incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ)) * x (Sum.inr 0)) ∈ 𝒪[k] ↔
        p.pr (incA D (star μ)) * s' * ((q.1 : k) * (p.pr (incA D μ) * x (Sum.inr 0))) ∈ 𝒪[k] := fun x => by
      rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff, hnorm, RingHom.map_neg, RingHom.map_neg, RingHom.map_mul,
        RingHom.map_mul, RingHom.map_mul, RingHom.map_mul]
      generalize p.pr (incA D (T : D.host.E)) = a at hT
      generalize p.pr (incA D μ) = b
      generalize p.pr (incA D (star μ)) = c
      have h4 : valuation k (s' * (-(b * c * a) * x (Sum.inr 0))) =
          valuation k (c * s' * ((q.1 : k) * (b * x (Sum.inr 0)))) := by
        simp only [Valuation.map_mul, Valuation.map_neg, hT]
        ac_rfl
      rw [h4]
    constructor
    · intro h x hx
      have hx' : x = β₀.b *ᵥ (β₀.b' *ᵥ x) := by rw [mulVec_mulVec, β₀.bb', one_mulVec]
      rw [hx'] at hx ⊢
      rw [pair_sumFrame o ζ hs, h3]
      exact h _ hx
    · intro h x hx
      rw [← h3, ← pair_sumFrame o ζ hs]
      exact h _ hx

end Place

end GlobalTheory.Core.Mi.LatMatch

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualCoreComponentGluedAlongPairStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDualCore_component_gluedAlongPair : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (n : Type) [Fintype n] [DecidableEq n] (β : GlobalTheory.FinPl.Frame p A n) (β₀ : GlobalTheory.FinPl.Frame p S (n ⊕ Fin 1)) (M : Lat S) (μ : D.host.E) (T : ℕ) (q : GlobalTheory.LatPair.Unif k), IsSumFrame o ζ β β₀ → IsSelfDualC S M → μ ≠ 0 → LineAt (vecB o ζ) μ M p.v → star ζ ⬝ᵥ L.gram *ᵥ ζ = -(μ * star μ * (T : D.host.E)) → valuation k (p.pr (incA D (T : D.host.E))) = valuation k ((q.1 : 𝒪[k]) : k) → ∃ P : GlobalTheory.LatPair.Pair k n, GluedW β₀ M q (p.pr (incA D μ)) P := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.exists_gluedW | exact GlobalTheory.Core.Mi.LatMatch.exists_gluedW | (intros; apply GlobalTheory.Core.Mi.LatMatch.exists_gluedW <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameLatticeMembershipCriterion
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch

theorem sum_fin_two_mul_add_one {M : Type*} [AddCommMonoid M] {ρ n : ℕ} (hn : n = 2 * ρ + 1) (f : Fin n → M)
    (a b : Fin ρ → M) (m : M) (ha : ∀ (i : Fin ρ) (j : Fin n), j.1 = i.1 → f j = a i) (hm : ∀ j : Fin n, j.1 = ρ → f j = m)
    (hb : ∀ (i : Fin ρ) (j : Fin n), j.1 + i.1 = 2 * ρ → f j = b i) :
    ∑ j, f j = ∑ i, a i + m + ∑ i, b i := by
  subst hn
  have e : ρ + (1 + ρ) = 2 * ρ + 1 := by omega
  rw [← Fin.sum_congr' f e, Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_one, add_assoc]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => ha i _ (by simp)
  · congr 1
    · exact hm _ (by simp)
    · rw [← Equiv.sum_comp Fin.revPerm b]
      refine Finset.sum_congr rfl fun i _ => hb _ _ ?_
      simp [Fin.val_rev]
      omega

theorem mul_div_mem_integer_iff {k : Type} [Field k] [ValuativeRel k] {c : k} (hc : valuation k c = 1) (w z : k) :
    w * (z / c) ∈ 𝒪[k] ↔ w * z ∈ 𝒪[k] := by
  rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff, map_mul, map_mul, map_div₀, hc, div_one]

end GlobalTheory.Core.Mi.LatMatch

namespace GlobalTheory.Core.Mi.LatMatch

theorem mul_mul_div_cancel_left' {k : Type} [Field k] {c : k} (hc : c ≠ 0) (P X : k) : c * P * (X / c) = P * X := by
  field_simp

end GlobalTheory.Core.Mi.LatMatch

end
end

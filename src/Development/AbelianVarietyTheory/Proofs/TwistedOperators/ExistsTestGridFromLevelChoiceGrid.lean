module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinerOfKFiniteVectors
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceStdParamIsParam
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicityMapEqZeroOfTranslatedEvaluationAeZer

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSelfDualFrameOfStandardSelfDualLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSelfDualFrameOfStandardSelfDualLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory
namespace SDFrameCompletion

theorem exists_isSDFrame_of_isSelfDualC : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), (Λ : Set (Fin V.rank → D.host.E)) = L0c D V → IsSelfDualC V Λ → ∃ β, IsSDFrame V β Λ 1 := by
  intro D V Λ hΛ hsd
  exact GlobalTheory.AdelicFrame.exists_isSDFrame D V Λ hΛ (GlobalTheory.AdIsom.dualL_eq hsd)

end SDFrameCompletion
end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSelfDualFrameOfStandardSelfDualLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_selfDual_frame_of_standard_selfDual_lattice : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), (Λ : Set (Fin V.rank → D.host.E)) = L0c D V → IsSelfDualC V Λ → ∃ β, IsSDFrame V β Λ 1 := by
  first | exact @GlobalTheory.SDFrameCompletion.exists_isSDFrame_of_isSelfDualC | exact GlobalTheory.SDFrameCompletion.exists_isSDFrame_of_isSelfDualC | (intros; apply GlobalTheory.SDFrameCompletion.exists_isSDFrame_of_isSelfDualC <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOrthogonalSumTestGridOfLevelChoiceGrid
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOrthogonalSumTestGridOfLevelChoiceGrid
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridJoin

variable {D : D7}

theorem hT_eq_coords (S : HSp D) (x y : S.V) :
    S.hT x y = ∑ i, ∑ j, star (S.frame.repr x i) * S.gram i j * S.frame.repr y j := by
  conv_lhs => rw [← S.frame.sum_repr x, ← S.frame.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    starRingEnd_apply, Finset.mul_sum, RingHom.id_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Formalism.BasicNotions.HSpace.gram]
  ring

theorem hT_cols (S : HSp D) {k l : ℕ} (a : Matrix (Fin S.rank) (Fin k) D.host.E) (b : Matrix (Fin S.rank) (Fin l) D.host.E)
    (q : Fin k) (p : Fin l) :
    S.hT (S.frame.equivFun.symm (fun i => a i q)) (S.frame.equivFun.symm (fun i => b i p)) =
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) a * S.gram * b) q p := by
  rw [hT_eq_coords]
  have e1 : ∀ v : Fin S.rank → D.host.E, S.frame.repr (S.frame.equivFun.symm v) = v := fun v => by
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  simp only [e1, Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem exists_orthogonalSum_testGrid_of_levelChoiceGrid {D : D7} (A B : GlobalTheory.Grid.Node D) {c : ℕ} {ε : D.host.E}
    (d : GlobalTheory.ChiGrid.HermitianOrthogonalExtensionData A.V B.V c ε) (𝔟 : Fin c → GlobalTheory.Grid.FrId D) (_hε : ε = 1 ∨ ε = -1)
    (hΛ : B.Λ = d.lat A.Λ 𝔟) :
    ∃ d' : GlobalTheory.Grid.HermitianOrthogonalExtensionData A B c, d'.ι = d.ι ∧ d'.Is (fun p q => GlobalTheory.ChiGrid.antiDiagonalSignGramMatrix c ε p q) 𝔟 := by
  refine ⟨⟨d.ι, fun p => B.V.frame.equivFun.symm (fun k => d.a k p)⟩, rfl, ?_⟩
  have e1 : ∀ v : Fin B.V.rank → D.host.E, B.V.frame.repr (B.V.frame.equivFun.symm v) = v := fun v => by
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  refine ⟨d.isom, ?_, ?_, d.rank, ?_⟩
  ·
    intro x p
    show B.V.hT _ (d.ι x) = 0
    conv_lhs => rw [← A.V.frame.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, smul_eq_mul]
    refine Finset.sum_eq_zero fun k _ => ?_
    have h1 := B.V.herm.eq (d.ι (A.V.frame k)) (B.V.frame.equivFun.symm (fun i => d.a i p))
    have h2 : d.ι (A.V.frame k) = B.V.frame.equivFun.symm (fun i => frameMat B.V A.V d.ι i k) := by
      apply B.V.frame.equivFun.injective
      rw [LinearEquiv.apply_symm_apply]
      ext i
      simp [frameMat, LinearMap.toMatrix_apply]
    have h3 : B.V.hT (d.ι (A.V.frame k)) (B.V.frame.equivFun.symm (fun i => d.a i p)) = 0 := by
      rw [h2, hT_cols, d.perp]; rfl
    rw [← h1, h3]
    simp
  ·
    intro p q
    show B.V.hT _ _ = _
    rw [hT_cols, d.gram]
    simp only [GlobalTheory.ChiGrid.antiDiagonalSignGramMatrix]
    split_ifs <;> first | rfl | (exfalso; omega) | (simp_all [Fin.ext_iff]; omega) | simp_all
  ·
    have key : ∀ (x : A.V.V) (t : Fin c → D.host.E),
        B.V.frame.equivFun (d.ι x + ∑ p, t p • B.V.frame.equivFun.symm (fun k => d.a k p)) =
          frameMat B.V A.V d.ι *ᵥ A.V.frame.equivFun x + d.a *ᵥ t := by
      intro x t
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_add (f := _), map_sum]
      congr 1
      · simp only [Module.Basis.equivFun_apply, frameMat]
        exact (LinearMap.toMatrix_mulVec_repr _ _ _ _).symm
      · simp only [map_smul, LinearEquiv.apply_symm_apply]
        funext i
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
        exact Finset.sum_congr rfl fun p _ => mul_comm _ _
    intro y
    show B.V.frame.equivFun y ∈ B.Λ ↔ _
    rw [hΛ]
    constructor
    · rintro ⟨z, hz, u, hu, hy⟩
      refine ⟨A.V.frame.equivFun.symm z, ?_, u, hu, ?_⟩
      · show A.V.frame.equivFun (A.V.frame.equivFun.symm z) ∈ A.Λ
        rwa [LinearEquiv.apply_symm_apply]
      · apply B.V.frame.equivFun.injective
        rw [key, LinearEquiv.apply_symm_apply]
        exact hy
    · rintro ⟨x, hx, t, ht, rfl⟩
      exact ⟨A.V.frame.equivFun x, hx, t, ht, key x t⟩

end GlobalTheory.GridJoin

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOrthogonalSumTestGridOfLevelChoiceGridStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_extensionData_antiDiagonalSignGram_of_lat_eq : ∀ {D : D7} (A B : GlobalTheory.Grid.Node D) {c : ℕ} {ε : D.host.E} (d : GlobalTheory.ChiGrid.HermitianOrthogonalExtensionData A.V B.V c ε) (𝔟 : Fin c → GlobalTheory.Grid.FrId D), (ε = 1 ∨ ε = -1) → B.Λ = d.lat A.Λ 𝔟 → ∃ d' : GlobalTheory.Grid.HermitianOrthogonalExtensionData A B c, d'.ι = d.ι ∧ d'.Is (fun p q => GlobalTheory.ChiGrid.antiDiagonalSignGramMatrix c ε p q) 𝔟 := by
  first | exact @GlobalTheory.GridJoin.exists_orthogonalSum_testGrid_of_levelChoiceGrid | exact GlobalTheory.GridJoin.exists_orthogonalSum_testGrid_of_levelChoiceGrid | (intros; apply GlobalTheory.GridJoin.exists_orthogonalSum_testGrid_of_levelChoiceGrid <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsHarishChandraParamGridRowRealParameter
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsHarishChandraParamGridRowRealParameter
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridHC

open GlobalTheory.SignedHC Finset

theorem inCoset_weightX (D : D7) (τ : D.what₂.Tau) (j : ℕ) : InCoset (1 / 2) ((GlobalTheory.Grid.grid D τ).weightX j) := by
  induction j with
  | zero => exact GlobalTheory.ChiGrid.inCoset_weightX_zero (GlobalTheory.ChiGrid.odd_sLen D)
  | succ j ih =>
    rw [(GlobalTheory.Grid.grid D τ).weightX_succ]
    intro x hx
    rcases mem_union.1 hx with h | h
    · exact ih x h
    · obtain ⟨a, -, rfl⟩ := GlobalTheory.SignedHC.mem_block.1 h
      obtain ⟨u, hu⟩ := D.R.t_odd
      have e : ((GlobalTheory.Grid.grid D τ).t : ℚ) = 2 * u + 1 := by
        have : ((GlobalTheory.Grid.grid D τ).t : ℚ) = D.R.t := rfl
        rw [this, hu]; push_cast; ring
      refine ⟨-(GlobalTheory.Grid.grid D τ).e (j + 1) + u - a, ?_⟩
      push_cast
      rw [e]
      ring

theorem even_rkX (D : D7) (j : ℕ) : Even (GlobalTheory.Grid.rkX D j) := GlobalTheory.ChiGrid.even_rankX D j

theorem isHCParam_parXp : ∀ (D : D7), HostHyp D → ∀ (j : ℕ), 1 ≤ j → j ≤ D.R.m → ∀ (τ : D.what₂.Tau) (n : ℕ) (lam : Fin n → ℝ)
    (ε : Fin n → Bool), n = GlobalTheory.Grid.rkX D j → IsEnum (GlobalTheory.Grid.parXp D j τ) lam ε → Formalism.QuantumDeterminants.IsHCParam lam := by
  intro D _ j _ _ τ n lam ε hn hE
  obtain ⟨hanti, q, hq, hS⟩ := hE
  refine ⟨hanti, fun a => ?_⟩
  have hmem : (q a, ε a) ∈ GlobalTheory.Grid.parXp D j τ := by
    rw [hS]; exact mem_image.2 ⟨a, mem_univ _, rfl⟩
  have hx : q a ∈ (GlobalTheory.Grid.grid D τ).weightX j := by
    obtain ⟨x, hx, hxe⟩ := mem_image.1 hmem
    have : x = q a := congrArg Prod.fst hxe
    exact this ▸ hx
  obtain ⟨z, hz⟩ := inCoset_weightX D τ j (q a) hx
  obtain ⟨k, hk⟩ := even_rkX D j
  refine ⟨z - k + 1, ?_⟩
  rw [hq a, hz, hn, hk]
  push_cast
  ring

end GlobalTheory.GridHC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsHarishChandraParamGridRowRealParameterStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHarishChandraParam_gridRowRealParameter : ∀ (D : D7), HostHyp D → ∀ (j : ℕ), 1 ≤ j → j ≤ D.R.m → ∀ (τ : D.what₂.Tau) (n : ℕ) (lam : Fin n → ℝ) (ε : Fin n → Bool), n = GlobalTheory.Grid.rkX D j → IsEnum (GlobalTheory.Grid.parXp D j τ) lam ε → Formalism.QuantumDeterminants.IsHCParam lam := by
  first | exact @GlobalTheory.GridHC.isHCParam_parXp | exact GlobalTheory.GridHC.isHCParam_parXp | (intros; apply GlobalTheory.GridHC.isHCParam_parXp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TestGridPlaceDataOfLevelChoiceGrid
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TestGridPlaceDataOfLevelChoiceGrid
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.GridJoin

theorem natCast_mem_under_iff (Aa : Type) [CommRing Aa] [IsDomain Aa] {B : Type} [CommRing B] [IsDomain B]
    [Algebra Aa B] [Algebra.IsIntegral Aa B] (w : HeightOneSpectrum B) (n : ℕ) :
    (n : Aa) ∈ (w.under Aa).asIdeal ↔ (n : B) ∈ w.asIdeal := by
  rw [HeightOneSpectrum.under_asIdeal, Ideal.mem_under, map_natCast]

theorem placeDat_of_grid : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc}, (∀ PP ∈ R.Pg, ∀ PP' ∈ R.Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') → PP = PP') → Formalism.L2.Host.SplitsCompletely {G'.pl.w G'.pl.v0} → (∀ k, GlobalTheory.ChiGrid.q0 D ≠ D.host.g k) → (GlobalTheory.ChiGrid.q0 D ≠ D.sp.T ∧ ∀ u : D.what₂.Word, GlobalTheory.ChiGrid.q0 D ≠ (D.mem u).A.T) → ∀ e : AE D, IsIdemSum e G'.pl.W0 → ∃ Z : GlobalTheory.Grid.PlaceDat D, Z.Is R.Pg R.Q e ∧ Z.q0 = GlobalTheory.ChiGrid.q0 D ∧ Z.w0 = G'.pl.w G'.pl.v0 ∧ Z.e0 = G'.pl.depth sc G'.pl.v0 ∧ Z.W R.Pg = G'.pl.W0 ∧ Z.ideal R.Pg = G'.modul ∧ Z.S0 R.Pg = G'.pl.S0 ∧ ∀ w, w ∈ R.Pg ∨ w ∈ Z.Wd → w.under (𝓞 D.host.F) ∈ GlobalTheory.ChiGrid.S1 D := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc F hR G' hPg hsplit hg hT e he
  classical

  have hPgOver : ∀ PP ∈ R.Pg, ∃ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    intro PP hPP
    obtain ⟨k, hk⟩ := (hR.lev.Pg PP).1 hPP
    refine ⟨k, (natCast_mem_under_iff (𝓞 D.host.K) PP _).1 ?_⟩
    rw [show PP.under (𝓞 D.host.K) = R.C.P.pb k from hk]
    exact R.C.P.pb_over k
  have gS1 : ∀ (v : Pl D.host.F) (k : Fin 2), ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal → v ∈ S1 D := by
    intro v k hk
    rw [S1_mem_OmF]
    fin_cases k
    · exact Or.inl hk
    · exact Or.inr (Or.inl hk)
  have hPgS1 : ∀ PP ∈ R.Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ S1 D := by
    intro PP hPP
    obtain ⟨k, hk⟩ := hPgOver PP hPP
    exact gS1 _ k ((natCast_mem_under_iff (𝓞 D.host.F) PP _).2 hk)
  set P := G'.pl with hPdef
  have hS0 : ∀ v ∈ S1 D, v ∈ insert P.v0 (S1 D) := fun v hv => Finset.mem_insert_of_mem hv
  have hv0 : P.v0 ∈ insert P.v0 (S1 D) := Finset.mem_insert_self _ _

  have hPgw : ∀ PP ∈ R.Pg, P.w ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) = PP := by
    intro PP hPP
    obtain ⟨k, hk⟩ := hPgOver PP hPP
    have hkF := (natCast_mem_under_iff (𝓞 D.host.F) PP _).2 hk
    exact hPg _ (P.w_g _ k hkF) _ hPP (P.w_over _ (hS0 _ (gS1 _ k hkF)))
  let pd : Pl D.host.F → Prop := fun v =>
    ((D.host.pde : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal ∨ ((D.host.pde' : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal
  let Wd : Finset (Pl D.host.E) := ((S1 D).filter pd).image P.w
  let Z : GlobalTheory.Grid.PlaceDat D := ⟨q0 D, P.w P.v0, P.depth sc P.v0, Wd⟩
  have hmemWd : ∀ w, w ∈ Wd ↔ ∃ v ∈ S1 D, pd v ∧ P.w v = w := by
    intro w
    simp only [Wd, Finset.mem_image, Finset.mem_filter, and_assoc]

  have hW : Z.W R.Pg = P.W0 := by
    ext x
    simp only [GlobalTheory.Grid.PlaceDat.W, Places.W0, Places.S0, Finset.mem_union, Finset.mem_singleton, Finset.mem_image,
      Finset.mem_insert, Z]
    constructor
    · rintro ((hx | hx) | rfl)
      · exact ⟨_, Or.inr (hPgS1 x hx), hPgw x hx⟩
      · obtain ⟨v, hv, -, rfl⟩ := (hmemWd x).1 hx
        exact ⟨v, Or.inr hv, rfl⟩
      · exact ⟨P.v0, Or.inl rfl, rfl⟩
    · rintro ⟨v, hv | hv, rfl⟩
      · exact Or.inr (by rw [hv])
      · rcases (S1_mem_OmF D).1 hv with h | h | h | h
        · exact Or.inl (Or.inl (P.w_g v 0 h))
        · exact Or.inl (Or.inl (P.w_g v 1 h))
        · exact Or.inl (Or.inr ((hmemWd _).2 ⟨v, hv, Or.inl h, rfl⟩))
        · exact Or.inl (Or.inr ((hmemWd _).2 ⟨v, hv, Or.inr h, rfl⟩))
  have hinj : ∀ v ∈ P.S0, ∀ v' ∈ P.S0, P.w v = P.w v' → v = v' := fun v hv v' hv' h =>
    (P.under_w hv).symm.trans ((congrArg _ h).trans (P.under_w hv'))
  have hIdeal : Z.ideal R.Pg = G'.modul := by
    rw [GlobalTheory.Grid.PlaceDat.ideal, hW, Places.W0, Finset.prod_image hinj]
    refine Finset.prod_congr rfl fun v hv => ?_
    congr 1
    have hv0' : P.v0 ∈ P.S0 := P.mem_S0_of_sum_eq.2 (Or.inl rfl)
    simp only [GlobalTheory.Grid.PlaceDat.depth, Z]
    by_cases h : v = P.v0
    · rw [h, if_pos rfl]
    · rw [if_neg (fun h' => h (hinj v hv _ hv0' h'))]
      unfold Places.depth
      rw [if_neg h]
  have hS0eq : Z.S0 R.Pg = P.S0 := by
    ext v
    simp only [GlobalTheory.Grid.PlaceDat.S0, hW, Places.W0, Finset.mem_image]
    constructor
    · rintro ⟨_, ⟨v', hv', rfl⟩, rfl⟩
      rwa [P.under_w hv']
    · intro hv
      exact ⟨_, ⟨v, hv, rfl⟩, P.under_w hv⟩

  have hWdS1 : ∀ w ∈ Wd, w.under (𝓞 D.host.F) ∈ S1 D := by
    intro w hw
    obtain ⟨v, hv, -, rfl⟩ := (hmemWd w).1 hw
    rw [P.w_over v (hS0 v hv)]; exact hv
  have hq := leastSplitAuxiliaryPrimeThetaChain_spec D
  refine ⟨Z, ?_, rfl, rfl, rfl, hW, hIdeal, hS0eq, ?_⟩
  · refine
      { prime := hq.1
        five_le := ?_
        referencePlaceOverPrime := ?_
        split := hsplit
        ne_g := hg
        ne_pde := leastSplitAuxiliaryPrime_ne_typePrimes D
        referencePrimeNeTwist := hT
        coprime := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hq.1).2 hq.2.2)
        offQ := ?_
        depth_pos := P.depth_pos sc P.v0
        Wd_over := ?_
        Wd_all := ?_
        idem := by rw [hW]; exact he }
    · have h1 : 0 < LevelStarExponents.condE D := by
        have := D.host.qd_big
        unfold LevelStarExponents.condE
        exact mul_pos (mul_pos D.host.QS_pos (by omega)) (by omega)
      have h4 : 4 ≤ LevelStarExponents.condE D := Nat.le_of_dvd h1 (by unfold LevelStarExponents.condE; exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left ((Dvd.intro_left (2 ^ D.R.e) (by rw [pow_add]; norm_num)).trans D.host.tower_dvd) _) _)
      have h2 := (rPr_spec D).1.two_le
      have h3 : 5 < Formalism.MainNotions.rPrAv D * LevelStarExponents.condE D := by nlinarith
      show 5 ≤ q0 D
      by_contra hlt
      have hm := hq.2.1
      rw [Nat.mod_eq_of_lt (by show q0 D < _; omega)] at hm
      exact hq.1.one_lt.ne' hm
    · show (((q0 D : ℕ) : 𝓞 D.host.E) ∈ (P.w P.v0).asIdeal)
      refine (natCast_mem_under_iff (𝓞 D.host.F) _ _).1 ?_
      rw [P.w_over _ hv0]; exact P.basePlace_over_qZero
    · intro t w hw
      show w.under (𝓞 D.host.F) ≠ (P.w P.v0).under (𝓞 D.host.F)
      rw [P.w_over _ hv0]
      exact P.levelPlace_ne_basePlace t w hw
    · intro w hw
      obtain ⟨v, hv, hpd, rfl⟩ := (hmemWd w).1 hw
      have hu := P.w_over v (hS0 v hv)
      rcases hpd with h | h
      · left; show ((D.host.pde : ℕ) : 𝓞 D.host.E) ∈ (P.w v).asIdeal
        exact (natCast_mem_under_iff (𝓞 D.host.F) _ _).1 (by rw [hu]; exact h)
      · right; show ((D.host.pde' : ℕ) : 𝓞 D.host.E) ∈ (P.w v).asIdeal
        exact (natCast_mem_under_iff (𝓞 D.host.F) _ _).1 (by rw [hu]; exact h)
    · intro p hp
      have hpd : ∀ v : Pl D.host.F, ((p : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal → pd v := by
        intro v h
        rcases hp with rfl | rfl
        · exact Or.inl h
        · exact Or.inr h
      have hS1 : ∀ v : Pl D.host.F, ((p : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal → v ∈ S1 D := by
        intro v h
        rcases hp with rfl | rfl
        · exact (S1_mem_OmF D).2 (Or.inr (Or.inr (Or.inl h)))
        · exact (S1_mem_OmF D).2 (Or.inr (Or.inr (Or.inr h)))
      refine ⟨?_, ?_, ?_⟩
      · intro w hw
        have h := (natCast_mem_under_iff (𝓞 D.host.F) w p).2 hw
        exact ⟨P.w (w.under (𝓞 D.host.F)), (hmemWd _).2 ⟨_, hS1 _ h, hpd _ h, rfl⟩,
          P.w_over _ (hS0 _ (hS1 _ h))⟩
      · obtain ⟨𝔭, h𝔭⟩ := P.w_de p hp
        refine ⟨𝔭, fun w hw hpw => ?_⟩
        obtain ⟨v, hv, -, rfl⟩ := (hmemWd w).1 hw
        have h := (natCast_mem_under_iff (𝓞 D.host.F) (P.w v) p).2 hpw
        rw [P.w_over v (hS0 v hv)] at h
        exact h𝔭 v h
      · intro t w hw hpw
        have h := (natCast_mem_under_iff (𝓞 D.host.F) w p).2 hpw
        rw [P.w_Q t w hw (hS1 _ h)]
        exact (hmemWd _).2 ⟨_, hS1 _ h, hpd _ h, rfl⟩
  · rintro w (hw | hw)
    · exact hPgS1 w hw
    · exact hWdS1 w hw

end GlobalTheory.GridJoin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TestGridPlaceDataOfLevelChoiceGridStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.testGridPlaceData_of_levelChoiceGrid : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc}, (∀ PP ∈ R.Pg, ∀ PP' ∈ R.Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') → PP = PP') → Formalism.L2.Host.SplitsCompletely {G'.pl.w G'.pl.v0} → (∀ k, GlobalTheory.ChiGrid.q0 D ≠ D.host.g k) → (GlobalTheory.ChiGrid.q0 D ≠ D.sp.T ∧ ∀ u : D.what₂.Word, GlobalTheory.ChiGrid.q0 D ≠ (D.mem u).A.T) → ∀ e : AE D, IsIdemSum e G'.pl.W0 → ∃ Z : GlobalTheory.Grid.PlaceDat D, Z.Is R.Pg R.Q e ∧ Z.q0 = GlobalTheory.ChiGrid.q0 D ∧ Z.w0 = G'.pl.w G'.pl.v0 ∧ Z.e0 = G'.pl.depth sc G'.pl.v0 ∧ Z.W R.Pg = G'.pl.W0 ∧ Z.ideal R.Pg = G'.modul ∧ Z.S0 R.Pg = G'.pl.S0 ∧ ∀ w, w ∈ R.Pg ∨ w ∈ Z.Wd → w.under (𝓞 D.host.F) ∈ GlobalTheory.ChiGrid.S1 D := by
  first | exact @GlobalTheory.GridJoin.placeDat_of_grid | exact GlobalTheory.GridJoin.placeDat_of_grid | (intros; apply GlobalTheory.GridJoin.placeDat_of_grid <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharacterGridIsAuxiliaryCharacterTestGrid
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharacterGridIsAuxiliaryCharacterTestGrid
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Grid

theorem heckeCharacterGrid_isAuxiliaryCharacter_testGrid_alt : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Grid.gap D = GlobalTheory.ChiGrid.gap D 1 → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (Z : GlobalTheory.Grid.PlaceDat D), Z.S0 R.Pg = G'.pl.S0 → (∀ w, w ∈ R.Pg ∨ w ∈ Z.Wd → w.under (𝓞 D.host.F) ∈ GlobalTheory.ChiGrid.S1 D) → (∀ w ∈ Z.Wd, Formalism.L2.Host.OverP D.host D.host.pde w ∨ Formalism.L2.Host.OverP D.host D.host.pde' w) → Z.w0 = G'.pl.w G'.pl.v0 → ∀ i, 1 ≤ i → i ≤ D.R.m → Z.IsGridPlaceAuxiliaryHeckeCharacter R.Pg (fun τ => GlobalTheory.Grid.cen D τ i) (G'.ch.chiH i) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc hgap hc G' Z hS0 hS1 hwd hw0 i hi1 hi2
  have hcen : ∀ τ, GlobalTheory.Grid.cen D τ i = GlobalTheory.ChiGrid.cen D sc.cGap τ i := by
    intro τ
    rw [hc]
    unfold GlobalTheory.Grid.cen GlobalTheory.ChiGrid.cen GlobalTheory.Grid.gridOf
    rw [hgap]
    rfl
  have hunit : (G'.ch.chiH i).IsUnitary := GlobalTheory.T.heckeChar_isUnitary_of_unitary_infinityType _ _ _ _ (G'.ch.inf i hi1 hi2)
  refine ⟨hunit, G'.ch.triv i hi1 hi2, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun τ => 2 * GlobalTheory.ChiGrid.cen D sc.cGap τ i, fun τ => ?_, G'.ch.inf i hi1 hi2⟩
    show ((2 * GlobalTheory.ChiGrid.cen D sc.cGap τ i : ℤ) : ℚ) = 2 * ((GlobalTheory.Grid.cen D τ i : ℤ) : ℚ)
    rw [hcen τ]; push_cast; ring
  · intro w hw
    rw [hS0] at hw
    exact G'.ch.unr i hi1 hi2 w hw
  · intro w hw
    exact G'.ch.lev1 i hi1 hi2 w (hS1 w hw)
  · intro w hw x hx
    exact G'.ch.wild i hi1 hi2 w (hwd w hw) x hx
  · have hu : Z.w0.under (𝓞 D.host.F) = G'.pl.v0 := by
      rw [hw0]; exact G'.pl.under_w (G'.pl.mem_S0_of_sum_eq.2 (Or.inl rfl))
    exact G'.ch.lev0 i hi1 hi2 Z.w0 hu

end GlobalTheory.Grid

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharacterGridIsAuxiliaryCharacterTestGridStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeCharacterGrid_isAuxiliaryCharacter_testGrid : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Grid.gap D = GlobalTheory.ChiGrid.gap D 1 → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (Z : GlobalTheory.Grid.PlaceDat D), Z.S0 R.Pg = G'.pl.S0 → (∀ w, w ∈ R.Pg ∨ w ∈ Z.Wd → w.under (𝓞 D.host.F) ∈ GlobalTheory.ChiGrid.S1 D) → (∀ w ∈ Z.Wd, Formalism.L2.Host.OverP D.host D.host.pde w ∨ Formalism.L2.Host.OverP D.host D.host.pde' w) → Z.w0 = G'.pl.w G'.pl.v0 → ∀ i, 1 ≤ i → i ≤ D.R.m → Z.IsGridPlaceAuxiliaryHeckeCharacter R.Pg (fun τ => GlobalTheory.Grid.cen D τ i) (G'.ch.chiH i) := by
  first | exact @GlobalTheory.Grid.heckeCharacterGrid_isAuxiliaryCharacter_testGrid_alt | exact GlobalTheory.Grid.heckeCharacterGrid_isAuxiliaryCharacter_testGrid_alt | (intros; apply GlobalTheory.Grid.heckeCharacterGrid_isAuxiliaryCharacter_testGrid_alt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsHarishChandraParamGridColumnRealParameter
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsHarishChandraParamGridColumnRealParameter
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Grid

open GlobalTheory.SignedHC

theorem isHCParam_parP : ∀ (D : D7), HostHyp D → ∀ (i : ℕ), i ≤ D.R.m → ∀ (τ : D.what₂.Tau) (n : ℕ) (lam : Fin n → ℝ) (ε : Fin n → Bool), n = GlobalTheory.Grid.rkP D i → IsEnum (GlobalTheory.Grid.parP D i τ) lam ε → Formalism.QuantumDeterminants.IsHCParam lam := by
  intro D _ i _ τ n lam ε hn hE
  obtain ⟨hanti, q, hq, hS⟩ := hE
  refine ⟨hanti, fun a => ?_⟩
  have hmem : q a ∈ (grid D τ).weightX 0 := by
    have h0 : (q a, ε a) ∈ parP D i τ := by
      rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    rcases GridData.mem_parPi.1 h0 with ⟨l, hl, h⟩ | ⟨h1, _⟩ | ⟨l, h1, h2, h3, _⟩
    · exact GridData.mem_weightX.2 (Or.inl (GridData.mem_tops.2 ⟨l, hl, (Prod.ext_iff.1 h).1⟩))
    · exact GridData.mem_weightX.2 (Or.inr (Or.inl h1))
    · exact GridData.mem_weightX.2 (Or.inr (Or.inr (Or.inl ⟨l, by omega, h2, h3⟩)))
  have hs : Odd (grid D τ).s := GlobalTheory.ChiGrid.odd_sLen D
  obtain ⟨z, hz⟩ := GlobalTheory.ChiGrid.inCoset_weightX_zero hs _ hmem
  obtain ⟨u, hu⟩ := GlobalTheory.ChiGrid.even_rankP D i
  have hn' : (n : ℝ) = (u : ℝ) + u := by
    have : n = u + u := hn.trans hu
    rw [this]; push_cast; ring
  refine ⟨z + 1 - u, ?_⟩
  rw [hq a, hz, hn']
  push_cast
  ring

end GlobalTheory.Grid
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsHarishChandraParamGridColumnRealParameterStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHarishChandraParam_gridColumnRealParameter : ∀ (D : D7), HostHyp D → ∀ (i : ℕ), i ≤ D.R.m → ∀ (τ : D.what₂.Tau) (n : ℕ) (lam : Fin n → ℝ) (ε : Fin n → Bool), n = GlobalTheory.Grid.rkP D i → IsEnum (GlobalTheory.Grid.parP D i τ) lam ε → Formalism.QuantumDeterminants.IsHCParam lam := by
  first | exact @GlobalTheory.Grid.isHCParam_parP | exact GlobalTheory.Grid.isHCParam_parP | (intros; apply GlobalTheory.Grid.isHCParam_parP <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTestGridFromLevelChoiceGrid
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GridJoin

section Cast

variable {D : D7}

def hermitianOrthogonalExtensionDataCast {A A' B B' : GlobalTheory.Grid.Node D} {c : ℕ} (hA : A = A') (hB : B = B') (d : GlobalTheory.Grid.HermitianOrthogonalExtensionData A B c) :
    GlobalTheory.Grid.HermitianOrthogonalExtensionData A' B' c := hA ▸ hB ▸ d

theorem gridDecompositionCast_is_iff {A A' B B' : GlobalTheory.Grid.Node D} {c : ℕ} (hA : A = A') (hB : B = B') (d : GlobalTheory.Grid.HermitianOrthogonalExtensionData A B c)
    (g : Fin c → Fin c → D.host.E) (𝔟 : Fin c → GlobalTheory.Grid.FrId D) : (hermitianOrthogonalExtensionDataCast hA hB d).Is g 𝔟 ↔ d.Is g 𝔟 := by
  subst hA hB; rfl

def hermitianOrthogonalExtensionDataZero (A B : GlobalTheory.Grid.Node D) (c : ℕ) : GlobalTheory.Grid.HermitianOrthogonalExtensionData A B c := ⟨0, 0⟩

theorem joinStair {T : Type} {L : LevCh D T} (P : GlobalTheory.ChiGrid.Places L) (sc : GlobalTheory.ChiGrid.Consts) (c : ℕ) :
    GlobalTheory.ChiGrid.stairId (P.stA sc) (P.stAbar sc) c = GlobalTheory.Grid.staircaseExtensionIdeal (P.modul sc) c := by
  funext p
  simp only [GlobalTheory.ChiGrid.stairId, GlobalTheory.ChiGrid.Places.stA, GlobalTheory.ChiGrid.Places.stAbar, GlobalTheory.ChiGrid.Places.modulBar,
    GlobalTheory.Grid.staircaseExtensionIdeal, mul_pow, inv_pow, mul_inv, inv_inv]

theorem joinStair_top (c : ℕ) :
    GlobalTheory.ChiGrid.stairId D.host.AA D.host.AAbar c = GlobalTheory.Grid.staircaseExtensionIdeal (D := D) ⊤ c := by
  funext p
  simp [GlobalTheory.ChiGrid.stairId, GlobalTheory.Grid.staircaseExtensionIdeal, Ideal.pointwise_smul_def, Ideal.map_top, mul_pow, inv_pow]

theorem joinGram_one : (fun p q : Fin 1 => GlobalTheory.ChiGrid.antiDiagonalSignGramMatrix 1 (1 : D.host.E) p q) = fun _ _ => 1 := by
  funext p q
  fin_cases p; fin_cases q; simp [GlobalTheory.ChiGrid.antiDiagonalSignGramMatrix]

theorem joinGram_neg (c : ℕ) : (fun p q : Fin c => GlobalTheory.ChiGrid.antiDiagonalSignGramMatrix c (-1 : D.host.E) p q) = GlobalTheory.Grid.antiDiagonalSignGramMatrix D.host.E c := by
  funext p q
  rfl

end Cast

theorem exists_gridPre_spaces : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesUpqExists → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → (∀ X : GlobalTheory.ChiGrid.Node, X.InRange D.R.m → (∀ j, X ≠ .grid 0 j) → (G'.Λ X : Set _) = L0c D (G'.V X)) → (∀ PP ∈ R.Pg, ∀ PP' ∈ R.Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') → PP = PP') → Formalism.L2.Host.SplitsCompletely {G'.pl.w G'.pl.v0} → (∀ k, GlobalTheory.ChiGrid.q0 D ≠ D.host.g k) → (GlobalTheory.ChiGrid.q0 D ≠ D.sp.T ∧ ∀ u : D.what₂.Word, GlobalTheory.ChiGrid.q0 D ≠ (D.mem u).A.T) → (∀ i j, 1 ≤ i → i ≤ D.R.m → j ≤ D.R.m → ∀ τ, ∃ (lam : Fin (G'.V (.grid i j)).rank → ℝ) (ε : Fin (G'.V (.grid i j)).rank → Bool), IsEnum (GlobalTheory.Grid.parV D i j τ) lam ε ∧ (W.onb (.grid i j) τ)ᴴ * gramAt D (G'.V (.grid i j)) τ * W.onb (.grid i j) τ = Formalism.REAL.Jm ε) → (∀ i, i ≤ D.R.m → ∀ τ, ∃ (lam : Fin (G'.V (.core i)).rank → ℝ) (ε : Fin (G'.V (.core i)).rank → Bool), IsEnum (GlobalTheory.Grid.parP D i τ) lam ε ∧ (W.onb (.core i) τ)ᴴ * gramAt D (G'.V (.core i)) τ * W.onb (.core i) τ = Formalism.REAL.Jm ε) → (∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ, ∃ (lam : Fin (G'.V (.top j)).rank → ℝ) (ε : Fin (G'.V (.top j)).rank → Bool), IsEnum (GlobalTheory.Grid.parXp D j τ) lam ε ∧ (W.onb (.top j) τ)ᴴ * gramAt D (G'.V (.top j)) τ * W.onb (.top j) τ = Formalism.REAL.Jm ε) → W.cart (.top 0) = W.cart (.core D.R.m) → W.onb (.top 0) = W.onb (.core D.R.m) → ∀ e : AE D, IsIdemSum e G'.pl.W0 → ∃ G : GlobalTheory.Grid.GridPre R, G.idem = e ∧ G.IsSpaces ∧ G.IsChars ∧ SpAgree G W := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc hDS hH F hR hsc G' W hW hL hPg hsplit hg hT hOV hOP hOX hcT hoT e he
  classical
  obtain ⟨Z, hZ, hq0, hw0, he0, hWZ, hlvl, hS0, hS1⟩ := GlobalTheory.T.testGridPlaceData_of_levelChoiceGrid hR hPg hsplit hg hT e he
  let Sx : GlobalTheory.ChiGrid.Node → D.what₂.Tau → SPar := fun X => match X with
    | .grid i j => GlobalTheory.Grid.parV D i j
    | .core i => GlobalTheory.Grid.parP D i
    | .top j => GlobalTheory.Grid.parXp D j
  let good : GlobalTheory.ChiGrid.Node → Prop := fun X => match X with
    | .grid i j => 1 ≤ i ∧ i ≤ D.R.m ∧ j ≤ D.R.m
    | .core i => i ≤ D.R.m
    | .top j => 1 ≤ j ∧ j ≤ D.R.m
  have hgood : ∀ X, good X → X.InRange D.R.m ∧ ∀ j, X ≠ .grid 0 j := by
    intro X hX
    rcases X with ⟨i, j⟩ | i | j
    · exact ⟨⟨hX.2.1, hX.2.2⟩, fun j' h => by cases h; exact absurd hX.1 (by omega)⟩
    · exact ⟨hX, fun j' h => GlobalTheory.ChiGrid.Node.noConfusion h⟩
    · exact ⟨hX.2, fun j' h => GlobalTheory.ChiGrid.Node.noConfusion h⟩
  have hMod : ∀ X, good X → ∃ M : DSModel (G'.V X) (Sx X), cart M = W.cart X ∧ onb M = W.onb X := by
    intro X hX
    have hv := G'.isV (hgood X hX).1 (hgood X hX).2
    refine GlobalTheory.T.exists_discreteSeriesModel_of_orthonormalBasis_cartan D hDS (G'.V X) (Sx X) (W.onb X) (W.cart X) ?_ (W.onb_is X (hgood X hX).1)
    intro τ
    rcases X with ⟨i, j⟩ | i | j
    · obtain ⟨lam, ε, h1, h2⟩ := hOV i j hX.1 hX.2.1 hX.2.2 τ
      exact ⟨lam, ε, h1, GlobalTheory.T.isHarishChandraParam_gridVertexRealParameter D hH i j hX.1 hX.2.1 hX.2.2 τ _ lam ε hv.rank h1, h2⟩
    · obtain ⟨lam, ε, h1, h2⟩ := hOP i hX τ
      exact ⟨lam, ε, h1, GlobalTheory.T.isHarishChandraParam_gridColumnRealParameter D hH i hX τ _ lam ε hv.rank h1, h2⟩
    · obtain ⟨lam, ε, h1, h2⟩ := hOX j hX.1 hX.2 τ
      exact ⟨lam, ε, h1, GlobalTheory.T.isHarishChandraParam_gridRowRealParameter D hH j hX.1 hX.2 τ _ lam ε hv.rank h1, h2⟩
  have hFr : ∀ X, good X → ∃ β, IsSDFrame (G'.V X) β (G'.Λ X) 1 := fun X hX =>
    GlobalTheory.T.exists_selfDual_frame_of_standard_selfDual_lattice D _ _ (hL X (hgood X hX).1 (hgood X hX).2) (G'.isV (hgood X hX).1 (hgood X hX).2).sd
  choose M hM using hMod
  choose β hβ using hFr
  let mk : ∀ X, good X → GlobalTheory.Grid.Node D := fun X h => ⟨G'.V X, Sx X, M X h, G'.Λ X, β X h⟩
  let node : GlobalTheory.ChiGrid.Node → GlobalTheory.Grid.Node D := fun X => if h : good X then mk X h else GlobalTheory.Grid.row0 R 0
  have node_pos : ∀ X (h : good X), node X = mk X h := fun X h => dif_pos h
  have mk_is : ∀ X (h : good X), (mk X h).Is (X.rank D) (X.neg D.R.m) (Sx X) := fun X h => by
    have hv := G'.isV (hgood X h).1 (hgood X h).2
    exact ⟨hv.rank, hv.sigOK, hv.sig, rfl, hβ X h⟩
  have mk_agree : ∀ X (h : good X), NodeAgree (mk X h) W X := fun X h =>
    ⟨rfl, HEq.rfl, heq_of_eq (hM X h).1, heq_of_eq (hM X h).2⟩
  let GS : GlobalTheory.Grid.GridSp D :=
    { toPlaceDat := Z, nV := fun i j => node (.grid (i + 1) j), P := fun i => node (.core i), nX := fun j => node (.top (j + 1)) }
  have vert_eq : ∀ n x, 1 ≤ n → GS.vert R n x = node (.grid n x) := by
    intro n x hn
    cases n with
    | zero => omega
    | succ n => rfl
  have Xp_eq : ∀ n, 1 ≤ n → GS.Xp n = node (.top n) := by
    intro n hn
    cases n with
    | zero => omega
    | succ n => rfl
  have gP : ∀ i, i ≤ D.R.m → good (.core i) := fun i h => h
  have gV : ∀ i j, 1 ≤ i → i ≤ D.R.m → j ≤ D.R.m → good (.grid i j) := fun i j h1 h2 h3 => ⟨h1, h2, h3⟩
  have gX : ∀ j, 1 ≤ j → j ≤ D.R.m → good (.top j) := fun j h1 h2 => ⟨h1, h2⟩
  have hm2 := D.R.two_le_m

  obtain ⟨dP, -, hdP⟩ := GlobalTheory.T.exists_extensionData_antiDiagonalSignGram_of_lat_eq (GlobalTheory.Grid.row0 R 0) (mk (.core 0) (gP 0 (by omega))) G'.sp.dec0 (fun _ => 1) (Or.inl rfl)
    G'.sp.lat0

  have exV : ∀ i (h : 1 ≤ i ∧ i ≤ D.R.m), ∃ d : GlobalTheory.Grid.HermitianOrthogonalExtensionData (mk (.core i) (gP i h.2)) (mk (.grid i 0) (gV i 0 h.1 h.2 (by omega))) (i - 1),
      d.Is (fun p q => GlobalTheory.ChiGrid.antiDiagonalSignGramMatrix (i - 1) (-1 : D.host.E) p q) (GlobalTheory.ChiGrid.stairId (G'.pl.stA sc) (G'.pl.stAbar sc) (i - 1)) :=
    fun i h => (GlobalTheory.T.exists_extensionData_antiDiagonalSignGram_of_lat_eq _ _ (G'.sp.colDec i h.1 h.2) _ (Or.inr rfl) (G'.sp.colLat i h.1 h.2)).imp fun _ h => h.2
  choose dV hdV using exV

  have exX : ∀ j (h : j + 1 < D.R.m), ∃ d : GlobalTheory.Grid.HermitianOrthogonalExtensionData (mk (.top (j + 1)) (gX (j + 1) (by omega) h.le))
      (mk (.grid D.R.m (j + 1)) (gV D.R.m (j + 1) (by omega) le_rfl h.le)) (D.R.m - 1 - (j + 1)),
      d.Is (fun p q => GlobalTheory.ChiGrid.antiDiagonalSignGramMatrix (D.R.m - 1 - (j + 1)) (-1 : D.host.E) p q)
        (GlobalTheory.ChiGrid.stairId D.host.AA D.host.AAbar (D.R.m - 1 - (j + 1))) :=
    fun j h => (GlobalTheory.T.exists_extensionData_antiDiagonalSignGram_of_lat_eq _ _ (G'.sp.rowDecS j h) _ (Or.inr rfl) (G'.sp.rowLat j h)).imp fun _ h => h.2
  choose dX hdX using exX

  obtain ⟨dZ, -, hdZ⟩ := GlobalTheory.T.exists_extensionData_antiDiagonalSignGram_of_lat_eq (mk (.grid D.R.m D.R.m) (gV D.R.m D.R.m (by omega) le_rfl le_rfl))
    (mk (.top D.R.m) (gX D.R.m (by omega) le_rfl)) G'.sp.topDec (fun _ => 1) (Or.inl rfl) G'.sp.topLat
  let G : GlobalTheory.Grid.GridPre R :=
    { toGridSp := GS
      idem := e
      chiH := G'.ch.chiH
      chi := G'.ch.chi
      decP := hermitianOrthogonalExtensionDataCast rfl (node_pos (.core 0) (gP 0 (by omega))).symm dP
      decV := fun i => if h : 1 ≤ i ∧ i ≤ D.R.m then
        hermitianOrthogonalExtensionDataCast (node_pos (.core i) (gP i h.2)).symm ((vert_eq i 0 h.1).trans (node_pos (.grid i 0) (gV i 0 h.1 h.2 (by omega)))).symm (dV i h) else hermitianOrthogonalExtensionDataZero _ _ _
      decX := fun j => if h : j + 1 < D.R.m then
        hermitianOrthogonalExtensionDataCast (node_pos (.top (j + 1)) (gX (j + 1) (by omega) h.le)).symm ((vert_eq D.R.m (j + 1) (by omega)).trans (node_pos (.grid D.R.m (j + 1)) (gV D.R.m (j + 1) (by omega) le_rfl h.le))).symm (dX j h) else hermitianOrthogonalExtensionDataZero _ _ _
      decZ := hermitianOrthogonalExtensionDataCast ((vert_eq D.R.m D.R.m (by omega)).trans (node_pos (.grid D.R.m D.R.m) (gV D.R.m D.R.m (by omega) le_rfl le_rfl))).symm
        ((Xp_eq D.R.m (by omega)).trans (node_pos (.top D.R.m) (gX D.R.m (by omega) le_rfl))).symm dZ
      X := fun _ _ => ⟨1, 0, 0⟩
      ωT := fun _ _ _ => 1
      vacT := fun _ _ => 0
      ItT := fun _ _ => 0
      ωC := fun _ _ => 1
      vacC := fun _ => 0
      ItC := fun _ => 0
      dn := fun _ => ⟨1, 0, 0⟩
      ItU := fun _ => 0
      m00 := ⟨0, ∅⟩
      mV := fun _ _ => ⟨0, ∅⟩
      mP := fun _ => ⟨0, ∅⟩
      mX := fun _ => ⟨0, ∅⟩
      vC := fun _ _ => 0 }
  refine ⟨G, rfl, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i j hi hj
      show (node (.grid (i + 1) j)).Is _ _ _
      rw [node_pos (.grid (i + 1) j) (gV (i + 1) j (by omega) hi hj)]
      exact mk_is _ _
    · intro i hi
      show (node (.core i)).Is _ _ _
      rw [node_pos (.core i) (gP i hi)]
      exact mk_is _ _
    · intro j hj
      show (node (.top (j + 1))).Is _ _ _
      rw [node_pos (.top (j + 1)) (gX (j + 1) (by omega) hj)]
      exact mk_is _ _
    · dsimp only [G]
      rw [gridDecompositionCast_is_iff, ← joinGram_one]
      exact hdP
    · intro i hi1 hi2
      dsimp only [G]
      rw [dif_pos ⟨hi1, hi2⟩, gridDecompositionCast_is_iff]
      have hl' : Z.ideal R.Pg = G'.pl.modul sc := hlvl
      have := hdV i ⟨hi1, hi2⟩
      rw [joinGram_neg, joinStair, ← hl'] at this
      exact this
    · intro j hj
      dsimp only [G]
      rw [dif_pos hj, gridDecompositionCast_is_iff]
      have := hdX j hj
      rw [joinGram_neg, joinStair_top] at this
      exact this
    · dsimp only [G]
      rw [gridDecompositionCast_is_iff, ← joinGram_one]
      exact hdZ
  · exact ⟨hZ, fun i h1 h2 => GlobalTheory.T.heckeCharacterGrid_isAuxiliaryCharacter_testGrid (GlobalTheory.T.gridMinimalGap_eq_chiGridGapGamma_one D) hsc Z hS0 hS1 hZ.Wd_over hw0 i h1 h2, fun i h1 h2 => G'.ch.chi_eq i h1 h2⟩
  · refine ⟨?_, ?_, ?_, hq0, hw0, he0, hWZ, hlvl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩
    · intro i j hi hj
      cases i with
      | zero => exact GlobalTheory.T.testGridRowZero_vertices_agree_weilData W hW j hj
      | succ i =>
        show NodeAgree (node (.grid (i + 1) j)) W (.grid (i + 1) j)
        rw [node_pos (.grid (i + 1) j) (gV (i + 1) j (by omega) hi hj)]
        exact mk_agree _ _
    · intro i hi
      show NodeAgree (node (.core i)) W (.core i)
      rw [node_pos (.core i) (gP i hi)]
      exact mk_agree _ _
    · intro j hj
      cases j with
      | zero =>
        show NodeAgree (node (.core D.R.m)) W (.top 0)
        rw [node_pos (.core D.R.m) (gP D.R.m le_rfl)]
        exact ⟨rfl, HEq.rfl, heq_of_eq ((hM _ _).1.trans hcT.symm), heq_of_eq ((hM _ _).2.trans hoT.symm)⟩
      | succ j =>
        show NodeAgree (node (.top (j + 1))) W (.top (j + 1))
        rw [node_pos (.top (j + 1)) (gX (j + 1) (by omega) hj)]
        exact mk_agree _ _

end GlobalTheory.GridJoin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTestGridFromLevelChoiceGridStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_testGrid_from_levelChoiceGrid : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesUpqExists → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → (∀ X : GlobalTheory.ChiGrid.Node, X.InRange D.R.m → (∀ j, X ≠ .grid 0 j) → (G'.Λ X : Set _) = L0c D (G'.V X)) → (∀ PP ∈ R.Pg, ∀ PP' ∈ R.Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') → PP = PP') → Formalism.L2.Host.SplitsCompletely {G'.pl.w G'.pl.v0} → (∀ k, GlobalTheory.ChiGrid.q0 D ≠ D.host.g k) → (GlobalTheory.ChiGrid.q0 D ≠ D.sp.T ∧ ∀ u : D.what₂.Word, GlobalTheory.ChiGrid.q0 D ≠ (D.mem u).A.T) → (∀ i j, 1 ≤ i → i ≤ D.R.m → j ≤ D.R.m → ∀ τ, ∃ (lam : Fin (G'.V (.grid i j)).rank → ℝ) (ε : Fin (G'.V (.grid i j)).rank → Bool), IsEnum (GlobalTheory.Grid.parV D i j τ) lam ε ∧ (W.onb (.grid i j) τ)ᴴ * gramAt D (G'.V (.grid i j)) τ * W.onb (.grid i j) τ = Formalism.REAL.Jm ε) → (∀ i, i ≤ D.R.m → ∀ τ, ∃ (lam : Fin (G'.V (.core i)).rank → ℝ) (ε : Fin (G'.V (.core i)).rank → Bool), IsEnum (GlobalTheory.Grid.parP D i τ) lam ε ∧ (W.onb (.core i) τ)ᴴ * gramAt D (G'.V (.core i)) τ * W.onb (.core i) τ = Formalism.REAL.Jm ε) → (∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ, ∃ (lam : Fin (G'.V (.top j)).rank → ℝ) (ε : Fin (G'.V (.top j)).rank → Bool), IsEnum (GlobalTheory.Grid.parXp D j τ) lam ε ∧ (W.onb (.top j) τ)ᴴ * gramAt D (G'.V (.top j)) τ * W.onb (.top j) τ = Formalism.REAL.Jm ε) → W.cart (.top 0) = W.cart (.core D.R.m) → W.onb (.top 0) = W.onb (.core D.R.m) → ∀ e : AE D, IsIdemSum e G'.pl.W0 → ∃ G : GlobalTheory.Grid.GridPre R, G.idem = e ∧ G.IsSpaces ∧ G.IsChars ∧ SpAgree G W := by
  first | exact @GlobalTheory.GridJoin.exists_gridPre_spaces | exact GlobalTheory.GridJoin.exists_gridPre_spaces | (intros; apply GlobalTheory.GridJoin.exists_gridPre_spaces <;> assumption)
end

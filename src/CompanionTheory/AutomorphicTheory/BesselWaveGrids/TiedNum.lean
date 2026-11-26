module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.TBBTie
public import CompanionTheory.AutomorphicTheory.BesselWaveGrids.KDecayOfGap
public import CompanionTheory.AutomorphicTheory.BesselWaveGrids.FamilyThroughDiscreteSeries
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SupExistsOfInterlaced
public import CompanionTheory.HarishChandraModules.NonemptyRepresentations.TypeHW

@[expose] public section

section -- merged from CompanionTheory.HarishChandraModules.NonemptyRepresentations.IsData
open MeasureTheory Matrix

noncomputable section

namespace CompanionTheory.D.Inhab.IsDataInh

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5

theorem glev_last_eq (k r : ℕ) : Glev k r (Fin.last r) = B2.UWb k r := by
  ext g
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, fun a => h2 a (by simp)⟩, fun ⟨h1, h2⟩ => ⟨h1, fun a _ => h2 a⟩⟩

theorem haar_glev_last (k r : ℕ) : ∃ μ : Measure (Mt k r), B.IsHaarOn (Glev k r (Fin.last r)) μ := by
  rw [glev_last_eq]
  exact Formalism.FourierDecayAlt.P.opposite_weyl_haar_exists k r

theorem isData_of_place {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Mx P.k P.r → (Wq →L[ℂ] Wq))
    (hP : IsPlace P z z' π π') (μ : Measure (Mt P.k P.r)) (hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ)
    (l0 : ℕ) :
    ∃ (X : ActualOps P.k P.r z z' π π') (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r)
      (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))), IsData P z z' π π' X μ L st l0 := by
  obtain ⟨X⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist Wp Wq P z z' π π' hP
  obtain ⟨L, st, h1, h2, h3, h4, h5, h6⟩ := Formalism.FourierDecayAlt.P.level_start_actual Wp Wq P z z' π π' hP X l0
  exact ⟨X, L, st, hP, hμ, h1, h2, h3, h4, h5, h6⟩

end CompanionTheory.D.Inhab.IsDataInh
end
end

section -- merged from CompanionTheory.AutomorphicTheory.BesselWaveGrids.TypeHC
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace CompanionTheory.WaveGrid.TypeHC

section param
open PI.UpqRep PI.HwUniqW GlobalTheory.BesselFrame GlobalTheory.SupNonzero

variable {k r : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (W →L[ℂ] W)}

theorem isType_of_hc {u : ℕ → ℝ} {u₀ : Fin k → ℝ} (hz : Formalism.QuantumDeterminants.inWb k r z) (hT : 0 < Formalism.QuantumDeterminants.Tz k r z)
    (hπ : IsHCTypeW k r z u₀ π) (hu : ∀ s : Fin k, u (s.val + 1) = u₀ s) : Q.IsType k r z π u := by
  obtain ⟨p1, pmul, punit, pcont⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_facts hT hπ
  have hrep : Formalism.QuantumDeterminants.IsCRepOn (Formalism.QuantumDeterminants.UWset k r z) π := ⟨p1, pmul⟩
  have hcont : ContinuousOn π (Formalism.QuantumDeterminants.UWset k r z) := continuousOn_clm_apply.2 pcont
  obtain ⟨g, hg, h₀⟩ := hπ
  have hirr : ∀ S : Submodule ℂ W, (∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ v ∈ S, π h v ∈ S) → S = ⊥ ∨ S = ⊤ :=
    fun S hS => h₀.2.2.2.2.2.1 S le_top fun x hx v hv => hS _ (conj_mem_UW hg (by
      have := Matrix.mem_unitaryGroup_iff'.mp hx.1
      rw [Matrix.star_eq_conjTranspose] at this
      exact mem_UJset_allPos.2 this)) v hv
  obtain ⟨E, hgl, -, hE⟩ := GlobalTheory.UnitaryDerived.exists_derived_action k W _ h₀.2.2.1
  obtain ⟨v, hv, hq⟩ := qdet_eigen h₀ E hgl hE
  have hB := isFrameOf hg
  set A := g * incl k r with hA
  set B := Aᴴ * Hpk k r with hBd
  have hd : ∀ Z : Matrix (Fin k) (Fin k) ℂ, Zᴴ = -Z → ∀ x, Q.dRep π (A * Z * B) x = ∑ a, ∑ b, Z a b • E a b x := by
    intro Z hZ x
    rw [← (hE Z hZ x).deriv]
    unfold Q.dRep
    congr 1
    funext t
    rw [conj_blockW hg.1, ← exp_corner _ _ (co_mul hg.1), Matrix.mul_smul, Matrix.smul_mul]
  have hH : (Formalism.QuantumDeterminants.Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_left_inv Hpk_mul_self
  have hc : ∀ Y : Matrix (Fin k) (Fin k) ℂ,
      (Formalism.QuantumDeterminants.Hpk k r)⁻¹ * (A * Y * B)ᴴ * Formalism.QuantumDeterminants.Hpk k r = A * Yᴴ * B := by
    intro Y
    rw [hH, hBd]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Hpk_conjTranspose, ← Matrix.mul_assoc,
      Hpk_mul_self, Matrix.one_mul]
    rfl
  have hEB : Qr.EB π (fun a => g *ᵥ bvec (bl k r a)) = E := by
    funext a b
    refine LinearMap.ext fun x => ?_
    have hl := P.QrD.frame_lie hB a b
    show P.QrD.ecOp π _ x = _
    rw [← P.QrD.ecRep_eq hrep hcont hl.1 hl.2, unitB_eq]
    unfold Q.EcRep Formalism.QuantumDeterminants.hpart1 Formalism.QuantumDeterminants.hpart2
    rw [← hA, ← hBd, hc, ← Matrix.sub_mul, ← Matrix.mul_sub, ← Matrix.add_mul, ← Matrix.mul_add, ← Matrix.smul_mul,
      ← Matrix.mul_smul, ← Matrix.smul_mul, ← Matrix.mul_smul, hd, hd]
    · simp only [Finset.smul_sum, smul_smul, ← Finset.sum_add_distrib, ← add_smul]
      have e : ∀ c d, ((1 / 2 : ℂ) • (Matrix.single a b (1 : ℂ) - (Matrix.single a b (1 : ℂ))ᴴ)) c d +
          Complex.I * ((1 / (2 * Complex.I) : ℂ) • (Matrix.single a b (1 : ℂ) + (Matrix.single a b (1 : ℂ))ᴴ)) c d =
          Matrix.single a b (1 : ℂ) c d := by
        intro c d
        simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
        field_simp
        ring
      simp only [e]
      simp [Matrix.single, ite_and, ite_smul]
    · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose, ← neg_smul, add_comm]
      congr 1
      simp [Complex.conj_ofNat]
    · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose, ← smul_neg, neg_sub]
      congr 1
      simp
  let K : Submodule ℂ W :=
    { carrier := {x | ∀ Y : ℂ, Formalism.REAL.qdet E (Y + ((k : ℂ) - 1) / 2) x = (∏ s, (Y + (u₀ s : ℂ))) • x}
      add_mem' := fun ha hb w => by rw [map_add (f := _), ha w, hb w, smul_add]
      zero_mem' := fun w => by simp
      smul_mem' := fun s x hx w => by rw [map_smul, hx w, smul_comm] }
  have hKs : Qr.Stab (Qr.EB π (fun a => g *ᵥ bvec (bl k r a))) K := by
    rw [hEB]
    intro a b x hx w
    have := congrArg (fun T : Module.End ℂ W => T x) (Formalism.REAL.qDetCentral _ k _ hgl (w + ((k : ℂ) - 1) / 2) a b)
    simp only [Module.End.mul_apply] at this
    rw [this, hx w, map_smul]
  have hK := P.lie_stabilizer W k r z π _ hz hT ⟨hrep, hcont⟩ hB K hKs
  have hKt : K = ⊤ := (hirr K hK).resolve_left ((Submodule.ne_bot_iff K).2 ⟨v, hq, hv⟩)
  refine ⟨h₀.1, hrep, hcont, punit, hirr, fun Bs hBs w x => ?_⟩
  have hx : x ∈ K := hKt ▸ Submodule.mem_top
  have e := hx (w - ((k : ℂ) - 1) / 2)
  rw [sub_add_cancel] at e
  rw [(P.frame_general_linear W k r k z π Bs ⟨hrep, hcont⟩ hBs).2, P.QrCap.capChange hz hT ⟨hrep, hcont⟩ hBs hB, hEB, e,
    CompanionTheory.D.Inhab.TypeHW.prod_Icc]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [hu]
  ring

end param

theorem exists_place : ∃ Cb : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Mx P.k P.r → (Wq →L[ℂ] Wq))
    (μW μW' : Measure (Formalism.QuantumDeterminants.Mt P.k P.r)) (l0 : ℕ), Q.IsPlace P z z' π π' → 2 ≤ P.k → 1 ≤ l0 → l0 ≤ P.k →
    B.IsHaarOn (Formalism.QuantumDeterminants.UWset P.k P.r z) μW → μW Set.univ = 1 →
    B.IsHaarOn (Formalism.QuantumDeterminants.UWset P.k P.r z') μW' → μW' Set.univ = 1 →
    ∃ p : KB.Pl P Wp Wq, p.l0 = l0 ∧ p.T.base.z = z ∧ p.T.base.z' = z' ∧ p.T.base.π = π ∧ p.T.base.π' = π' ∧
      p.T.base.μW = μW ∧ p.T.base.μN = D.muN P.k P.r ∧ p.T.base.μW' = μW' ∧
      KB.InDDplus2 P p.l0 p.T.base Cb p.Θ := by
  obtain ⟨Cb, -, hTL⟩ := Formalism.FourierDecayAlt.P.top_lift_exists
  refine ⟨Cb, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P z z' π π' μW μW' l0 hP hk hl1 hl2 hW hW1 hW' hW1'
  obtain ⟨μ, hμ⟩ := CompanionTheory.D.Inhab.IsDataInh.haar_glev_last P.k P.r
  obtain ⟨hOK, hz, hz', hT, hT', ⟨-, hr, hc, hu, -, -⟩, ⟨-, hr', hc', hu', -, -⟩⟩ := id hP
  obtain ⟨B0, e1, e2, e3, e4, -⟩ := Formalism.FourierDecayAlt.P.setting_with_prescribed_data_exists P.k P.r Wp Wq z z' π π' hOK.k_pos hz hz'
    (by rw [hT]; exact hOK.T_pos) (by rw [hT']; exact hOK.T'_pos) hr hr' hu hu' hc hc'
  obtain ⟨T0, -, -, -, -, hN0⟩ := Formalism.FourierDecayAlt.P.exists_normalized_tower P.k P.r Wp Wq B0
  have hmuN : B.IsHaarOn (Formalism.QuantumDeterminants.Nset P.k P.r) (D.muN P.k P.r) := by
    have h := (hN0 0 (Nat.zero_le _)).2.2
    have h' : T0.base.μN = D.muN P.k P.r := (by simpa using h : (T0.bs 0).μN = D.muN P.k P.r)
    exact h' ▸ T0.base.haarN
  subst e1 e2 e3 e4
  let Bs : B.RealPlaceData P.k P.r Wp Wq :=
    { B0 with μW := μW, μN := D.muN P.k P.r, μW' := μW', haarW := hW, haarN := hmuN, haarW' := hW' }
  obtain ⟨T, hTb, hTN⟩ := Formalism.FourierDecayAlt.P.exists_level_tower P.k P.r Wp Wq Bs hW1 hW1' rfl
  have hPl : Q.IsPlace P T.base.z T.base.z' T.base.π T.base.π' := by
    rw [hTb]; exact hP
  obtain ⟨ν', m₀, hF⟩ := Formalism.FourierDecayAlt.P.HaarMassHermitianCurvature.frame_of T.base
  obtain ⟨X, L, st, hD⟩ := CompanionTheory.D.Inhab.IsDataInh.isData_of_place P _ _ _ _ hPl μ hμ l0
  obtain ⟨Θ, hI, hDD⟩ := hTL Wp Wq P T.base X μ L st l0 hl1 hl2 hD
  obtain ⟨f1, f2, f3⟩ := Formalism.FourierDecayAlt.P.HaarMassHermitianCurvature.frameVec_facts T.base ν' m₀ hF
  obtain ⟨TP⟩ := Formalism.FourierDecayAlt.P.type_projectors_exist Wp Wq P T.base.z T.base.z' T.base.π T.base.π' (m₀ *ᵥ ν') hPl
    f1 f2 f3
  refine ⟨⟨l0, T, ν', m₀, Θ, TP, ⟨hl1, hl2, hk⟩, hTN, hF, hPl, ⟨X, μ, L, st, hD, hI⟩⟩, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hDD⟩
  · change T.base.z = B0.z; rw [hTb]
  · change T.base.z' = B0.z'; rw [hTb]
  · change T.base.π = B0.π; rw [hTb]
  · change T.base.π' = B0.π'; rw [hTb]
  · change T.base.μW = μW; rw [hTb]
  · change T.base.μN = D.muN P.k P.r; rw [hTb]
  · change T.base.μW' = μW'; rw [hTb]

end CompanionTheory.WaveGrid.TypeHC
end
end

section -- merged from CompanionTheory.AutomorphicTheory.BesselWaveGrids.NqOfLamData
namespace CompanionTheory.WaveGrid.Inhab

open Formalism.FourierDecayAlt Finset CompanionTheory.WaveGrid GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid

theorem int_of_half {k : ℕ} {u v : ℕ → ℝ} (hk : 1 ≤ k)
    (hu : ∀ i, 1 ≤ i → i ≤ k → ∃ m : ℤ, u i - ((k : ℝ) - 1) / 2 = m)
    (hv : ∀ i, 1 ≤ i → i ≤ k → ∃ m : ℤ, v i - ((k : ℝ) - 1) / 2 = m) :
    ∀ i ∈ Icc 1 k, ∃ n : ℤ, v i - u 1 = n := by
  intro i hi
  obtain ⟨hi1, hik⟩ := Finset.mem_Icc.1 hi
  obtain ⟨m1, hm1⟩ := hu 1 le_rfl hk
  obtain ⟨m2, hm2⟩ := hv i hi1 hik
  exact ⟨m2 - m1, by push_cast; linarith⟩

theorem ok_diff (P : M.Par) (hk : 1 ≤ P.k) (hT : 0 < P.T) (hT' : 0 < P.T') (lam : Fin (2 * P.r + P.k + 1) → ℝ)
    (b : ℝ) (hc : Formalism.QuantumDeterminants.IsHCParam lam) (hu : HypType P.k P.r lam P.u b) (hu' : HypType P.k P.r lam P.u' b) :
    P.OK := by
  refine ⟨hk, hT, hT', int_of_half hk hu.half hu.half, int_of_half hk hu.half hu'.half, ?_⟩
  intro i hi
  obtain ⟨hi1, hik⟩ := Finset.mem_Icc.1 hi
  obtain ⟨a1, a2⟩ := inter_half hc hu i hi1 hik
  obtain ⟨b1, b2⟩ := inter_half hc hu' i hi1 hik
  simp only [M.Par.lo, M.Par.hi]
  have hmax := max_le a2 b2
  have hmin := le_min a1 b1
  linarith

end CompanionTheory.WaveGrid.Inhab
end

section -- merged from CompanionTheory.AutomorphicTheory.BesselWaveGrids.GapSizes
noncomputable section

namespace CompanionTheory.WaveGrid.GapSizes

theorem sizes (Cg m N P s : ℝ) (hCg : 1000 ≤ Cg) (hm2 : 2 ≤ m) (hmN : m ≤ N) (hPN : N ^ 3 ≤ P) (hs : 1 ≤ s) :
    120 * N ^ 3 ≤ Cg * (m ^ 4 * s) * P / 4 ∧ 125 * m ^ 2 * N ^ 3 ≤ Cg * m ^ 4 * P / 32 := by
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hN3 : (0 : ℝ) ≤ N ^ 3 := by positivity
  have hm2' : (4 : ℝ) ≤ m ^ 2 := by nlinarith
  have hm4e : m ^ 4 = m ^ 2 * m ^ 2 := by ring
  have hm4 : (16 : ℝ) ≤ m ^ 4 := by rw [hm4e]; nlinarith
  have hm4' : 4 * m ^ 2 ≤ m ^ 4 := by rw [hm4e]; nlinarith
  have hCg0 : (0 : ℝ) ≤ Cg := by linarith
  constructor
  · have a : (16 : ℝ) ≤ m ^ 4 * s := le_trans hm4 (le_mul_of_one_le_right (by positivity) hs)
    have b : (16000 : ℝ) ≤ Cg * (m ^ 4 * s) := by nlinarith
    have c : 16000 * N ^ 3 ≤ Cg * (m ^ 4 * s) * P :=
      le_trans (mul_le_mul_of_nonneg_right b hN3) (mul_le_mul_of_nonneg_left hPN (by positivity))
    linarith
  · have b : 4000 * m ^ 2 ≤ Cg * m ^ 4 := by nlinarith
    have c : 4000 * m ^ 2 * N ^ 3 ≤ Cg * m ^ 4 * P :=
      le_trans (mul_le_mul_of_nonneg_right b hN3) (mul_le_mul_of_nonneg_left hPN (by positivity))
    linarith

theorem consts (k r : ℕ) (hk : 1 ≤ k) :
    Formalism.FourierDecayAlt.ThreeDimData.Mexp r ≤ (2 * (r : ℝ) + 2) ^ 2 / 2 ∧ 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.Mexp r ∧
    Formalism.FourierDecayAlt.ThreeDimData.AS k r ≤ 2 * (2 * (r : ℝ) + k + 1) ^ 3 ∧ 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AS k r ∧
    Formalism.FourierDecayAlt.ThreeDimData.AG k r ≤ 4 * (2 * (r : ℝ) + k + 1) ^ 3 ∧ 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AG k r := by
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set N : ℝ := 2 * (r : ℝ) + k + 1 with hN
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hN2 : N ^ 2 ≤ N ^ 3 := by nlinarith
  have hdN : Formalism.FourierDecayAlt.ThreeDimData.dN k r ≤ 2 * N ^ 2 := by unfold Formalism.FourierDecayAlt.ThreeDimData.dN; rw [hN]; nlinarith
  have hdN0 : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.dN k r := by unfold Formalism.FourierDecayAlt.ThreeDimData.dN; nlinarith
  have hnk : ((2 * r + k : ℕ) : ℝ) ≤ N := by rw [hN]; push_cast; linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Formalism.FourierDecayAlt.ThreeDimData.Mexp; nlinarith
  · unfold Formalism.FourierDecayAlt.ThreeDimData.Mexp; positivity
  · unfold Formalism.FourierDecayAlt.ThreeDimData.AS
    have : ((2 * r + k : ℕ) : ℝ) * Formalism.FourierDecayAlt.ThreeDimData.dN k r ≤ N * (2 * N ^ 2) :=
      mul_le_mul hnk hdN hdN0 (by linarith)
    nlinarith
  · unfold Formalism.FourierDecayAlt.ThreeDimData.AS; positivity
  · unfold Formalism.FourierDecayAlt.ThreeDimData.AG
    have e1 : ((k : ℝ) + r) ≤ N := by rw [hN]; linarith
    have e2 : ((r : ℝ) + 1) ≤ N := by rw [hN]; linarith
    have e3 : ((k : ℝ) + r) * ((r : ℝ) + 1) ≤ N * N := mul_le_mul e1 e2 (by linarith) (by linarith)
    nlinarith
  · unfold Formalism.FourierDecayAlt.ThreeDimData.AG; positivity

theorem gapOK_of (k r : ℕ) (hk : 1 ≤ k) (Cg : ℝ) (hCg : 1000 ≤ Cg) :
    Formalism.FourierDecayAlt.ThreeDimData.GapOK k r (Cg * ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
      (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3) / 4) := by
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have em : ((2 * r + 2 : ℕ) : ℝ) = 2 * (r : ℝ) + 2 := by push_cast; ring
  have eN : ((2 * r + k + 1 : ℕ) : ℝ) = 2 * (r : ℝ) + k + 1 := by push_cast; ring
  have e3 : ((3 * (r + 1) : ℕ) : ℝ) = 3 * ((r : ℝ) + 1) := by push_cast; ring
  unfold Formalism.FourierDecayAlt.ThreeDimData.GapOK
  rw [em, eN, e3]
  generalize hm : 2 * (r : ℝ) + 2 = m
  generalize hN : 2 * (r : ℝ) + k + 1 = N
  have hm2 : (2 : ℝ) ≤ m := by rw [← hm]; linarith
  have hmN : m ≤ N := by rw [← hm, ← hN]; linarith
  have hmpos : (0 : ℝ) < m := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hsq : Real.sqrt (2 * ((r : ℝ) + 1)) = Real.sqrt m := by rw [← hm]; ring_nf
  have h92 : m ^ ((9 : ℝ) / 2) = m ^ 4 * Real.sqrt m := by
    rw [show (9 : ℝ) / 2 = ((4 : ℕ) : ℝ) + 1 / 2 by norm_num, Real.rpow_add hmpos, Real.rpow_natCast,
      Real.sqrt_eq_rpow]
  have hs1 : (1 : ℝ) ≤ Real.sqrt m := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  have hspos : (0 : ℝ) < Real.sqrt m := by linarith
  have hN3 : (1 : ℝ) ≤ N ^ 3 := one_le_pow₀ hN1
  have hPN : N ^ 3 ≤ 3 * ((r : ℝ) + 1) * N ^ 2 + N ^ 3 := by
    have : (0 : ℝ) ≤ 3 * ((r : ℝ) + 1) * N ^ 2 := by positivity
    linarith
  obtain ⟨s1, s2⟩ := sizes Cg m N (3 * ((r : ℝ) + 1) * N ^ 2 + N ^ 3) (Real.sqrt m) hCg hm2 hmN hPN hs1
  have hA : Formalism.FourierDecayAlt.ThreeDimData.aOf r (Cg * m ^ ((9 : ℝ) / 2) * (3 * ((r : ℝ) + 1) * N ^ 2 + N ^ 3) / 4) =
      Cg * m ^ 4 * (3 * ((r : ℝ) + 1) * N ^ 2 + N ^ 3) / 32 := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.aOf
    rw [hsq, h92]
    field_simp
    ring
  obtain ⟨cM, cM0, cS, cS0, cG, cG0⟩ := consts k r hk
  rw [hm] at cM
  rw [hN] at cS cG
  have hm2' : (4 : ℝ) ≤ m ^ 2 := by nlinarith
  have hN3' : (0 : ℝ) ≤ N ^ 3 := by positivity
  have hmm : m ^ 2 * N ^ 3 ≥ 4 * N ^ 3 := by nlinarith
  have hX : 4 * N ^ 3 ≤ m ^ 2 * N ^ 3 := by nlinarith
  have hX1 : (4 : ℝ) ≤ m ^ 2 * N ^ 3 := by linarith
  refine ⟨hk, ?_, ?_, ?_⟩
  · rw [h92]; linarith
  · rw [hA]
    have hsum : Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r ≤ 6 * N ^ 3 := by linarith
    have hL : 2 * Formalism.FourierDecayAlt.ThreeDimData.Mexp r * (Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r) ≤ 2 * (m ^ 2 / 2) * (6 * N ^ 3) :=
      mul_le_mul (by linarith) hsum (by positivity) (by positivity)
    have hL' : 2 * (m ^ 2 / 2) * (6 * N ^ 3) = 6 * (m ^ 2 * N ^ 3) := by ring
    have s2' : 125 * (m ^ 2 * N ^ 3) ≤ Cg * m ^ 4 * (3 * ((r : ℝ) + 1) * N ^ 2 + N ^ 3) / 32 := by
      have : 125 * m ^ 2 * N ^ 3 = 125 * (m ^ 2 * N ^ 3) := by ring
      linarith
    linarith only [hL, hL', s2', cG, hX, hX1]
  · rw [hA]
    have hN23 : N ^ 2 ≤ N ^ 3 := by
      have : N ^ 3 = N ^ 2 * N := by ring
      rw [this]; exact le_mul_of_one_le_right (by positivity) hN1
    have h9 : 9 * ((r : ℝ) + 1) = 4.5 * m := by rw [← hm]; ring
    have e1 : 9 * ((r : ℝ) + 1) * N ^ 2 ≤ 4.5 * m * N ^ 3 := by
      rw [h9]; exact mul_le_mul_of_nonneg_left hN23 (by positivity)
    have hq : 4.5 * m ≤ 3 * m ^ 2 := by nlinarith only [hm2]
    have e2 : 4.5 * m * N ^ 3 ≤ 3 * (m ^ 2 * N ^ 3) := by
      have := mul_le_mul_of_nonneg_right hq hN3'
      linarith only [this]
    have s2' : 125 * (m ^ 2 * N ^ 3) ≤ Cg * m ^ 4 * (3 * ((r : ℝ) + 1) * N ^ 2 + N ^ 3) / 32 := by
      have : 125 * m ^ 2 * N ^ 3 = 125 * (m ^ 2 * N ^ 3) := by ring
      linarith
    linarith only [e1, e2, hX, hX1, s2', cG]

end CompanionTheory.WaveGrid.GapSizes
end
end

noncomputable section

namespace CompanionTheory.WaveGrid.Tied

open MeasureTheory Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.L2.SG.Pf.BesselExpansion Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open CompanionTheory.WaveGrid CompanionTheory.WaveGrid.Coef

def ExpBall : Prop :=
  ∀ C : ℝ, 0 ≤ C → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 a₁ : ℕ) (R0 : BranchingSupport.Rep P.k P.r)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (ν₀ : Fin (2 * P.r + P.k + 1) → ℤ),
    BranchingSupport.Num P.k P.r lam P.u b bv ga h q0 → BranchingSupport.Num P.k P.r lam P.u' b bv ga h q0 →
    P.T ≤ b ^ (C * ((2 * P.r + 2 : ℕ) : ℝ)) → P.T' ≤ b ^ (C * ((2 * P.r + 2 : ℕ) : ℝ)) →
    BranchingSupport.n1 ν₀ + (P.r + 1) * a₁ + (P.r + 1) * (P.r + 2) ≤ q0 →
    R0.IsDS (PI.BesselPeriodGGP.eps48 P.k P.r) (fun a => lam a + (ν₀ a : ℝ)) →
    (haveI := FiniteDimensional.complete ℂ Wp; PI.CapelliEig.IsKFinCoefT (k := P.k) (r := P.r) R0.σ f) →
    CutBP.BigCellDerivativeExpansion p f b (C / 2 + 6) a₁

section num

variable {k r : ℕ}

def gapY (k r : ℕ) : ℝ :=
  ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
    (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3)

theorem pow_four_le_rpow_nine_halves (r : ℕ) : ((2 * r + 2 : ℕ) : ℝ) ^ 4 ≤ ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) := by
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ 2 * r + 2)) (by norm_num)

theorem thrX_le_gapY (k r : ℕ) : thrX k r ≤ gapY k r := by
  unfold thrX gapY
  have h1 : ((r : ℝ) + 1) ^ 4 ≤ ((2 * r + 2 : ℕ) : ℝ) ^ 4 :=
    pow_le_pow_left₀ (by positivity) (by push_cast; linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]) 4
  have e : ((2 * r + k + 1 : ℕ) : ℝ) = 2 * (r : ℝ) + k + 1 := by push_cast; ring
  rw [e]
  exact mul_le_mul_of_nonneg_right (h1.trans (pow_four_le_rpow_nine_halves r)) (by positivity)

theorem mul_le_gapY (k r : ℕ) : ((2 * r + 2 : ℕ) : ℝ) ^ 4 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 ≤ gapY k r :=
  mul_le_mul (pow_four_le_rpow_nine_halves r) (le_add_of_nonneg_left (by positivity)) (by positivity) (by positivity)

theorem fourth_power_le_gap (k r : ℕ) : ((2 * r + 2 : ℕ) : ℝ) ^ 4 ≤ gapY k r :=
  le_trans (le_mul_of_one_le_right (by positivity)
    (one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)))) (mul_le_gapY k r)

theorem cube_le_gap (k r : ℕ) : ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 ≤ gapY k r :=
  le_trans (le_mul_of_one_le_left (by positivity)
    (one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ 2 * r + 2)))) (mul_le_gapY k r)

theorem hypType_of (hk : 1 ≤ k) {lam : Fin (2 * r + k + 1) → ℝ} {u : Fin k → ℝ} {b : ℝ} (hlam : IsHCParam lam)
    (hu : IsHCParam u) (hI : InterlaceS (by omega) u lam) (hb : ∀ i, |u i| ≤ b) : HypType k r lam (lamN u) b := by
  refine { half := ?_, inter := ?_, u_le := ?_ }
  · intro i h1 h2
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [lamN_succ u ⟨j, by omega⟩]
    exact hu.2 _
  · refine ⟨fun s t hst => hlam.1 (by simpa using hst), fun s => ⟨fun hs => ?_, fun hs => ?_⟩⟩
    · have hs' : (s : ℕ) < k := by simpa using hs
      rw [lamN_succ u ⟨s, hs'⟩]
      by_cases h : (s : ℕ) + 1 < k
      · exact (hI.1 s h).1
      · have e : (s : ℕ) = k - 1 := by omega
        have := hI.2 (by omega)
        simp only [← e] at this
        exact this
    · have hs' : (s : ℕ) + 1 < k := by
        have : (s : ℕ) + 2 ≤ k := by simpa using hs
        omega
      rw [show (s : ℕ) + 2 = (s + 1) + 1 from rfl, lamN_succ u ⟨s + 1, hs'⟩]
      exact (hI.1 s hs').2
  · intro i h1 h2
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [lamN_succ u ⟨j, by omega⟩]
    exact hb _

theorem gap_of_lt {n : ℕ} {lam : Fin n → ℝ} {g : ℝ} (hlam : IsHCParam lam) (hg : AllGaps lam g) {a c : Fin n}
    (h : a < c) : g ≤ lam a - lam c := by
  have h1 := hg a c h.ne
  rwa [abs_of_pos (sub_pos.2 (hlam.1 h))] at h1

theorem shape_of (hk : 1 ≤ k) {lam : Fin (2 * r + k + 1) → ℝ} {u : Fin k → ℝ} {bv : ℝ} (hlam : IsHCParam lam)
    (hu : IsHCParam u) (hI : InterlaceS (by omega) u lam) (hS : ShapeS u lam bv) :
    (∀ a : Fin (2 * r + k + 1), a.val + 1 < k → 0 ≤ lam a ∧ lam a ≤ bv / 8) ∧
      ∀ a : Fin (2 * r + k + 1), k ≤ a.val + 1 → -2 * bv ≤ lam a ∧ lam a ≤ -bv := by
  refine ⟨fun a ha => (hS a).1 ⟨⟨_, (hI.1 a ha).1⟩, ⟨_, (hI.1 a ha).2⟩⟩, fun a ha => (hS a).2 ?_⟩
  rintro ⟨-, i, hi⟩
  have h1 := hI.2 (by omega)
  have h2 : lam a ≤ lam ⟨k - 1, by omega⟩ := hlam.1.antitone (by rw [Fin.le_def]; simp only; omega)
  have h3 : u ⟨k - 1, by omega⟩ ≤ u i := hu.1.antitone (by rw [Fin.le_def]; simp only; omega)
  linarith

theorem scaled_le {T ka b Ch : ℝ} (r : ℕ) (hb : 1 ≤ b) (hka : 0 < ka) (h1 : ka ≤ b ^ Ch)
    (hT : T * (1 / ka) ^ (2 * r) ≤ b ^ (Ch * ((2 * r + 2 : ℕ) : ℝ))) : T ≤ b ^ (2 * |Ch| * ((2 * r + 2 : ℕ) : ℝ)) := by
  have hb0 : 0 < b := by linarith
  have e : T = T * (1 / ka) ^ (2 * r) * ka ^ (2 * r) := by
    rw [mul_assoc, ← mul_pow, one_div, inv_mul_cancel₀ hka.ne', one_pow, mul_one]
  have h2 : ka ^ (2 * r) ≤ b ^ (|Ch| * ((2 * r + 2 : ℕ) : ℝ)) := by
    calc ka ^ (2 * r) ≤ (b ^ |Ch|) ^ (2 * r) :=
          pow_le_pow_left₀ hka.le (h1.trans (Real.rpow_le_rpow_of_exponent_le hb (le_abs_self _))) _
      _ ≤ (b ^ |Ch|) ^ (2 * r + 2) := pow_le_pow_right₀ (Real.one_le_rpow hb (abs_nonneg _)) (by omega)
      _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hb0.le]
  have h3 : b ^ (Ch * ((2 * r + 2 : ℕ) : ℝ)) ≤ b ^ (|Ch| * ((2 * r + 2 : ℕ) : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hb (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  calc T = _ := e
    _ ≤ b ^ (|Ch| * ((2 * r + 2 : ℕ) : ℝ)) * b ^ (|Ch| * ((2 * r + 2 : ℕ) : ℝ)) :=
        mul_le_mul (hT.trans h3) h2 (by positivity) (by positivity)
    _ = _ := by rw [← Real.rpow_add hb0]; congr 1; ring

end num


open CompanionTheory.LimBd.Main (ZuckT CoefCC) in
theorem coefCC1_of {t : ∀ n : ℕ, (Fin n → Bool) → ℝ} {Ct : ℝ} (hCt : 0 ≤ Ct)
    (ht : ∀ n ε, 1 ≤ n → t n ε ≤ Ct * (n : ℝ) ^ 3) (hZ : ZuckT t) (hK : PI.KFinSmooth) (hC : CoefCC) :
    CoefCC1 (Ct + |Formalism.MainNotions.BigCellDensity.c3| + 2) := by
  intro k r L f _ hf hgap
  have hfK : CutBP.KFinDSCoef L.ε L.lam f := by
    obtain ⟨Pm, Qm, h1, h2, h3⟩ := hf
    exact ⟨L.Hs, _, _, _, L.σ, Pm, Qm, L.hlam, L.hσ, h1, h2, fun g _ => h3 g⟩
  have hc := abs_nonneg Formalism.MainNotions.BigCellDensity.c3
  have hX := thrX_nonneg k r
  have hY1 := thrX_le_gapY k r
  have hY2 := fourth_power_le_gap k r
  have hY3 := cube_le_gap k r
  have hm : (1 : ℝ) ≤ ((2 * r + 2 : ℕ) : ℝ) ^ 4 := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ 2 * r + 2))
  have h1 := ht (2 * r + k + 1) L.ε (by omega)
  have h2 := mul_le_mul_of_nonneg_left hY3 hCt
  have h3 := mul_le_mul_of_nonneg_left hY1 hc
  have hD := kDecay_of_gap hZ k r L.ε (X := |Formalism.MainNotions.BigCellDensity.c3| * thrX k r) (d := 0)
    (h := (Ct + |Formalism.MainNotions.BigCellDensity.c3| + 2) * gapY k r) (mul_nonneg hc hX) le_rfl (by nlinarith)
  have hg : PI.ZuckTensor.GapAtLeast L.ε L.lam ((Ct + |Formalism.MainNotions.BigCellDensity.c3| + 2) * gapY k r - 2 * 0) := by
    rw [mul_zero, sub_zero, gapY, ← mul_assoc]
    exact hgap
  exact JCx2.sq_inCC_mono (thr_conv k r (le_abs_self _) hc (by linarith)) le_rfl (kfin_inCC hK hC hD hg hfK 1)

end CompanionTheory.WaveGrid.Tied

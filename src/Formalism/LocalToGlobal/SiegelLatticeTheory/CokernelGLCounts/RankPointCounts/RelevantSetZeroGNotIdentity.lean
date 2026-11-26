module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DimFormC
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGram
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RelevantSetZeroGNotIdentity
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.MainNotions.S.Cnt Formalism.MainNotions.KappaEndpoints Formalism.MainNotions.LatticeGluingRadicals Formalism.MainNotions.BridgeLemma

namespace Formalism.L2.SG.KappaOffDiagonal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section ZsC1b

variable {D : D7} {X : HidaSetting D}

theorem fixedFlag_level_ne_zero (D : D7) (u : D.what₂.Word) : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 :=
  Nat.cast_ne_zero.mpr (D.mem u).A.T_prime.ne_zero

theorem relevantSet_zeroG_not_identity {Y : Full X} {u : D.what₂.Word} {t : GTu Y u} (ht : t ∈ relSet Y u) :
    t.relevant ∧ t.G = 0 ∧ ¬ t.isId := by
  obtain ⟨⟨hG, hid⟩, hr⟩ := ht
  refine ⟨hr, ?_, hid⟩
  have h : Gt t = 0 := hG
  unfold Gt at h
  by_contra hne
  rw [if_neg hne] at h
  exact one_ne_zero h

theorem exists_nfFull_of_relevant_of_G_eq_zero (Y : Full X) {u : D.what₂.Word} (t : GTu Y u) (hr : t.relevant) (hG : t.G = 0) :
    ∃ (j : ℕ) (hj : j ≤ D.R.rS) (c : D.host.E),
      Formalism.HermitianLatticeCounting.S6.NFFull (nfF (lf D (X.Fu u)).fl (fixedFlag_level_ne_zero D u)) (nfF (frq X t.rep).fl (nf_T_ne D u)) j hj c := by
  obtain ⟨hrel, hG0⟩ := relRepC D X Y u u t hr hG
  obtain ⟨σ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
  have hpos : 0 < (σ ((Tu D u : ℕ) : D.host.E)).re := by
    rw [map_natCast, Complex.natCast_re]
    exact_mod_cast tie_Tu_pos D u
  refine Formalism.HermitianLatticeCounting.Final.S6.normalForm D.host.E (hS D).V σ (nfH (hS D)) D.R.rS _ _ (fun x => p_starConj D σ x)
    hpos hpos (nf_pos _ _ (p_posX D _ (tie_Tu_pos D u) _) σ) (nf_pos _ _ (p_posX D _ (tie_Tu_pos D u) _) σ)
    (nf_rel D.host.F (tie_trace D.sp.cm) _ _ _ _ hrel) ?_
  rw [nf_G (lf D (X.Fu u)).fl (frq X t.rep).fl (fixedFlag_level_ne_zero D u) (nf_T_ne D u)]
  exact hG0

theorem index_eq_normalForm {Y : Full X} {u : D.what₂.Word} (t : GTu Y u) {j : ℕ} {hj : j ≤ D.R.rS} {c : D.host.E}
    (hN : Formalism.HermitianLatticeCounting.S6.NFFull (nfF (lf D (X.Fu u)).fl (fixedFlag_level_ne_zero D u)) (nfF (frq X t.rep).fl (nf_T_ne D u)) j hj c) :
    jT t = j := by
  have hfin := hN.1.2.1
  rw [nf_II (lf D (X.Fu u)).fl (frq X t.rep).fl (fixedFlag_level_ne_zero D u) (nf_T_ne D u)] at hfin
  unfold jT
  rw [hfin]
  omega

theorem realAbs_zero_eq_one (rd : ℝ) (τ : D.host.E →+* ℂ) (x : D.host.E) (hx : x = 1) :
    absReal rd τ D.R.rS 0 x = 1 := by
  subst hx
  simp [absReal, frameExp]

theorem delta_pos_le_height_sq (hPF : PFHost D) (large₂ : SizeData₂ D) {CH C : ℝ} (hCH : 0 ≤ CH) (hC : 2 * (CH + 1) ≤ C)
    {Y : Full X} {u : D.what₂.Word} (t : GTu Y u) (ht : t ∈ relSet Y u) :
    0 < k2Del D (jT t) (labT t) ∧
      k2Del D (jT t) (labT t) ≤ Hb large₂.sc.b C D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2 := by
  obtain ⟨hr, hG, -⟩ := relevantSet_zeroG_not_identity ht
  obtain ⟨j, hj, c, hN⟩ := exists_nfFull_of_relevant_of_G_eq_zero Y t hr hG
  have hjT := index_eq_normalForm t hN
  have hD : Dl (lf D (X.Fu u)).fl (frq X t.rep).fl j ≠ 0 := (nf_gen _ _ _ _ j hj c hN).2.2.2.1
  have hlab : labT t (jT t) = Dl (lf D (X.Fu u)).fl (frq X t.rep).fl j := by
    unfold labT
    rw [if_pos le_rfl, hjT]
  have hdel : k2Del D (jT t) (labT t) =
      ∏ τ : D.what₂.Tau, absReal D.host.rdE (embS D τ) D.R.rS (jT t) (labT t (jT t)) ^ 2 := by
    unfold k2Del
    exact hPF _ _
  have hrd := pf_rd_pos D
  have hpos : ∀ τ, 0 < absReal D.host.rdE (embS D τ) D.R.rS (jT t) (labT t (jT t)) := by
    intro τ
    unfold absReal
    rw [hlab]
    exact mul_pos (norm_pos_iff.2 ((map_ne_zero _).2 hD)) (Real.rpow_pos_of_pos hrd _)
  refine ⟨by rw [hdel]; exact Finset.prod_pos fun τ _ => pow_pos (hpos τ) 2, ?_⟩
  rw [hdel]
  have hb := two_le_scale_b D large₂
  have hH1 : 1 ≤ H1C large₂ CH := by
    unfold H1C
    exact Real.one_le_rpow (by linarith) (by positivity)
  unfold k2S
  rw [← Finset.prod_pow]
  refine Formalism.HermitianLatticeCounting.Final.S6.normSgBound D.what₂.Tau D.R.rS D.R.f _ _ (H1C large₂ CH) _ (szf_card_Tau D)
    (by linarith) (two_pow_le_height_bound _ CH C _ _ _ hb (two_rank_add_two_eq_m D) hCH hC) (fun τ => (hpos τ).le) (fun τ => ?_) (fun τ => ?_)
  · exact (Finset.le_fold_max _).2 (Or.inl le_rfl)
  · rcases Nat.eq_zero_or_pos (jT t) with h0 | h0
    · have hl0 : labT t (jT t) = 1 := by
        rw [hlab, ← hjT, h0]
        unfold Dl leadMinorE
        simp
      have h1 : absReal D.host.rdE (embS D τ) D.R.rS (jT t) (labT t (jT t)) = 1 := by
        rw [h0] at hl0 ⊢
        exact realAbs_zero_eq_one _ _ _ hl0
      rw [h1]
      have h2 : (1 : ℝ) ≤ (2 * H1C large₂ CH) ^ (2 * D.R.rS) := one_le_pow₀ (by linarith)
      have h3 : (1 : ℝ) / (2 * H1C large₂ CH) ^ (2 * D.R.rS) ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact h2
      exact h3.trans ((Finset.le_fold_max _).2 (Or.inl le_rfl))
    · have hmem : jT t ∈ k2ends D (jT t) (labT t) := by
        unfold k2ends
        simp only [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨h0, le_rfl⟩, by rw [hlab]; exact hD⟩
      exact (Finset.le_fold_max _).2 (Or.inr ⟨jT t, hmem, le_rfl⟩)

theorem localNorm_le_height_sq (hPF : PFHost D) (large₂ : SizeData₂ D) {CH C : ℝ} (hCH : 0 ≤ CH) (hC : 2 * (CH + 1) ≤ C)
    {Y : Full X} {u : D.what₂.Word} (t : GTu Y u) (l : ℕ) (hl : l ∈ k2ends D (jT t) (labT t)) :
    ((Nloc (ddS D) D.R.rS l (labT t l) : ℚ) : ℝ) ≤
      Hb large₂.sc.b C D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2 := by
  have hb := two_le_scale_b D large₂
  have hH1 : 1 ≤ H1C large₂ CH := by
    unfold H1C
    exact Real.one_le_rpow (by linarith) (by positivity)
  have hrd := pf_rd_pos D
  rw [hPF]
  unfold k2S
  rw [← Finset.prod_pow]
  refine Formalism.HermitianLatticeCounting.Final.S6.normSgBound D.what₂.Tau D.R.rS D.R.f _ _ (H1C large₂ CH) _ (szf_card_Tau D)
    (by linarith) (two_pow_le_height_bound _ CH C _ _ _ hb (two_rank_add_two_eq_m D) hCH hC) (fun τ => ?_) (fun τ => ?_) (fun τ => ?_)
  · unfold absReal
    positivity
  · exact (Finset.le_fold_max _).2 (Or.inl le_rfl)
  · exact (Finset.le_fold_max _).2 (Or.inr ⟨l, hl, le_rfl⟩)

end ZsC1b

theorem DelC_holds : DelC := by
  intro Cg cb Cw cT CT C0 CH hCH
  refine ⟨2 * (CH + 1), fun C hC => ⟨0, 0, fun C' Cl _ _ D large₂ X Y u hH _ t ht => ?_⟩⟩
  exact delta_pos_le_height_sq (PFHost_of_data D hH.1.2.1) large₂ hCH hC t ht

end Formalism.L2.SG.KappaOffDiagonal
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ExpQuarterMulExpQuarterLeTwo
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full

namespace Formalism.L2.SG.KappaOffDiagonal.PgLe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem finrank_F {D : D7} (X : HidaSetting D) : Module.finrank ℚ X.B.I.F = D.R.f := by
  have e1 : Module.finrank ℚ X.B.I.E = Module.finrank ℚ D.host.E :=
    (X.ιE.toRatAlgEquiv).toLinearEquiv.finrank_eq
  have e2 : Module.finrank ℚ X.B.I.F * Module.finrank X.B.I.F X.B.I.E = Module.finrank ℚ X.B.I.E :=
    Module.finrank_mul_finrank ℚ X.B.I.F X.B.I.E
  have e3 : Module.finrank X.B.I.F X.B.I.E = 2 := X.B.I.cm.deg2
  have e4 : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring_nf
  rw [e3] at e2
  omega

theorem one_factor (k b g : ℝ) (f : ℕ) (hk : 1 ≤ k) (hb : 2 ≤ b) (hg : (k * b) ^ 8 ≤ g) (hf : (f : ℝ) ≤ k) :
    (1 + 3 / g) ^ f ≤ Real.exp (1 / 4) := by
  have hk0 : 0 ≤ k := by linarith
  have hkb : 2 * k ≤ k * b := by nlinarith
  have hkb2 : 2 ≤ k * b := by linarith
  have h7 : (2:ℝ) ^ 7 ≤ (k * b) ^ 7 := by gcongr
  have h9 : (k * b) * 2 ^ 7 ≤ (k * b) * (k * b) ^ 7 := mul_le_mul_of_nonneg_left h7 (by linarith)
  have h8 : (k * b) ^ 8 = (k * b) * (k * b) ^ 7 := by ring
  have hg12 : 12 * (f : ℝ) ≤ g := by nlinarith
  have hgpos : 0 < g := by nlinarith
  have hx : 1 + 3 / g ≤ Real.exp (3 / g) := by
    have := Real.add_one_le_exp (3 / g)
    linarith
  have h0 : 0 ≤ 1 + 3 / g := by positivity
  calc (1 + 3 / g) ^ f ≤ Real.exp (3 / g) ^ f := by gcongr
    _ = Real.exp (f * (3 / g)) := (Real.exp_nat_mul _ f).symm
    _ ≤ Real.exp (1 / 4) := by
        apply Real.exp_le_exp.mpr
        have he : (f : ℝ) * (3 / g) = 3 * f / g := by ring
        rw [he, div_le_iff₀ hgpos]
        linarith

theorem exp_quarter_mul_exp_quarter_le_two : Real.exp (1 / 4) * Real.exp (1 / 4) ≤ 2 := by
  rw [← Real.exp_add]
  have h : Real.exp (1 / 4 + 1 / 4) ^ 2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h1 := Real.exp_one_lt_d9
  have hpos := Real.exp_pos (1 / 4 + 1 / 4)
  nlinarith

theorem pgLeC_of (hS : Formalism.L2.SG.Pf.SatGramLoc.SplitPrimeLoc) (hRC : Formalism.L2.SG.Pf.SatGramLoc.RedCore) : PgLeC := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y hH => ?_⟩
  have hPg := Formalism.L2.SG.Pf.SatGram.tt_eq' hS hRC Y.TR
  unfold Formalism.L2.SG.RowsConc.PgC
  rw [hPg, finrank_F X]
  obtain ⟨⟨hS0, -, -⟩, hP⟩ := hH
  obtain ⟨-, -, -, hfk, -⟩ := hS0
  have hg := hP.2.1
  have hb := Formalism.MainNotions.KappaEndpoints.two_le_scale_b D large₂
  have hk : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k; exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hf : (D.R.f : ℝ) ≤ D.R.k := by exact_mod_cast hfk
  have h0 := one_factor (D.R.k : ℝ) large₂.sc.b (D.host.g 0 : ℝ) D.R.f hk hb (hg 0).1 hf
  have h1 := one_factor (D.R.k : ℝ) large₂.sc.b (D.host.g 1 : ℝ) D.R.f hk hb (hg 1).1 hf
  calc (1 + 3 / (D.host.g 0 : ℝ)) ^ D.R.f * (1 + 3 / (D.host.g 1 : ℝ)) ^ D.R.f
      ≤ Real.exp (1 / 4) * Real.exp (1 / 4) :=
        mul_le_mul h0 h1 (by positivity) (Real.exp_pos _).le
    _ ≤ 2 := exp_quarter_mul_exp_quarter_le_two

end Formalism.L2.SG.KappaOffDiagonal.PgLe
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGVanish
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic

namespace Formalism.L2.SG.NGVanish

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hsEmb_eq_zero {Wq Wp : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (A : Wq →L[ℂ] Wp)
    (h : Formalism.L2.SG.PackageTie.hsEmb A = 0) : A = 0 := by
  have hi : ∀ i, A (stdOrthonormalBasis ℂ Wq i) = 0 := by
    intro i
    have := congrArg (fun v : Formalism.L2.SG.PackageTie.HS Wq Wp => WithLp.ofLp v i) h
    simpa [Formalism.L2.SG.PackageTie.hsEmb] using this
  have hA : (A : Wq →ₗ[ℂ] Wp) = 0 :=
    (stdOrthonormalBasis ℂ Wq).toBasis.ext (fun i => by simpa using hi i)
  ext x
  simpa using congrArg (fun f : Wq →ₗ[ℂ] Wp => f x) hA

def FormNGC : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ ν, Pinned X u u' ν → ∀ t ∈ (Y.tO u u').ngSet, (Y.tO u u').vec t ≠ 0 →
        (∃ w : Point D.host.E (D.R.rS + 1), toPts w = ptPN t ∧ ∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g) ∧
        ∀ w : Point D.host.E (D.R.rS + 1), toPts w = ptPN t → (∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g) →
          ∃ (c : ℂ) (A : X.Vpi u →L[ℂ] X.Vpi u) (B : X.Vpi u' →L[ℂ] X.Vpi u'),
            OOt t = c • A.comp ((haveI := FiniteDimensional.complete ℂ (X.Vpi u)
              OO (ν (Formalism.L2.SG.RealObj.gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u')
                (Formalism.L2.SG.RealObj.gamW X u u' w)).comp B)

theorem stepTermVanish_of_form (h : FormNGC) : StepTermVanish := by
  intro Cg cb Cw cT CT C0
  obtain ⟨a₀, b₀, h2⟩ := h Cg cb Cw cT CT C0
  refine ⟨a₀, b₀, fun C' Cl e1 e2 D large₂ X Y u u' hc ν hν t ht hJ => ?_⟩
  by_contra hv
  obtain ⟨⟨w, hw, hrep⟩, hform⟩ := h2 C' Cl e1 e2 D large₂ X Y u u' hc ν hν t ht hv
  have hex : ∃ w' : Point D.host.E (D.R.rS + 1), toPts w' = ptPN t ∧ ∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w' g :=
    ⟨w, hw, hrep⟩
  unfold J2of at hJ
  rw [dite_eq_left hex] at hJ
  have hJw : Jw Y u u' ν hex.choose = 0 :=
    hsEmb_eq_zero _ (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hJ))
  obtain ⟨c, A, B, hO⟩ := hform hex.choose hex.choose_spec.1 hex.choose_spec.2
  have key : ∀ (k χ c : ℂ) (A : X.Vpi u →L[ℂ] X.Vpi u) (Z : X.Vpi u' →L[ℂ] X.Vpi u)
      (B : X.Vpi u' →L[ℂ] X.Vpi u'), k • Z = 0 → k • (χ • (c • A.comp (Z.comp B))) = 0 := by
    intro k χ c A Z B hZ
    have hy : ∀ y, k • Z y = 0 := fun y => by simpa using congrArg (fun T => T y) hZ
    ext x
    simp only [smul_apply, ContinuousLinearMap.comp_apply, zero_apply]
    rw [smul_comm k χ, smul_comm k c, ← map_smul A k, hy]
    simp
  have hamp : ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t = 0 := by
    unfold ampN
    rw [hO]
    unfold Jw at hJw
    exact key _ _ _ _ _ _ hJw
  apply hv
  show vec (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t = 0
  unfold vec
  rw [hamp]
  simp
  rfl

end Formalism.L2.SG.NGVanish
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DecompPhaseCOf
noncomputable section

open scoped Classical ComplexConjugate

namespace Formalism.L2.SG.Pf.RowForm

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets
  Formalism.L2.SG.MassDataConc Formalism.L2.SG.MassDataForm MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
  (vR : Term D u u' (X.Fu u) (Y.what₂ u) → ℝ)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
  (κ : Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)

def DecompPhaseC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s : LiftT X Y u u' κ R ρ), s.1.relevant →
    (∃ γ, Formalism.L2.SG.RealObj.IsPtRep X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) γ) ∧
      ∃ g ∈ X.SinfU u, ∃ g' ∈ X.SinfU u',
        s.1.pt.1 = g * Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) * g'⁻¹ ∧
        Formalism.L2.SG.TermOp.chiN X (Formalism.L2.SG.TermOp.kOf X u u' ((Y.cs u).h ((Y.cs u).base s.1.lam) : X.B.I.Gf)
                  ((Y.cs u').h ((Y.cs u').base s.1.lam') : X.B.I.Gf) s.1.pt) *
          (X.psiInfU u g * conj (X.psiInfU u' g')) =
          Formalism.L2.SG.PairVal.phaseAt s.1.toTerm (Formalism.L2.SG.PairVal.ptOf s.1.toTerm)

theorem decompPhaseC_of (h3 : LiftDecompC X Y u u' κ) (h6 : PhaseTieC X Y u u' κ) : DecompPhaseC X Y u u' κ := by
  intro R ρ s hrel
  obtain ⟨hpt, g, hg, g', hg', hdec⟩ := h3 R ρ s hrel
  exact ⟨hpt, g, hg, g', hg', hdec, h6 R ρ s hrel g hg g' hg' hdec⟩

theorem normalFormC_of' (h1 : LiftAtSomeC X Y u u' κ)
    (h2 : Formalism.L2.SG.PairVal.CellPtUnique D u u' (X.Fu u) (Y.what₂ u))
    (h3 : DecompPhaseC X Y u u' κ) (h4 : DFrameAtS X u u' i0 i0' 1) (h4' : LiftGPosC X Y u u' κ)
    (h5 : FormTranspC X Y u u' vR νq κ) :
    NormalFormC X Y u u' vR i0 i0' νq κ := by
  intro R ρ s hrel
  obtain ⟨hpt, g, hg, g', hg', hdec, hph⟩ := h3 R ρ s hrel
  have hDF : ∃ p : X.B.I.Ginf × X.B.I.Ginf, Formalism.L2.SG.RealObj.IsDFrameX X u u' 1 i0 i0'
      (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm)) p.1 p.2 := by
    obtain ⟨h, h', hh⟩ := h4 one_pos _ hpt (h4' R ρ s hrel)
    exact ⟨(h, h'), hh⟩
  have hcS : hDF.choose.1 ∈ X.SinfU u := Formalism.L2.SG.RealObj.InfCut.hsetU_sub X u hDF.choose_spec.1
  have hcS' : hDF.choose.2 ∈ X.SinfU u' := Formalism.L2.SG.RealObj.InfCut.hsetU_sub X u' hDF.choose_spec.2.1
  have hcSi : hDF.choose.1⁻¹ ∈ X.SinfU u := Formalism.L2.SG.RealObj.InfCut.sinfU_inv X u hcS
  refine ⟨(Formalism.L2.SG.RealObj.InfCut.piIso X u hDF.choose.1 hcS).trans (Formalism.L2.SG.RealObj.InfCut.piIso X u g hg),
    (Formalism.L2.SG.RealObj.InfCut.piIso X u' hDF.choose.2 hcS').trans (Formalism.L2.SG.RealObj.InfCut.piIso X u' g' hg'), ?_⟩
  have hat : s.1.toTerm.atPt (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) := by
    obtain ⟨w0, hw0⟩ := h1 R ρ s hrel
    exact Formalism.L2.SG.PairVal.ptOf_spec _ ⟨w0, hw0, hrel⟩
  have hcT : Formalism.L2.SG.PairVal.cTerm vR s.1.toTerm =
      Formalism.L2.SG.PairVal.phaseAt s.1.toTerm (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) * (vR s.1.toTerm : ℂ) :=
    Formalism.L2.SG.PairVal.cTerm_of_atPt vR _ hat (fun w' hw' => h2 _ w' _ hw' hat)
  have hV : Formalism.L2.SG.RealObj.unscaledOperatorAtPointRepresentative X u u' 1 i0 i0' νq (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) =
      (X.piU u hDF.choose.1⁻¹).comp ((haveI := FiniteDimensional.complete ℂ (X.Vpi u)
        Formalism.L2.SG.TermOp.OO (νq (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm))) Set.univ
          (X.Wu u) (X.Wu u') (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm))).comp
        (X.piU u' hDF.choose.2)) := by
    unfold Formalism.L2.SG.RealObj.unscaledOperatorAtPointRepresentative Formalism.L2.SG.RealObj.unscaledFrameConjugatedOperator
    rw [if_pos hpt, dite_eq_left hDF]
  have hO : Formalism.L2.SG.TermOp.OOt s.1 =
      (((vR s.1.toTerm : ℝ) : ℂ) * (X.psiInfU u g * conj (X.psiInfU u' g'))) •
        (((Formalism.L2.SG.RealObj.InfCut.piIso X u g hg).toContinuousLinearEquiv : X.Vpi u →L[ℂ] X.Vpi u).comp
          ((haveI := FiniteDimensional.complete ℂ (X.Vpi u)
            Formalism.L2.SG.TermOp.OO (νq (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm))) Set.univ
              (X.Wu u) (X.Wu u') (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm))).comp
            ((Formalism.L2.SG.RealObj.InfCut.piIso X u' g' hg').symm.toContinuousLinearEquiv : X.Vpi u' →L[ℂ] X.Vpi u'))) := by
    rw [h5 R ρ s hrel g hg g' hg' hdec, ← smul_smul]
    congr 1
    rw [hdec]
    exact ClassFrameNormal.oo_map_mulLeft _ _ _ _ g g' _ _ _ _
      (fun x => (X.Wu_spec u).1 g hg x) (fun x => (X.Wu_spec u').1 g' hg' x)
  have e1 : ∀ z, X.piU u hDF.choose.1 (X.piU u hDF.choose.1⁻¹ z) = z := fun z => by
    rw [← ContinuousLinearMap.mul_apply, ← (X.piU_rep u).2.1 _ hcS _ hcSi, mul_inv_cancel, (X.piU_rep u).1,
      ContinuousLinearMap.one_apply]
  have e2 : ∀ y, X.piU u' hDF.choose.2 ((Formalism.L2.SG.RealObj.InfCut.piIso X u' hDF.choose.2 hcS').symm y) = y :=
    fun y => (Formalism.L2.SG.RealObj.InfCut.piIso X u' hDF.choose.2 hcS').apply_symm_apply y
  unfold chiOO frameVal
  rw [hO, hcT, hV, smul_smul, ← hph]
  have hsc : ∀ a c r : ℂ, a * (r * c) = a * c * r := fun a c r => by ring
  rw [hsc]
  congr 1
  ext x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.symm_trans, Formalism.L2.SG.RealObj.InfCut.piIso_apply, e1, e2]

end Formalism.L2.SG.Pf.RowForm
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocOrbSumShift
noncomputable section

namespace Formalism.L2.SG.Pf.LocOrbSumPf

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups MeasureTheory
open Formalism.L2.SG.LsDatumB
open Classical

section ShiftPf

variable {D : Formalism.BasicNotions.D7}

theorem blkMod_eq (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) :
    ∀ a s t x y, 1 ≤ a → a - 1 ≤ x → a - 1 ≤ y → x + y + 1 = 2 * (a - 1) + s → x ≤ D.R.rS → y ≤ D.R.rS →
      ¬ (x = D.R.rS ∧ y = D.R.rS) →
        blkMod δ T T' p a s t = Formalism.L2.SG.Pf.rho δ p x * Formalism.L2.SG.Pf.rho δ p y * Formalism.L2.SG.Pf.kap p *
          (D.s.atP p).ιE t := by
  intro a s t x y h1 h2 h3 h4 h5 h6 h7
  rw [← Formalism.L2.SG.Pf.blkTop_eq δ T T' p a s t x y h1 h2 h3 h4 h5 h6 h7]
  unfold blkTop
  rw [if_neg]
  rintro ⟨hs, rfl⟩
  omega

theorem modMat_off (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) (w : Point D.host.E (D.R.rS + 1))
    (x y : Fin (D.R.rS + 1)) (hn : ¬ (x = Fin.last D.R.rS ∧ y = Fin.last D.R.rS)) :
    modMat δ T T' p w x y = Formalism.L2.SG.Pf.rho δ p x * Formalism.L2.SG.Pf.rho δ p y * Formalism.L2.SG.Pf.kap p *
      (D.s.atP p).ιE (ptMat w x y) := by
  have hn' : ¬ ((x : ℕ) = D.R.rS ∧ (y : ℕ) = D.R.rS) := fun h =>
    hn ⟨Fin.ext (by rw [Fin.val_last]; exact h.1), Fin.ext (by rw [Fin.val_last]; exact h.2)⟩
  have e := Formalism.L2.SG.Pf.ptEntry_scale (D.s.atP p).ιE (blkMod δ T T' p) (Formalism.L2.SG.Pf.rho δ p)
    (Formalism.L2.SG.Pf.kap p) D.R.rS (blkMod_eq δ T T' p) w.1 1
    x y le_rfl (by have := x.isLt; omega) (by have := y.isLt; omega) (by simpa using hn')
  simp only [Nat.sub_self, zero_add] at e
  show ptEntry (mapBlocks (blkMod δ T T' p) 1 w.1) x y = _
  rw [e]
  rfl

theorem modMat_last (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) (w : Point D.host.E (D.R.rS + 1))
    (l0 : List (D.host.E × ℕ)) (t : D.host.E) (hb : w.1 = l0 ++ [(t, 1)]) (hs : (l0.map Prod.snd).sum = D.R.rS) :
    modMat δ T T' p w (Fin.last _) (Fin.last _) = blkMod δ T T' p (D.R.rS + 1) 1 t := by
  show ptEntry (mapBlocks (blkMod δ T T' p) 1 w.1) D.R.rS D.R.rS = _
  have hs' : ((mapBlocks (blkMod δ T T' p) 1 l0).map Prod.snd).sum = D.R.rS := by
    rw [Formalism.L2.SG.Pf.mapBlocks_snd, hs]
  rw [hb, Formalism.L2.SG.Pf.mapBlocks_append, Formalism.L2.SG.Pf.ptEntry_append_ge _ _ _ _ hs'.le, if_pos hs'.le, hs',
    Nat.sub_self, hs, add_comm]
  simp [mapBlocks, ptEntry]

theorem corner_zero {B : Type} [Zero B] (f : ℕ → ℕ → D.host.E → B) (w : Point D.host.E (D.R.rS + 1))
    (l0 : List (D.host.E × ℕ)) (t : D.host.E) (s : ℕ) (hb : w.1 = l0 ++ [(t, s)])
    (hs : (l0.map Prod.snd).sum + s = D.R.rS + 1) (h2 : 2 ≤ s) :
    ptEntry (mapBlocks f 1 w.1) D.R.rS D.R.rS = 0 := by
  have hs' : ((mapBlocks f 1 l0).map Prod.snd).sum = (l0.map Prod.snd).sum := by
    rw [Formalism.L2.SG.Pf.mapBlocks_snd]
  have hle : ((mapBlocks f 1 l0).map Prod.snd).sum ≤ D.R.rS := by rw [hs']; omega
  rw [hb, Formalism.L2.SG.Pf.mapBlocks_append, Formalism.L2.SG.Pf.ptEntry_append_ge _ _ _ _ hle, if_pos hle, hs']
  simp only [mapBlocks, ptEntry]
  split_ifs <;> first | rfl | omega

theorem last_big (w : Point D.host.E (D.R.rS + 1)) (h0 : Dmin w D.R.rS = 0) :
    ∃ l0 t s, w.1 = l0 ++ [(t, s)] ∧ (l0.map Prod.snd).sum + s = D.R.rS + 1 ∧ 2 ≤ s := by
  have hne : w.1 ≠ [] := by
    intro h
    have := w.2.2
    rw [h] at this
    simp at this
  obtain ⟨l0, b, hb⟩ : ∃ l0 b, w.1 = l0 ++ [b] :=
    ⟨w.1.dropLast, w.1.getLast hne, (List.dropLast_append_getLast hne).symm⟩
  obtain ⟨t, s⟩ := b
  have hmem := w.2.1 (t, s) (by rw [hb]; simp)
  have hsum : (l0.map Prod.snd).sum + s = D.R.rS + 1 := by
    have := w.2.2
    rw [hb] at this
    simpa using this
  refine ⟨l0, t, s, hb, hsum, ?_⟩
  by_contra hlt
  have hs1 : s = 1 := by have := hmem.2; omega
  subst hs1
  have := Formalism.L2.SG.Pf.dmin_snoc w l0 t hb (by omega)
  rw [h0, zero_mul] at this
  exact Formalism.MainNotions.BridgeLemma.Dmin_top_ne w this

theorem modShift_holds (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) :
    ModShift δ T T' p w := by
  intro a ha
  ext x y
  rw [Matrix.add_apply]
  by_cases hc : x = Fin.last D.R.rS ∧ y = Fin.last D.R.rS
  · obtain ⟨rfl, rfl⟩ := hc
    have hsh : shM δ T T' p w (Fin.last _) (Fin.last _) = cornerSh δ T T' p w := by simp [shM]
    rw [hsh]
    by_cases h0 : Dmin w D.R.rS = 0
    · have hc0 : cornerSh δ T T' p w = 0 := by unfold cornerSh; rw [if_pos h0]
      rw [hc0, add_zero]
      obtain ⟨l0, t, s, hb, hs, h2⟩ := last_big w h0
      have e1 := corner_zero (blkTop δ T T' p) w l0 t s hb hs h2
      have e2 := corner_zero (blkMod δ T T' p) w l0 t s hb hs h2
      show Loc.ptEntryL a.blocks D.R.rS D.R.rS = ptEntry (mapBlocks (blkMod δ T T' p) 1 w.1) D.R.rS D.R.rS
      rw [Formalism.L2.SG.Pf.ptEntryL_eq, Formalism.L2.SG.Pf.modPt_blocks δ T T' p w a ha, e1, e2]
    · obtain ⟨l0, t, hb, hs⟩ := Formalism.L2.SG.Pf.last_one w h0
      rw [Formalism.L2.SG.Pf.amat_last δ T T' p w a ha l0 t hb hs, modMat_last δ T T' p w l0 t hb hs]
      unfold cornerSh
      rw [if_neg h0, Formalism.L2.SG.Pf.zeta_snoc w h0 l0 t hb hs]
      unfold blkTop
      rw [if_pos ⟨by omega, rfl⟩]
  · rw [Formalism.L2.SG.Pf.amat_eq δ T T' p w a ha x y hc, modMat_off δ T T' p w x y hc]
    have : shM δ T T' p w x y = 0 := by simp only [shM, Matrix.of_apply]; rw [if_neg hc]
    rw [this, add_zero]

end ShiftPf

end Formalism.L2.SG.Pf.LocOrbSumPf
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NinfConjIff
noncomputable section

open scoped Classical ComplexConjugate
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.KappaOffDiagonal

open Matrix

namespace Formalism.L2.SG.CovariantRepresentation

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Mat

variable {n r : ℕ}

theorem hJ_unitary (ε : Fin n → Bool) (P : Matrix (Fin n) (Fin n) ℂ) (hU : Pᴴ * Formalism.REAL.Jm ε * P = Formalism.REAL.Jm ε)
    (x y : Fin n → ℂ) : hJ ε (P *ᵥ x) (P *ᵥ y) = hJ ε x y := by
  delta hJ
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hU]

theorem fix_span (e : Fin r → Fin n → ℂ) (Q : Matrix (Fin n) (Fin n) ℂ) (he : ∀ a, Q *ᵥ e a = e a) (k : ℕ) :
    ∀ x ∈ spanLt e k, Q *ᵥ x = x := by
  delta spanLt
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, -, rfl⟩ := hy
    exact he a
  | zero => exact Matrix.mulVec_zero Q
  | add y z _ _ hy hz => rw [Matrix.mulVec_add, hy, hz]
  | smul c y _ hy => rw [Matrix.mulVec_smul, hy]

theorem inN_conj (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (P Q g : Matrix (Fin n) (Fin n) ℂ)
    (hQP : Q * P = 1) (hU : Pᴴ * Formalism.REAL.Jm ε * P = Formalism.REAL.Jm ε) (he : ∀ a, P *ᵥ e a = e a) (hz : P *ᵥ z = z)
    (hg : InN ε e z g) : InN ε e z (Q * g * P) := by
  have hQv' : ∀ v, Q *ᵥ (P *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, hQP, Matrix.one_mulVec]
  have hQv : ∀ v, P *ᵥ v = v → Q *ᵥ v = v := fun v hv =>
    calc Q *ᵥ v = Q *ᵥ (P *ᵥ v) := by rw [hv]
      _ = v := hQv' v
  have hQe : ∀ a, Q *ᵥ e a = e a := fun a => hQv (e a) (he a)
  have key : ∀ (v : Fin n → ℂ) (k : ℕ), P *ᵥ v = v → (g - 1) *ᵥ v ∈ spanLt e k →
      (Q * g * P - 1) *ᵥ v ∈ spanLt e k := by
    intro v k hv hw
    have h : (Q * g * P - 1) *ᵥ v = Q *ᵥ ((g - 1) *ᵥ v) := by
      rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_sub, hQv v hv]
    rw [h, fix_span e Q hQe k _ hw]
    exact hw
  obtain ⟨⟨h1a, h1b⟩, h2⟩ := hg
  refine ⟨⟨fun a => key (e a) a (he a) (h1a a), key z r hz h1b⟩, fun y hy => ?_⟩
  have hy' : ∀ a, hJ ε (e a) (P *ᵥ y) = 0 := fun a =>
    calc hJ ε (e a) (P *ᵥ y) = hJ ε (P *ᵥ e a) (P *ᵥ y) := by rw [he a]
      _ = hJ ε (e a) y := hJ_unitary ε P hU (e a) y
      _ = 0 := hy a
  have hw := h2 (P *ᵥ y) hy'
  have h : (Q * g * P - 1) *ᵥ y = Q *ᵥ ((g - 1) *ᵥ (P *ᵥ y)) := by
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub, hQv' y]
  rw [h, fix_span e Q hQe r _ hw]
  exact hw

end Mat

section Grp

variable {D : D7} (X : HidaSetting D)

theorem fix_inv (s : X.B.I.Ginf) {v : InfinitePlace X.B.I.F} {x : Fin X.B.I.n → ℂ} (hx : uMat (s v) *ᵥ x = x) :
    uMat (s⁻¹ v) *ᵥ x = x := by
  have h1 : uMat (s⁻¹ v) * uMat (s v) = 1 := by
    delta uMat
    simp
  calc uMat (s⁻¹ v) *ᵥ x = uMat (s⁻¹ v) *ᵥ (uMat (s v) *ᵥ x) := by rw [hx]
    _ = x := by rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]

theorem ninf_conj (u : D.what₂.Word) (s : X.B.I.Ginf)
    (he : ∀ v a, uMat (s v) *ᵥ rv X.B.I v (X.eR a) = rv X.B.I v (X.eR a))
    (hz : ∀ v, uMat (s v) *ᵥ rv X.B.I v (X.zR u) = rv X.B.I v (X.zR u))
    {r : X.B.I.Ginf} (hr : r ∈ X.NinfU u) : s⁻¹ * r * s ∈ X.NinfU u := by
  dsimp [HidaSetting.NinfU, Ninf] at hr ⊢
  intro v
  have h1 : uMat (s⁻¹ v) * uMat (s v) = 1 := by
    delta uMat
    simp
  have hmul : uMat ((s v)⁻¹ * r v * s v) = uMat (s⁻¹ v) * uMat (r v) * uMat (s v) := by
    delta uMat
    simp
  have hU : (uMat (s v))ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * uMat (s v) = Formalism.REAL.Jm (X.B.I.ε v) := by
    delta uMat
    first
    | exact (s v).2
    | exact (s v).1.2
    | simpa using (s v).2
  rw [hmul]
  exact inN_conj _ _ _ (uMat (s v)) (uMat (s⁻¹ v)) (uMat (r v)) h1 hU (he v) (hz v) (hr v)

theorem ninf_conj_iff (u : D.what₂.Word) (s : X.B.I.Ginf)
    (he : ∀ v a, uMat (s v) *ᵥ rv X.B.I v (X.eR a) = rv X.B.I v (X.eR a))
    (hz : ∀ v, uMat (s v) *ᵥ rv X.B.I v (X.zR u) = rv X.B.I v (X.zR u)) (r : X.B.I.Ginf) :
    r ∈ X.NinfU u ↔ s⁻¹ * r * s ∈ X.NinfU u := by
  constructor
  · exact ninf_conj X u s he hz
  · intro h
    have he' : ∀ v a, uMat (s⁻¹ v) *ᵥ rv X.B.I v (X.eR a) = rv X.B.I v (X.eR a) :=
      fun v a => fix_inv X s (he v a)
    have hz' : ∀ v, uMat (s⁻¹ v) *ᵥ rv X.B.I v (X.zR u) = rv X.B.I v (X.zR u) :=
      fun v => fix_inv X s (hz v)
    have h2 := ninf_conj X u s⁻¹ he' hz' h
    simpa [mul_assoc] using h2

end Grp


open Formalism.L2.SG.TermOp.Vanish in
theorem fixNormC : FixNormC := by
  intro D X Y u u' t h hh r
  have hfe : ∀ v a, uMat (h v) *ᵥ rv X.B.I v (X.eR a) = rv X.B.I v (X.eR a) :=
    fun v a => fix_rv hh (basis_mem_fixedSubspace t.rep a) v
  have hfz : ∀ v, uMat (h v) *ᵥ rv X.B.I v (X.zR u) = rv X.B.I v (X.zR u) :=
    fun v => fix_rv hh (zu_mem_fixedSubspaceOfRepresentative t.rep) v
  have hfe' : ∀ v a, uMat ((t.pt.1⁻¹ * h * t.pt.1) v) *ᵥ rv X.B.I v (X.eR a) = rv X.B.I v (X.eR a) :=
    fun v a => fix'_rv hh (ge_mem_fixedSubspace t.rep a) v
  have hfz' : ∀ v, uMat ((t.pt.1⁻¹ * h * t.pt.1) v) *ᵥ rv X.B.I v (X.zR u') = rv X.B.I v (X.zR u') :=
    fun v => fix'_rv hh (gz_mem_fixedSubspace t.rep) v
  have e : t.pt.1⁻¹ * (h⁻¹ * r * h) * t.pt.1 =
      (t.pt.1⁻¹ * h * t.pt.1)⁻¹ * (t.pt.1⁻¹ * r * t.pt.1) * (t.pt.1⁻¹ * h * t.pt.1) := by group
  show (r ∈ X.NinfU u ∧ t.pt.1⁻¹ * r * t.pt.1 ∈ X.NinfU u') ↔
    (h⁻¹ * r * h ∈ X.NinfU u ∧ t.pt.1⁻¹ * (h⁻¹ * r * h) * t.pt.1 ∈ X.NinfU u')
  rw [e, ← ninf_conj_iff X u h hfe hfz r, ← ninf_conj_iff X u' _ hfe' hfz' (t.pt.1⁻¹ * r * t.pt.1)]

end Formalism.L2.SG.CovariantRepresentation
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.KloostermanTermANonneg
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.MainNotions.S.Cnt Formalism.MainNotions.KappaEndpoints

set_option linter.dupNamespace false

namespace Formalism.L2.SG.KappaOffDiagonal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Asm

variable {D : D7} {X : HidaSetting D}

theorem kloostermanTermA_nonneg (large₂ : SizeData₂ D) {C Ch Cc : ℝ} (hC : 0 ≤ C) (hCh : 0 ≤ Ch) (hCc : 0 ≤ Cc) (j : ℕ) :
    0 ≤ k2A1 large₂ C Ch Cc j := by
  have hHb : ∀ c, 0 < Hb large₂.sc.b c D.R.m D.R.f := fun c => by unfold Hb Scale.b; positivity
  have h1 : 0 ≤ C / (D.R.k : ℝ) := div_nonneg hC (Nat.cast_nonneg _)
  unfold k2A1
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg h1 _)
    (Real.rpow_nonneg (hHb C).le _)) (Real.rpow_nonneg (hHb Ch).le _)) (Real.rpow_nonneg (hHb C).le _))
    (Real.rpow_nonneg (hHb Cc).le _)

theorem label_sum {large₂ : SizeData₂ D} {Y : Full X} {u : D.what₂.Word} {CH Cs C Ch Cp Cc : ℝ}
    (hC : 0 ≤ C) (hCh : 0 ≤ Ch) (hCs : Cp + 4 ≤ Cs)
    (hDel : ∀ t ∈ relSet Y u, 0 < k2Del D (jT t) (labT t) ∧
      k2Del D (jT t) (labT t) ≤ Hb large₂.sc.b C D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2)
    (j : ℕ) (hj : j ∈ Finset.Icc 1 D.R.rS)
    (hcos : ∀ T : Finset (ℕ → D.host.E), (∀ δ ∈ T, ∃ t ∈ relSet Y u, jT t = j ∧ labT t = δ) →
      ∑ δ ∈ T, k2S D (H1C large₂ CH) j δ ^ (-(3 * (D.R.rS : ℝ))) ≤ Hb large₂.sc.b Cc D.R.m D.R.f ^ (Cc * (D.R.rS : ℝ)))
    (T : Finset (ℕ → D.host.E)) (hTm : ∀ δ ∈ T, ∃ t ∈ relSet Y u, jT t = j ∧ labT t = δ) :
    ∑ δ ∈ T, k2a large₂ CH Cs C j δ * k2e large₂ CH Ch Cp j δ ≤ k2A1 large₂ C Ch Cc j := by
  have hH : H1C large₂ CH = large₂.sc.b ^ (CH * (D.R.m : ℝ)) := rfl
  rw [hH] at hDel hcos
  have hHb : ∀ c, 0 < Hb large₂.sc.b c D.R.m D.R.f := fun c => by unfold Hb Scale.b; positivity
  have hk : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have hrk : D.R.rS + 3 ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    unfold Ranks.rS
    omega
  have hrkR : (D.R.rS : ℝ) + 3 ≤ D.R.k := by exact_mod_cast hrk
  have hjr : (j : ℝ) ≤ D.R.rS := by exact_mod_cast (Finset.mem_Icc.1 hj).2
  have hS1 : ∀ δ, 1 ≤ k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ := by
    intro δ
    unfold k2S
    refine Finset.prod_induction _ (fun x => 1 ≤ x) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb)
      le_rfl fun τ _ => ?_
    unfold k2sg
    exact (Finset.le_fold_max 1).2 (Or.inl le_rfl)
  have hK0 : 0 ≤ ((C / D.R.k) ^ ((j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f) * Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) *
        Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4)) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (div_nonneg hC hk) _) (Real.rpow_nonneg (hHb C).le _))
      (Real.rpow_nonneg (hHb Ch).le _)
  have hK : 0 ≤ ((C / D.R.k) ^ ((j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f) * Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) *
        Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4)) * Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ) + 1) / 2) := mul_nonneg hK0 (Real.rpow_nonneg (hHb C).le _)
  have key : ∀ δ ∈ T, k2a large₂ CH Cs C j δ * k2e large₂ CH Ch Cp j δ ≤
      (((C / D.R.k) ^ ((j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f) * Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) *
        Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4)) * Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ) + 1) / 2)) * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ (-(3 * (D.R.rS : ℝ))) := by
    intro δ hδ
    obtain ⟨t, ht, hjt, hlt⟩ := hTm δ hδ
    obtain ⟨hΔ0, hΔle⟩ := hDel t ht
    rw [hjt, hlt] at hΔ0 hΔle
    have hS := hS1 δ
    have hS0 : 0 ≤ k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ := by linarith
    have e1 : k2Del D j δ ^ (-(((D.R.k : ℝ) - 1 - j) / 2)) * k2Del D j δ ^ ((D.R.k : ℝ) / 2) =
        k2Del D j δ ^ (((j : ℝ) + 1) / 2) := by
      rw [← Real.rpow_add hΔ0]; congr 1; ring
    have e2 : k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ (-(Cs * D.R.k)) * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ (Cp * D.R.k) = k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ ((Cp - Cs) * D.R.k) := by
      rw [← Real.rpow_add (by linarith)]; congr 1; ring
    have b1 : k2Del D j δ ^ (((j : ℝ) + 1) / 2) ≤ Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ) + 1) / 2) * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ ((j : ℝ) + 1) := by
      calc k2Del D j δ ^ (((j : ℝ) + 1) / 2) ≤ (Hb large₂.sc.b C D.R.m D.R.f * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ 2) ^ (((j : ℝ) + 1) / 2) :=
            Real.rpow_le_rpow hΔ0.le hΔle (by positivity)
        _ = Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ) + 1) / 2) * (k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ 2) ^ (((j : ℝ) + 1) / 2) :=
            Real.mul_rpow (hHb C).le (by positivity)
        _ = Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ) + 1) / 2) * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ ((j : ℝ) + 1) := by
            rw [← Real.rpow_natCast (k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ) 2, ← Real.rpow_mul hS0]; congr 2; push_cast; ring
    have b2 : k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ ((j : ℝ) + 1) * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ ((Cp - Cs) * D.R.k) ≤ k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ (-(3 * (D.R.rS : ℝ))) := by
      rw [← Real.rpow_add (by linarith)]
      apply Real.rpow_le_rpow_of_exponent_le hS
      nlinarith [mul_le_mul_of_nonneg_right hCs hk]
    calc k2a large₂ CH Cs C j δ * k2e large₂ CH Ch Cp j δ
        = ((C / D.R.k) ^ ((j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f) * Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) *
        Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4)) * (k2Del D j δ ^ (-(((D.R.k : ℝ) - 1 - j) / 2)) * k2Del D j δ ^ ((D.R.k : ℝ) / 2)) *
            (k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ (-(Cs * D.R.k)) * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ (Cp * D.R.k)) := by
          unfold k2a k2e; ring
      _ = ((C / D.R.k) ^ ((j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f) * Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) *
        Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4)) * k2Del D j δ ^ (((j : ℝ) + 1) / 2) * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ ((Cp - Cs) * D.R.k) := by rw [e1, e2]
      _ ≤ ((C / D.R.k) ^ ((j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f) * Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) *
        Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4)) * (Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ) + 1) / 2) * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ ((j : ℝ) + 1)) * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ ((Cp - Cs) * D.R.k) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left b1 hK0) (Real.rpow_nonneg hS0 _)
      _ = (((C / D.R.k) ^ ((j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f) * Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) *
        Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4)) * Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ) + 1) / 2)) *
            (k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ ((j : ℝ) + 1) * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ ((Cp - Cs) * D.R.k)) := by ring
      _ ≤ (((C / D.R.k) ^ ((j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f) * Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) *
        Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4)) * Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ) + 1) / 2)) * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ (-(3 * (D.R.rS : ℝ))) :=
          mul_le_mul_of_nonneg_left b2 hK
  calc ∑ δ ∈ T, k2a large₂ CH Cs C j δ * k2e large₂ CH Ch Cp j δ
      ≤ ∑ δ ∈ T, (((C / D.R.k) ^ ((j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f) * Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) *
        Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4)) * Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ) + 1) / 2)) * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ (-(3 * (D.R.rS : ℝ))) :=
        Finset.sum_le_sum key
    _ = (((C / D.R.k) ^ ((j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f) * Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) *
        Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4)) * Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ) + 1) / 2)) * ∑ δ ∈ T, k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ (-(3 * (D.R.rS : ℝ))) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ (((C / D.R.k) ^ ((j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f) * Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) *
        Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4)) * Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ) + 1) / 2)) * Hb large₂.sc.b Cc D.R.m D.R.f ^ (Cc * (D.R.rS : ℝ)) :=
        mul_le_mul_of_nonneg_left (hcos T hTm) hK
    _ = k2A1 large₂ C Ch Cc j := by unfold k2A1; ring

theorem rank_bound {large₂ : SizeData₂ D} {Y : Full X} {u : D.what₂.Word} {CH Cs C Ch Cp Cc : ℝ}
    (hC : 0 ≤ C) (hCh : 0 ≤ Ch) (hCs : Cp + 4 ≤ Cs) (hK : 0 ≤ dpiC X u * massC Y u)
    (hType : TypeAt large₂ Y u CH Cs C Ch Cp)
    (hDel : ∀ t ∈ relSet Y u, 0 < k2Del D (jT t) (labT t) ∧
      k2Del D (jT t) (labT t) ≤ Hb large₂.sc.b C D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2)
    (hcos : ∀ j ∈ Finset.Icc 1 D.R.rS, ∀ T : Finset (ℕ → D.host.E),
      (∀ δ ∈ T, ∃ t ∈ relSet Y u, jT t = j ∧ labT t = δ) →
      ∑ δ ∈ T, k2S D (H1C large₂ CH) j δ ^ (-(3 * (D.R.rS : ℝ))) ≤ Hb large₂.sc.b Cc D.R.m D.R.f ^ (Cc * (D.R.rS : ℝ)))
    (j' : ℕ) (hj' : j' ∈ Finset.Icc 1 D.R.rS) (j'' : ℕ) (hj'' : j'' ∈ Finset.Icc 1 D.R.rS)
    (S : Finset (GTu Y u × GTu Y u))
    (hS : ∀ p ∈ S, p ∈ (Y.tO u u).allPairs (relSet Y u) ∧ jT p.1 = j' ∧ jT p.2 = j'') :
    ∑ p ∈ S, ‖(Y.tO u u).vec p.1‖ * ‖(Y.tO u u).vec p.2‖ ≤
      dpiC X u * massC Y u * (k2A1 large₂ C Ch Cc j' * k2A1 large₂ C Ch Cc j'') := by
  have hHb : ∀ c, 0 < Hb large₂.sc.b c D.R.m D.R.f := fun c => by unfold Hb Scale.b; positivity
  have hk : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have hSpos : ∀ j δ, 0 ≤ k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ := by
    intro j δ
    unfold k2S
    refine Finset.prod_nonneg fun τ _ => ?_
    unfold k2sg
    exact le_trans zero_le_one ((Finset.le_fold_max 1).2 (Or.inl le_rfl))
  have hA0 : ∀ j δ, (∃ t ∈ relSet Y u, jT t = j ∧ labT t = δ) →
      0 ≤ k2a large₂ CH Cs C j δ * k2e large₂ CH Ch Cp j δ := by
    rintro j δ ⟨t, ht, rfl, rfl⟩
    have hΔ := (hDel t ht).1
    unfold k2a k2e
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg (div_nonneg hC hk) _)
      (Real.rpow_nonneg hΔ.le _)) (Real.rpow_nonneg (hHb C).le _)) (Real.rpow_nonneg (hSpos _ _) _))
      (mul_nonneg (mul_nonneg (Real.rpow_nonneg hΔ.le _) (Real.rpow_nonneg (hHb Ch).le _))
        (Real.rpow_nonneg (hSpos _ _) _))
  have hT1 : ∀ δ ∈ S.image (fun p => labT p.1), ∃ t ∈ relSet Y u, jT t = j' ∧ labT t = δ := by
    intro δ hδ
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hδ
    exact ⟨p.1, (hS p hp).1.1, (hS p hp).2.1, rfl⟩
  have hT2 : ∀ δ ∈ S.image (fun p => labT p.2), ∃ t ∈ relSet Y u, jT t = j'' ∧ labT t = δ := by
    intro δ hδ
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hδ
    exact ⟨p.2, (hS p hp).1.2.1, (hS p hp).2.2, rfl⟩
  have hmap : ∀ p ∈ S, (labT p.1, labT p.2) ∈
      S.image (fun p => labT p.1) ×ˢ S.image (fun p => labT p.2) := fun p hp =>
    Finset.mem_product.2 ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩
  have hL1 := label_sum hC hCh hCs hDel j' hj' (hcos j' hj') _ hT1
  have hL2 := label_sum hC hCh hCs hDel j'' hj'' (hcos j'' hj'') _ hT2
  have hs1 := Finset.sum_nonneg fun δ hδ => hA0 _ _ (hT1 δ hδ)
  have hs2 := Finset.sum_nonneg fun δ hδ => hA0 _ _ (hT2 δ hδ)
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  calc _ ≤ ∑ l ∈ S.image (fun p => labT p.1) ×ˢ S.image (fun p => labT p.2),
        dpiC X u * massC Y u * ((k2a large₂ CH Cs C j' l.1 * k2e large₂ CH Ch Cp j' l.1) *
          (k2a large₂ CH Cs C j'' l.2 * k2e large₂ CH Ch Cp j'' l.2)) := by
        refine Finset.sum_le_sum fun l _ => hType j' hj' j'' hj'' l.1 l.2 _ fun p hp => ?_
        obtain ⟨hpS, hpl⟩ := Finset.mem_filter.1 hp
        obtain ⟨h1, h2, h3⟩ := hS p hpS
        exact ⟨h1, h2, h3, congrArg Prod.fst hpl, congrArg Prod.snd hpl⟩
    _ = dpiC X u * massC Y u *
          ((∑ δ ∈ S.image (fun p => labT p.1), k2a large₂ CH Cs C j' δ * k2e large₂ CH Ch Cp j' δ) *
           (∑ δ ∈ S.image (fun p => labT p.2), k2a large₂ CH Cs C j'' δ * k2e large₂ CH Ch Cp j'' δ)) := by
        rw [← Finset.mul_sum, Finset.sum_product, Finset.sum_mul_sum]
    _ ≤ dpiC X u * massC Y u * (k2A1 large₂ C Ch Cc j' * k2A1 large₂ C Ch Cc j'') :=
        mul_le_mul_of_nonneg_left (mul_le_mul hL1 hL2 hs2 (hs1.trans hL1)) hK

theorem fin_bound {large₂ : SizeData₂ D} {Y : Full X} {u : D.what₂.Word} {CH Cs C Ch Cp Cc : ℝ}
    (hC : 0 ≤ C) (hCh : 0 ≤ Ch) (hCs : Cp + 4 ≤ Cs) (hK : 0 ≤ dpiC X u * massC Y u)
    (hIrr : ∀ t ∈ (Y.tO u u).degSet, ¬ t.relevant → (Y.tO u u).vec t = 0)
    (hJ : ∀ t ∈ relSet Y u, 1 ≤ jT t)
    (hType : TypeAt large₂ Y u CH Cs C Ch Cp)
    (hDel : ∀ t ∈ relSet Y u, 0 < k2Del D (jT t) (labT t) ∧
      k2Del D (jT t) (labT t) ≤ Hb large₂.sc.b C D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2)
    (hcos : ∀ j ∈ Finset.Icc 1 D.R.rS, ∀ T : Finset (ℕ → D.host.E),
      (∀ δ ∈ T, ∃ t ∈ relSet Y u, jT t = j ∧ labT t = δ) →
      ∑ δ ∈ T, k2S D (H1C large₂ CH) j δ ^ (-(3 * (D.R.rS : ℝ))) ≤ Hb large₂.sc.b Cc D.R.m D.R.f ^ (Cc * (D.R.rS : ℝ)))
    (S : Finset (GTu Y u × GTu Y u)) (hS : ∀ p ∈ S, p ∈ (Y.tO u u).allPairs (Y.tO u u).degSet) :
    ∑ p ∈ S, ‖(Y.tO u u).vec p.1‖ * ‖(Y.tO u u).vec p.2‖ ≤
      dpiC X u * massC Y u * (∑ j ∈ Finset.Icc 1 D.R.rS, k2A1 large₂ C Ch Cc j) ^ 2 := by
  have hne : ∀ p ∈ S, ‖(Y.tO u u).vec p.1‖ * ‖(Y.tO u u).vec p.2‖ ≠ 0 →
      p.1.relevant ∧ p.2.relevant := by
    intro p hp hF
    by_contra h
    apply hF
    rcases not_and_or.1 h with h1 | h1
    · rw [hIrr _ (hS p hp).1 h1, norm_zero, zero_mul]
    · rw [hIrr _ (hS p hp).2.1 h1, norm_zero, mul_zero]
  have hmap : ∀ p ∈ S.filter (fun p => p.1.relevant ∧ p.2.relevant),
      (jT p.1, jT p.2) ∈ Finset.Icc 1 D.R.rS ×ˢ Finset.Icc 1 D.R.rS := by
    intro p hp
    obtain ⟨hpS, h1, h2⟩ := Finset.mem_filter.1 hp
    have r1 : p.1 ∈ relSet Y u := Set.mem_inter (hS p hpS).1 h1
    have r2 : p.2 ∈ relSet Y u := Set.mem_inter (hS p hpS).2.1 h2
    refine Finset.mem_product.2 ⟨Finset.mem_Icc.2 ⟨hJ _ r1, ?_⟩, Finset.mem_Icc.2 ⟨hJ _ r2, ?_⟩⟩ <;>
      exact Nat.sub_le _ _
  rw [← Finset.sum_filter_of_ne hne, ← Finset.sum_fiberwise_of_maps_to hmap]
  calc _ ≤ ∑ l ∈ Finset.Icc 1 D.R.rS ×ˢ Finset.Icc 1 D.R.rS,
        dpiC X u * massC Y u * (k2A1 large₂ C Ch Cc l.1 * k2A1 large₂ C Ch Cc l.2) := by
        refine Finset.sum_le_sum fun l hl => rank_bound hC hCh hCs hK hType hDel hcos l.1
          (Finset.mem_product.1 hl).1 l.2 (Finset.mem_product.1 hl).2 _ fun p hp => ?_
        obtain ⟨hpF, hpl⟩ := Finset.mem_filter.1 hp
        obtain ⟨hpS, h1, h2⟩ := Finset.mem_filter.1 hpF
        exact ⟨⟨Set.mem_inter (hS p hpS).1 h1, Set.mem_inter (hS p hpS).2.1 h2, (hS p hpS).2.2⟩,
          congrArg Prod.fst hpl, congrArg Prod.snd hpl⟩
    _ = dpiC X u * massC Y u * (∑ j ∈ Finset.Icc 1 D.R.rS, k2A1 large₂ C Ch Cc j) ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_product, sq, Finset.sum_mul_sum]

end Asm

end Formalism.L2.SG.KappaOffDiagonal
end
end

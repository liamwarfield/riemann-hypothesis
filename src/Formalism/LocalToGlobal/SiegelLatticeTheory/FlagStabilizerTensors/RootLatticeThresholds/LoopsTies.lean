module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTRph
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepNormOneOfLeaves
public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.HHRed
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaCutoffLimit

@[expose] public section

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.ProdMaxGzInvLe
noncomputable section

open scoped Classical

namespace Formalism.MainNotions.S.Pv.HH

open Finset NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

def Gbd (b C β : ℝ) (Z : GramM D) : ℝ := (2 * β ^ 2 * (b ^ (C * (D.R.m : ℝ) ^ 2)) ^ 2) ^ D.R.f * sizeZ D b C Z ^ 2

theorem embS_star (τ : D.what₂.Tau) (x : D.host.E) : embS D τ (star x) = starRingEnd ℂ (embS D τ x) := by
  unfold embS
  first
  | exact NumberField.IsCMField.complexEmbedding_complexConj _ _
  | exact NumberField.IsCMField.embedding_complexConj _ _
  | exact NumberField.IsCMField.map_complexConj _ _
  | exact (NumberField.IsCMField.complexEmbedding_complexConj (K := D.host.E) (D.host.emb _) x : _)

theorem frameExp_succ : frameExp D.R.rS (D.R.rS + 1) = frameExp D.R.rS D.R.rS := by
  unfold frameExp
  rw [Finset.sum_Icc_succ_top (by omega)]
  simp

def wG : ℝ := D.host.rdE ^ (-(2 * (frameExp D.R.rS D.R.rS : ℝ)))

private theorem one_le_host_rdE : 1 ≤ D.host.rdE := by
  unfold Formalism.BasicNotions.Host.rdE
  apply Real.one_le_rpow _ (by positivity)
  have h := NumberField.discr_ne_zero D.host.E
  have h' : (1 : ℤ) ≤ |discr D.host.E| := Int.one_le_abs h
  have h'' : ((1 : ℤ) : ℝ) ≤ ((|discr D.host.E| : ℤ) : ℝ) := by exact_mod_cast h'
  simpa [Int.cast_abs] using h''

theorem wG_pos : 0 < wG D := by
  unfold wG
  exact Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (one_le_host_rdE D)) _

theorem absGz_eq {u u' : D.what₂.Word} (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : FlagU D u')
    (τ : D.what₂.Tau) :
    |Cnt.Gz D (Tu D u) (Tu D u') (ZhatL (lf D F0) F') τ| = ‖embS D τ (Gval (lf D F0) F')‖ * wG D ^ 2 := by
  have e1 : ∀ x : D.host.E, embS D τ (x * star x) = ((Complex.normSq (embS D τ x) : ℝ) : ℂ) := by
    intro x; rw [map_mul, embS_star, Complex.mul_conj]
  have hG : embS D τ (Gval (lf D F0) F') =
      (((Complex.normSq (embS D τ (leadMinorE (ZhatL (lf D F0) F') (D.R.rS + 1)))) -
        ((Tu D u : ℕ) : ℝ) * ((Tu D u' : ℕ) : ℝ) *
          Complex.normSq (embS D τ (leadMinorE (ZhatL (lf D F0) F') D.R.rS)) : ℝ) : ℂ) := by
    show embS D τ (Gflag (lf D F0).fl F'.fl) = _
    unfold Gflag Dl
    rw [map_sub, e1, map_mul, e1, map_mul, map_natCast, map_natCast]
    push_cast
    ring
  rw [hG, Complex.norm_real, Real.norm_eq_abs]
  unfold Cnt.Gz absDl absReal
  rw [frameExp_succ]
  simp only [Complex.normSq_eq_norm_sq]
  rw [← abs_of_pos (pow_pos (wG_pos D) 2), ← abs_mul]
  congr 1
  unfold wG
  ring

end Formalism.MainNotions.S.Pv.HH

end
end

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.GramFlagFamilyOfDetProduct
noncomputable section

open scoped Classical

namespace Formalism.MainNotions.GramProductBounds

open NumberField Module IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.LatticeGluingRadicals
  Formalism.MainNotions.BridgeLemma₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem NE_pow (D : D7) : NE (E := D.host.E) (gS D) ^ (D.R.rS + 1) = (gS D : ℝ) ^ (D.R.m * D.R.f) := by
  unfold NE
  rw [j_finrank D, ← pow_mul]
  congr 1
  have h2 := D.R.two_le_m
  obtain ⟨k, hk⟩ := D.R.m_even
  have hm : 2 * (D.R.rS + 1) = D.R.m := by
    unfold Ranks.rS
    omega
  rw [← hm]
  ring

end Formalism.MainNotions.GramProductBounds

end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopsEv
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Cnt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LoopTieOf Formalism.L2.SG.LoopsCut Formalism.FourierDecayAlt

namespace Formalism.L2.SG.LoopsEv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section One

variable {D : D7} {large₂ : SizeData₂ D} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}

theorem loopsAmp_at {C' Cl Cg cb Cw cT CT C0 A C K₀ A₀ : ℝ}
    (hH : Cnt.Hyp D large₂ u u' C' Cl Cg cb Cw cT CT C0 A) (hT : ConcTie X Y) (hA : (Y.tO u u').AbsConv)
    (hC : 1 ≤ C) (hCT : CT ≤ C) (hK₀ : K₀ ≤ C') (hA₀1 : 1 ≤ A₀) (hCl4 : 4 ≤ Cl)
    (hClA : 3 + 6 * Real.log (3 * A₀) ≤ Cl)
    (hXiH : Formalism.HermitianLatticeCounting.LatticeSumBounds.XiHyp C D.R.k (2 * D.R.rS + 2) D.R.f large₂.sc.b D.host.v (NT D u)
      (Formalism.MainNotions.BridgeLemma.XiB D large₂ u C))
    (HS : ∀ s, 2 ≤ s → s ≤ D.R.k → ClassLe (Y.tO u u') (bigS (Y.tO u u') s)
      (A₀ * rowS C D.R.k D.R.rS D.R.f s large₂.sc.b (X.B.g : ℝ) D.host.v (GamS D large₂)
        (Formalism.MainNotions.BridgeLemma.XiB D large₂ u C) * ddC X Y u u'))
    (H1 : ClassLe (Y.tO u u') ((Y.tO u u').nsc (Y.tO u u').genSet)
      (A₀ * oneT C D.R.k D.R.rS D.R.f large₂.sc.b (X.B.g : ℝ) (GamS D large₂) * ddC X Y u u')) :
    ∃ (Al NT' Gam : ℝ) (Xi : ℕ → ℝ), 1 ≤ Al ∧
      Formalism.HermitianLatticeCounting.LatticeSumBounds.Params C K₀ D.R.k (2 * D.R.rS + 2) D.R.f large₂.sc.b (X.B.g : ℝ) D.host.v NT' Gam ∧
      Formalism.HermitianLatticeCounting.LatticeSumBounds.XiHyp C D.R.k (2 * D.R.rS + 2) D.R.f large₂.sc.b D.host.v NT' Xi ∧
      6 * Real.log (3 * Al) ≤ (D.R.k : ℝ) * D.R.f * Real.log D.R.k ∧
      Formalism.L2.SG.RowsOther.LoopsAmp (Y.tO u u') Al C D.R.k D.R.rS D.R.f large₂.sc.b (X.B.g : ℝ) D.host.v Gam Xi
        (ddC X Y u u') := by
  have hP := params_at hH.1 X u hCl4 hCT hC hK₀
  obtain ⟨hn1, hn2, hn3⟩ := hyp_nums hH.1
  have hL := Formalism.MainNotions.BridgeLemma.d_one_le_L D large₂
  have hM := unitM_nonneg D large₂
  have hCG := large₂.CGam_pos
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = GamS D large₂ / gamCap D large₂ C := ⟨_, rfl⟩
  have hρe : ρ = Real.exp ((large₂.CGam - min large₂.CGam C) * unitM D large₂) := by rw [hρ, gam_ratio]
  have hmin0 : 0 ≤ min large₂.CGam C := le_min hCG.le (by linarith)
  have hlogρ : Real.log ρ ≤ (D.R.k : ℝ) / 8 := by
    rw [hρe, Real.log_exp]
    have e1 : (large₂.CGam - min large₂.CGam C) * unitM D large₂ ≤ large₂.CGam * unitM D large₂ :=
      mul_le_mul_of_nonneg_right (by linarith) hM
    linarith
  have hρ1 : 1 ≤ ρ := by
    rw [hρe]; exact Real.one_le_exp (mul_nonneg (by linarith [min_le_left large₂.CGam C]) hM)
  have hρ0 : 0 ≤ ρ := by linarith
  have hGr : GamS D large₂ = ρ * gamCap D large₂ C := by
    rw [hρ]; field_simp [(gamCap_pos D large₂ C).ne']
  have hdd := dd_nonneg hT u u'
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hb := Formalism.MainNotions.BridgeLemma.d_two_le_b D large₂
  have hb0 : (0 : ℝ) < large₂.sc.b := by linarith
  have hg : 0 < (X.B.g : ℝ) := by
    have h5 : ((D.R.k : ℝ) * large₂.sc.b) ^ 8 ≤ (X.B.g : ℝ) := hP.2.2.2.2.1
    have h8 : 0 < ((D.R.k : ℝ) * large₂.sc.b) ^ 8 := by positivity
    linarith
  have hv : 0 ≤ D.host.v := by linarith [hP.2.2.2.2.2.2.1]
  have hC0 : (0 : ℝ) ≤ C := by linarith
  have hGc0 : 0 ≤ gamCap D large₂ C := (gamCap_pos D large₂ C).le
  refine ⟨A₀ * ρ ^ 3, NT D u, gamCap D large₂ C, Formalism.MainNotions.BridgeLemma.XiB D large₂ u C,
    one_le_mul_of_one_le_of_one_le hA₀1 (one_le_pow₀ hρ1), hP, hXiH,
    log_size hk1 hL hn3 hn2 hClA hA₀1 hρ1 hlogρ, ?_⟩
  refine loopsAmp_of_classes (Y.tO u u') (A₀ * ρ ^ 3) C D.R.k D.R.rS D.R.f large₂.sc.b (X.B.g : ℝ) D.host.v
    (gamCap D large₂ C) (Formalism.MainNotions.BridgeLemma.XiB D large₂ u C) (ddC X Y u u') hA.2.2.le hA.2.1 (corank_le_k Y u u') ?_ ?_
  · intro s hs2 hsk
    have hB := HS s hs2 hsk
    rw [hGr] at hB
    have hX0 := xi_nonneg hXiH s hs2 hsk
    have hnd : 0 ≤ Formalism.HermitianLatticeCounting.LatticeSumBounds.ndRow C D.R.k (2 * D.R.rS + 2) D.R.f s large₂.sc.b (X.B.g : ℝ) D.host.v
        (gamCap D large₂ C) (Formalism.MainNotions.BridgeLemma.XiB D large₂ u C) := ndRow_nonneg hC0 hb0 hg hv hGc0 hX0
    have hdg : 0 ≤ Formalism.HermitianLatticeCounting.LatticeSumBounds.degRow C D.R.k (2 * D.R.rS + 2) D.R.f s large₂.sc.b (X.B.g : ℝ) D.host.v
        (gamCap D large₂ C) (Formalism.MainNotions.BridgeLemma.XiB D large₂ u C) := degRow_nonneg hC0 hb0 hg hv hGc0 hX0
    have hsc := rowS_scale C D.R.k D.R.rS D.R.f s large₂.sc.b (X.B.g : ℝ) D.host.v (gamCap D large₂ C) ρ
      (Formalism.MainNotions.BridgeLemma.XiB D large₂ u C) hρ1 hnd
    have hrow0 : 0 ≤ rowS C D.R.k D.R.rS D.R.f s large₂.sc.b (X.B.g : ℝ) D.host.v (gamCap D large₂ C)
        (Formalism.MainNotions.BridgeLemma.XiB D large₂ u C) := by
      unfold rowS; exact add_nonneg hnd (mul_nonneg (sq_nonneg _) hdg)
    exact le_trans hB (scale_le hA₀1 le_rfl hdd hsc hrow0 hρ0)
  · have hB := H1
    rw [hGr] at hB
    have h0 : 0 ≤ oneT C D.R.k D.R.rS D.R.f large₂.sc.b (X.B.g : ℝ) (gamCap D large₂ C) := oneT_nonneg hC0 hb0 hGc0
    have hsc := oneT_scale C D.R.k D.R.rS D.R.f large₂.sc.b (X.B.g : ℝ) (gamCap D large₂ C) ρ hρ1 h0
    exact le_trans hB (scale_le hA₀1 le_rfl hdd hsc h0 hρ0)

end One

section Fam

variable {eps : ℝ} (Fm : FamP eps) (C1 : ℝ) (At : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
  (Yt : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    LoopTie (Fm.D x i) (Fm.L x i) (At x hx i) u u' C1)
  (Cc : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ConcAt (Fm.D x i) (At x hx i))

end Fam

end Formalism.L2.SG.LoopsEv
end
end

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf Formalism.L2.SG.LoopsFinal Formalism.L2.SG.NGCut.LeadingMinorIntegrality

namespace Formalism.L2.SG.LoopsTies

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Entry

variable {D : D7}

theorem rhoF_eq (a : Fin (D.R.rS + 1)) : rhoF D a = (D.host.rdE ^ (D.R.rS - (a : ℕ)))⁻¹ := by
  have ha : (a : ℕ) ≤ D.R.rS := Nat.lt_succ_iff.mp a.isLt
  unfold rhoF
  rw [show ((D.R.rS : ℝ) - (a : ℕ)) = ((D.R.rS - (a : ℕ) : ℕ) : ℝ) by push_cast [Nat.cast_sub ha]; ring,
    Real.rpow_neg (rd_pos (D := D)).le, Real.rpow_natCast]

def phiAB (a b : Fin (D.R.rS + 1)) : D.host.E →+ (D.what₂.Tau → ℂ) where
  toFun x τ := ((rhoF D a * rhoF D b : ℝ) : ℂ) * embS D τ x
  map_zero' := by funext τ; simp
  map_add' x y := by funext τ; simp [mul_add]

def latAB (a b : Fin (D.R.rS + 1)) : AddSubgroup (D.what₂.Tau → ℂ) :=
  ((Submodule.toAddSubgroup (dI D ^ ((D.R.rS - (a : ℕ)) + (D.R.rS - (b : ℕ))))).map
    (algebraMap (𝓞 D.host.E) D.host.E).toAddMonoidHom).map (phiAB a b)

theorem one_le_prod_phi (a b : Fin (D.R.rS + 1)) (o : 𝓞 D.host.E)
    (ho : o ∈ dI D ^ ((D.R.rS - (a : ℕ)) + (D.R.rS - (b : ℕ)))) (h0 : (o : D.host.E) ≠ 0) :
    1 ≤ ∏ τ, ‖phiAB a b (o : D.host.E) τ‖ := by
  set n := (D.R.rS - (a : ℕ)) + (D.R.rS - (b : ℕ)) with hn
  have hrd := rd_pos (D := D)
  have hsq := prod_sq_ge n o ho h0
  have h2 : ∏ w : InfinitePlace D.host.E, w (o : D.host.E) ^ 2 = ∏ τ, ‖embS D τ (o : D.host.E)‖ ^ 2 := by
    rw [Formalism.MainNotions.InterlacingSignCuts.prod_places D]
    rfl
  rw [h2] at hsq
  set P := ∏ τ, ‖embS D τ (o : D.host.E)‖ with hP
  have hP0 : 0 ≤ P := Finset.prod_nonneg fun _ _ => norm_nonneg _
  have hsq' : ((D.host.rdE ^ D.R.f) ^ n) ^ 2 ≤ P ^ 2 := by
    have e1 : ((D.host.rdE ^ D.R.f) ^ n) ^ 2 = (D.host.rdE ^ D.R.f) ^ (2 * n) := by rw [← pow_mul, mul_comm]
    have e2 : P ^ 2 = ∏ τ, ‖embS D τ (o : D.host.E)‖ ^ 2 := by rw [hP, Finset.prod_pow]
    rw [e1, e2]; exact hsq
  have hPge : (D.host.rdE ^ D.R.f) ^ n ≤ P := by
    have h := Real.sqrt_le_sqrt hsq'
    rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq hP0] at h
  have hρ : rhoF D a * rhoF D b = (D.host.rdE ^ n)⁻¹ := by
    rw [rhoF_eq, rhoF_eq, ← mul_inv, ← pow_add]
  have hρ0 : 0 ≤ rhoF D a * rhoF D b := by rw [hρ]; positivity
  have e1 : ∀ τ, ‖phiAB a b (o : D.host.E) τ‖ = (rhoF D a * rhoF D b) * ‖embS D τ (o : D.host.E)‖ := by
    intro τ
    show ‖((rhoF D a * rhoF D b : ℝ) : ℂ) * embS D τ (o : D.host.E)‖ = _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ0]
  rw [Finset.prod_congr rfl fun τ _ => e1 τ, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    D.what₂.card_Tau, ← hP, hρ]
  have hpos : 0 < (D.host.rdE ^ n)⁻¹ ^ D.R.f := by positivity
  calc (1 : ℝ) = (D.host.rdE ^ n)⁻¹ ^ D.R.f * (D.host.rdE ^ D.R.f) ^ n := by
        rw [inv_pow, ← pow_mul, ← pow_mul, mul_comm n D.R.f, inv_mul_cancel₀ (by positivity)]
    _ ≤ (D.host.rdE ^ n)⁻¹ ^ D.R.f * P := mul_le_mul_of_nonneg_left hPge hpos.le

theorem zhatL_mem (T : TermTie D) {u u' : D.what₂.Word} (t : D.s.Term u u')
    (hX : XLam (T.abelian₂ t) (T.fl t) = XS D (T.fl t).fl) (hX' : XLam (T.abelian₂ t) (T.fl' t) = XS D (T.fl' t).fl)
    (c d : Fin (D.R.rS + 1)) :
    ∃ o ∈ dI D ^ ((D.R.rS - (c : ℕ)) + (D.R.rS - (d : ℕ))), (o : D.host.E) = ZhatL (T.fl t) (T.fl' t) c d := by
  obtain ⟨o, ho, e⟩ := zhatOM_mem (T.fixed t).2.1 (T.fl t) (T.fl' t) (T.fixed t).2.2.1.1 hX (T.lift' t).1 hX' c d
  refine ⟨(-1) ^ (D.R.rS - (d : ℕ)) * o, Ideal.mul_mem_left _ _ ho, ?_⟩
  have e2 : (((-1) ^ (D.R.rS - (d : ℕ)) * o : 𝓞 D.host.E) : D.host.E) =
      (-1) ^ (D.R.rS - (d : ℕ)) * (o : D.host.E) := by simp
  rw [e2, e]
  simp only [ZhatOM]
  rw [← mul_assoc, ← mul_pow]
  norm_num

theorem zequiv_mem {Z Z₂ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E} (hZ : ZEquiv Z Z₂)
    (hm : ∀ c d : Fin (D.R.rS + 1), ∃ o ∈ dI D ^ ((D.R.rS - (c : ℕ)) + (D.R.rS - (d : ℕ))), (o : D.host.E) = Z c d)
    (a b : Fin (D.R.rS + 1)) :
    ∃ o ∈ dI D ^ ((D.R.rS - (a : ℕ)) + (D.R.rS - (b : ℕ))), (o : D.host.E) = Z₂ a b := by
  obtain ⟨A, B, hA0, -, hB0, -, rfl⟩ := hZ
  choose o ho he using hm
  refine ⟨∑ c, ∑ d, A a c * o c d * B d b, ?_, ?_⟩
  · refine Ideal.sum_mem _ fun c _ => Ideal.sum_mem _ fun d _ => ?_
    by_cases hc : a < c
    · rw [hA0 a c hc]; simp
    by_cases hd : b < d
    · rw [hB0 d b hd]; simp
    push Not at hc hd
    have hc' : (c : ℕ) ≤ a := hc
    have hd' : (d : ℕ) ≤ b := hd
    have ha : (a : ℕ) ≤ D.R.rS := Nat.lt_succ_iff.mp a.isLt
    have hb : (b : ℕ) ≤ D.R.rS := Nat.lt_succ_iff.mp b.isLt
    have hle : dI D ^ ((D.R.rS - (c : ℕ)) + (D.R.rS - (d : ℕ))) ≤ dI D ^ ((D.R.rS - (a : ℕ)) + (D.R.rS - (b : ℕ))) :=
      Ideal.pow_le_pow_right (by omega)
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (hle (ho c d)))
  · simp only [Matrix.mul_apply, Matrix.map_apply, Finset.sum_mul]
    push_cast
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    exact congrArg (fun x => ((A a d : 𝓞 D.host.E) : D.host.E) * x * ((B c b : 𝓞 D.host.E) : D.host.E)) (he d c)

theorem entryLat_of (T : TermTie D) {u u' : D.what₂.Word}
    (hX : ∀ t : D.s.Term u u', XLam (T.abelian₂ t) (T.fl t) = XS D (T.fl t).fl ∧
      XLam (T.abelian₂ t) (T.fl' t) = XS D (T.fl' t).fl) :
    BridgeLemma₂.wordPairEntriesInLattice T u u' := by
  intro a b
  refine ⟨latAB a b, ?_, ?_⟩
  · intro x hx hx0
    obtain ⟨y, hy, rfl⟩ := AddSubgroup.mem_map.1 hx
    obtain ⟨o, ho, rfl⟩ := AddSubgroup.mem_map.1 hy
    have h0 : ((o : 𝓞 D.host.E) : D.host.E) ≠ 0 := by
      intro h
      apply hx0
      show phiAB a b ((algebraMap (𝓞 D.host.E) D.host.E) o) = 0
      rw [show (algebraMap (𝓞 D.host.E) D.host.E) o = ((o : 𝓞 D.host.E) : D.host.E) from rfl, h, map_zero]
    exact one_le_prod_phi a b o ho h0
  · intro t Z _ _ hZ
    obtain ⟨o, ho, e⟩ := zequiv_mem hZ (fun c d => zhatL_mem T t (hX t).1 (hX t).2 c d) a b
    refine AddSubgroup.mem_map.2 ⟨(o : D.host.E), AddSubgroup.mem_map.2 ⟨o, ho, rfl⟩, ?_⟩
    funext τ
    show ((rhoF D a * rhoF D b : ℝ) : ℂ) * embS D τ (o : D.host.E) = _
    rw [e]

end Entry

section Conc

theorem entryLatC_holds : EntryLatC := by
  intro D X Y hF hI W H A hV u u'
  refine entryLat_of _ fun t => ⟨?_, (pdC W hI t).2.2.2⟩
  exact ((Formalism.L2.SG.Pf.WittFlags.RowRepsIso_holds D (W.δ u) (W.isom u) (X.Fu u) (Y.what₂ u) (Y.rowsOK u)).1 _
    (lamOf_mem W hI t)).2.2

end Conc

section Norm

variable {D : D7}

theorem rpow_negNat {x : ℝ} (hx : 0 < x) (k : ℕ) : x ^ (-(k : ℝ)) = (x ^ k)⁻¹ := by
  rw [Real.rpow_neg hx.le, Real.rpow_natCast]

theorem two_frameExp (l : ℕ) (hl : l ≤ D.R.rS + 1) : 2 * frameExp D.R.rS l = l * (2 * D.R.rS + 1 - l) := by
  have h := Formalism.MainNotions.BridgeLemma.d_frameExp_cast D.R.rS l hl
  have h2 := two_sum_sub D.R.rS l hl
  have h3 : (frameExp D.R.rS l : ℝ) = ((∑ i : Fin l, (D.R.rS - (i : ℕ)) : ℕ) : ℝ) := by
    rw [h]; push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    have : (i : ℕ) ≤ D.R.rS := by have := i.isLt; omega
    rw [Nat.cast_sub this]
  have h4 : frameExp D.R.rS l = ∑ i : Fin l, (D.R.rS - (i : ℕ)) := by exact_mod_cast h3
  rw [h4, h2]

theorem leadMinor_mem (T : TermTie D) {u u' : D.what₂.Word} (t : D.s.Term u u')
    (hX : XLam (T.abelian₂ t) (T.fl t) = XS D (T.fl t).fl) (hX' : XLam (T.abelian₂ t) (T.fl' t) = XS D (T.fl' t).fl)
    (q : ℕ) (hq : q ≤ D.R.rS + 1) :
    ∃ o ∈ dI D ^ (q * (2 * D.R.rS + 1 - q)), (o : D.host.E) = leadMinorE (ZhatL (T.fl t) (T.fl' t)) q := by
  obtain ⟨o, ho, e⟩ := lead_mem (T.fixed t).2.1 (T.fl t) (T.fl' t) (T.fixed t).2.2.1.1 hX (T.lift' t).1 hX' q hq
  rw [lead_ZhatOM _ q hq] at e
  refine ⟨(∏ b : Fin q, (-1 : 𝓞 D.host.E) ^ (D.R.rS - (b : ℕ))) * o, Ideal.mul_mem_left _ _ ho, ?_⟩
  have hs : (∏ b : Fin q, (-1 : D.host.E) ^ (D.R.rS - (b : ℕ))) * (∏ b : Fin q, (-1 : D.host.E) ^ (D.R.rS - (b : ℕ))) = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun b _ => ?_
    rw [← mul_pow]; norm_num
  have e2 : (((∏ b : Fin q, (-1 : 𝓞 D.host.E) ^ (D.R.rS - (b : ℕ))) * o : 𝓞 D.host.E) : D.host.E) =
      (∏ b : Fin q, (-1 : D.host.E) ^ (D.R.rS - (b : ℕ))) * (o : D.host.E) := by simp
  rw [e2, e, ← mul_assoc, hs, one_mul]

theorem gval_mem (T : TermTie D) {u u' : D.what₂.Word} (t : D.s.Term u u')
    (hX : XLam (T.abelian₂ t) (T.fl t) = XS D (T.fl t).fl) (hX' : XLam (T.abelian₂ t) (T.fl' t) = XS D (T.fl' t).fl) :
    ∃ o ∈ dI D ^ (2 * (D.R.rS * (D.R.rS + 1))), (o : D.host.E) = Gval (T.fl t) (T.fl' t) := by
  set N := D.R.rS * (D.R.rS + 1) with hN
  obtain ⟨o1, ho1, e1⟩ := leadMinor_mem T t hX hX' (D.R.rS + 1) le_rfl
  obtain ⟨o2, ho2, e2⟩ := leadMinor_mem T t hX hX' D.R.rS (Nat.le_succ _)
  have x1 : (D.R.rS + 1) * (2 * D.R.rS + 1 - (D.R.rS + 1)) = N := by
    rw [hN, show 2 * D.R.rS + 1 - (D.R.rS + 1) = D.R.rS by omega, mul_comm]
  have x2 : D.R.rS * (2 * D.R.rS + 1 - D.R.rS) = N := by
    rw [hN, show 2 * D.R.rS + 1 - D.R.rS = D.R.rS + 1 by omega]
  rw [x1] at ho1
  rw [x2] at ho2
  obtain ⟨s1, hs1, es1⟩ := star_mem_pow N o1 ho1
  obtain ⟨s2, hs2, es2⟩ := star_mem_pow N o2 ho2
  refine ⟨o1 * s1 - ((Tu D u : ℕ) * (Tu D u' : ℕ) : 𝓞 D.host.E) * (o2 * s2), ?_, ?_⟩
  · rw [two_mul, pow_add]
    exact Ideal.sub_mem _ (Ideal.mul_mem_mul ho1 hs1) (Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul ho2 hs2))
  · have c1 : ((o1 * s1 - ((Tu D u : ℕ) * (Tu D u' : ℕ) : 𝓞 D.host.E) * (o2 * s2) : 𝓞 D.host.E) : D.host.E) =
        (o1 : D.host.E) * (s1 : D.host.E) - ((Tu D u : ℕ) : D.host.E) * ((Tu D u' : ℕ) : D.host.E) *
          ((o2 : D.host.E) * (s2 : D.host.E)) := by push_cast; ring
    rw [c1, es1, es2, e1, e2]
    rfl

def GzNonnegC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (Formalism.L2.SG.PackageTie2.sOf hF)) (W : WittDat X) (H : TieHyp W hI)
    (A : AmpDat X) (hV : PvalForm W hI A) (u u' : D.what₂.Word) (t : D.s.Term u u'), D.s.Gterm t ≠ 0 →
    D.s.relevant t → ∀ τ, 0 ≤ Formalism.MainNotions.S.Cnt.Gz D (Tu D u) (Tu D u')
      (BridgeLemma₂.termGramMatrix (termTieOf W hI H A hV) t) τ

theorem normTie_of (T : TermTie D) {u u' : D.what₂.Word}
    (hX : ∀ t : D.s.Term u u', XLam (T.abelian₂ t) (T.fl t) = XS D (T.fl t).fl ∧
      XLam (T.abelian₂ t) (T.fl' t) = XS D (T.fl' t).fl)
    (hPos : ∀ t : D.s.Term u u', D.s.Gterm t ≠ 0 → D.s.relevant t →
      ∀ τ, 0 ≤ Formalism.MainNotions.S.Cnt.Gz D (Tu D u) (Tu D u') (BridgeLemma₂.termGramMatrix T t) τ) :
    BridgeLemma₂.wordPairNormRelation T u u' := by
  have hrd := rd_pos (D := D)
  intro t hG hrel
  refine ⟨?_, ?_⟩
  ·
    set N := D.R.rS * (D.R.rS + 1) with hN
    obtain ⟨o, ho, eo⟩ := gval_mem T t (hX t).1 (hX t).2
    have hG0 : (o : D.host.E) ≠ 0 := by
      rw [eo]; intro h; apply hG
      have := T.G_eq t
      rw [h] at this
      exact (algebraMap D.host.F D.host.E).injective (by rw [this, map_zero])
    have hsq := prod_sq_ge (2 * N) o ho hG0
    have h2 : ∏ w : InfinitePlace D.host.E, w (o : D.host.E) ^ 2 = ∏ τ, ‖embS D τ (o : D.host.E)‖ ^ 2 := by
      rw [Formalism.MainNotions.InterlacingSignCuts.prod_places D]
      rfl
    rw [h2] at hsq
    set P := ∏ τ, ‖embS D τ (o : D.host.E)‖ with hP
    have hP0 : 0 ≤ P := Finset.prod_nonneg fun _ _ => norm_nonneg _
    have hPge : (D.host.rdE ^ D.R.f) ^ (2 * N) ≤ P := by
      have e1 : ((D.host.rdE ^ D.R.f) ^ (2 * N)) ^ 2 = (D.host.rdE ^ D.R.f) ^ (2 * (2 * N)) := by
        rw [← pow_mul, mul_comm]
      have e2 : P ^ 2 = ∏ τ, ‖embS D τ (o : D.host.E)‖ ^ 2 := by rw [hP, Finset.prod_pow]
      have h := Real.sqrt_le_sqrt (show ((D.host.rdE ^ D.R.f) ^ (2 * N)) ^ 2 ≤ P ^ 2 by rw [e1, e2]; exact hsq)
      rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq hP0] at h
    have hW : Formalism.MainNotions.S.Pv.HH.wG D ^ 2 = (D.host.rdE ^ (2 * N))⁻¹ := by
      unfold Formalism.MainNotions.S.Pv.HH.wG
      have e : (2 * (frameExp D.R.rS D.R.rS : ℝ)) = ((2 * frameExp D.R.rS D.R.rS : ℕ) : ℝ) := by push_cast; ring
      rw [e, rpow_negNat hrd, two_frameExp D.R.rS (Nat.le_succ _),
        show 2 * D.R.rS + 1 - D.R.rS = D.R.rS + 1 by omega, ← hN, inv_pow, ← pow_mul, mul_comm N 2]
    have habs : ∀ τ, Formalism.MainNotions.S.Cnt.Gz D (Tu D u) (Tu D u') (BridgeLemma₂.termGramMatrix T t) τ =
        ‖embS D τ (o : D.host.E)‖ * Formalism.MainNotions.S.Pv.HH.wG D ^ 2 := by
      intro τ
      have h := Formalism.MainNotions.S.Pv.HH.absGz_eq D (T.fl t).fl (T.fl' t) τ
      rw [abs_of_nonneg (hPos t hG hrel τ)] at h
      rw [eo]
      exact h
    rw [Finset.prod_congr rfl fun τ _ => habs τ, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      D.what₂.card_Tau, ← hP, hW]
    calc (1 : ℝ) = (D.host.rdE ^ D.R.f) ^ (2 * N) * ((D.host.rdE ^ (2 * N))⁻¹) ^ D.R.f := by
          rw [inv_pow, ← pow_mul, ← pow_mul, mul_comm D.R.f (2 * N), mul_inv_cancel₀ (by positivity)]
      _ ≤ P * ((D.host.rdE ^ (2 * N))⁻¹) ^ D.R.f := mul_le_mul_of_nonneg_right hPge (by positivity)
  ·
    intro l hl hD
    obtain ⟨o, ho, eo⟩ := leadMinor_mem T t (hX t).1 (hX t).2 l hl
    have hD0 : (o : D.host.E) ≠ 0 := by rw [eo]; exact hD
    have hsq := prod_sq_ge (l * (2 * D.R.rS + 1 - l)) o ho hD0
    have h2 : ∏ w : InfinitePlace D.host.E, w (o : D.host.E) ^ 2 = ∏ τ, ‖embS D τ (o : D.host.E)‖ ^ 2 := by
      rw [Formalism.MainNotions.InterlacingSignCuts.prod_places D]
      rfl
    rw [h2] at hsq
    have hw : D.host.rdE ^ (-(2 * (frameExp D.R.rS l : ℝ))) = (D.host.rdE ^ (l * (2 * D.R.rS + 1 - l)))⁻¹ := by
      have e : (2 * (frameExp D.R.rS l : ℝ)) = ((2 * frameExp D.R.rS l : ℕ) : ℝ) := by push_cast; ring
      rw [e, rpow_negNat hrd, two_frameExp l hl]
    have habs : ∀ τ, Formalism.MainNotions.S.Cnt.absDl D (BridgeLemma₂.termGramMatrix T t) l τ ^ 2 =
        ‖embS D τ (o : D.host.E)‖ ^ 2 * ((D.host.rdE ^ (l * (2 * D.R.rS + 1 - l)))⁻¹) ^ 2 := by
      intro τ
      unfold Formalism.MainNotions.S.Cnt.absDl absReal
      rw [hw, ← eo, mul_pow]
    rw [Finset.prod_congr rfl fun τ _ => habs τ, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      D.what₂.card_Tau]
    set m := l * (2 * D.R.rS + 1 - l)
    calc (1 : ℝ) = (D.host.rdE ^ D.R.f) ^ (2 * m) * (((D.host.rdE ^ m)⁻¹) ^ 2) ^ D.R.f := by
          rw [inv_pow, inv_pow, ← pow_mul, ← pow_mul, ← pow_mul, show D.R.f * (2 * m) = m * (2 * D.R.f) by ring,
            mul_inv_cancel₀ (by positivity)]
      _ ≤ (∏ τ, ‖embS D τ (o : D.host.E)‖ ^ 2) * (((D.host.rdE ^ m)⁻¹) ^ 2) ^ D.R.f :=
          mul_le_mul_of_nonneg_right hsq (by positivity)

theorem normTieC_of (hPos : GzNonnegC) : NormTieC := by
  intro D X Y hF hI W H A hV u u'
  refine normTie_of _ (fun t => ⟨?_, (pdC W hI t).2.2.2⟩) (hPos D X Y hF hI W H A hV u u')
  exact ((Formalism.L2.SG.Pf.WittFlags.RowRepsIso_holds D (W.δ u) (W.isom u) (X.Fu u) (Y.what₂ u) (Y.rowsOK u)).1 _
    (lamOf_mem W hI t)).2.2

end Norm

section Pos

variable {D : D7}

theorem gz_eq (T : TermTie D) {u u' : D.what₂.Word} (t : D.s.Term u u') (τ : D.what₂.Tau) :
    Formalism.MainNotions.S.Cnt.Gz D (Tu D u) (Tu D u') (BridgeLemma₂.termGramMatrix T t) τ =
      (embS D τ (Gval (T.fl t) (T.fl' t))).re * Formalism.MainNotions.S.Pv.HH.wG D ^ 2 := by
  have e1 : ∀ x : D.host.E, embS D τ (x * star x) = ((Complex.normSq (embS D τ x) : ℝ) : ℂ) := by
    intro x; rw [map_mul, Formalism.MainNotions.S.Pv.HH.embS_star, Complex.mul_conj]
  have hG : embS D τ (Gval (T.fl t) (T.fl' t)) =
      (((Complex.normSq (embS D τ (leadMinorE (ZhatL (T.fl t) (T.fl' t)) (D.R.rS + 1)))) -
        ((Tu D u : ℕ) : ℝ) * ((Tu D u' : ℕ) : ℝ) *
          Complex.normSq (embS D τ (leadMinorE (ZhatL (T.fl t) (T.fl' t)) D.R.rS)) : ℝ) : ℂ) := by
    show embS D τ (Gflag (T.fl t).fl (T.fl' t).fl) = _
    unfold Gflag Dl
    rw [map_sub, e1, map_mul, e1, map_mul, map_natCast, map_natCast]
    push_cast
    ring
  rw [hG, Complex.ofReal_re]
  unfold Formalism.MainNotions.S.Cnt.Gz Formalism.MainNotions.S.Cnt.absDl absReal
  rw [Formalism.MainNotions.S.Pv.HH.frameExp_succ]
  simp only [Complex.normSq_eq_norm_sq]
  unfold Formalism.MainNotions.S.Pv.HH.wG
  ring

theorem gz_nonneg (T : TermTie D) {u u' : D.what₂.Word} (t : D.s.Term u u') (hG : D.s.Gterm t ≠ 0) (τ : D.what₂.Tau) :
    0 ≤ Formalism.MainNotions.S.Cnt.Gz D (Tu D u) (Tu D u') (BridgeLemma₂.termGramMatrix T t) τ := by
  rw [gz_eq T t τ]
  exact mul_nonneg (Formalism.MainNotions.BridgeLemma.tie_G_pos T t hG (embS D τ)).le (sq_nonneg _)

theorem gzNonnegC_holds : GzNonnegC :=
  fun _ _ _ _ _ _ _ _ _ _ _ t hG _ τ => gz_nonneg _ t hG τ

theorem normTieC_holds : NormTieC := normTieC_of gzNonnegC_holds

end Pos

section G0

variable {D : D7}

theorem gram_determinant_term_of_det (T : TermTie D) {u u' : D.what₂.Word}
    (h : ∀ t : D.s.Term u u', D.s.Gterm t ≠ 0 →
      NG (T.abelian₂ t) (T.fl t) (T.fl' t) = ∏ τ, Formalism.MainNotions.S.Cnt.Gz D (Tu D u) (Tu D u') (BridgeLemma₂.termGramMatrix T t) τ) :
    @Formalism.MainNotions.BridgeLemma.LatticeDeterminantFactorization D T u u' := by
  intro t hG
  unfold G0
  rw [h t hG, Formalism.MainNotions.GramProductBounds.NE_pow D, div_eq_mul_inv, inv_pow]

def DetUUC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (Formalism.L2.SG.PackageTie2.sOf hF)) (W : WittDat X) (H : TieHyp W hI)
    (A : AmpDat X) (hV : PvalForm W hI A) (u u' : D.what₂.Word) (t : D.s.Term u u'), D.s.Gterm t ≠ 0 →
    NG ((termTieOf W hI H A hV).abelian₂ t) ((termTieOf W hI H A hV).fl t) ((termTieOf W hI H A hV).fl' t) =
      ∏ τ, Formalism.MainNotions.S.Cnt.Gz D (Tu D u) (Tu D u') (BridgeLemma₂.termGramMatrix (termTieOf W hI H A hV) t) τ

theorem gramDeterminant_of_unipotent_det (h : DetUUC) : GramDeterminantCount :=
  fun D X Y hF hI W H A hV u u' => gram_determinant_term_of_det _ (h D X Y hF hI W H A hV u u')

end G0

section Cor

open Formalism.L2.SG.LoopsEv

variable {eps : ℝ} (Fm : FamP eps) (C1 : ℝ)
  (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, HidaSetting (Fm.D x i))
  (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Full (X x hx i))
  (hF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), FinX (Y x hx i))
  (hI : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), SIso (Fm.D x i).s (Formalism.L2.SG.PackageTie2.sOf (hF x hx i)))
  (W : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), WittDat (X x hx i))
  (H : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), TieHyp (W x hx i) (hI x hx i))
  (A : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), AmpDat (X x hx i))
  (hV : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), PvalForm (W x hx i) (hI x hx i) (A x hx i))

end Cor

end Formalism.L2.SG.LoopsTies

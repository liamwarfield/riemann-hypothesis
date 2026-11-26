module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyPacketOfEquivalentStatement
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.FamilyGenusBoundOfSiegelRatio

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LoopsCut
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Cnt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc
  Formalism.FourierDecayAlt

namespace Formalism.L2.SG.LoopsCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁)

def bigS (s : ℕ) : Set (τ × τ) := {p | p ∈ X.allPairs X.nzSet ∧ X.s0 p.1 p.2 = s}

def rowS (C : ℝ) (k r f s : ℕ) (b g v Gam : ℝ) (Xi : ℕ → ℝ) : ℝ :=
  Formalism.HermitianLatticeCounting.LatticeSumBounds.ndRow C k (2 * r + 2) f s b g v Gam Xi +
    Gam ^ 2 * Formalism.HermitianLatticeCounting.LatticeSumBounds.degRow C k (2 * r + 2) f s b g v Gam Xi

def oneT (C : ℝ) (k r f : ℕ) (b g Gam : ℝ) : ℝ :=
  C ^ f * Formalism.HermitianLatticeCounting.LatticeSumBounds.bigH C (2 * r + 2) f b ^ (C * ((2 * r + 2 : ℕ) : ℝ) ^ 3) * Gam *
    Real.exp (C * ((2 * r + 2 : ℕ) : ℝ) ^ 6 * f * Real.log b) *
    Real.sqrt ((C * g⁻¹ ^ (2 * r + 1) * ((k : ℝ) ^ r)⁻¹) ^ (k * f))

def ClassLe (Q : Set (τ × τ)) (B : ℝ) : Prop := X.Gam1 * RowsOther.ampSum X Q ≤ B

theorem ind_le_cover {f : τ × τ → ℝ} (hf : ∀ p, 0 ≤ f p) (S : Finset ℕ) (P : ℕ → Set (τ × τ))
    (P' Q : Set (τ × τ)) (hQ : Q ⊆ (⋃ s ∈ S, P s) ∪ P') (p : τ × τ) :
    Q.indicator f p ≤ ∑ s ∈ S, (P s).indicator f p + P'.indicator f p := by
  have hnn : ∀ (R : Set (τ × τ)), 0 ≤ R.indicator f p := fun R => Set.indicator_nonneg (fun q _ => hf q) p
  have hsum : 0 ≤ ∑ s ∈ S, (P s).indicator f p := Finset.sum_nonneg (fun i _ => hnn (P i))
  by_cases hp : p ∈ Q
  · rw [Set.indicator_of_mem hp]
    rcases (Set.mem_union _ _ _).1 (hQ hp) with h | h
    · obtain ⟨s, hsS, hps⟩ := Set.mem_iUnion₂.1 h
      have h1 : (P s).indicator f p = f p := Set.indicator_of_mem hps f
      have h2 : (P s).indicator f p ≤ ∑ s ∈ S, (P s).indicator f p :=
        Finset.single_le_sum (f := fun s => (P s).indicator f p) (fun i _ => hnn (P i)) hsS
      have h3 := hnn P'
      linarith
    · have h1 : P'.indicator f p = f p := Set.indicator_of_mem h f
      linarith
  · rw [Set.indicator_apply, if_neg hp]
    exact add_nonneg hsum (hnn P')

theorem amp_summable (hv : Summable (fun t => ‖X.vec t‖)) (Q : Set (τ × τ)) :
    Summable (Q.indicator (fun p : τ × τ => ‖X.vec p.1‖ * ‖X.vec p.2‖)) := by
  exact (Summable.mul_of_nonneg hv hv (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).indicator Q

theorem ampSum_cover (hv : Summable (fun t => ‖X.vec t‖)) (S : Finset ℕ) (P : ℕ → Set (τ × τ))
    (P' Q : Set (τ × τ)) (hQ : Q ⊆ (⋃ s ∈ S, P s) ∪ P') :
    RowsOther.ampSum X Q ≤ ∑ s ∈ S, RowsOther.ampSum X (P s) + RowsOther.ampSum X P' := by
  have hs : ∀ R : Set (τ × τ), Summable (R.indicator (fun p : τ × τ => ‖X.vec p.1‖ * ‖X.vec p.2‖)) :=
    fun R => amp_summable X hv R
  have hsum : Summable (fun p => ∑ s ∈ S, (P s).indicator (fun p : τ × τ => ‖X.vec p.1‖ * ‖X.vec p.2‖) p +
      P'.indicator (fun p : τ × τ => ‖X.vec p.1‖ * ‖X.vec p.2‖) p) :=
    (summable_sum fun s _ => hs (P s)).add (hs P')
  have hle := Summable.tsum_le_tsum
    (fun p => ind_le_cover (fun p => mul_nonneg (norm_nonneg (X.vec p.1)) (norm_nonneg (X.vec p.2))) S P P' Q hQ p)
    (hs Q) hsum
  unfold RowsOther.ampSum
  rw [Summable.tsum_add (summable_sum fun s _ => hs (P s)) (hs P'),
    Summable.tsum_finsetSum (fun s _ => hs (P s))] at hle
  exact hle

theorem pp_cover (k : ℕ) (hk : ∀ t t', X.s0 t t' ≤ k) :
    RowsOther.PP X ⊆ (⋃ s ∈ Finset.Icc 2 k, bigS X s) ∪ X.nsc X.genSet := by
  intro p hp
  unfold RowsOther.PP at hp
  rcases (Set.mem_union _ _ _).1 hp with h | h
  · have h' : p ∈ X.allPairs X.nzSet ∧ 2 ≤ X.s0 p.1 p.2 := h
    left
    refine Set.mem_iUnion₂.2 ⟨X.s0 p.1 p.2, Finset.mem_Icc.2 ⟨h'.2, hk p.1 p.2⟩, ?_⟩
    show p ∈ X.allPairs X.nzSet ∧ X.s0 p.1 p.2 = X.s0 p.1 p.2
    exact ⟨h'.1, rfl⟩
  · right
    exact h

theorem loopsAmp_of_classes (A C : ℝ) (k r f : ℕ) (b g v Gam : ℝ) (Xi : ℕ → ℝ) (dd : ℝ)
    (hG : 0 ≤ X.Gam1) (hv : Summable (fun t => ‖X.vec t‖)) (hk : ∀ t t', X.s0 t t' ≤ k)
    (hS : ∀ s, 2 ≤ s → s ≤ k → ClassLe X (bigS X s) (A * rowS C k r f s b g v Gam Xi * dd))
    (h1 : ClassLe X (X.nsc X.genSet) (A * oneT C k r f b g Gam * dd)) :
    RowsOther.LoopsAmp X A C k r f b g v Gam Xi dd := by
  refine ⟨amp_summable X hv _, ?_⟩
  have hc := ampSum_cover X hv (Finset.Icc 2 k) (bigS X) (X.nsc X.genSet) (RowsOther.PP X) (pp_cover X k hk)
  have hsum : ∑ s ∈ Finset.Icc 2 k, X.Gam1 * RowsOther.ampSum X (bigS X s) ≤
      ∑ s ∈ Finset.Icc 2 k, A * rowS C k r f s b g v Gam Xi * dd :=
    Finset.sum_le_sum fun s hs => hS s (Finset.mem_Icc.1 hs).1 (Finset.mem_Icc.1 hs).2
  have e : ∑ s ∈ Finset.Icc 2 k, A * rowS C k r f s b g v Gam Xi * dd =
      A * (∑ s ∈ Finset.Icc 2 k, Formalism.HermitianLatticeCounting.LatticeSumBounds.ndRow C k (2 * r + 2) f s b g v Gam Xi +
        Gam ^ 2 * ∑ s ∈ Finset.Icc 2 k, Formalism.HermitianLatticeCounting.LatticeSumBounds.degRow C k (2 * r + 2) f s b g v Gam Xi) * dd := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    unfold rowS; ring
  calc X.Gam1 * RowsOther.ampSum X (RowsOther.PP X)
      ≤ X.Gam1 * (∑ s ∈ Finset.Icc 2 k, RowsOther.ampSum X (bigS X s) + RowsOther.ampSum X (X.nsc X.genSet)) :=
        mul_le_mul_of_nonneg_left hc hG
    _ = ∑ s ∈ Finset.Icc 2 k, X.Gam1 * RowsOther.ampSum X (bigS X s) +
          X.Gam1 * RowsOther.ampSum X (X.nsc X.genSet) := by rw [mul_add, Finset.mul_sum]
    _ ≤ ∑ s ∈ Finset.Icc 2 k, A * rowS C k r f s b g v Gam Xi * dd + A * oneT C k r f b g Gam * dd :=
        add_le_add hsum h1
    _ = _ := by rw [e]; unfold oneT; ring

end Gen

section Sizes

variable (D : D7) (large₂ : SizeData₂ D)

def unitM : ℝ := (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L

def gamCap (C : ℝ) : ℝ := Real.exp (min large₂.CGam C * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L)

theorem unitM_nonneg : 0 ≤ unitM D large₂ := by
  unfold unitM
  have hL : 0 ≤ large₂.sc.L := by
    unfold Formalism.BasicNotions.Scale.L
    exact Real.rpow_nonneg (by linarith [large₂.sc.one_lt_alt]) _
  exact mul_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _)) hL

theorem gamCap_pos (C : ℝ) : 0 < gamCap D large₂ C := Real.exp_pos _

theorem gam_ratio (C : ℝ) :
    GamS D large₂ / gamCap D large₂ C = Real.exp ((large₂.CGam - min large₂.CGam C) * unitM D large₂) := by
  unfold Formalism.MainNotions.S.GamS gamCap unitM
  rw [← Real.exp_sub]
  congr 1
  ring

end Sizes

theorem params_at {D : D7} {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT C0 C K₀ : ℝ}
    (h : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (X : HidaSetting D) (u : D.what₂.Word) (hCl : 4 ≤ Cl) (hCT : CT ≤ C)
    (hC : 1 ≤ C) (hK : K₀ ≤ C') :
    Formalism.HermitianLatticeCounting.LatticeSumBounds.Params C K₀ D.R.k (2 * D.R.rS + 2) D.R.f large₂.sc.b (X.B.g : ℝ) D.host.v (NT D u) (gamCap D large₂ C) := by
  obtain ⟨_, h2, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h23, h24, _⟩ := h.1
  have h2' : C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L ≤ D.R.k := h2
  have h23' : Formalism.MainNotions.S.Tr D u ≤ large₂.sc.b ^ (CT * (D.R.m : ℝ)) := (h23 u).2
  have h24' : Cl ≤ (D.R.m : ℝ) := h24
  have hm : 4 ≤ D.R.m := by
    have : (4 : ℝ) ≤ D.R.m := by linarith
    exact_mod_cast this
  have hL := Formalism.MainNotions.BridgeLemma.d_one_le_L D large₂
  have hM : 0 ≤ (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by positivity
  have hK' : K₀ * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L ≤ D.R.k := by
    have := mul_le_mul_of_nonneg_right hK hM
    nlinarith
  have P := Formalism.MainNotions.BridgeLemma.parameters_of_hypotheses D large₂ h u hm (by linarith) (le_max_of_le_left hCT : CT ≤ max C large₂.CGam)
    (le_max_right _ _) hK'
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, _, _, _⟩ := P
  have hg : (X.B.g : ℝ) = gg D := by rw [X.g_eq]; unfold gg; push_cast; ring
  have hb := Formalism.MainNotions.BridgeLemma.d_two_le_b D large₂
  have hb1 : (1 : ℝ) ≤ large₂.sc.b := by linarith
  rw [← Formalism.MainNotions.BridgeLemma.d_m_eq D, hg]
  refine ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, ?_, ?_, ?_⟩
  · unfold NT
    have h1 : ((D.mem u).A.T : ℝ) ≤ large₂.sc.b ^ (C * (D.R.m : ℝ)) :=
      h23'.trans (Real.rpow_le_rpow_of_exponent_le hb1 (by gcongr))
    calc ((D.mem u).A.T : ℝ) ^ D.R.f ≤ (large₂.sc.b ^ (C * (D.R.m : ℝ))) ^ D.R.f := by
          have : (0 : ℝ) ≤ ((D.mem u).A.T : ℝ) := Nat.cast_nonneg _
          gcongr
      _ = large₂.sc.b ^ (C * (D.R.m : ℝ) * D.R.f) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
  · unfold gamCap
    have := large₂.CGam_pos
    have h0 : 0 ≤ min large₂.CGam C := le_min this.le (by linarith)
    exact Real.one_le_exp (by positivity)
  · unfold gamCap
    rw [Formalism.MainNotions.BridgeLemma.d_log_b]
    exact Real.exp_le_exp.2 (by
      have := min_le_right large₂.CGam C
      have h5 : 0 ≤ (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := hM
      nlinarith)

theorem xi_nonneg {C : ℝ} {k m f : ℕ} {b v NT : ℝ} {Xi : ℕ → ℝ} (h : Formalism.HermitianLatticeCounting.LatticeSumBounds.XiHyp C k m f b v NT Xi)
    (s : ℕ) (h2 : 2 ≤ s) (hk : s ≤ k) : 0 ≤ Xi s := by
  obtain ⟨hA, hB⟩ := h
  by_cases hs : s + 2 ≤ k
  · exact (hA s h2 hs).1
  · exact (hB s (by omega)).1

theorem ndRow_nonneg {C : ℝ} {k m f s : ℕ} {b g v Gam : ℝ} {Xi : ℕ → ℝ} (hC : 0 ≤ C) (hb : 0 < b) (hg : 0 < g)
    (hv : 0 ≤ v) (hG : 0 ≤ Gam) (hX : 0 ≤ Xi s) : 0 ≤ Formalism.HermitianLatticeCounting.LatticeSumBounds.ndRow C k m f s b g v Gam Xi := by
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.ndRow
  have hH : 0 ≤ Formalism.HermitianLatticeCounting.LatticeSumBounds.bigH C m f b := by
    unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.bigH
    exact Real.rpow_nonneg hb.le _
  refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) hX) ?_)
    (Real.rpow_nonneg hH _)) ?_) hG
  · exact pow_nonneg (div_nonneg (by norm_num) hg.le) _
  · exact pow_nonneg (mul_nonneg (Nat.cast_nonneg _) hv) _
  · exact pow_nonneg hC _
  · exact pow_nonneg (mul_nonneg (mul_nonneg hC (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) _

theorem degRow_nonneg {C : ℝ} {k m f s : ℕ} {b g v Gam : ℝ} {Xi : ℕ → ℝ} (hC : 0 ≤ C) (hb : 0 < b) (hg : 0 < g)
    (hv : 0 ≤ v) (hG : 0 ≤ Gam) (hX : 0 ≤ Xi s) : 0 ≤ Formalism.HermitianLatticeCounting.LatticeSumBounds.degRow C k m f s b g v Gam Xi := by
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.degRow
  have hH : 0 ≤ Formalism.HermitianLatticeCounting.LatticeSumBounds.bigH C m f b := by
    unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.bigH
    exact Real.rpow_nonneg hb.le _
  refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) hX) ?_)
    (Real.rpow_nonneg hH _)) ?_) hG) (Real.exp_pos _).le) ?_
  · exact pow_nonneg (div_nonneg (by norm_num) hg.le) _
  · exact pow_nonneg (mul_nonneg (Nat.cast_nonneg _) hv) _
  · exact pow_nonneg hC _
  · exact pow_nonneg (mul_nonneg (mul_nonneg hC (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) _
  · exact pow_nonneg (div_nonneg hC (Nat.cast_nonneg _)) _

theorem oneT_nonneg {C : ℝ} {k r f : ℕ} {b g Gam : ℝ} (hC : 0 ≤ C) (hb : 0 < b) (hG : 0 ≤ Gam) :
    0 ≤ oneT C k r f b g Gam := by
  unfold oneT
  have hH : 0 ≤ Formalism.HermitianLatticeCounting.LatticeSumBounds.bigH C (2 * r + 2) f b := by
    unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.bigH
    exact Real.rpow_nonneg hb.le _
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hC _) (Real.rpow_nonneg hH _)) hG)
    (Real.exp_pos _).le) (Real.sqrt_nonneg _)

theorem rho_le_cube {ρ : ℝ} (hρ : 1 ≤ ρ) : ρ ≤ ρ ^ 3 := by
  nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ ρ) (sub_nonneg.2 hρ)) (by linarith : (0:ℝ) ≤ ρ + 1)]

theorem scale_le {A₁ A₀ ρ R R' dd : ℝ} (h1 : 1 ≤ A₁) (hA : A₁ ≤ A₀) (hdd : 0 ≤ dd) (hR : R' ≤ ρ ^ 3 * R)
    (hR0 : 0 ≤ R) (hρ : 0 ≤ ρ) : A₁ * R' * dd ≤ A₀ * ρ ^ 3 * R * dd := by
  have hρ3 : 0 ≤ ρ ^ 3 * R := mul_nonneg (pow_nonneg hρ 3) hR0
  have h2 : A₁ * R' ≤ A₀ * (ρ ^ 3 * R) :=
    le_trans (mul_le_mul_of_nonneg_left hR (by linarith)) (mul_le_mul_of_nonneg_right hA hρ3)
  calc A₁ * R' * dd ≤ A₀ * (ρ ^ 3 * R) * dd := mul_le_mul_of_nonneg_right h2 hdd
    _ = A₀ * ρ ^ 3 * R * dd := by ring

theorem log_size {k f lk Cl L A₀ ρ : ℝ} (hk1 : 1 ≤ k) (hL : 1 ≤ L) (hCl0 : 0 < Cl) (hfl : Cl * L ≤ f * lk)
    (hClA : 3 + 6 * Real.log (3 * A₀) ≤ Cl) (hA : 1 ≤ A₀) (hρ1 : 1 ≤ ρ) (hlogρ : Real.log ρ ≤ k / 8) :
    6 * Real.log (3 * (A₀ * ρ ^ 3)) ≤ k * f * lk := by
  have hA3 : 0 < 3 * A₀ := by linarith
  have hρpos : 0 < ρ := by linarith
  have hlog : Real.log (3 * (A₀ * ρ ^ 3)) = Real.log (3 * A₀) + 3 * Real.log ρ := by
    rw [← mul_assoc, Real.log_mul hA3.ne' (pow_pos hρpos 3).ne', Real.log_pow]
    push_cast
    ring
  have hlA : 0 ≤ Real.log (3 * A₀) := Real.log_nonneg (by linarith)
  have hfl2 : Cl ≤ f * lk := le_trans (le_mul_of_one_le_right hCl0.le hL) hfl
  have h3 : 3 + 6 * Real.log (3 * A₀) ≤ f * lk := le_trans hClA hfl2
  have h4 : k * (3 + 6 * Real.log (3 * A₀)) ≤ k * (f * lk) := mul_le_mul_of_nonneg_left h3 (by linarith)
  rw [hlog]
  nlinarith [mul_nonneg (sub_nonneg.2 hk1) hlA, h4, hlogρ]

theorem hyp_nums {D : D7} {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT C0 : ℝ} (h : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) :
    large₂.CGam * unitM D large₂ ≤ (D.R.k : ℝ) / 8 ∧ Cl * large₂.sc.L ≤ (D.R.f : ℝ) * Real.log D.R.k ∧ 0 < Cl := by
  have hS := h.1
  have h1 : 8 * large₂.CGam ≤ C' := hS.1
  have h2 : C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L ≤ D.R.k := hS.2.1
  have h6 : Cl * large₂.sc.L ≤ (D.R.f : ℝ) * Real.log D.R.k := hS.2.2.2.2.2.1
  have hp := h.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hCl : 0 < Cl := hp.2.2.2.2
  have hU := unitM_nonneg D large₂
  refine ⟨?_, h6, hCl⟩
  have h8 : large₂.CGam * unitM D large₂ * 8 ≤ C' * unitM D large₂ := by
    nlinarith [mul_le_mul_of_nonneg_right h1 hU]
  have e : C' * unitM D large₂ = C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by
    unfold unitM
    ring
  linarith

theorem ite_le {P : Prop} [h : Decidable P] {a n : ℕ} (ha : a ≤ n) : @ite ℕ P h a 0 ≤ n := by
  split <;> omega

theorem rowS_scale (C : ℝ) (k r f s : ℕ) (b g v Gc ρ : ℝ) (Xi : ℕ → ℝ) (hρ : 1 ≤ ρ)
    (h0 : 0 ≤ Formalism.HermitianLatticeCounting.LatticeSumBounds.ndRow C k (2 * r + 2) f s b g v Gc Xi) :
    rowS C k r f s b g v (ρ * Gc) Xi ≤ ρ ^ 3 * rowS C k r f s b g v Gc Xi := by
  have e1 : Formalism.HermitianLatticeCounting.LatticeSumBounds.ndRow C k (2 * r + 2) f s b g v (ρ * Gc) Xi =
      ρ * Formalism.HermitianLatticeCounting.LatticeSumBounds.ndRow C k (2 * r + 2) f s b g v Gc Xi := by
    unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.ndRow
    ring
  have e2 : Formalism.HermitianLatticeCounting.LatticeSumBounds.degRow C k (2 * r + 2) f s b g v (ρ * Gc) Xi =
      ρ * Formalism.HermitianLatticeCounting.LatticeSumBounds.degRow C k (2 * r + 2) f s b g v Gc Xi := by
    unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.degRow
    ring
  have h3 := mul_le_mul_of_nonneg_right (rho_le_cube hρ) h0
  unfold rowS
  rw [e1, e2]
  nlinarith [h3]

theorem oneT_scale (C : ℝ) (k r f : ℕ) (b g Gc ρ : ℝ) (hρ : 1 ≤ ρ) (h0 : 0 ≤ oneT C k r f b g Gc) :
    oneT C k r f b g (ρ * Gc) ≤ ρ ^ 3 * oneT C k r f b g Gc := by
  have e : oneT C k r f b g (ρ * Gc) = ρ * oneT C k r f b g Gc := by
    unfold oneT
    ring
  rw [e]
  exact mul_le_mul_of_nonneg_right (rho_le_cube hρ) h0

theorem corank_le_k {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word) :
    ∀ t t', (Y.tO u u').s0 t t' ≤ D.R.k := by
  intro t t'
  exact ite_le (Nat.sub_le _ _)

section Closed

def XiSizesC : Prop :=
  ∀ Cg cb Cw cT CT C0 A : ℝ, ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∃ C'₀ Cl₀ : ℝ,
    ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word),
      Formalism.MainNotions.S.Cnt.Hyp D large₂ u u' C' Cl Cg cb Cw cT CT C0 A →
        Formalism.HermitianLatticeCounting.LatticeSumBounds.XiHyp C D.R.k (2 * D.R.rS + 2) D.R.f large₂.sc.b D.host.v (NT D u) (Formalism.MainNotions.BridgeLemma.XiB D large₂ u C)

end Closed

end Formalism.L2.SG.LoopsCut

namespace Formalism.L2.SG.LoopsCut

theorem xiSizesC_of (hS : Formalism.HermitianLatticesTheory.SiegelMassRatio) : XiSizesC := by
  intro Cg cb Cw cT CT C0 A
  have he : (1 : ℝ) ≤ Real.exp 1 * Real.pi := by
    have h1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have h2 : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
    nlinarith
  refine ⟨408 * (Real.exp 1 * Real.pi), by linarith, fun C hC => ⟨0, 1, fun C' Cl _ hCl D large₂ u u' hH => ?_⟩⟩
  have hmax : max 1 (1 / Cl) ≤ 1 := max_le le_rfl (by rw [div_le_one (by linarith)]; exact hCl)
  have hM2 := Formalism.MainNotions.BridgeLemma₂.plane_mass_bound_parameters D large₂ u u' C' Cl Cg cb Cw cT CT C0 A 8
    (le_trans (mul_le_mul_of_nonneg_left hmax (by norm_num)) (by norm_num))
  have hX := Formalism.MainNotions.BridgeLemma.first_bound_of_mass_ratio D large₂ u u' C' Cl Cg cb Cw cT CT C0 A 8 408
    (Formalism.MainNotions.BridgeLemma.lattice_count_first_of_siegel hS D) hM2 (by norm_num) le_rfl hCl
  have hCX : |(408 : ℝ)| * max 1 |Real.exp 1 * Real.pi| ≤ C := by
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 408), abs_of_pos (by positivity), max_eq_right he]; exact hC
  have hXi := Formalism.MainNotions.BridgeLemma.xiHyp_of_stX D large₂ hH hX hCX (by linarith)
  rw [← Formalism.MainNotions.BridgeLemma.d_m_eq D]
  exact hXi

end Formalism.L2.SG.LoopsCut
end
end

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2

namespace Formalism.L2.SG.LoopTieOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Pins

variable {D : D7} {X : HidaSetting D}

def ampL {Y : Full X} {u u' : D.what₂.Word} (s : TT Y u u') : ℝ :=
  ‖Formalism.L2.SG.PackageTie.hsEmb (Formalism.L2.SG.TermOp.ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') s)‖

def rowL {Y : Full X} {u u' : D.what₂.Word} (s : TT Y u u') :=
  Formalism.L2.SG.TermOp.rowOf Y.TR (Y.cs u) (Y.cs u') s

variable (Y : Full X)

def AmpFibreConst : Prop :=
  ∀ (u u' : D.what₂.Word) (t : RT Y u u') (s s' : fib Y t), ampL s.1 = ampL s'.1

def FibreCount : Prop :=
  ∀ (u u' : D.what₂.Word) (t₁ t₂ : RT Y u u') (S : Finset (TT Y u u' × TT Y u u')),
    (∀ x ∈ S, x.1.toTerm = t₁ ∧ x.2.toTerm = t₂ ∧ rowL x.1 = rowL x.2) →
      ∑ x ∈ S, wRow D (X.Fu u') x.1.lam' ≤ 1

def GamPin : Prop := ∀ u u' : D.what₂.Word, (Y.tO u u').Gam1 = gaG D

variable {Y} (hF : FinX Y) (hI : SIso D.s (sOf hF))

def JtPin (T : TermTie D) : Prop :=
  ∀ (u u' : D.what₂.Word) (t : D.s.Term u u') (s : TT Y u u'), s.toTerm = hI.eT u u' t →
    hsNormSq (T.Jt t) = ampL s ^ 2

def WRowPin (T : TermTie D) : Prop :=
  ∀ (u u' : D.what₂.Word) (p : D.s.Pair u u') (s : TT Y u u'), s.toTerm = hI.eT u u' (D.s.pfst p) →
    T.wRow p = wRow D (X.Fu u) s.lam

end Pins

section Cmp

variable {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y} {hI : SIso D.s (sOf hF)}

def pairOf {u u' : D.what₂.Word} (x : TT Y u u' × TT Y u u') (h : rowL x.1 = rowL x.2) : RP Y u u' :=
  ⟨(x.1.toTerm, x.2.toTerm), ⟨x.1, rfl⟩, ⟨x.2, rfl⟩, h⟩

theorem wRow_nonneg' {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    0 ≤ wRow D F0 Λ := by
  exact inv_nonneg.mpr (Nat.cast_nonneg _)

theorem lam_eq_of_row {u u' : D.what₂.Word} {s₁ s₂ : TT Y u u'} (h : rowL s₁ = rowL s₂) :
    s₁.lam = s₂.lam ∧ s₁.lam' = s₂.lam' := by
  unfold rowL Formalism.L2.SG.TermOp.rowOf at h
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
  exact ⟨h.1, h.2.1⟩

private theorem norm_tO_vec_eq_wt_mul_ampL {u u' : D.what₂.Word} (s : TT Y u u') :
    ‖(Y.tO u u').vec s‖ = Formalism.L2.SG.TermOp.wt s * ampL s := by
  classical
  have key : ∀ i, (Y.tO u u').vec s i = if i = (⟨s.lam, s.mem⟩, ⟨s.lam', s.mem'⟩) then
      ((Formalism.L2.SG.TermOp.wt s : ℝ) : ℂ) • Formalism.L2.SG.PackageTie.hsEmb
        (Formalism.L2.SG.TermOp.ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') s) else 0 := fun i => rfl
  have hwt : 0 ≤ Formalism.L2.SG.TermOp.wt s := Real.sqrt_nonneg _
  rw [PiLp.norm_eq_of_L2, Finset.sum_eq_single (⟨s.lam, s.mem⟩, ⟨s.lam', s.mem'⟩)]
  · rw [key, if_pos rfl, Real.sqrt_sq (norm_nonneg _), norm_smul, Complex.norm_real,
      Real.norm_of_nonneg hwt]
    rfl
  · intro b _ hb
    rw [key, if_neg hb, norm_zero]
    ring
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem fibre_le (T : TermTie D) (hJ : JtPin hF hI T) (hW : WRowPin hF hI T) (hC : FibreCount Y)
    {u u' : D.what₂.Word} (p : D.s.Pair u u') (S : Finset (TT Y u u' × TT Y u u'))
    (hS : ∀ x ∈ S, ∃ h : rowL x.1 = rowL x.2, hI.eP u u' p = pairOf x h) :
    ∑ x ∈ S, ‖(Y.tO u u').vec x.1‖ * ‖(Y.tO u u').vec x.2‖ ≤ Formalism.MainNotions.BridgeLemma.wP T p := by
  classical
  have hq1 : ((hI.eP u u' p).l1).toTerm = hI.eT u u' (D.s.pfst p) := by
    rw [hI.pfst]
    exact (hI.eP u u' p).2.choose.2
  have hw0 : 0 ≤ T.wRow p := by
    rw [hW u u' p _ hq1]
    exact wRow_nonneg' _ _
  have hwP : 0 ≤ Formalism.MainNotions.BridgeLemma.wP T p :=
    mul_nonneg hw0 (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have ee : ∀ x ∈ S, x.1.toTerm = hI.eT u u' (D.s.pfst p) ∧ x.2.toTerm = hI.eT u u' (D.s.psnd p) ∧
      rowL x.1 = rowL x.2 := by
    intro x hx
    obtain ⟨h, hp⟩ := hS x hx
    refine ⟨?_, ?_, h⟩
    · rw [hI.pfst, hp]
      rfl
    · rw [hI.psnd, hp]
      rfl
  have key : ∀ x ∈ S, ‖(Y.tO u u').vec x.1‖ * ‖(Y.tO u u').vec x.2‖ =
      Formalism.MainNotions.BridgeLemma.wP T p * wRow D (X.Fu u') x.1.lam' := by
    intro x hx
    obtain ⟨e1, e2, h⟩ := ee x hx
    have a1 : Formalism.MainNotions.BridgeLemma.aT T (D.s.pfst p) = ampL x.1 := by
      unfold Formalism.MainNotions.BridgeLemma.aT
      rw [hJ u u' _ x.1 e1]
      exact Real.sqrt_sq (norm_nonneg _)
    have a2 : Formalism.MainNotions.BridgeLemma.aT T (D.s.psnd p) = ampL x.2 := by
      unfold Formalism.MainNotions.BridgeLemma.aT
      rw [hJ u u' _ x.2 e2]
      exact Real.sqrt_sq (norm_nonneg _)
    obtain ⟨hl, hl'⟩ := lam_eq_of_row h
    rw [norm_tO_vec_eq_wt_mul_ampL, norm_tO_vec_eq_wt_mul_ampL, Formalism.MainNotions.BridgeLemma.wP, a1, a2, hW u u' p x.1 e1]
    have hw2 : Formalism.L2.SG.TermOp.wt x.2 = Formalism.L2.SG.TermOp.wt x.1 := by
      unfold Formalism.L2.SG.TermOp.wt
      rw [hl, hl']
    have hs : Formalism.L2.SG.TermOp.wt x.1 * Formalism.L2.SG.TermOp.wt x.1 =
        wRow D (X.Fu u) x.1.lam * wRow D (X.Fu u') x.1.lam' :=
      Real.mul_self_sqrt (mul_nonneg (wRow_nonneg' (X.Fu u) x.1.lam) (wRow_nonneg' (X.Fu u') x.1.lam'))
    rw [hw2]
    linear_combination (ampL x.1 * ampL x.2) * hs
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum]
  calc Formalism.MainNotions.BridgeLemma.wP T p * ∑ x ∈ S, wRow D (X.Fu u') x.1.lam'
      ≤ Formalism.MainNotions.BridgeLemma.wP T p * 1 :=
        mul_le_mul_of_nonneg_left (hC u u' (hI.eT u u' (D.s.pfst p)) (hI.eT u u' (D.s.psnd p)) S ee) hwP
    _ = Formalism.MainNotions.BridgeLemma.wP T p := mul_one _

def recP {u u' : D.what₂.Word} (x : TT Y u u' × TT Y u u') (h : rowL x.1 = rowL x.2) : D.s.Pair u u' :=
  (hI.eP u u').symm (pairOf x h)

theorem eP_recP {u u' : D.what₂.Word} (x : TT Y u u' × TT Y u u') (h : rowL x.1 = rowL x.2) :
    hI.eP u u' (recP (hI := hI) x h) = pairOf x h := by
  exact (hI.eP u u').apply_symm_apply _

theorem finSum_le (T : TermTie D) (hJ : JtPin hF hI T) (hW : WRowPin hF hI T) (hC : FibreCount Y)
    {u u' : D.what₂.Word} (S : Finset (TT Y u u' × TT Y u u')) (hS : ∀ x ∈ S, rowL x.1 = rowL x.2) :
    ∑ x ∈ S, ‖(Y.tO u u').vec x.1‖ * ‖(Y.tO u u').vec x.2‖ ≤
      ∑ p ∈ S.attach.image (fun x => recP (hI := hI) x.1 (hS x.1 x.2)), Formalism.MainNotions.BridgeLemma.wP T p := by
  classical
  have hmap : ∀ x ∈ S.attach, (fun x : {x // x ∈ S} => recP (hI := hI) x.1 (hS x.1 x.2)) x ∈
      S.attach.image (fun x => recP (hI := hI) x.1 (hS x.1 x.2)) := fun x hx => Finset.mem_image_of_mem _ hx
  rw [← Finset.sum_attach S, ← Finset.sum_fiberwise_of_maps_to hmap]
  refine Finset.sum_le_sum fun p _ => ?_
  have hS' : ∀ x ∈ (S.attach.filter (fun y => recP (hI := hI) y.1 (hS y.1 y.2) = p)).map
      (Function.Embedding.subtype _), ∃ h : rowL x.1 = rowL x.2, hI.eP u u' p = pairOf x h := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 hx
    refine ⟨hS y.1 y.2, ?_⟩
    rw [← (Finset.mem_filter.1 hy).2]
    exact eP_recP _ _
  have := fibre_le T hJ hW hC p _ hS'
  rwa [Finset.sum_map] at this

end Cmp

section Classes

variable {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y} {hI : SIso D.s (sOf hF)}


open Formalism.MainNotions.BridgeLemma in
theorem ampSum_le_of_rows (T : TermTie D) (hJ : JtPin hF hI T) (hW : WRowPin hF hI T) (hC : FibreCount Y)
    {large₂ : SizeData₂ D} {u u' : D.what₂.Word} {C1 : ℝ} (L : LoopTie D large₂ T u u' C1) (Q : D.s.Pair u u' → Prop) (B : ℝ)
    (hB : RowBound T L Q B) (Q' : Set (TT Y u u' × TT Y u u'))
    (hQ : ∀ x ∈ Q', ∃ h : rowL x.1 = rowL x.2, Q (recP (hI := hI) x h)) :
    Formalism.L2.SG.RowsOther.ampSum (Y.tO u u') Q' ≤ massRows D L.F0 L.what₂ * dimPi (hc := D.hcW) u * B := by
  classical
  unfold Formalism.L2.SG.RowsOther.ampSum
  refine Real.tsum_le_of_sum_le (fun p => ?_) (fun s => ?_)
  · exact Set.indicator_nonneg (fun p _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)) p
  · have hS : ∀ x ∈ s.filter (· ∈ Q'), rowL x.1 = rowL x.2 := fun x hx => (hQ x (Finset.mem_filter.1 hx).2).choose
    refine le_trans (le_of_eq ?_) (le_trans (finSum_le T hJ hW hC _ hS) (hB _ ?_))
    · rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : i ∈ Q' <;> simp [hi]
    · intro p hp
      obtain ⟨⟨x, hx⟩, -, rfl⟩ := Finset.mem_image.1 hp
      exact (hQ x (Finset.mem_filter.1 hx).2).choose_spec


open Formalism.MainNotions.BridgeLemma in
theorem rowBound_or (T : TermTie D) {large₂ : SizeData₂ D} {u u' : D.what₂.Word} {C1 : ℝ} (L : LoopTie D large₂ T u u' C1)
    {Q₁ Q₂ : D.s.Pair u u' → Prop} {B₁ B₂ : ℝ} (h₁ : RowBound T L Q₁ B₁) (h₂ : RowBound T L Q₂ B₂) :
    RowBound T L (fun p => Q₁ p ∨ Q₂ p) (B₁ + B₂) := by
  intro S hS
  classical
  rw [← Finset.sum_filter_add_sum_filter_not S Q₁, mul_add]
  refine add_le_add (h₁ _ fun p hp => (Finset.mem_filter.1 hp).2) (h₂ _ fun p hp => ?_)
  obtain ⟨hpS, hn⟩ := Finset.mem_filter.1 hp
  exact (hS p hpS).resolve_left hn

theorem pfst_recP {u u' : D.what₂.Word} (x : TT Y u u' × TT Y u u') (h : rowL x.1 = rowL x.2) :
    hI.eT u u' (D.s.pfst (recP (hI := hI) x h)) = x.1.toTerm := by
  rw [hI.pfst, eP_recP]
  rfl

theorem psnd_recP {u u' : D.what₂.Word} (x : TT Y u u' × TT Y u u') (h : rowL x.1 = rowL x.2) :
    hI.eT u u' (D.s.psnd (recP (hI := hI) x h)) = x.2.toTerm := by
  rw [hI.psnd, eP_recP]
  rfl

theorem gterm_ne {u u' : D.what₂.Word} (t : D.s.Term u u') (s : TT Y u u') (e : hI.eT u u' t = s.toTerm)
    (hs : s.G ≠ 0) : D.s.Gterm t ≠ 0 := by
  rw [hI.Gterm, e]
  intro h0
  apply hs
  have := congrArg Subtype.val h0
  exact this

theorem generic_of {u u' : D.what₂.Word} (t : D.s.Term u u') (s : TT Y u u') (e : hI.eT u u' t = s.toTerm)
    (hs : s.generic) : D.s.generic t := by
  rw [hI.generic, e]
  exact hs

theorem corank_of_pair {u u' : D.what₂.Word} (x : TT Y u u' × TT Y u u') (h : rowL x.1 = rowL x.2) :
    D.s.s0 (recP (hI := hI) x h) = Formalism.L2.SG.TermOp.s0T x.1 x.2 := by
  rw [hI.s0, eP_recP]
  exact (hF.pairIndep u u' _ _ x.1 x.2 (pairOf x h).2.choose.2 (pairOf x h).2.choose_spec.choose.2
    (pairOf x h).2.choose_spec.choose_spec h).1

theorem scal_recP {u u' : D.what₂.Word} (x : TT Y u u' × TT Y u u') (h : rowL x.1 = rowL x.2) :
    D.s.scalarPair (recP (hI := hI) x h) ↔ liftScalar x.1 x.2 := by
  rw [hI.scalarPair, eP_recP]
  exact (hF.pairIndep u u' _ _ x.1 x.2 (pairOf x h).2.choose.2 (pairOf x h).2.choose_spec.choose.2
    (pairOf x h).2.choose_spec.choose_spec h).2

theorem G_ne_of_Gt {u u' : D.what₂.Word} (s : TT Y u u') (h : (Y.tO u u').G s ≠ 0) : s.G ≠ 0 := by
  intro h0
  apply h
  show (if s.G = 0 then (0 : ℝ) else 1) = 0
  rw [if_pos h0]

theorem bigS_cls (T : TermTie D) {u u' : D.what₂.Word} (s : ℕ) :
    ∀ x ∈ LoopsCut.bigS (Y.tO u u') s, ∃ h : rowL x.1 = rowL x.2,
      (fun p => Formalism.MainNotions.BridgeLemma.clsND T s p ∨ Formalism.MainNotions.BridgeLemma.clsDeg T s p) (recP (hI := hI) x h) := by
  intro x hx
  obtain ⟨⟨h1, h2, h⟩, hs⟩ := hx
  refine ⟨h, ?_⟩
  have g1 := gterm_ne (hI := hI) _ x.1 (pfst_recP x h) (G_ne_of_Gt x.1 h1)
  have g2 := gterm_ne (hI := hI) _ x.2 (psnd_recP x h) (G_ne_of_Gt x.2 h2)
  have e0 : D.s.s0 (recP (hI := hI) x h) = s := (corank_of_pair x h).trans hs
  by_cases hn : Formalism.MainNotions.BridgeLemma.ndP T (recP (hI := hI) x h)
  · exact Or.inl ⟨g1, g2, e0, hn⟩
  · exact Or.inr ⟨g1, g2, e0, hn⟩

theorem nsc_cls {u u' : D.what₂.Word} :
    ∀ x ∈ (Y.tO u u').nsc (Y.tO u u').genSet, ∃ h : rowL x.1 = rowL x.2,
      Formalism.MainNotions.BridgeLemma.clsOne (recP (hI := hI) x h) := by
  intro x hx
  obtain ⟨⟨h1, h2, h⟩, hs, hns⟩ := hx
  refine ⟨h, gterm_ne (hI := hI) _ x.1 (pfst_recP x h) (G_ne_of_Gt x.1 h1.1),
    gterm_ne (hI := hI) _ x.2 (psnd_recP x h) (G_ne_of_Gt x.2 h2.1),
    generic_of (hI := hI) _ x.1 (pfst_recP x h) h1.2, generic_of (hI := hI) _ x.2 (psnd_recP x h) h2.2,
    (corank_of_pair x h).trans hs, ?_⟩
  intro hc
  apply hns
  have hsc := (scal_recP x h).1 hc
  have hl := lam_eq_of_row h
  show Formalism.L2.SG.TermOp.scalT x.1 x.2
  unfold Formalism.L2.SG.TermOp.scalT
  have hs' : Formalism.L2.SG.TermOp.s0T x.1 x.2 = 1 := hs
  unfold Formalism.L2.SG.TermOp.s0T at hs'
  rw [if_pos hl] at hs'
  exact ⟨hl, hs', hsc⟩

theorem classS_le (T : TermTie D) (hJ : JtPin hF hI T) (hW : WRowPin hF hI T) (hC : FibreCount Y)
    {large₂ : SizeData₂ D} {u u' : D.what₂.Word} {C1 : ℝ} (L : LoopTie D large₂ T u u' C1) (C : ℝ)
    (hn : Formalism.MainNotions.BridgeLemma.RowsND T L C) (hd : Formalism.MainNotions.BridgeLemma.RowsDeg T L C) (s : ℕ) (h2 : 2 ≤ s) (hk : s ≤ D.R.k) :
    Formalism.L2.SG.RowsOther.ampSum (Y.tO u u') (LoopsCut.bigS (Y.tO u u') s) ≤
      massRows D L.F0 L.what₂ * dimPi (hc := D.hcW) u *
        (LatticeSumBounds.ndRow C D.R.k D.R.m D.R.f s large₂.sc.b (gg D) D.host.v (GamS D large₂) (Formalism.MainNotions.BridgeLemma.XiB D large₂ u C) *
                         Formalism.MainNotions.BridgeLemma.rDD D u' +
          LatticeSumBounds.degRow C D.R.k D.R.m D.R.f s large₂.sc.b (gg D) D.host.v (GamS D large₂) (Formalism.MainNotions.BridgeLemma.XiB D large₂ u C)) := by
  exact ampSum_le_of_rows T hJ hW hC L _ _ (rowBound_or T L (hn s h2 hk) (hd s h2 hk)) _ (bigS_cls T s)

theorem classOne_le (T : TermTie D) (hJ : JtPin hF hI T) (hW : WRowPin hF hI T) (hC : FibreCount Y)
    {large₂ : SizeData₂ D} {u u' : D.what₂.Word} {C1 : ℝ} (L : LoopTie D large₂ T u u' C1) (C : ℝ)
    (h1 : Formalism.MainNotions.BridgeLemma.RowsOne T L C) :
    Formalism.L2.SG.RowsOther.ampSum (Y.tO u u') ((Y.tO u u').nsc (Y.tO u u').genSet) ≤
      massRows D L.F0 L.what₂ * dimPi (hc := D.hcW) u * (Formalism.MainNotions.BridgeLemma.oneB D large₂ C * Formalism.MainNotions.BridgeLemma.rDD D u') := by
  exact ampSum_le_of_rows T hJ hW hC L _ _ h1 _ nsc_cls

end Classes

section Cut

variable {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y} {hI : SIso D.s (sOf hF)}

theorem gam_mul_le (hG : GamPin Y) {large₂ : SizeData₂ D} {T : TermTie D} {u u' : D.what₂.Word} {C1 : ℝ}
    (L : LoopTie D large₂ T u u' C1) (hFo : UnitaryVolumeMass.FormAt D u) {a B : ℝ}
    (h : a ≤ massRows D L.F0 L.what₂ * dimPi (hc := D.hcW) u * B) :
    (Y.tO u u').Gam1 * a ≤ (D.duS u : ℝ) * B := by
  rw [hG u u', ← hFo L.F0 L.flag_e_eq_hyperbolic L.formsAtZero L.what₂ L.isRows]
  calc gaG D * a ≤ gaG D * (massRows D L.F0 L.what₂ * dimPi (hc := D.hcW) u * B) :=
        mul_le_mul_of_nonneg_left h (Formalism.MainNotions.BridgeLemma.gaG_nonneg D)
    _ = gaG D * massRows D L.F0 L.what₂ * dimPi (hc := D.hcW) u * B := by ring

theorem ddC_eq (hCT : Formalism.L2.SG.RowsConc.ConcTie X Y) (u u' : D.what₂.Word) :
    Formalism.L2.SG.RowsConc.ddC X Y u u' = (D.duS u : ℝ) * Formalism.MainNotions.BridgeLemma.rDD D u' := by
  obtain ⟨-, -, h3, h4, -⟩ := hCT
  unfold Formalism.L2.SG.RowsConc.ddC Formalism.MainNotions.BridgeLemma.rDD
  rw [h3, h3, h4]
  ring

theorem window {large₂ : SizeData₂ D} {u u' : D.what₂.Word} {C' Cl Cg cb Cw cT CT C0 A : ℝ}
    (hH : Cnt.Hyp D large₂ u u' C' Cl Cg cb Cw cT CT C0 A) :
    1 ≤ C0 ∧ 1 ≤ C0 * Formalism.MainNotions.BridgeLemma.rDD D u' * GamS D large₂ ^ 2 := by
  unfold Cnt.Hyp Cnt.Hyp0 at hH
  obtain ⟨⟨-, hD, hC0⟩, -⟩ := hH
  refine ⟨hC0, ?_⟩
  unfold StandingNumericalData at hD
  have hw := (hD.2.2.2.2.2.2.2.2.2.1 u').1
  rw [Formalism.MainNotions.BridgeLemma.d_GamP_eq (D := D) (large₂ := large₂) u'] at hw
  have hDs : 0 < D.what₂.Dstar := Formalism.MainNotions.BridgeLemma.Dstar_pos D
  have hG : 0 < GamS D large₂ := Real.exp_pos _
  have hC0p : 0 < C0 := by linarith
  rw [zpow_neg, zpow_ofNat, div_le_iff₀ hC0p] at hw
  unfold Formalism.MainNotions.BridgeLemma.rDD
  rw [show C0 * ((D.duS u' : ℝ) / D.what₂.Dstar) * GamS D large₂ ^ 2 =
      ((D.duS u' : ℝ) * C0 * GamS D large₂ ^ 2) / D.what₂.Dstar by ring, le_div_iff₀ hDs, one_mul]
  have h2 : D.what₂.Dstar = (GamS D large₂ ^ 2)⁻¹ * D.what₂.Dstar * GamS D large₂ ^ 2 := by field_simp
  rw [h2]
  exact mul_le_mul_of_nonneg_right hw (sq_nonneg _)

theorem rowsSC_at (T : TermTie D) (hJ : JtPin hF hI T) (hW : WRowPin hF hI T) (hC : FibreCount Y) (hG : GamPin Y)
    {large₂ : SizeData₂ D} {u u' : D.what₂.Word} {C1 : ℝ} (L : LoopTie D large₂ T u u' C1) (hFo : UnitaryVolumeMass.FormAt D u)
    (hCT : Formalism.L2.SG.RowsConc.ConcTie X Y) {C' Cl Cg cb Cw cT CT C0 A : ℝ}
    (hH : Cnt.Hyp D large₂ u u' C' Cl Cg cb Cw cT CT C0 A) (C : ℝ)
    (hn : Formalism.MainNotions.BridgeLemma.RowsND T L C) (hd : Formalism.MainNotions.BridgeLemma.RowsDeg T L C) (s : ℕ) (h2 : 2 ≤ s) (hk : s ≤ D.R.k)
    (hnd0 : 0 ≤ LatticeSumBounds.ndRow C D.R.k (2 * D.R.rS + 2) D.R.f s large₂.sc.b (X.B.g : ℝ) D.host.v (GamS D large₂)
      (Formalism.MainNotions.BridgeLemma.XiB D large₂ u C))
    (hdg0 : 0 ≤ LatticeSumBounds.degRow C D.R.k (2 * D.R.rS + 2) D.R.f s large₂.sc.b (X.B.g : ℝ) D.host.v (GamS D large₂)
      (Formalism.MainNotions.BridgeLemma.XiB D large₂ u C)) :
    LoopsCut.ClassLe (Y.tO u u') (LoopsCut.bigS (Y.tO u u') s)
      (max 1 C0 * LoopsCut.rowS C D.R.k D.R.rS D.R.f s large₂.sc.b (X.B.g : ℝ) D.host.v (GamS D large₂)
        (Formalism.MainNotions.BridgeLemma.XiB D large₂ u C) * Formalism.L2.SG.RowsConc.ddC X Y u u') := by
  have hwin := window hH
  have hw := hwin.2
  have hH' := hH
  unfold Cnt.Hyp Cnt.Hyp0 at hH'
  obtain ⟨⟨-, hD, -⟩, -⟩ := hH'
  unfold StandingNumericalData at hD
  have hwu := (hD.2.2.2.2.2.2.2.2.2.1 u).1
  rw [Formalism.MainNotions.BridgeLemma.d_GamP_eq (D := D) (large₂ := large₂) u] at hwu
  have hDs : 0 < D.what₂.Dstar := Formalism.MainNotions.BridgeLemma.Dstar_pos D
  have hGs : 0 < GamS D large₂ := Real.exp_pos _
  have hC0p : 0 < C0 := by linarith [hwin.1]
  have hdu0 : 0 ≤ (D.duS u : ℝ) := le_trans (div_pos (mul_pos (zpow_pos hGs _) hDs) hC0p).le hwu
  have hR : 0 ≤ Formalism.MainNotions.BridgeLemma.rDD D u' := by
    by_contra hneg
    push_neg at hneg
    have : C0 * Formalism.MainNotions.BridgeLemma.rDD D u' * GamS D large₂ ^ 2 < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hC0p hneg) (pow_pos hGs 2)
    linarith
  have hgg : gg D = (X.B.g : ℝ) := by
    rw [X.g_eq]
    push_cast
    rfl
  have hcl := gam_mul_le hG L hFo (classS_le T hJ hW hC L C hn hd s h2 hk)
  rw [Formalism.MainNotions.BridgeLemma.d_m_eq (D := D), hgg] at hcl
  unfold LoopsCut.ClassLe
  rw [ddC_eq hCT]
  unfold LoopsCut.rowS
  set N := LatticeSumBounds.ndRow C D.R.k (2 * D.R.rS + 2) D.R.f s large₂.sc.b (X.B.g : ℝ) D.host.v (GamS D large₂)
    (Formalism.MainNotions.BridgeLemma.XiB D large₂ u C) with hN
  set E := LatticeSumBounds.degRow C D.R.k (2 * D.R.rS + 2) D.R.f s large₂.sc.b (X.B.g : ℝ) D.host.v (GamS D large₂)
    (Formalism.MainNotions.BridgeLemma.XiB D large₂ u C) with hE
  have hM1 : 1 ≤ max 1 C0 := le_max_left _ _
  have hMC : C0 ≤ max 1 C0 := le_max_right _ _
  have e1 : (D.duS u : ℝ) * N * Formalism.MainNotions.BridgeLemma.rDD D u' ≤
      max 1 C0 * ((D.duS u : ℝ) * N * Formalism.MainNotions.BridgeLemma.rDD D u') :=
    le_mul_of_one_le_left (mul_nonneg (mul_nonneg hdu0 hnd0) hR) hM1
  have e2 : (D.duS u : ℝ) * E ≤ (max 1 C0 * Formalism.MainNotions.BridgeLemma.rDD D u' * GamS D large₂ ^ 2) * ((D.duS u : ℝ) * E) :=
    le_mul_of_one_le_left (mul_nonneg hdu0 hdg0)
      (le_trans hw (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hMC hR) (sq_nonneg _)))
  have e3 : max 1 C0 * (N + GamS D large₂ ^ 2 * E) * ((D.duS u : ℝ) * Formalism.MainNotions.BridgeLemma.rDD D u') =
      max 1 C0 * ((D.duS u : ℝ) * N * Formalism.MainNotions.BridgeLemma.rDD D u') +
        (max 1 C0 * Formalism.MainNotions.BridgeLemma.rDD D u' * GamS D large₂ ^ 2) * ((D.duS u : ℝ) * E) := by ring
  have e4 : (D.duS u : ℝ) * (N * Formalism.MainNotions.BridgeLemma.rDD D u' + E) =
      (D.duS u : ℝ) * N * Formalism.MainNotions.BridgeLemma.rDD D u' + (D.duS u : ℝ) * E := by ring
  rw [e3]
  linarith

theorem oneB_eq {large₂ : SizeData₂ D} (C : ℝ) :
    Formalism.MainNotions.BridgeLemma.oneB D large₂ C = LoopsCut.oneT C D.R.k D.R.rS D.R.f large₂.sc.b (X.B.g : ℝ) (GamS D large₂) := by
  have hg : gg D = (X.B.g : ℝ) := by
    rw [X.g_eq]
    push_cast
    rfl
  unfold Formalism.MainNotions.BridgeLemma.oneB LoopsCut.oneT
  rw [hg]

theorem oneSC_at (T : TermTie D) (hJ : JtPin hF hI T) (hW : WRowPin hF hI T) (hC : FibreCount Y) (hG : GamPin Y)
    {large₂ : SizeData₂ D} {u u' : D.what₂.Word} {C1 : ℝ} (L : LoopTie D large₂ T u u' C1) (hFo : UnitaryVolumeMass.FormAt D u)
    (hCT : Formalism.L2.SG.RowsConc.ConcTie X Y) (C0 C : ℝ) (hC0' : 0 ≤ C)
    (h1 : Formalism.MainNotions.BridgeLemma.RowsOne T L C) :
    LoopsCut.ClassLe (Y.tO u u') ((Y.tO u u').nsc (Y.tO u u').genSet)
      (max 1 C0 * LoopsCut.oneT C D.R.k D.R.rS D.R.f large₂.sc.b (X.B.g : ℝ) (GamS D large₂) *
        Formalism.L2.SG.RowsConc.ddC X Y u u') := by
  unfold LoopsCut.ClassLe
  rw [← oneB_eq (X := X) C, ddC_eq hCT]
  have hcl := gam_mul_le hG L hFo (classOne_le T hJ hW hC L C h1)
  have hA : 0 ≤ Formalism.L2.SG.RowsOther.ampSum (Y.tO u u') ((Y.tO u u').nsc (Y.tO u u').genSet) := by
    unfold Formalism.L2.SG.RowsOther.ampSum
    exact tsum_nonneg fun p => Set.indicator_nonneg (fun p _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)) p
  have hg0 : 0 ≤ (Y.tO u u').Gam1 := by
    rw [hG u u']
    exact Formalism.MainNotions.BridgeLemma.gaG_nonneg D
  have hq : 0 ≤ (D.duS u : ℝ) * (Formalism.MainNotions.BridgeLemma.oneB D large₂ C * Formalism.MainNotions.BridgeLemma.rDD D u') :=
    le_trans (mul_nonneg hg0 hA) hcl
  have hM1 : 1 ≤ max 1 C0 := le_max_left _ _
  calc _ ≤ _ := hcl
    _ ≤ max 1 C0 * ((D.duS u : ℝ) * (Formalism.MainNotions.BridgeLemma.oneB D large₂ C * Formalism.MainNotions.BridgeLemma.rDD D u')) :=
      le_mul_of_one_le_left hq hM1
    _ = _ := by ring

end Cut

section Fam

structure ConcAt (D : D7) (T : TermTie D) where
  X : HidaSetting D
  Y : Full X
  hF : FinX Y
  hI : SIso D.s (sOf hF)
  jt : JtPin hF hI T
  wr : WRowPin hF hI T
  fc : FibreCount Y
  gam : GamPin Y

variable {eps : ℝ} (Fm : FamP eps) (C1 : ℝ) (At : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
  (Yt : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    LoopTie (Fm.D x i) (Fm.L x i) (At x hx i) u u' C1)
  (Cc : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ConcAt (Fm.D x i) (At x hx i))

end Fam

section Parts

open MeasureTheory

structure LoopRowsDat (D : D7) (T : TermTie D) (u u' : D.what₂.Word) where
  F0 : FlagG (VS D) D.R.rS (Tu D u : D.host.E)
  flag_e_eq_hyperbolic : F0.e = D.sp.hypE
  formsAtZero : F0.z = D.zmOf u
  what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)
  isRows : IsRowReps D F0 what₂
  fl_eq : ∀ t : D.s.Term u u', T.fl t = lf D F0
  Lam_mem : ∀ t : D.s.Term u u', T.abelian₂ t ∈ what₂
  frame_ok : ∀ t : D.s.Term u u', FrameOK D (T.abelian₂ t) (T.fl' t)
  wRow_eq : ∀ p : D.s.Pair u u', T.wRow p = wRow D F0 (T.abelian₂ (D.s.pfst p))
  pair_inj : ∀ p q : D.s.Pair u u', T.abelian₂ (D.s.pfst p) = T.abelian₂ (D.s.pfst q) →
    (∃ n' ∈ NLam (T.abelian₂ (D.s.pfst p)) (lf D F0), ∃ n'' ∈ NLam (T.abelian₂ (D.s.pfst p)) (lf D F0),
      FrameEqv D n' (T.fl' (D.s.pfst p)) (T.fl' (D.s.pfst q)) ∧
      FrameEqv D n'' (T.fl' (D.s.psnd p)) (T.fl' (D.s.psnd q)) ∧
      ∀ x ∈ orth (hS D) (Xsp (T.fl' (D.s.pfst q))),
        T.beta q x - n'' (T.beta p (n'.symm x)) ∈ Xsp (T.fl' (D.s.psnd q))) → p = q

structure LoopLocDat (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C1 : ℝ) : Type 1 where
  θ : ℝ
  θ_win : normWin D large₂ C1 θ
  W : D.what₂.Tau → LocW D.R.k D.R.rS
  goodW : ∀ τ, GoodW D τ u u' θ (W τ)
  A : ∀ τ, LocS (W τ)
  goodS : ∀ τ, GoodS D (lamD D τ) (A τ)
  deg_eq : ∀ τ, (A τ).deg = D.dsig τ

structure LoopTermDat (D : D7) (large₂ : SizeData₂ D) (T : TermTie D) (u u' : D.what₂.Word) (C1 : ℝ)
    (B : LoopLocDat D large₂ u u' C1) : Type 1 where
  γ : D.s.Term u u' → D.what₂.Tau → MatKR D.R.k D.R.rS
  pt : D.s.Term u u' → D.what₂.Tau → Point ℂ (D.R.rS + 1)
  θR : D.s.Term u u' → D.what₂.Tau → ℝ
  νR : D.s.Term u u' → D.what₂.Tau → Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)
  volR : D.s.Term u u' → ℝ
  volR_pos : ∀ t, 0 < volR t
  gram : ∀ (t : D.s.Term u u') τ a b, Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (B.W τ).z (B.W τ).z' (γ t τ) a b =
    ((rhoF D a * rhoF D b : ℝ) : ℂ) * embS D τ (ZhatL (T.fl t) (T.fl' t) a b)
  rel : ∀ t : D.s.Term u u', D.s.Gterm t ≠ 0 → D.s.relevant t → ∀ τ,
    RelPt D (B.W τ).z (B.W τ).z' (γ t τ) (pt t τ) ∧ normWin D large₂ C1 (θR t τ) ∧
      RMeas D (B.W τ) (γ t τ) (θR t τ) (νR t τ)
  J_irr : ∀ t : D.s.Term u u', D.s.Gterm t ≠ 0 → ¬ D.s.relevant t → T.Jt t = 0
  J_norm : ∀ t : D.s.Term u u', D.s.Gterm t ≠ 0 → D.s.relevant t →
    hsNormSq (T.Jt t) = volR t ^ 2 * ∏ τ, hsNormSq ((B.A τ).J (νR t τ) (γ t τ))

def loopTieOfParts {D : D7} {large₂ : SizeData₂ D} {T : TermTie D} {u u' : D.what₂.Word} {C1 : ℝ}
    (R : LoopRowsDat D T u u') (B : LoopLocDat D large₂ u u' C1) (M : LoopTermDat D large₂ T u u' C1 B) :
    LoopTie D large₂ T u u' C1 where
  F0 := R.F0
  flag_e_eq_hyperbolic := R.flag_e_eq_hyperbolic
  formsAtZero := R.formsAtZero
  what₂ := R.what₂
  isRows := R.isRows
  fl_eq := R.fl_eq
  Lam_mem := R.Lam_mem
  frame_ok := R.frame_ok
  wRow_eq := R.wRow_eq
  pair_inj := R.pair_inj
  θ := B.θ
  θ_win := B.θ_win
  W := B.W
  goodW := B.goodW
  A := B.A
  goodS := B.goodS
  deg_eq := B.deg_eq
  γ := M.γ
  pt := M.pt
  θR := M.θR
  νR := M.νR
  volR := M.volR
  volR_pos := M.volR_pos
  gram := M.gram
  rel := M.rel
  J_irr := M.J_irr
  J_norm := M.J_norm

variable {D : D7} {X : HidaSetting D} {Y : Full X}

end Parts

end Formalism.L2.SG.LoopTieOf

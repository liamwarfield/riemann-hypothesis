module

public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLemVN
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticesMeanEqGenusMean
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbMassStabilizerLe
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LValEtaBounds
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeanCountPrimitiveSublatticesOverGenus

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneLeRatioMul
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal Classical

namespace GlobalTheory.MassRatioInvBound

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private lemma sqrt_pow_eq_pow_sqrt (a : ℝ) (ha : 0 ≤ a) (f : ℕ) : Real.sqrt (a ^ f) = Real.sqrt a ^ f := by
  rw [← Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg a) f), ← pow_mul, mul_comm, pow_mul,
    Real.sq_sqrt ha]

private lemma one_le_factorial_mul_exp_div_pow (k : ℕ) (hk : 1 ≤ k) :
    1 ≤ ((k - 1).factorial : ℝ) * k * (Real.exp 1) ^ k / (k : ℝ) ^ k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hk0 : (0 : ℝ) < (k : ℝ) ^ k := pow_pos hkpos k
  have hn : (k - 1).factorial * k = k.factorial := by
    rw [mul_comm]; exact Nat.mul_factorial_pred (by omega)
  have hf : ((k - 1).factorial : ℝ) * k = (k.factorial : ℝ) := by exact_mod_cast hn
  rw [hf, le_div_iff₀ hk0, one_mul, Real.exp_one_pow]
  have h := Real.pow_div_factorial_le_exp (x := (k : ℝ)) (Nat.cast_nonneg k) k
  have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  rw [div_le_iff₀ hfac] at h
  rw [mul_comm]
  exact h

theorem one_le_ratio_mul (f k : ℕ) (v L : ℝ) (hv : 0 < v) (hk : 1 ≤ k) (hL : ((2 : ℝ) ^ f)⁻¹ ≤ L) :
    1 ≤ (((k - 1).factorial : ℝ) * (v / Real.pi) ^ k) ^ f / Real.sqrt ((2 * v) ^ f) * L *
      ((Real.exp 1 * Real.pi / (k * v)) ^ (k * f) * (2 * (k : ℝ) * (2 * v) ^ ((1 : ℝ) / 2)) ^ f) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hpi := Real.pi_pos
  have hs0 : 0 < Real.sqrt (2 * v) := Real.sqrt_pos.mpr (by linarith)
  have hrp : (2 * v) ^ ((1 : ℝ) / 2) = Real.sqrt (2 * v) := by rw [Real.sqrt_eq_rpow]
  rw [hrp, sqrt_pow_eq_pow_sqrt (2 * v) (by linarith) f, pow_mul]

  have hcol : (((k - 1).factorial : ℝ) * (v / Real.pi) ^ k) ^ f / Real.sqrt (2 * v) ^ f * L *
      (((Real.exp 1 * Real.pi / (k * v)) ^ k) ^ f * (2 * (k : ℝ) * Real.sqrt (2 * v)) ^ f) =
      ((((k - 1).factorial : ℝ) * (v / Real.pi) ^ k) * (Real.exp 1 * Real.pi / (k * v)) ^ k *
        (2 * (k : ℝ) * Real.sqrt (2 * v)) / Real.sqrt (2 * v)) ^ f * L := by
    rw [div_pow, mul_pow, mul_pow]
    ring

  have hbase : (((k - 1).factorial : ℝ) * (v / Real.pi) ^ k) * (Real.exp 1 * Real.pi / (k * v)) ^ k *
      (2 * (k : ℝ) * Real.sqrt (2 * v)) / Real.sqrt (2 * v) =
      (((k - 1).factorial : ℝ) * k * (Real.exp 1) ^ k / (k : ℝ) ^ k) * 2 := by
    have hv0 : v ≠ 0 := hv.ne'
    have hk0 : (k : ℝ) ≠ 0 := hkpos.ne'
    have hp0 : Real.pi ≠ 0 := hpi.ne'
    have hs : Real.sqrt (2 * v) ≠ 0 := hs0.ne'
    rw [div_pow, div_pow, mul_pow, mul_pow]
    field_simp
  rw [hcol, hbase, mul_pow]
  have hA := one_le_factorial_mul_exp_div_pow k hk
  have hAf : 1 ≤ (((k - 1).factorial : ℝ) * k * (Real.exp 1) ^ k / (k : ℝ) ^ k) ^ f := one_le_pow₀ hA
  have h2 : 1 ≤ (2 : ℝ) ^ f * L := by
    have h := mul_le_mul_of_nonneg_left hL (by positivity : (0 : ℝ) ≤ 2 ^ f)
    rwa [mul_inv_cancel₀ (by positivity)] at h
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ (((k - 1).factorial : ℝ) * k * (Real.exp 1) ^ k / (k : ℝ) ^ k) ^ f * ((2 : ℝ) ^ f * L) :=
        mul_le_mul hAf h2 zero_le_one (by linarith)
    _ = _ := by ring

theorem stdH_eq (D : D7) (j : ℕ) : Cnt.stdH D.host.E j = massTelescope_form D.host.E j := rfl

theorem stdLat_eq (D : D7) (j : ℕ) : Cnt.stdLat D.host.E j = massTelescope_lat D.host.E j := by
  unfold Cnt.stdLat massTelescope_lat
  congr 2
  funext i
  simp [Pi.basisFun_apply]

theorem massS_eq (D : D7) (j : ℕ) :
    Cnt.massS D j = mass (massTelescope_form D.host.E j) (massTelescope_lat D.host.E j) := by
  unfold Cnt.massS Cnt.massU
  rw [stdH_eq, stdLat_eq]

theorem mass_pred_le : ∀ D : D7, UnitaryVolumeMass.stMassRatio D → Cnt.massS D (D.R.k - 1) ≤ Cnt.massS D D.R.k * ((Real.exp 1 * Real.pi / (D.R.k * D.host.v)) ^ (D.R.k * D.R.f) * (2 * (D.R.k : ℝ) * D.host.rdE ^ ((1 : ℝ) / 2)) ^ D.R.f) := by
  intro D hM
  have hk : 5 ≤ D.R.k := D.R.k_ge
  have hrd : D.host.rdE = 2 * D.host.v := by
    unfold Formalism.BasicNotions.Host.v
    ring
  have hv : 0 < D.host.v := by
    unfold Formalism.BasicNotions.Host.v Formalism.BasicNotions.Host.rdE
    have hd : (0 : ℝ) < |(NumberField.discr D.host.E : ℝ)| :=
      abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero D.host.E))
    exact div_pos (Real.rpow_pos_of_pos hd _) two_pos
  have hK : Formalism.HermitianLatticesTheory.IsCMUnram D.host.E := D.sp.cm.cmUnram
  have hL := (GlobalTheory.EtaValueBound.lValEta_bounds D.host.E hK D.R.k (by omega)).1
  rw [Formalism.MainNotions.StandardLattice.fDeg_host] at hL
  have hrat := hM D.R.k (by omega) (Fin D.R.k → D.host.E) (Fin (D.R.k - 1) → D.host.E)
    (massTelescope_form D.host.E D.R.k) (massTelescope_form D.host.E (D.R.k - 1))
    (massTelescope_lat D.host.E D.R.k) (massTelescope_lat D.host.E (D.R.k - 1))
    (massTelescope_symm D.host.E _) (massTelescope_symm D.host.E _)
    (massTelescope_ortho D.host.E _) (massTelescope_ortho D.host.E _)
  unfold massRatioRightSide at hrat
  rw [Formalism.MainNotions.StandardLattice.fDeg_host, Formalism.MainNotions.StandardLattice.vInv_host] at hrat
  have key := one_le_ratio_mul D.R.f D.R.k D.host.v (lValEta D.host.E D.R.k) hv (by omega) hL
  rw [massS_eq, massS_eq, hrd]
  set a := mass (massTelescope_form D.host.E D.R.k) (massTelescope_lat D.host.E D.R.k) with ha
  set b := mass (massTelescope_form D.host.E (D.R.k - 1)) (massTelescope_lat D.host.E (D.R.k - 1))
    with hb
  set R := (((D.R.k - 1).factorial : ℝ) * (D.host.v / Real.pi) ^ D.R.k) ^ D.R.f /
    Real.sqrt ((2 * D.host.v) ^ D.R.f) * lValEta D.host.E D.R.k with hR

  have hb0 : 0 ≤ b := by
    rw [hb]
    unfold mass
    split_ifs
    · exact Finset.sum_nonneg fun _ _ => by positivity
    · exact le_rfl
  have hRpos : 0 < R := by
    have h2 : (0 : ℝ) < (2 ^ D.R.f)⁻¹ := by positivity
    have hLpos : 0 < lValEta D.host.E D.R.k := lt_of_lt_of_le h2 hL
    have hpi := Real.pi_pos
    rw [hR]
    positivity
  have hbne : b ≠ 0 := by
    intro h0
    rw [h0, div_zero] at hrat
    linarith
  have hab : a = R * b := by rw [← hrat, div_mul_cancel₀ a hbne]
  rw [hab]
  calc b = b * 1 := (mul_one b).symm
    _ ≤ b * (R * ((Real.exp 1 * Real.pi / (D.R.k * D.host.v)) ^ (D.R.k * D.R.f) *
        (2 * (D.R.k : ℝ) * (2 * D.host.v) ^ ((1 : ℝ) / 2)) ^ D.R.f)) :=
        mul_le_mul_of_nonneg_left key hb0
    _ = _ := by ring

end GlobalTheory.MassRatioInvBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeanPrimitiveCorankOneSublatticesBound
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal Classical

namespace GlobalTheory.Mass.PrimMeanCorankOne

theorem num (a b Mk X Y c₁ c₂ de NT HH l m : ℝ) (j : ℕ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hMk : 0 ≤ Mk)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hA : a ≤ Mk * (X * Y)) (hB : b ≤ c₁ * c₂) (hm : Mk * NT ^ j ≤ m) (hde : 1 ≤ de) (hdH : de ≤ HH)
    (hN : 1 ≤ NT) (hNH : NT ≤ HH) (hl : 0 ≤ l) :
    a * b * de ^ j * (de ^ (4 + l) * NT ^ 2 * (de * NT) ^ (2 + l)) ≤
      ((de / NT) ^ j * X * (Y * c₁ * c₂ * HH ^ (11 + 3 * l))) * m := by
  have hd0 : 0 ≤ de := by linarith
  have hN0 : 0 < NT := by linarith
  have hH1 : 1 ≤ HH := le_trans hde hdH
  have hH0 : 0 < HH := by linarith
  have hR : de ^ (4 + l) * NT ^ 2 * (de * NT) ^ (2 + l) ≤ HH ^ (11 + 3 * l) := by
    have e1 : de ^ (4 + l) ≤ HH ^ (4 + l) := Real.rpow_le_rpow hd0 hdH (by linarith)
    have e2 : NT ^ 2 ≤ HH ^ 2 := pow_le_pow_left₀ hN0.le hNH 2
    have e3 : (de * NT) ^ (2 + l) ≤ (HH * HH) ^ (2 + l) :=
      Real.rpow_le_rpow (by positivity) (mul_le_mul hdH hNH hN0.le hH0.le) (by linarith)
    have e4 : HH ^ (4 + l) * HH ^ 2 * (HH * HH) ^ (2 + l) = HH ^ (10 + 3 * l) := by
      rw [Real.mul_rpow hH0.le hH0.le, ← Real.rpow_natCast HH 2, ← Real.rpow_add hH0,
        ← Real.rpow_add hH0, ← Real.rpow_add hH0]
      congr 1; push_cast; ring
    have e5 : HH ^ (10 + 3 * l) ≤ HH ^ (11 + 3 * l) := Real.rpow_le_rpow_of_exponent_le hH1 (by linarith)
    calc _ ≤ HH ^ (4 + l) * HH ^ 2 * (HH * HH) ^ (2 + l) := by
          gcongr
      _ = HH ^ (10 + 3 * l) := e4
      _ ≤ _ := e5
  have hR0 : 0 ≤ de ^ (4 + l) * NT ^ 2 * (de * NT) ^ (2 + l) := by positivity
  calc a * b * de ^ j * (de ^ (4 + l) * NT ^ 2 * (de * NT) ^ (2 + l))
      ≤ (Mk * (X * Y)) * (c₁ * c₂) * de ^ j * HH ^ (11 + 3 * l) := by gcongr
    _ = ((de / NT) ^ j * X * (Y * c₁ * c₂ * HH ^ (11 + 3 * l))) * (Mk * NT ^ j) := by
        rw [div_pow]; field_simp
    _ ≤ _ := by gcongr

end GlobalTheory.Mass.PrimMeanCorankOne

namespace GlobalTheory.Mass.PrimMeanCorankOne

theorem main : ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A : ℝ), UnitaryVolumeMass.stMassRatio D → Formalism.MainNotions.BridgeLemma₂.PrimitiveMeanCorankOne D large₂ u u' C' Cl Cg cb Cu cT CT C0 A := by
  intro D large₂ u u' C' Cl Cg cb Cu cT CT C0 A hR
  letI := D.host.cmStar
  intro hyp F0 he hz what₂ hrows de hde HH hdH hNH
  obtain ⟨-, ⟨-, hTp, -, hT3, -, hTs, -⟩, -⟩ := hyp
  unfold Cnt.MeanLe
  rcases what₂.eq_empty_or_nonempty with e | ⟨Λ₀, hΛ₀⟩
  · subst e; simp
  have hΛ₀r := hrows.1 Λ₀ hΛ₀
  have hK : IsCMUnram D.host.E := D.sp.cm.cmUnram
  obtain ⟨⟨hPD, hrk⟩, hrow⟩ := GlobalTheory.Mass.RowPerp.main D u F0 he hz
  obtain ⟨hint, hcyc⟩ := hrow Λ₀ hΛ₀r
  have hs := (D.sp.X 0).herm
  have hM := (GlobalTheory.Mass.RowPerpMass.main D u F0 he hz hTp hTs Λ₀ hΛ₀r).2
  have hgen := (GlobalTheory.Mass.CyclicGenus.main _ _ _ hK hs (D.sp.X 0).nondeg _ hTp hTs).2
  have hMG := GlobalTheory.MeanGenus.mean_rows_eq_mean_genus D u hTp hT3 hTs F0 he hz what₂ hrows Λ₀ hΛ₀r
  set h := (D.sp.X 0).hT with hh
  obtain ⟨reps, hreps⟩ := (final_massBasic _ _ h hs (GlobalTheory.Mass.GenusOrb.trace_pos_of_PD h hPD) _ hint.1).1
  set N : Submodule (𝓞 D.host.E) (D.sp.X 0).V → ℕ∞ := fun L => (primSp h L (D.R.k - 1) (de ^ 2)).encard with hN
  have hNinv : ∀ γ ∈ isom h, ∀ L, N (gmap γ L) = N L := fun γ hγ L =>
    (GlobalTheory.Mass.PrimMove.main _ _ h hK hs (D.sp.X 0).nondeg ⟨γ, hγ⟩ L ⊥ _ _).2
  have hMG' := hMG reps hreps N hNinv
  have hl : (∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ) *
      (Cnt.cntPrim h (Lat.L0X D Λ (lf D F0)) (D.R.k - 1) de : ℝ≥0∞)) =
      ∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ) * (N (Lat.L0X D Λ (lf D F0)) : ℝ≥0∞) := by
    refine Finset.sum_congr rfl fun Λ hΛ => ?_
    rw [(GlobalTheory.Mass.DetAgree.main _ _ h hK hs hPD _ (hrow Λ (hrows.1 Λ hΛ)).1).2.2.1]
  generalize Lat.L0X D Λ₀ (lf D F0) = L₀ at *
  obtain ⟨hm1, hm2, hst, -, hsum⟩ := GlobalTheory.Mass.GenusOrb.main _ _ h hK hs hPD L₀ hint.1
  have hr := hsum reps (fun L => (N L : ℝ≥0∞)) hreps (fun g M => by
    change ((N (gmap g.1 M) : ℕ∞) : ℝ≥0∞) = _
    rw [hNinv g.1 g.2 M])
  rw [hl]
  have hf : 1 ≤ D.R.f := by
    have h1 := D.R.toFrame.ord_pos
    have h2 : D.R.f = 2 * D.R.toFrame.ord := rfl
    omega
  have hk3 : 3 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  set t : ℕ := Lat.Tu D u ^ D.R.f with ht_def
  have ht : 1 ≤ t := Nat.one_le_pow _ _ hTp.pos
  have hmem : ∀ L ∈ genus h L₀, IsIntLat h L ∧ discN h L = t ^ 2 ∧
      (∃ s : Finset (D.sp.X 0).V, s.card ≤ 1 ∧
        dual h L = L ⊔ Submodule.span (𝓞 D.host.E) (s : Set (D.sp.X 0).V)) ∧
      ∀ x ∈ dual h L, ((Lat.Tu D u : ℕ) : 𝓞 D.host.E) • x ∈ L := by
    intro L hL
    obtain ⟨a, ⟨e⟩⟩ := (hgen L₀ L hint hcyc).1 hL
    obtain ⟨b, c⟩ := GlobalTheory.Mass.PrimMeanRow.disc_of_equiv h L _ e
    refine ⟨a, by rw [b, GlobalTheory.Mass.PrimMeanRow.finrank_E, ht_def, ← pow_mul]; ring_nf,
      ((GlobalTheory.Mass.DetAgree.main _ _ h hK hs hPD L a).2.2.2.1 1).1 c, ?_⟩
    intro x hx
    have h1 : ((Lat.Tu D u : ℕ) : 𝓞 D.host.E) • e (Submodule.Quotient.mk ⟨x, hx⟩) = 0 := by
      obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (e (Submodule.Quotient.mk ⟨x, hx⟩))
      rw [← hr, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
        Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    have h3 : ((Lat.Tu D u : ℕ) : 𝓞 D.host.E) •
        (Submodule.Quotient.mk ⟨x, hx⟩ : ↥(dual h L) ⧸ L.comap (dual h L).subtype) = 0 :=
      e.injective (by rw [map_smul, h1, map_zero])
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at h3
    exact h3
  have hU := GlobalTheory.Mass.StdMass.main _ hK
  have hT0 : ((Lat.Tu D u : ℕ) : 𝓞 D.host.E) ≠ 0 := by exact_mod_cast hTp.ne_zero
  have hnorm : Ideal.absNorm (Ideal.span {((Lat.Tu D u : ℕ) : 𝓞 D.host.E)}) = t ^ 2 := by
    rw [Ideal.absNorm_span_singleton, Algebra.norm_natCast, RingOfIntegers.rank,
      GlobalTheory.Mass.PrimMeanRow.finrank_E, ht_def, ← pow_mul]
    simp only [Int.natAbs_pow, Int.natAbs_natCast]
    ring_nf
  have hP := GlobalTheory.Mass.PrimMeanOne.main GlobalTheory.Mass.MaxFormula.main _ _ h hK hs hPD
    (GlobalTheory.Mass.exists_orthoLattice_of_unimodular _ hK) (D.R.k - 1) (by omega) (by rw [hrk]; omega)
    _ _ _ (hU (D.R.k - 1)).1 (hU (D.R.k - 1)).2.1 _ _ _ (hU 1).1 (hU 1).2.1 de t _ hde ht hT0 hnorm
    (genus h L₀) hst hmem
  have hv : 0 < D.host.v := Formalism.MainNotions.StandardLattice.host_v_pos D
  have hNT1 : 1 ≤ Cnt.NT D u := one_le_pow₀ (by exact_mod_cast hTp.one_le)
  have htNT : ((t : ℕ) : ℝ) = Cnt.NT D u := by
    rw [ht_def, Cnt.NT]; push_cast; rfl
  have hfd : fDeg D.host.E = D.R.f := GlobalTheory.Mass.PrimMeanRow.fDeg_E D
  have hA : Cnt.massU D.host.E (D.R.k - 1) ≤ Cnt.massS D D.R.k *
      ((Real.exp 1 * Real.pi / (D.R.k * D.host.v)) ^ (D.R.k * D.R.f) *
        (2 * (D.R.k : ℝ) * D.host.rdE ^ ((1 : ℝ) / 2)) ^ D.R.f) :=
    GlobalTheory.MassRatioInvBound.mass_pred_le D hR
  have hB : Cnt.massU D.host.E 1 ≤ (classNumber D.host.E : ℝ) * 2 ^ D.R.f := by
    have e1 := ((hU 1).2.2.2.2 _ (Formalism.HermitianLattices.Ext.L3.stdForm D.host.E 1) (Formalism.HermitianLattices.Ext.L3.stdLat D.host.E 1)
      (Formalism.HermitianLattices.Ext.L3.stdLat_isOrtho D.host.E 1)).1
    have e2 := Formalism.MainNotions.BridgeLemVN.mass_std_one_le hK
    rw [e1, hfd] at e2
    push_cast at e2
    exact e2
  have hbound := num (Cnt.massU D.host.E (D.R.k - 1)) (Cnt.massU D.host.E 1) (Cnt.massS D D.R.k)
    ((Real.exp 1 * Real.pi / (D.R.k * D.host.v)) ^ (D.R.k * D.R.f))
    ((2 * (D.R.k : ℝ) * D.host.rdE ^ ((1 : ℝ) / 2)) ^ D.R.f) (classNumber D.host.E : ℝ) (2 ^ D.R.f)
    de (Cnt.NT D u) HH (Real.logb 2 D.R.f) (mass h L₀) (D.R.k - 1)
    (hU (D.R.k - 1)).2.2.1.le (hU 1).2.2.1.le (hU D.R.k).2.2.1.le (by positivity)
    (by have := GlobalTheory.Mass.PrimMeanRow.one_le_rdE D; positivity) (Nat.cast_nonneg _) (by positivity)
    hA hB hM (by exact_mod_cast hde) hdH hNT1 hNH
    (Real.logb_nonneg one_lt_two (by exact_mod_cast hf))
  have key : (∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ) * ((N (Lat.L0X D Λ (lf D F0)) : ℕ∞) : ℝ≥0∞)) *
      ENNReal.ofReal (mass h L₀) ≤
      ((∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ)) *
        ENNReal.ofReal (((de : ℝ) / Cnt.NT D u) ^ (D.R.k - 1) *
          (Real.exp 1 * Real.pi / (D.R.k * D.host.v)) ^ (D.R.k * D.R.f) *
          (Formalism.MainNotions.BridgeLemma₂.classWeightAlt D * HH ^ (11 + 3 * Real.logb 2 D.R.f)))) * ENNReal.ofReal (mass h L₀) := by
    rw [hMG', hr, mul_assoc, ← ENNReal.ofReal_mul' hm2.le]
    refine mul_le_mul' le_rfl (hP.trans (ENNReal.ofReal_le_ofReal ?_))
    rw [hfd, htNT]
    unfold Formalism.MainNotions.BridgeLemma₂.classWeightAlt
    exact hbound
  exact (ENNReal.mul_le_mul_iff_left (ENNReal.ofReal_pos.2 hm2).ne' ENNReal.ofReal_ne_top).1 key

end GlobalTheory.Mass.PrimMeanCorankOne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeanPrimitiveCorankOneSublatticesBoundStatement
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mean_primitive_corank_one_sublattices_bound : ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A : ℝ), UnitaryVolumeMass.stMassRatio D → Formalism.MainNotions.BridgeLemma₂.PrimitiveMeanCorankOne D large₂ u u' C' Cl Cg cb Cu cT CT C0 A := by
  first | exact @GlobalTheory.Mass.PrimMeanCorankOne.main | exact GlobalTheory.Mass.PrimMeanCorankOne.main | (intros; apply GlobalTheory.Mass.PrimMeanCorankOne.main <;> assumption)
end

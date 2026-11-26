module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsUnifAt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepCharacterLawsNormOneIdelesOfKernelChain

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MtFiniteOrder
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.L2.Forms

noncomputable section

namespace GlobalTheory.TieFinOrd


set_option maxHeartbeats 4000000 in
theorem mt_finite_order : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i < D.R.m, ∀ y : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm), Matrix.GeneralLinearGroup.det y.1 ∈ intU D.host.F D.host.E → ∃ n : ℕ, 0 < n ∧ (t.O u μ).mt (i + 1) (dtU y) ^ n = 1) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a H T i hi y hint
  classical
  letI := D.host.cmStar
  have hzU : Matrix.GeneralLinearGroup.det y.1 ∈ U1 (sigD D) := det_in_unitary_one D.host.F D.host.E (sigD D) 1 1 (by simp) y.1 y.2
  set z := Matrix.GeneralLinearGroup.det y.1 with hz
  have hconj : conjId (sigD D) z = z⁻¹ := by
    have h1 : z * conjId (sigD D) z = 1 := hzU
    exact eq_inv_of_mul_eq_one_right h1
  have hh90 : h90 (sigD D) z = Matrix.GeneralLinearGroup.det (y * y).1 := by
    show z / conjId (sigD D) z = _
    rw [hconj, div_inv_eq_mul]
    show _ = Matrix.GeneralLinearGroup.det (y.1 * y.1)
    rw [map_mul]
  set x : (AfE t.X.F t.X.E)ˣ := Units.map A.iA.symm.toRingHom.toMonoidHom z with hxdef
  have hxx : Units.map A.iA.toRingHom.toMonoidHom x = z := by
    ext
    simp [x]
  have hq : A.q x = dtU (y * y) := H.q_dt x (y * y) (by rw [hxx, hh90])
  have hcoe : ∀ w : AfE t.X.F t.X.E, A.iA w ∈ RInt D.host.F D.host.E ↔ w ∈ RInt t.X.F t.X.E := H.iA_int
  have hxint : x ∈ intU t.X.F t.X.E := by
    refine ⟨(hcoe _).1 ?_, (hcoe _).1 ?_⟩
    · simpa [x] using hint.1
    · simpa [x] using hint.2
  have hiso : IsAdIso (GlobalTheory.Mem.Col2.afIso t.X.F t.X.E) :=
    ⟨GlobalTheory.Mem.Col2.afIso_tmul_one _ _, GlobalTheory.Mem.Col2.mem_rInt_iff _ _⟩
  have hmu : ∃ n : ℕ, 0 < n ∧ D.muTil (i + 1) (A.q x) ^ n = 1 := by
    rw [H.muTil _ hiso ⟨i, hi⟩ (GlobalTheory.Mem.ReadEx.toIdl t.X.F t.X.E x) x (fun w => rfl) (GlobalTheory.Mem.ReadEx.toIdl_snd x).symm]
    exact GlobalTheory.HeckeFin.finite_order _ _ _ (fun w => rfl) ((GlobalTheory.Mem.ReadEx.mem_intU_iff x).1 hxint)
  obtain ⟨n, hn, hmun⟩ := hmu
  have hsq : (t.O u μ).mt (i + 1) (dtU y) ^ 2 = (t.O u μ).mt (i + 1) (A.q x) := by
    rw [hq, map_mul, map_mul, sq]
  by_cases hμ : μ = D.what₂.mu0
  · refine ⟨2 * n, by omega, ?_⟩
    rw [pow_mul, hsq, (H.ref hμ).2]
    exact hmun
  · obtain ⟨ξ, hξ, hmt⟩ := H.tw μ hμ rfl
    have htor := (t.tup μ).2
    simp only [tupGrp, finChar, Subgroup.mem_inf] at htor
    obtain ⟨k, hk, hkk⟩ := (isOfFinOrder_iff_pow_eq_one).1 htor.1.1.1.2
    refine ⟨2 * (n * k), by positivity, ?_⟩
    rw [pow_mul, hsq, hmt u, twMt, if_pos ⟨by omega, by omega⟩, MonoidHom.mul_apply, mul_pow, pow_mul, hmun, one_pow, one_mul,
      hξ x, ← map_pow, mul_comm, pow_mul]
    have : ((t.tup μ : Chr t.X.F t.X.E t.X.K) x) ^ k = 1 := by
      rw [← MonoidHom.pow_apply, hkk, MonoidHom.one_apply]
    rw [this, one_pow, map_one]

end GlobalTheory.TieFinOrd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SumAltSignRange
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

namespace GlobalTheory.TwV.Xc

theorem sum_alt_sign_range (m : ℕ) :
    ∑ i ∈ Finset.range (2 * m), (if i % 2 = 1 then (-1 : ℤ) else 1) = 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    have h1 : (2 * m) % 2 = 0 := by omega
    have h2 : (2 * m + 1) % 2 = 1 := by omega
    simp [h1, h2]

theorem sum_alt_sign_pos (n' : ℕ) (hn : Even n') :
    ∑ s : Fin n', (if IsOddPos s then (-1 : ℤ) else 1) = 0 := by
  obtain ⟨m, rfl⟩ := hn
  calc (∑ s : Fin (m + m), (if IsOddPos s then (-1 : ℤ) else 1))
        = ∑ i ∈ Finset.range (m + m), (if i % 2 = 1 then (-1 : ℤ) else 1) := by
          rw [← Fin.sum_univ_eq_sum_range]; rfl
    _ = 0 := by simpa [two_mul] using sum_alt_sign_range m

theorem vm_eq_of_shift (p : ℕ) [Fact p.Prime] (X : Sys p) (v : X.Pl) (l : ℕ) (e : Fin (X.G.P.n' v) → ℤ) (k : ℤ)
    (hk : ∀ s, X.w v l s = e s - k) :
    X.vm v l = ∑ s : Fin (X.G.P.n' v), (if IsOddPos s then -1 else 1) * e s := by
  have hw : ∑ s : Fin (X.G.P.n' v), (if IsOddPos s then -1 else 1) * X.w v l s = X.vm v l := by
    unfold Sys.vm
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases h : IsOddPos s <;> simp [h]
  rw [← hw]
  have e1 : ∀ s, (if IsOddPos s then (-1 : ℤ) else 1) * X.w v l s =
      (if IsOddPos s then -1 else 1) * e s - (if IsOddPos s then (-1 : ℤ) else 1) * k := by
    intro s; rw [hk s]; ring
  rw [Finset.sum_congr rfl (fun s _ => e1 s), Finset.sum_sub_distrib, ← Finset.sum_mul,
    sum_alt_sign_pos _ (X.G.P.setting v).even, zero_mul, sub_zero]

theorem vm_shift_cancels : ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (v : X.Pl) (l : ℕ) (e : Fin (X.G.P.n' v) → ℤ) (k : ℤ),
    (∀ s, X.w v l s = e s - k) → X.vm v l = ∑ s : Fin (X.G.P.n' v), (if IsOddPos s then -1 else 1) * e s :=
  fun p _ X v l e k hk => vm_eq_of_shift p X v l e k hk

end GlobalTheory.TwV.Xc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormLamCTypeNormOne
noncomputable section

namespace GlobalTheory.TwU.RatNorm

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

variable {p : ℕ} [Fact p.Prime]

theorem frob_pow_int (X : Sys p) (v : X.Pl) (k : ℕ) (x : X.G.P.W v) :
    ∃ y : X.G.P.W v, (X.G.P.σ v ^ k) (algebraMap _ _ x) = algebraMap _ _ y := by
  induction k generalizing x with
  | zero => exact ⟨x, rfl⟩
  | succ k ih =>
    obtain ⟨y, hy⟩ := (X.G.P.setting v).frob x
    obtain ⟨z, hz⟩ := ih (x ^ p + (p : X.G.P.W v) * y)
    refine ⟨z, ?_⟩
    rw [pow_succ]
    show (X.G.P.σ v ^ k) ((X.G.P.σ v) (algebraMap _ _ x)) = _
    rw [hy, hz]

theorem norm_twG_int_le (X : Sys p) (E : CEmb X.G) (v : X.Pl) (s : Fin (X.G.P.n' v)) (x : X.G.P.W v) :
    ‖twG X E v s (algebraMap _ _ x)‖ ≤ 1 := by
  obtain ⟨y, hy⟩ := frob_pow_int X v s.val x
  have h := E.int (X.G.P.j v y)
  unfold twG
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  rw [hy, (X.G.P.setting v).ι_comp]
  exact h

theorem norm_twG_unit (X : Sys p) (E : CEmb X.G) (v : X.Pl) (s : Fin (X.G.P.n' v)) (u : (X.G.P.W v)ˣ) :
    ‖twG X E v s (algebraMap _ _ (u : X.G.P.W v))‖ = 1 := by
  have h1 := norm_twG_int_le X E v s (u : X.G.P.W v)
  have h2 := norm_twG_int_le X E v s ((u⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v)
  have h3 : twG X E v s (algebraMap _ _ (u : X.G.P.W v)) * twG X E v s (algebraMap _ _ ((u⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  have h4 := congrArg norm h3
  rw [norm_mul, norm_one] at h4
  nlinarith [norm_nonneg (twG X E v s (algebraMap _ _ (u : X.G.P.W v))),
    norm_nonneg (twG X E v s (algebraMap _ _ ((u⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v)))]

theorem norm_twG (X : Sys p) (E : CEmb X.G) (v : X.Pl) (s : Fin (X.G.P.n' v)) {y : X.G.P.Qq v} (hy : y ≠ 0) :
    ‖twG X E v s y‖ = ‖(p : ℂ_[p])‖ ^ ordP (X.G.P.W v) p y := by
  haveI := (X.G.P.setting v).frac_alt
  have hp := (X.G.P.setting v).p_unif
  obtain ⟨n, u, rfl⟩ := exists_eq_unit_mul_zpow₂ hp hy
  rw [ordP_eq hp n u, map_mul, map_zpow₀, map_natCast, norm_mul, norm_twG_unit, one_mul, norm_zpow]

theorem zpow_sum_fin {ι : Type*} (s : Finset ι) (r : ℝ) (hr : r ≠ 0) (f : ι → ℤ) :
    r ^ (∑ i ∈ s, f i) = ∏ i ∈ s, r ^ f i := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.sum_cons, Finset.prod_cons, zpow_add₀ hr, ih]

theorem norm_lamC_type_normOne : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (X : Sys p) (E : CEmb X.G)
    (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v),
    LamPos X E pos lam ρ → ∀ (e : D.what₂.Tau → ℤ) (z : D.host.E), z * D.host.conj z = 1 →
    ‖TaylorLogMetric.lamC lam (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ z ^ e τ)‖ =
      ‖(p : ℂ_[p])‖ ^ (∑ v : X.Pl, (∑ s : Fin (X.G.P.n' v), (if IsOddPos s then -1 else 1) * e (pos ⟨v, s⟩)) *
        ordP (X.G.P.W v) p (ρ v z)) := by
  intro D p _ X E pos lam ρ hL e z hz
  have hp0 : ‖(p : ℂ_[p])‖ ≠ 0 := norm_ne_zero_iff.2 (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have hmem : ∀ τ, TaylorLogMetric.embT D τ z ∈ TaylorLogMetric.Qbar := fun τ =>
    (mem_algebraicClosure_iff).2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) z).algHom (TaylorLogMetric.embT D τ).toRatAlgHom)
  have hprod : (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ z ^ e τ) ∈ TaylorLogMetric.Qbar := prod_mem fun τ _ => zpow_mem (hmem τ) _
  have h1 : TaylorLogMetric.lamC lam (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ z ^ e τ) = ∏ τ, TaylorLogMetric.lamC lam (TaylorLogMetric.embT D τ z) ^ e τ := by
    have e1 : (⟨∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ z ^ e τ, hprod⟩ : TaylorLogMetric.Qbar) = ∏ τ, (⟨TaylorLogMetric.embT D τ z, hmem τ⟩ : TaylorLogMetric.Qbar) ^ e τ := by
      apply Subtype.ext
      push_cast
      rfl
    unfold TaylorLogMetric.lamC
    rw [dite_eq_left hprod, e1, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [dite_eq_left (hmem τ), map_zpow₀]
  have hρ : ∀ v, ρ v z * ρ v (D.host.conj z) = 1 := fun v => by rw [← map_mul, hz, map_one]
  have hρ0 : ∀ v, ρ v z ≠ 0 := fun v h => by have := hρ v; rw [h, zero_mul] at this; exact zero_ne_one this
  have hf : ∀ v s, ‖TaylorLogMetric.lamC lam (TaylorLogMetric.embT D (pos ⟨v, s⟩) z)‖ ^ e (pos ⟨v, s⟩) =
      ‖(p : ℂ_[p])‖ ^ ((if IsOddPos s then -1 else 1) * e (pos ⟨v, s⟩) * ordP (X.G.P.W v) p (ρ v z)) := by
    intro v s
    by_cases hs : IsOddPos s
    · rw [LamPos.odd X E pos lam ρ hL v s hs, if_pos hs, eq_inv_of_mul_eq_one_right (hρ v), map_inv₀, norm_inv, norm_twG X E v s (hρ0 v),
        inv_zpow', ← zpow_mul]
      congr 1
      ring
    · rw [LamPos.even X E pos lam ρ hL v s hs, if_neg hs, norm_twG X E v s (hρ0 v), ← zpow_mul]
      congr 1
      ring
  rw [h1, norm_prod]
  simp_rw [norm_zpow]
  rw [← Equiv.prod_comp pos, Fintype.prod_sigma]
  simp_rw [hf, Finset.sum_mul]
  rw [zpow_sum_fin _ _ hp0]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [zpow_sum_fin _ _ hp0]

end GlobalTheory.TwU.RatNorm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormLambdaCharacterNormOneIdeleEqPPow
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.Xc


set_option maxHeartbeats 4000000 in
theorem lambdaCharacter_norm_eq_p_pow_of_pos : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ j (hj : j < D.R.m), FillAt (hT := hT) (H := H) (X := X) std j hj → ∀ x ∈ U1 (sigD D), ‖TaylorLogMetric.lamC S.lam (S.muT (j + 1) x)‖ = ‖((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w])‖ ^ (∑ v : (sysS H X std).Pl, (sysS H X std).vm v (j + 1) * ordA (A0 J) v x)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S _hD hSpl hPos j hj hFill x hx
  have hsc : ∀ y, sigD D y = D.host.conj y := fun y => bridge_star_holds D.R D.host y
  have hσ : ∀ a, sigD D (sigD D a) = a := fun a => by rw [hsc a]; exact Formalism.L2.PairingIndexBounds.F.sigD_conj D a
  obtain ⟨m, z, k, hm, hz, hkU, hkI, hxm⟩ := exists_pow_normOne_idele_eq_principal_mul_integralUnit _ _ (sigD D) hσ x hx
  have hz' : (z : D.host.E) * D.host.conj (z : D.host.E) = 1 := by rw [← hsc]; exact hz
  have hzU := GlobalTheory.TwV.MuLawPf.rationalIdele_mem_normOne_of_norm_eq_one z hz'
  have hmul := S.law.mu_mul j hj
  have hpow : ∀ n : ℕ, S.muT (j + 1) (x ^ n) = S.muT (j + 1) x ^ n := by
    intro n
    induction n with
    | zero => rw [pow_zero, pow_zero, hmul.1]
    | succ n ih => rw [pow_succ, pow_succ, hmul.2 _ (pow_mem hx n) _ hx, ih]
  have hsplit : S.muT (j + 1) x ^ m = S.muT (j + 1) (ratId D.host.F D.host.E z) * S.muT (j + 1) k := by
    rw [← hpow, hxm, hmul.2 _ hzU _ hkU]
  obtain ⟨e, he, hrat⟩ := S.law.mu_rat j hj

  obtain ⟨y, hy⟩ := GlobalTheory.TwV.MuLawPf.exists_unitaryOne_det_eq_normOneIdele hkU
  obtain ⟨n, hn, hroot⟩ := GlobalTheory.TieFinOrd.mt_finite_order J.A J.dtU J.a J.pins J.tie j hj y (by rw [hy]; exact hkI)
  have hkroot : S.muT (j + 1) k ^ n = 1 := by
    rw [← hy, S.law.mu_read j hj y, ← Units.val_pow_eq_pow_val, hroot, Units.val_one]

  have ha := S.law.mu_alg j hj x hx
  have hb := S.law.mu_alg j hj _ hzU
  have hc := S.law.mu_alg j hj k hkU
  have hlamC : ∀ (a : ℂ) (h : a ∈ TaylorLogMetric.Qbar), TaylorLogMetric.lamC S.lam a = S.lam ⟨a, h⟩ := fun a h => by
    unfold TaylorLogMetric.lamC; rw [dite_eq_left h]
  have eQ : (⟨S.muT (j + 1) x, ha⟩ : TaylorLogMetric.Qbar) ^ m = ⟨_, hb⟩ * ⟨_, hc⟩ := Subtype.ext (by push_cast; exact hsplit)
  have eQk : (⟨S.muT (j + 1) k, hc⟩ : TaylorLogMetric.Qbar) ^ n = 1 := Subtype.ext (by push_cast; exact hkroot)
  have hnormk : ‖S.lam ⟨_, hc⟩‖ = 1 := by
    have h1 := congrArg (fun q => ‖S.lam q‖) eQk
    simp only [map_pow, norm_pow, map_one, norm_one] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h1
  have hnorm_m : ‖TaylorLogMetric.lamC S.lam (S.muT (j + 1) x)‖ ^ m = ‖TaylorLogMetric.lamC S.lam (S.muT (j + 1) (ratId D.host.F D.host.E z))‖ := by
    have h1 := congrArg (fun q => ‖S.lam q‖) eQ
    simp only [map_pow, norm_pow, map_mul, norm_mul, hnormk, mul_one] at h1
    rw [hlamC _ ha, hlamC _ hb]
    exact h1
  have hratN := GlobalTheory.TwU.RatNorm.norm_lamC_type_normOne D _ (sysS H X std) S.E.toCEmb (hT.gat_pos u w hg) S.lam (J.rho std) hPos e (z : D.host.E) hz'
  rw [← hrat z hz'] at hratN

  have hvm : ∀ v : (sysS H X std).Pl, (sysS H X std).vm v (j + 1) = ∑ s : Fin ((sysS H X std).G.P.n' v), (if IsOddPos s then -1 else 1) * e (hT.gat_pos u w hg ⟨v, s⟩) := by
    intro v
    refine vm_shift_cancels _ (sysS H X std) v (j + 1) (fun s => e (hT.gat_pos u w hg ⟨v, s⟩))
      (((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ) + (((((sysS H X std).Pj (j + 1)).m + 1) / 2 : ℕ) : ℤ)) (fun s => ?_)
    rw [hFill e he v s, sub_sub]

  have hord : ∀ v : (sysS H X std).Pl, (m : ℤ) * ordA (A0 J) v x = ordP ((sysS H X std).G.P.W v) (D.what₂.places.resChar w) (J.rho std v (z : D.host.E)) := by
    intro v
    obtain ⟨hadd, hint, hratO, -⟩ := OrdA.ordA_props _ _ _ _ _ (A0 J) J.one.int hSpl.1 v
    have hp : ∀ n : ℕ, ordA (A0 J) v (x ^ n) = n * ordA (A0 J) v x := by
      intro n
      induction n with
      | zero =>
        have h1 := hadd 1 1
        rw [mul_one] at h1
        rw [pow_zero, Nat.cast_zero, zero_mul]
        linarith
      | succ n ih => rw [pow_succ, hadd, ih]; push_cast; ring
    rw [← hp, hxm, hadd, hratO, hint k hkI, add_zero]
  rw [← pow_left_inj₀ (norm_nonneg _) (zpow_nonneg (norm_nonneg _) _) hm.ne', hnorm_m, hratN, ← zpow_natCast, ← zpow_mul]
  congr 1
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [hvm v, ← hord v]
  ring

end GlobalTheory.TwV.Xc

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormLambdaCharacterNormOneIdeleEqPPowStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_lambdaCharacter_normOne_idele_eq_p_pow : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ j (hj : j < D.R.m), FillAt (hT := hT) (H := H) (X := X) std j hj → ∀ x ∈ U1 (sigD D), ‖TaylorLogMetric.lamC S.lam (S.muT (j + 1) x)‖ = ‖((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w])‖ ^ (∑ v : (sysS H X std).Pl, (sysS H X std).vm v (j + 1) * ordA (A0 J) v x)) := by
  first | exact @GlobalTheory.TwV.Xc.lambdaCharacter_norm_eq_p_pow_of_pos | exact GlobalTheory.TwV.Xc.lambdaCharacter_norm_eq_p_pow_of_pos | (intros; apply GlobalTheory.TwV.Xc.lambdaCharacter_norm_eq_p_pow_of_pos <;> assumption)
end

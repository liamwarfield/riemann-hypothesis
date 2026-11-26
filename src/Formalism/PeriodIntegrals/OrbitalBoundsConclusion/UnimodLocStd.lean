module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.ExistsIsometryMemLocalizedAtSingle
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepHSmulRight
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RamDef

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.UnitVecRam
noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

theorem unitVecRam : UnitVecRam := by
  classical
  intro a b c d ha hd lam hlam m _ _ Λ x0 y0 T i₀ hK x hxs hxT hx z₀ hz₀ hz₀T hz₀x hz₀ne
  obtain ⟨hOK, hΛ, hθ, h1, h2, hl, hQ, hi₀, hT⟩ := hK
  have hdp : Prime (d : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hκ0 : repKappa a b d ha hd lam hlam ≠ 0 := rep_kappa_ne a b d ha hd lam hlam
  have hr0 : ((Real.sqrt d : ℝ) : ℂ) ≠ 0 := by
    have : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
    exact_mod_cast this.ne'
  have hπ : 2 * cmTheta b d - b = Complex.I * ((Real.sqrt d : ℝ) : ℂ) := by unfold cmTheta; ring
  have hπ0 : (2 * cmTheta b d - b) ≠ 0 := by rw [hπ]; exact mul_ne_zero Complex.I_ne_zero hr0
  have hdc : (d : ℂ) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hππ : (2 * cmTheta b d - b)⁻¹ * conj (2 * cmTheta b d - b)⁻¹ = (d : ℂ)⁻¹ := by
    rw [map_inv₀, ← mul_inv]
    congr 1
    rw [hπ, map_mul, Complex.conj_I, Complex.conj_ofReal]
    linear_combination (-((Real.sqrt d : ℝ) : ℂ) ^ 2) * Complex.I_sq + rep_sqrt_sq d
  have nz : ∀ {z : ℤ}, ¬ (d : ℤ) ∣ z → (z : ℂ) ≠ 0 := by
    intro z hz h; apply hz; rw [show z = 0 by exact_mod_cast h]; exact dvd_zero _

  obtain ⟨n0, s0, hs0, e0⟩ := sat_norm hOK hΛ hθ hl hz₀
  have hn0 : n0 ≠ 0 := by
    intro h
    apply H_self_ne m (cmL a b d ha hd lam hlam) hz₀ne
    rw [e0, h]; simp
  let P : ℕ → Prop := fun j => SatMem d Λ (((2 * cmTheta b d - b)⁻¹) ^ j • z₀)
  have hbound : ∀ j, P j → j ≤ n0.natAbs := by
    intro j hj
    obtain ⟨p, q, hq, e⟩ := sat_norm hOK hΛ hθ hl hj
    have eH : stdH (cmL a b d ha hd lam hlam) m (((2 * cmTheta b d - b)⁻¹) ^ j • z₀) (((2 * cmTheta b d - b)⁻¹) ^ j • z₀)
        = ((d : ℂ)⁻¹) ^ j * stdH (cmL a b d ha hd lam hlam) m z₀ z₀ := by
      rw [LinearMap.map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, smul_eq_mul, map_pow,
        ← mul_assoc, ← mul_pow, hππ]
    rw [eH, e0] at e
    have e' : repKappa a b d ha hd lam hlam * ((p : ℂ) / q) =
        repKappa a b d ha hd lam hlam * ((n0 : ℂ) / ((s0 : ℂ) * (d : ℂ) ^ j)) := by
      calc _ = repKappa a b d ha hd lam hlam * p / q := by ring
        _ = _ := e.symm
        _ = _ := by ring
    have e'' := mul_left_cancel₀ hκ0 e'
    rw [div_eq_div_iff (nz hq) (mul_ne_zero (nz hs0) (pow_ne_zero _ hdc))] at e''
    have hZ : p * (s0 * (d : ℤ) ^ j) = n0 * q := by exact_mod_cast e''
    have hdj : (d : ℤ) ^ j ∣ n0 := by
      have h' : (d : ℤ) ^ j ∣ n0 * q := ⟨p * s0, by rw [← hZ]; ring⟩
      have hcop : IsCoprime ((d : ℤ) ^ j) q := IsCoprime.pow_left ((Prime.coprime_iff_not_dvd hdp).mpr hq)
      exact hcop.dvd_of_dvd_mul_right h'
    have hle : d ^ j ≤ n0.natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr hdj
      rw [Int.natAbs_pow, Int.natAbs_natCast] at this
      exact Nat.le_of_dvd (Int.natAbs_pos.mpr hn0) this
    have hlt : j < d ^ j := Nat.lt_pow_self hl.one_lt
    omega
  have hP0 : P 0 := by simpa [P] using hz₀
  set J := Nat.findGreatest P n0.natAbs with hJ
  have hPJ : P J := Nat.findGreatest_spec (P := P) (Nat.zero_le _) hP0
  have hPJ1 : ¬ P (J + 1) := by
    intro h
    by_cases hle : J + 1 ≤ n0.natAbs
    · exact Nat.findGreatest_is_greatest (Nat.lt_succ_self _) hle h
    · exact hle (hbound _ h)
  set xh : m → ℂ := ((2 * cmTheta b d - b)⁻¹) ^ J • z₀ with hxh
  have hxhT : ∀ j ∈ T, xh j = 0 := by intro j hj; simp [xh, hz₀T j hj]
  have hxhx : stdH (cmL a b d ha hd lam hlam) m xh x = 0 := by
    rw [hxh, LinearMap.map_smul, LinearMap.smul_apply, hz₀x, smul_zero]
  have hnot : ¬ SatMem d Λ ((2 * cmTheta b d - b)⁻¹ • xh) := by
    rw [hxh, smul_smul, ← pow_succ']; exact hPJ1
  have hxhs : SatMem d Λ xh := hPJ
  obtain ⟨s, hs, hsx⟩ := hPJ
  have hs' : ¬ (d : ℤ) ∣ (s : ℤ) := fun h => hs (by exact_mod_cast h)

  obtain ⟨y, hy, n, c₂, hny, hdn⟩ : ∃ y ∈ Λ, ∃ n c₂ : ℤ,
      stdH (cmL a b d ha hd lam hlam) m (s • xh) y = repKappa a b d ha hd lam hlam * ((n : ℂ) - c₂ * conj (cmTheta b d)) ∧
      ¬ (d : ℤ) ∣ 2 * n - c₂ * b := by
    by_contra hcon
    push_neg at hcon
    apply hnot
    refine ⟨s, hs, ?_⟩
    rw [smul_comm, ← hΛ]
    intro y' hy'
    obtain ⟨n', c', e1, -⟩ := rep_H_int a b c d ha hd lam hlam m hOK Λ hΛ hθ hsx hy'
    obtain ⟨k, hk⟩ := hcon y' hy' n' c' e1
    refine ⟨-k, ?_⟩
    unfold altE
    rw [LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul, e1, im_pi_inv, hk]
    push_cast
    field_simp

  set yz := zT T y with hyzdef
  have hyz : SatMem d Λ yz := rep_zT_sat a b c d ha hd lam hlam m hOK Λ hΛ hθ hl x0 y0 hQ T hT hy
  set μ := stdH (cmL a b d ha hd lam hlam) m yz x / stdH (cmL a b d ha hd lam hlam) m x x with hμdef
  set y' := yz - μ • x with hy'def
  have hy's : SatMem d Λ y' := by
    rcases hx with rfl | ⟨p, q, hp, hq, e⟩
    · simpa [y'] using hyz
    · obtain ⟨n2, c3, s2, hs2, e2⟩ := sat_pair hOK hΛ hθ hl hyz hxs
      have hμ : μ = (((q * n2 : ℤ) : ℂ) - ((q * c3 : ℤ) : ℂ) * conj (cmTheta b d)) / ((s2 * p : ℤ) : ℂ) := by
        have hp0 := nz hp
        have hq0 := nz hq
        have hs20 := nz hs2
        rw [hμdef, e2, e]
        push_cast
        field_simp
      refine rep_sat_sub d Λ hl hyz ?_
      rw [hμ]
      exact rep_sat_elt d Λ hl hθ hxs _ _ _ (not_dvd_mul' hl hs2 hp)
  have hy'T : ∀ j ∈ T, y' j = 0 := by
    intro j hj; simp [y', yz, zT, hj, hxT j hj]
  have hy'x : stdH (cmL a b d ha hd lam hlam) m y' x = 0 := by
    rcases hx with rfl | ⟨p, q, hp, hq, e⟩
    · simp
    · have hxx : stdH (cmL a b d ha hd lam hlam) m x x ≠ 0 := by
        rw [e]; exact div_ne_zero (mul_ne_zero hκ0 (nz hp)) (nz hq)
      rw [hy'def, map_sub, LinearMap.sub_apply, LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul, hμdef,
        div_mul_cancel₀ _ hxx, sub_self]
  have hxhy' : stdH (cmL a b d ha hd lam hlam) m xh y' = stdH (cmL a b d ha hd lam hlam) m xh y := by
    rw [hy'def, map_sub, (stdH (cmL a b d ha hd lam hlam) m xh).map_smulₛₗ μ x, hxhx, smul_zero, sub_zero]
    exact rep_H_zT a b d ha hd lam hlam m T hxhT
  have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast nz hs'
  have hxhy : stdH (cmL a b d ha hd lam hlam) m xh y =
      repKappa a b d ha hd lam hlam * ((n : ℂ) - c₂ * conj (cmTheta b d)) / s := by
    have e3 : stdH (cmL a b d ha hd lam hlam) m (s • xh) y = (s : ℂ) * stdH (cmL a b d ha hd lam hlam) m xh y := by
      rw [← Nat.cast_smul_eq_nsmul ℂ, LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [hny] at e3
    rw [eq_div_iff hsc]
    linear_combination (-1 : ℂ) * e3

  obtain ⟨p1, q1, hq1, e1⟩ := sat_norm hOK hΛ hθ hl hxhs
  obtain ⟨p2, q2, hq2, e2⟩ := sat_norm hOK hΛ hθ hl hy's
  by_cases hp1 : (d : ℤ) ∣ p1
  · by_cases hp2 : (d : ℤ) ∣ p2
    · refine ⟨xh + y', rep_sat_add d Λ hl hxhs hy's, ?_, ?_, ?_⟩
      · intro j hj; simp [hxhT j hj, hy'T j hj]
      · rw [map_add (f := _), LinearMap.add_apply, hxhx, hy'x, add_zero]
      · refine ⟨p1 * q2 * s + p2 * q1 * s + (2 * n - c₂ * b) * q1 * q2, q1 * q2 * s, ?_,
          not_dvd_mul' hl (not_dvd_mul' hl hq1 hq2) hs', ?_⟩
        · intro hdv
          have e4 : (2 * n - c₂ * b) * q1 * q2 =
              (p1 * q2 * s + p2 * q1 * s + (2 * n - c₂ * b) * q1 * q2) - (p1 * q2 * s + p2 * q1 * s) := by ring
          have : (d : ℤ) ∣ (2 * n - c₂ * b) * q1 * q2 := by
            rw [e4]
            exact dvd_sub hdv (dvd_add ((hp1.mul_right _).mul_right _) ((hp2.mul_right _).mul_right _))
          exact not_dvd_mul' hl (not_dvd_mul' hl hdn hq1) hq2 this
        · have hyx : stdH (cmL a b d ha hd lam hlam) m y' xh =
              repKappa a b d ha hd lam hlam * ((n : ℂ) - c₂ * cmTheta b d) / s := by
            rw [← rep_H_conj (cmL a b d ha hd lam hlam) m xh y', hxhy', hxhy]
            simp only [map_div₀, map_mul, map_sub, map_intCast, map_natCast, Complex.conj_conj,
              kappa_real a b d ha hd lam hlam]
          rw [map_add (stdH (cmL a b d ha hd lam hlam) m) xh y', LinearMap.add_apply, map_add (f := _), map_add (f := _), e1, e2, hxhy',
            hxhy, hyx]
          have htb := rep_theta_add_conj b d
          have hA : (q1 : ℂ) * (q1 : ℂ)⁻¹ = 1 := mul_inv_cancel₀ (nz hq1)
          have hB : (q2 : ℂ) * (q2 : ℂ)⁻¹ = 1 := mul_inv_cancel₀ (nz hq2)
          have hC : (s : ℂ) * (s : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hsc
          set κ := repKappa a b d ha hd lam hlam
          push_cast
          simp only [div_eq_mul_inv, mul_inv]
          linear_combination
            (-κ * p2 * (q2 : ℂ)⁻¹ * ((s : ℂ) * (s : ℂ)⁻¹) - κ * (s : ℂ)⁻¹ * (2 * n - c₂ * b) * ((q2 : ℂ) * (q2 : ℂ)⁻¹)) * hA +
            (-κ * p1 * (q1 : ℂ)⁻¹ * ((s : ℂ) * (s : ℂ)⁻¹) - κ * (s : ℂ)⁻¹ * (2 * n - c₂ * b)) * hB +
            (-κ * p1 * (q1 : ℂ)⁻¹ - κ * p2 * (q2 : ℂ)⁻¹) * hC +
            (-κ * (s : ℂ)⁻¹ * c₂) * htb
    · exact ⟨y', hy's, hy'T, hy'x, p2, q2, hp2, hq2, e2⟩
  · exact ⟨xh, hxhs, hxhT, hxhx, p1, q1, hp1, hq1, e1⟩

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepRamAsm
noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

theorem keyStartRam_of_unit (hU : UnitVecRam) : KeyStartRam := by
  intro a b c d ha hd lam hlam m _ _ Λ l x y T i₀ hK hld
  subst l
  have hK0 := hK
  obtain ⟨hOK, hsd, hθ, -, h2, hdp, hQ, hi₀, -⟩ := hK0
  set L := cmL a b d ha hd lam hlam with hL
  set κ := repKappa a b d ha hd lam hlam with hκdef
  set Q : ℤ := a * x ^ 2 + b * x * y + c * y ^ 2 with hQdef
  set f := fvec a b d lam x y i₀ with hf
  have hκ : κ ≠ 0 := rep_kappa_ne a b d ha hd lam hlam
  have hκc : conj κ = κ := kappa_real a b d ha hd lam hlam
  have hHf : stdH L m f f = κ * (Q : ℂ) := rep_norm_f a b c d ha hd lam hlam m hOK.1 x y i₀
  have hQ0 : (Q : ℂ) ≠ 0 := by
    have : Q ≠ 0 := fun h => hQ (h ▸ dvd_zero _)
    exact_mod_cast this
  have hfT : ∀ j ∈ T, f j = 0 := by
    intro j hj
    have hne : j ≠ i₀ := fun h => hi₀ (h ▸ hj)
    simp [hf, fvec, hne]
  have hfmem : f ∈ stdLat L m := rep_fvec_mem a b d ha hd lam hlam m x y i₀
  set M := relIdx Λ (stdLat L m) with hMdef
  have hMf : M • f ∈ Λ := by
    have h := AddSubgroup.nsmul_index_mem (Λ.addSubgroupOf (stdLat L m)) ⟨f, hfmem⟩
    rw [AddSubgroup.mem_addSubgroupOf] at h
    simpa [hMdef, relIdx, AddSubgroup.relIndex] using h
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast h2
  have hgf : M • f = (M : ℂ) • f := (Nat.cast_smul_eq_nsmul ℂ M f).symm
  set g := M • f with hg
  have hHs : ∀ (α β : ℂ) (u v : m → ℂ), stdH L m (α • u) (β • v) = α * conj β * stdH L m u v := by
    intro α β u v
    simp only [map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul]
    ring
  have hgT : ∀ j ∈ T, g j = 0 := by
    intro j hj
    simp [hgf, hfT j hj]
  have hg0 : g ≠ 0 := by
    intro h
    have h' : stdH L m g g = 0 := by rw [h]; simp
    rw [hgf, hHs, hHf] at h'
    have : (M : ℂ) * conj (M : ℂ) * (κ * Q) ≠ 0 := by
      simp only [map_natCast]
      exact mul_ne_zero (mul_ne_zero hMc hMc) (mul_ne_zero hκ hQ0)
    exact this h'
  have hgS : SatMem d Λ g := rep_sat_of_mem d Λ hMf hdp
  have hd1 : ¬ (d : ℤ) ∣ 1 := by
    intro h
    have := Int.eq_one_of_dvd_one (by positivity) h
    exact hdp.one_lt.ne' (by exact_mod_cast this)
  obtain ⟨y1, hy1S, hy1T, -, p1, q1, hp1, hq1, hy1H⟩ :=
    hU a b c d ha hd lam hlam m Λ x y T i₀ hK 0 (rep_sat_zero d Λ hdp) (by simp) (Or.inl rfl)
      g hgS hgT (by simp) hg0
  have hp1c : (p1 : ℂ) ≠ 0 := by
    have : p1 ≠ 0 := fun h => hp1 (h ▸ dvd_zero _)
    exact_mod_cast this
  have hq1c : (q1 : ℂ) ≠ 0 := by
    have : q1 ≠ 0 := fun h => hq1 (h ▸ dvd_zero _)
    exact_mod_cast this
  obtain ⟨n', c₂, s', hs', hpair⟩ := sat_pair hOK hsd hθ hdp hgS hy1S
  rw [← hL, ← hκdef] at hy1H hpair
  have hs'c : (s' : ℂ) ≠ 0 := by
    have : s' ≠ 0 := fun h => hs' (h ▸ dvd_zero _)
    exact_mod_cast this
  have hθc : conj (cmTheta b d) = (b : ℂ) - cmTheta b d := by
    have := rep_theta_add_conj b d
    linear_combination this
  set γ0 : ℂ := (q1 : ℂ) * ((n' : ℂ) - c₂ * conj (cmTheta b d)) with hγ0
  set z : m → ℂ := (((p1 * s' : ℤ) : ℂ)) • g - γ0 • y1 with hz
  have hzS : SatMem d Λ z := by
    have h1 := rep_sat_zsmul d Λ hgS (p1 * s')
    have h2 := rep_sat_elt d Λ hdp hθ hy1S (q1 * n') (q1 * c₂) 1 hd1
    have h3 : ((((q1 * n' : ℤ) : ℂ) - ((q1 * c₂ : ℤ) : ℂ) * conj (cmTheta b d)) / ((1 : ℤ) : ℂ)) = γ0 := by
      rw [hγ0]; push_cast; ring
    rw [h3] at h2
    exact rep_sat_sub d Λ hdp h1 h2
  have hzT : ∀ j ∈ T, z j = 0 := by
    intro j hj
    simp [hz, hgT j hj, hy1T j hj]
  have hzy : stdH L m z y1 = 0 := by
    have e1 : stdH L m z y1 = ((p1 * s' : ℤ) : ℂ) * stdH L m g y1 - γ0 * stdH L m y1 y1 := by
      simp only [hz, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [e1, hpair, hy1H, hγ0]
    push_cast
    field_simp
    ring
  by_cases hz0 : z = 0
  · set r : ℂ := ((p1 * s' : ℤ) : ℂ) * M with hr
    have hr0 : r ≠ 0 := by
      rw [hr]; push_cast
      exact mul_ne_zero (mul_ne_zero hp1c hs'c) hMc
    have hrc : conj r = r := by rw [hr]; simp
    have hrf : r • f = γ0 • y1 := by
      have : ((p1 * s' : ℤ) : ℂ) • g = γ0 • y1 := sub_eq_zero.mp (by rw [← hz]; exact hz0)
      rw [hgf, smul_smul] at this
      simpa [hr] using this
    set β : ℂ := γ0 / r with hβ
    have hβN : β * conj β = ((Q * q1 : ℤ) : ℂ) / ((p1 : ℤ) : ℂ) := by
      have e := congrArg (fun v => stdH L m v v) hrf
      simp only [hHs, hHf, hy1H, hrc] at e
      field_simp at e
      rw [hβ, map_div₀, hrc, div_mul_div_comm, div_eq_div_iff (mul_ne_zero hr0 hr0) hp1c]
      push_cast
      linear_combination -e
    have hβK : IsK b d β := by
      refine ⟨q1 * (n' - c₂ * b), q1 * c₂, p1 * s' * M, ?_, ?_⟩
      · have : ((p1 * s' * M : ℤ) : ℂ) ≠ 0 := by
          push_cast; exact mul_ne_zero (mul_ne_zero hp1c hs'c) hMc
        exact_mod_cast this
      · rw [hβ, hγ0, hθc]
        have : ((p1 * s' * (M : ℤ) : ℤ) : ℂ) = r := by rw [hr]; push_cast; ring
        rw [this]
        field_simp
        push_cast
        ring
    have hQq : ¬ (d : ℤ) ∣ Q * q1 := not_dvd_mul' hdp hQ hq1
    obtain ⟨s, hs⟩ := norm_square hOK hβK hQq hp1 hβN
    obtain ⟨k, hk⟩ := hs
    refine ⟨(s : ℂ) • y1, ⟨rep_sat_zsmul d Λ hy1S s, ?_, k, Q * q1, hQq, ?_⟩⟩
    · intro j hj; simp [hy1T j hj]
    · rw [hHs, hy1H, hHf]
      have hk' : (s : ℂ) ^ 2 * p1 = Q * q1 + d * k := by
        have := congrArg (fun t : ℤ => (t : ℂ)) hk
        push_cast at this
        linear_combination this
      simp only [map_intCast]
      push_cast
      field_simp
      linear_combination hk'
  · obtain ⟨y2, hy2S, hy2T, hy21, p2, q2, hp2, hq2, hy2H⟩ :=
      hU a b c d ha hd lam hlam m Λ x y T i₀ hK y1 hy1S hy1T (Or.inr ⟨p1, q1, hp1, hq1, by
        rw [hy1H]⟩) z hzS hzT hzy hz0
    rw [← hL, ← hκdef] at hy2H
    rw [← hL] at hy21
    have hp2c : (p2 : ℂ) ≠ 0 := by
      have : p2 ≠ 0 := fun h => hp2 (h ▸ dvd_zero _)
      exact_mod_cast this
    have hq2c : (q2 : ℂ) ≠ 0 := by
      have : q2 ≠ 0 := fun h => hq2 (h ▸ dvd_zero _)
      exact_mod_cast this
    have hy12 : stdH L m y1 y2 = 0 := by
      have := rep_H_conj (L := L) (m := m) y2 y1
      rw [hy21, map_zero] at this
      exact this.symm
    have hodd : d % 2 = 1 := by
      have := hOK.2.2.1
      omega
    obtain ⟨s, t, hst⟩ := pigeon hdp hodd (p1 * q2) (p2 * q1) (Q * q1 * q2)
      (not_dvd_mul' hdp hp1 hq2) (not_dvd_mul' hdp hp2 hq1)
    obtain ⟨k, hk⟩ := hst
    have hQq : ¬ (d : ℤ) ∣ Q * (q1 * q2) := not_dvd_mul' hdp hQ (not_dvd_mul' hdp hq1 hq2)
    refine ⟨(s : ℂ) • y1 + (t : ℂ) • y2,
      ⟨rep_sat_add d Λ hdp (rep_sat_zsmul d Λ hy1S s) (rep_sat_zsmul d Λ hy2S t), ?_, k, Q * (q1 * q2), hQq, ?_⟩⟩
    · intro j hj; simp [hy1T j hj, hy2T j hj]
    · have e : stdH L m ((s : ℂ) • y1 + (t : ℂ) • y2) ((s : ℂ) • y1 + (t : ℂ) • y2) =
          (s : ℂ) ^ 2 * stdH L m y1 y1 + (t : ℂ) ^ 2 * stdH L m y2 y2 := by
        simp only [map_add (f := _), LinearMap.add_apply, hHs, hy12, hy21, map_intCast]
        ring
      rw [e, hy1H, hy2H, hHf]
      have hk' : (s : ℂ) ^ 2 * (p1 * q2) + (t : ℂ) ^ 2 * (p2 * q1) = Q * q1 * q2 + d * k := by
        have := congrArg (fun t : ℤ => (t : ℂ)) hk
        push_cast at this
        linear_combination this
      push_cast
      field_simp
      linear_combination hk'

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepKeyRam
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepKey
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.KeyExact
noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

private theorem sum_sum_sub_isotropic_shift_eq_of_conj_eq_neg (L : PeriodPair) (m : Type) [Fintype m] [DecidableEq m] (i₀ : m) (φ : ℂ)
    (g : m → ℂ) :
    stdH L m (Pi.single i₀ φ) g = ((area L : ℂ))⁻¹ * (φ * conj (g i₀)) ∧
    stdH L m g (Pi.single i₀ φ) = ((area L : ℂ))⁻¹ * (g i₀ * conj φ) := by
  constructor
  · simp [stdH, matH, Matrix.smul_apply, Matrix.one_apply, Pi.single_apply]
    ring
  · simp [stdH, matH, Matrix.smul_apply, Matrix.one_apply, Pi.single_apply,
      apply_ite (starRingEnd ℂ), mul_ite]
    ring

private theorem H_affine_combination_eq_of_quadratic_relation {m : Type} [Fintype m] [DecidableEq m] (H : PI.ULS.Sesq (m → ℂ))
    (f w : m → ℂ) (κ rc Q N₁ γ ε : ℂ) (hN : N₁ ≠ 0)
    (hff : H f f = κ * Q) (hww : H w w = κ * Q * (1 + ε)) (hX : N₁ * (H f w + H w f) = κ * γ)
    (hrc : conj rc = rc) (hrD : rc * (N₁ * (2 * Q + Q * ε) - γ) = N₁ * Q * ε) :
    H (w + rc • (f - w)) (w + rc • (f - w)) = κ * Q := by
  simp only [map_add (f := _), map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, hrc]
  apply mul_left_cancel₀ hN
  linear_combination (N₁ * (1 - 2 * rc + rc ^ 2)) * hww + (N₁ * rc ^ 2) * hff +
    (rc - rc ^ 2) * hX + (κ * (rc - 1)) * hrD

private theorem cmTheta_add_conj_and_mul_conj (a : ℕ) (b c : ℤ) (d : ℕ) (h : CmOK a b c d) :
    cmTheta b d + conj (cmTheta b d) = b ∧ cmTheta b d * conj (cmTheta b d) = (a:ℂ) * c := by
  obtain ⟨h4, -, -, -⟩ := h
  have hs : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = d := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; simp
  have h4' : (4:ℂ) * a * c = (b:ℂ)^2 + d := by exact_mod_cast h4
  have hc : conj (cmTheta b d) = ((b:ℂ) - Complex.I * (Real.sqrt d : ℝ)) / 2 := by
    simp [cmTheta, map_div₀, Complex.conj_ofReal, map_ofNat]
    ring
  rw [hc]
  constructor
  · simp only [cmTheta]; ring
  · simp only [cmTheta]
    linear_combination (-((Real.sqrt d : ℝ) : ℂ)^2/4) * Complex.I_sq + (1/4) * hs - (1/4) * h4'

private theorem not_pow_dvd_two_mul_mul_of_not_dvd (l : ℕ) (hl : Nat.Prime l) (g k : ℕ) (hk : 3 ≤ k) (M₄ n₁ : ℕ)
    (hM : ¬ l ∣ M₄) (hn : ¬ l ∣ n₁) (Q₀ p q : ℤ) (hQ : ¬ (l:ℤ) ∣ Q₀) (hq : ¬ (l:ℤ) ∣ q) :
    ¬ (l:ℤ) ^ (g + 3) ∣ 2 * ((l ^ g * M₄ * n₁ : ℕ) : ℤ) * Q₀ * (2 * q + (l:ℤ) ^ k * p) := by
  intro hdvd
  have hp : Prime (l:ℤ) := Nat.prime_iff_prime_int.mp hl
  have hne : (l:ℤ) ^ g ≠ 0 := pow_ne_zero _ (by exact_mod_cast hl.ne_zero)
  have h1 : (l:ℤ) ^ 3 ∣ ((M₄:ℤ) * n₁ * Q₀) * (2 * (2 * q + (l:ℤ) ^ k * p)) := by
    have e1 : (l:ℤ) ^ (g + 3) = (l:ℤ) ^ g * (l:ℤ) ^ 3 := pow_add _ _ _
    have e2 : 2 * ((l ^ g * M₄ * n₁ : ℕ) : ℤ) * Q₀ * (2 * q + (l:ℤ) ^ k * p) =
        (l:ℤ) ^ g * (((M₄:ℤ) * n₁ * Q₀) * (2 * (2 * q + (l:ℤ) ^ k * p))) := by
      push_cast; ring
    rw [e1, e2] at hdvd
    exact (mul_dvd_mul_iff_left hne).mp hdvd
  have hnd : ¬ (l:ℤ) ∣ ((M₄:ℤ) * n₁ * Q₀) := by
    intro h
    rcases hp.dvd_or_dvd h with h | h
    · rcases hp.dvd_or_dvd h with h | h
      · exact hM (Int.natCast_dvd_natCast.mp h)
      · exact hn (Int.natCast_dvd_natCast.mp h)
    · exact hQ h
  have h2 := hp.pow_dvd_of_dvd_mul_left 3 hnd h1
  have h3 : (l:ℤ) ^ 3 ∣ 2 * (l:ℤ) ^ k * p :=
    Dvd.dvd.mul_right (Dvd.dvd.mul_left (pow_dvd_pow _ hk) _) _
  have h4 : (l:ℤ) ^ 3 ∣ q * 4 := by
    have e3 : q * 4 = 2 * (2 * q + (l:ℤ) ^ k * p) - 2 * (l:ℤ) ^ k * p := by ring
    rw [e3]
    exact dvd_sub h2 h3
  have h5 := hp.pow_dvd_of_dvd_mul_left 3 hq h4
  have h6 := Int.le_of_dvd (by norm_num) h5
  have hl2 : (2:ℤ) ≤ l := by exact_mod_cast hl.two_le
  have h7 : (2:ℤ) ^ 3 ≤ (l:ℤ) ^ 3 := by gcongr
  linarith

private theorem natAbs_smul_mem_of_zsmul_mem {V : Type} [AddCommGroup V] (Λ : AddSubgroup V) (z : ℤ) (v : V)
    (h : z • v ∈ Λ) : z.natAbs • v ∈ Λ := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg z
  · simpa [natCast_zsmul] using h
  · simpa [natCast_zsmul] using h

private theorem zsmul_affine_combination_eq {m : Type} (w f : m → ℂ) (E₀ P : ℤ) (n₁ M₃ l t h : ℕ) (hE : (E₀:ℂ) ≠ 0) :
    (E₀ * n₁ * M₃ : ℤ) • (w + ((l:ℂ) ^ (t + h) * P / E₀) • (f - w)) =
      (M₃ * E₀ - (l:ℤ) ^ (t + h) * P * M₃) • (n₁ • w) + ((l:ℤ) ^ t * P * n₁) • ((l ^ h * M₃) • f) := by
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply]
  simp only [zsmul_eq_mul, nsmul_eq_mul, smul_eq_mul]
  push_cast
  field_simp
  ring

theorem keyExact : KeyExact := by
  intro a b c d ha hd lam hlam m _ _ Λ l x y T i₀ hK
  obtain ⟨hcm, -, -, hr1, hr2, hl, hQ, hi₀, -⟩ := hK
  have hl1 : l ≠ 1 := hl.one_lt.ne'
  obtain ⟨g, M₄, hM₄, hM₁⟩ := Nat.exists_eq_pow_mul_and_not_dvd hr1 l hl1
  obtain ⟨h, M₃, hM₃, hM₂⟩ := Nat.exists_eq_pow_mul_and_not_dvd hr2 l hl1
  refine ⟨g + h + 3, fun k hk w hw => ?_⟩
  obtain ⟨⟨n₁, hn₁, hn₁w⟩, hzero, p, q, hlq, hHw⟩ := hw
  obtain ⟨hθs, hθp⟩ := cmTheta_add_conj_and_mul_conj a b c d hcm
  set L := cmL a b d ha hd lam hlam with hLdef
  set θ := cmTheta b d with hθdef
  set φ : ℂ := lam * (↑x * ↑a + ↑y * θ) with hφ
  have hf : fvec a b d lam x y i₀ = Pi.single i₀ φ := rfl
  rw [hf] at hHw ⊢
  have hω1 : L.ω₁ = lam * a := rfl
  have hω2 : L.ω₂ = lam * θ := rfl
  have hwstd : (relIdx (stdLat L m) Λ) • (n₁ • w) ∈ stdLat L m :=
    AddSubgroup.nsmul_relIndex_mem (stdLat L m) hn₁w
  rw [hM₁] at hwstd
  have hw0 := (AddSubgroup.mem_pi _).mp hwstd i₀ (Set.mem_univ _)
  obtain ⟨α, β, hαβ⟩ := PeriodPair.mem_lattice.mp hw0
  set N₁ : ℕ := l ^ g * M₄ * n₁ with hN₁
  have hwi : (N₁:ℂ) * w i₀ = lam * (α * a + β * θ) := by
    have e : ((l ^ g * M₄) • n₁ • w) i₀ = (N₁:ℂ) * w i₀ := by
      simp [hN₁, nsmul_eq_mul]
      ring
    rw [← e, ← hαβ, hω1, hω2]
    ring
  have hfΛ : (relIdx Λ (stdLat L m)) • (Pi.single i₀ φ) ∈ Λ := by
    apply AddSubgroup.nsmul_relIndex_mem Λ
    rw [stdLat, AddSubgroup.mem_pi]
    intro i _
    by_cases hi : i = i₀
    · subst hi
      simp only [Pi.single_eq_same]
      exact PeriodPair.mem_lattice.mpr ⟨x, y, by rw [hω1, hω2, hφ]; ring⟩
    · simp [Pi.single_eq_of_ne hi]
  rw [hM₂] at hfΛ
  set A : ℂ := ((area L : ℂ))⁻¹ with hA
  set Q₀ : ℤ := ↑a * x ^ 2 + b * x * y + c * y ^ 2 with hQ₀
  set γ : ℤ := 2 * α * x * a + (α * y + β * x) * b + 2 * β * y * c with hγ
  set κ : ℂ := A * (lam * conj lam * a) with hκ
  have hcφ : conj φ = conj lam * (x * a + y * conj θ) := by simp [hφ]
  have hff : stdH L m (Pi.single i₀ φ) (Pi.single i₀ φ) = κ * Q₀ := by
    rw [(sum_sum_sub_isotropic_shift_eq_of_conj_eq_neg L m i₀ φ _).1]
    simp only [Pi.single_eq_same]
    rw [hcφ, hφ, hκ, hQ₀]
    push_cast
    linear_combination (A * lam * conj lam * x * y * a) * hθs + (A * lam * conj lam * y ^ 2) * hθp
  have hwc : (N₁:ℂ) * conj (w i₀) = conj lam * (α * a + β * conj θ) := by
    have := congrArg (starRingEnd ℂ) hwi
    simpa using this
  have hX : (N₁:ℂ) * (stdH L m (Pi.single i₀ φ) w + stdH L m w (Pi.single i₀ φ)) = κ * γ := by
    rw [(sum_sum_sub_isotropic_shift_eq_of_conj_eq_neg L m i₀ φ w).1, (sum_sum_sub_isotropic_shift_eq_of_conj_eq_neg L m i₀ φ w).2, hcφ, hφ, hκ, hγ]
    push_cast
    linear_combination (A * lam * (x * a + y * θ)) * hwc +
      (A * conj lam * (x * a + y * conj θ)) * hwi +
      (A * lam * conj lam * a * (x * β + y * α)) * hθs + (A * lam * conj lam * 2 * β * y) * hθp
  have hww : stdH L m w w = κ * Q₀ * (1 + (l:ℂ) ^ k * p / q) := by rw [hHw, hff]
  have hsum := not_pow_dvd_two_mul_mul_of_not_dvd l hl g k (by omega) M₄ n₁ hM₄ hn₁ Q₀ p q hQ hlq
  obtain ⟨w', γ', hw'Λ, hw'z, hw'w, hw'X, hndv⟩ : ∃ (w' : m → ℂ) (γ' : ℤ), n₁ • w' ∈ Λ ∧
      (∀ j ∈ T, w' j = 0) ∧ stdH L m w' w' = κ * Q₀ * (1 + (l:ℂ) ^ k * p / q) ∧
      (N₁:ℂ) * (stdH L m (Pi.single i₀ φ) w' + stdH L m w' (Pi.single i₀ φ)) = κ * γ' ∧
      ¬ (l:ℤ) ^ (g + 3) ∣ (N₁:ℤ) * Q₀ * (2 * q + (l:ℤ) ^ k * p) - γ' * q := by
    by_cases hE : (l:ℤ) ^ (g + 3) ∣ (N₁:ℤ) * Q₀ * (2 * q + (l:ℤ) ^ k * p) - γ * q
    · refine ⟨-w, -γ, ?_, ?_, ?_, ?_, ?_⟩
      · rw [smul_neg]; exact neg_mem hn₁w
      · intro j hj; simp [hzero j hj]
      · simp [hww]
      · simp only [map_neg, LinearMap.neg_apply]
        push_cast
        linear_combination -hX
      · intro hE'
        apply hsum
        have e : 2 * ((l ^ g * M₄ * n₁ : ℕ) : ℤ) * Q₀ * (2 * q + (l:ℤ) ^ k * p) =
            ((N₁:ℤ) * Q₀ * (2 * q + (l:ℤ) ^ k * p) - γ * q) +
            ((N₁:ℤ) * Q₀ * (2 * q + (l:ℤ) ^ k * p) - (-γ) * q) := by
          rw [hN₁]
          push_cast
          ring
        rw [e]
        exact dvd_add hE hE'
    · exact ⟨w, γ, hn₁w, hzero, hww, hX, hE⟩
  set E : ℤ := (N₁:ℤ) * Q₀ * (2 * q + (l:ℤ) ^ k * p) - γ' * q with hEdef
  have hE0 : E ≠ 0 := fun h0 => hndv (h0 ▸ dvd_zero _)
  obtain ⟨j, e₀, he₀, hEabs⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.mpr hE0) l hl1
  have hj : j ≤ g + 2 := by
    by_contra hj
    apply hndv
    have h1 : l ^ (g + 3) ∣ E.natAbs := hEabs ▸ Dvd.dvd.mul_right (pow_dvd_pow l (by omega)) _
    have h2 : ((l ^ (g + 3) : ℕ) : ℤ) ∣ E := Int.natCast_dvd.mpr h1
    simpa using h2
  set E₀ : ℤ := E.sign * e₀ with hE₀def
  have hEE : E = (l:ℤ) ^ j * E₀ := by
    conv_lhs => rw [← Int.sign_mul_natAbs E, hEabs]
    rw [hE₀def]
    push_cast
    ring
  have hE₀ : ¬ (l:ℤ) ∣ E₀ := by
    intro hd'
    apply he₀
    have h1 := Int.natCast_dvd.mp hd'
    rwa [hE₀def, Int.natAbs_mul, Int.natAbs_sign_of_ne_zero hE0, one_mul, Int.natAbs_natCast] at h1
  have hE₀ne : (E₀:ℂ) ≠ 0 := by
    have : E₀ ≠ 0 := fun h0 => hE₀ (h0 ▸ dvd_zero _)
    exact_mod_cast this
  have hqne : (q:ℂ) ≠ 0 := by
    have : q ≠ 0 := fun h0 => hlq (h0 ▸ dvd_zero _)
    exact_mod_cast this
  have hN₁ne : (N₁:ℂ) ≠ 0 := by
    have hM₄0 : M₄ ≠ 0 := by rintro rfl; exact hM₄ (dvd_zero _)
    have hn₁0 : n₁ ≠ 0 := by rintro rfl; exact hn₁ (dvd_zero _)
    have : N₁ ≠ 0 := by
      rw [hN₁]
      exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hl.ne_zero) hM₄0) hn₁0
    exact_mod_cast this
  set t := k - j - h with ht
  have hkj : k - j = t + h := by omega
  set P : ℤ := Q₀ * p * N₁ with hP
  set rc : ℂ := (l:ℂ) ^ (k - j) * P / E₀ with hrcdef
  have hrc : conj rc = rc := by
    rw [hrcdef]
    simp [map_div₀]
  have hrD : rc * (N₁ * (2 * (Q₀:ℂ) + Q₀ * ((l:ℂ) ^ k * p / q)) - γ') =
      N₁ * Q₀ * ((l:ℂ) ^ k * p / q) := by
    have hEc : (E:ℂ) = (l:ℂ) ^ j * E₀ := by exact_mod_cast hEE
    have hEc2 : (E:ℂ) = N₁ * Q₀ * (2 * q + (l:ℂ) ^ k * p) - γ' * q := by
      rw [hEdef]; push_cast; ring
    have hpow : (l:ℂ) ^ k = (l:ℂ) ^ (k - j) * (l:ℂ) ^ j := by
      rw [← pow_add]; congr 1; omega
    have e1 : (N₁:ℂ) * (2 * (Q₀:ℂ) + Q₀ * ((l:ℂ) ^ k * p / q)) - γ' = (l:ℂ) ^ j * E₀ / q := by
      rw [← hEc, hEc2]
      field_simp
      try ring
    rw [e1, hrcdef, hP, hpow]
    push_cast
    field_simp
    try ring
  refine ⟨w' + rc • (Pi.single i₀ φ - w'), ?_, ?_, ?_⟩
  · have hmem : (E₀ * n₁ * M₃ : ℤ) • (w' + rc • (Pi.single i₀ φ - w')) ∈ Λ := by
      have key : (E₀ * n₁ * M₃ : ℤ) • (w' + rc • (Pi.single i₀ φ - w')) =
          (M₃ * E₀ - (l:ℤ) ^ (k - j) * P * M₃) • (n₁ • w') +
          ((l:ℤ) ^ t * P * n₁) • ((l ^ h * M₃) • Pi.single i₀ φ) := by
        rw [hrcdef, hkj]
        exact zsmul_affine_combination_eq w' (Pi.single i₀ φ) E₀ P n₁ M₃ l t h hE₀ne
      rw [key]
      exact add_mem (AddSubgroup.zsmul_mem _ hw'Λ _) (AddSubgroup.zsmul_mem _ hfΛ _)
    refine ⟨(E₀ * n₁ * M₃).natAbs, ?_, natAbs_smul_mem_of_zsmul_mem Λ _ _ hmem⟩
    intro hd'
    have hp : Prime (l:ℤ) := Nat.prime_iff_prime_int.mp hl
    have h1 : (l:ℤ) ∣ E₀ * n₁ * M₃ := Int.natCast_dvd.mpr hd'
    rcases hp.dvd_or_dvd h1 with h2 | h2
    · rcases hp.dvd_or_dvd h2 with h3 | h3
      · exact hE₀ h3
      · exact hn₁ (Int.natCast_dvd_natCast.mp h3)
    · exact hM₃ (Int.natCast_dvd_natCast.mp h2)
  · intro j' hj'
    have hne : j' ≠ i₀ := fun h' => hi₀ (h' ▸ hj')
    simp [hw'z j' hj', Pi.single_eq_of_ne hne]
  · rw [H_affine_combination_eq_of_quadratic_relation (stdH L m) (Pi.single i₀ φ) w' κ rc Q₀ N₁ γ' ((l:ℂ) ^ k * p / q) hN₁ne hff hw'w
      hw'X hrc hrD, hff]

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.KeyNewton
noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

theorem keyNewton : KeyNewton := by
  intro a b c d ha hd lam hlam m _ _ Λ l x y T i₀ h k hk w hw
  obtain ⟨hOK, -, hθ, -, -, hl, -, -, -⟩ := h
  obtain ⟨hwsat, hwT, p, q, hq, hww⟩ := hw
  obtain ⟨τ, r, s, hτ1, hτ2, hs, hτsat⟩ := rep_tau a b c d hOK Λ hθ hl
  have hlp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hq0 : (q : ℂ) ≠ 0 := by
    have : q ≠ 0 := by rintro rfl; exact hq (dvd_zero _)
    exact_mod_cast this
  have hs0 : (s : ℂ) ≠ 0 := by
    have : s ≠ 0 := by rintro rfl; exact hs (dvd_zero _)
    exact_mod_cast this
  set ε : ℂ := ((l ^ k * p : ℤ) : ℂ) / (q : ℂ) with hε
  have hεc : conj ε = ε := by rw [hε, map_div₀, map_intCast, map_intCast]
  have hξ : (1 - ε * τ) * conj (1 - ε * τ) = 1 - ε + ε ^ 2 * ((r : ℂ) / s) := by
    rw [map_sub, map_one, map_mul, hεc]
    linear_combination (-ε) * hτ1 + ε ^ 2 * hτ2
  refine ⟨(1 - ε * τ) • w, ?_, ?_, p ^ 2 * (r * q - s * q + l ^ k * p * r), q ^ 3 * s, ?_, ?_⟩
  · have e : (1 - ε * τ) • w = w - ε • (τ • w) := by rw [sub_smul, one_smul, smul_smul]
    rw [e, hε]
    exact rep_sat_sub l Λ hl hwsat (rep_sat_rat l Λ hl (hτsat w hwsat) _ _ hq)
  · intro j hj; simp [hwT j hj]
  · intro h
    rcases hlp.dvd_mul.mp h with h | h
    · exact hq (hlp.dvd_of_dvd_pow h)
    · exact hs h
  · rw [rep_H_smul, hξ, hww]
    rw [hε]
    push_cast
    field_simp
    ring

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

namespace PI.UnitaryGroupMassFormula.UnimodLocStd

theorem keyRep_of_start (hS : KeyStart) : KeyRep := keyRep_of hS keyNewton keyExact

end PI.UnitaryGroupMassFormula.UnimodLocStd
end

namespace PI.UnitaryGroupMassFormula.UnimodLocStd

theorem keyStart_of_keyStartRam (hR : KeyStartRam) : KeyStart := keyStart_of_ram hR

theorem keyRep_of_ram (hR : KeyStartRam) : KeyRep := keyRep_of_start (keyStart_of_keyStartRam hR)

end PI.UnitaryGroupMassFormula.UnimodLocStd
end

theorem unimodular_local_standard : PI.UnimodLocStd :=
  PI.UnitaryGroupMassFormula.UnimodLocStd.target_of_key
    (PI.UnitaryGroupMassFormula.UnimodLocStd.keyRep_of_ram
      (PI.UnitaryGroupMassFormula.UnimodLocStd.keyStartRam_of_unit PI.UnitaryGroupMassFormula.UnimodLocStd.unitVecRam))

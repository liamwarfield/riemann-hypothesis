module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.KumCongr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.Square

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SgIsog
open scoped MatrixGroups Matrix UpperHalfPlane
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

namespace UpperTheory.V.Z.Kato.Sym.SiegelIsogeny

open GlobalTheory.Sieg

private theorem prod_cth (c m : ℕ) (q t : ℂ) (hm : 0 < m) (hc : Nat.Coprime c m) (hq : ‖q‖ < 1) (ht : t ≠ 0) :
    ∏ j ∈ Finset.range m, cth c q (t * ee ((j : ℂ) / m)) = cth c (q ^ m) (t ^ m) := by
  have hm0 : m ≠ 0 := hm.ne'
  have hζ : IsPrimitiveRoot (Complex.exp (2 * ↑Real.pi * Complex.I / m)) m :=
    Complex.isPrimitiveRoot_exp m hm0
  set ζ := Complex.exp (2 * ↑Real.pi * Complex.I / m) with hζd
  have he : ∀ j : ℕ, ee ((j : ℂ) / m) = ζ ^ j := fun j => ee_nat_div_eq_pow m j
  simp_rw [he]
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hm0
  have hne : ∀ j : ℕ, t * ζ ^ j ≠ 0 := fun j => mul_ne_zero ht (pow_ne_zero _ hζ0)
  have p1 : ∏ j ∈ Finset.range m, (-(t * ζ ^ j)) = -(t ^ m) := by
    have h := prod_sub_pow_mul_of_isPrimitiveRoot hζ hm 0 t
    rw [zero_pow hm0, zero_sub] at h
    rw [← h]
    refine Finset.prod_congr rfl fun j _ => ?_
    ring
  have p2 : ∏ j ∈ Finset.range m, (1 - t * ζ ^ j) = 1 - t ^ m := by
    have h := prod_sub_pow_mul_of_isPrimitiveRoot hζ hm 1 t
    rw [one_pow] at h
    rw [← h]
    refine Finset.prod_congr rfl fun j _ => ?_
    ring
  have p3 : ∏ j ∈ Finset.range m, (1 - (t * ζ ^ j) ^ c) = 1 - (t ^ m) ^ c := by
    have h := prod_sub_pow_mul_of_isPrimitiveRoot (hζ.pow_of_coprime c hc) hm 1 (t ^ c)
    rw [one_pow] at h
    rw [← pow_mul, mul_comm m c, pow_mul, ← h]
    refine Finset.prod_congr rfl fun j _ => ?_
    ring
  have p4 : ∏ j ∈ Finset.range m, ∏' n : ℕ, cthFac c q (t * ζ ^ j) (n + 1) =
      ∏' n : ℕ, cthFac c (q ^ m) (t ^ m) (n + 1) := by
    rw [← Multipliable.tprod_finsetProd (fun j _ => cthFac_multipliable c q _ hq (hne j))]
    refine tprod_congr fun n => ?_
    exact prod_cthFac_mul_pow hζ hm hc q t (n + 1)
  simp only [cth, Finset.prod_mul_distrib, Finset.prod_div_distrib, Finset.prod_pow, Finset.prod_zpow,
    Finset.prod_const, Finset.card_range, p1, p2, p3, p4]

private theorem prod_sg (c k : ℕ) (x : Fin 2 → ℚ) (τ τ' : ℍ) (hk : 0 < k) (hc : Nat.Coprime c k)
    (h : (τ' : ℂ) = k * τ) :
    ∏ j ∈ Finset.range k, GlobalTheory.Sieg.sg c ![x 0, (x 1 + j) / k] τ = GlobalTheory.Sieg.sg c x τ' := by
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hq : ‖ee (τ : ℂ)‖ < 1 := by
    rw [ee, Complex.norm_exp, Real.exp_lt_one_iff]
    have hre : (2 * ↑Real.pi * Complex.I * (τ : ℂ)).re = -(2 * Real.pi * τ.im) := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre]
    have := τ.im_pos
    nlinarith [Real.pi_pos]
  set T := ee ((x 0 : ℂ) * τ + (x 1 : ℂ) / k) with hT
  have hT0 : T ≠ 0 := Complex.exp_ne_zero _
  have key := prod_cth c k (ee τ) T hk hc hq hT0
  have h1 : ∀ j ∈ Finset.range k, GlobalTheory.Sieg.sg c ![x 0, (x 1 + j) / k] τ = cth c (ee τ) (T * ee ((j : ℂ) / k)) := by
    intro j _
    simp only [GlobalTheory.Sieg.sg, pt, hT, ee, ← Complex.exp_add]
    congr 2
    push_cast
    field_simp
    ring
  rw [Finset.prod_congr rfl h1, key, GlobalTheory.Sieg.sg]
  congr 1
  · simp only [ee, ← Complex.exp_nat_mul, h]
    congr 1
    ring
  · simp only [hT, pt, ee, ← Complex.exp_nat_mul, h]
    congr 1
    field_simp

private theorem siegel_admissible_to_rat (c M : ℕ) [NeZero M] (h1 : 1 < c) (h6 : Nat.Coprime c 6) (hc : Nat.Coprime c M) (x : Row M)
    (hx : x ≠ 0) : GlobalTheory.Sieg.admitted c (toQ M x) := by
  refine ⟨h1, h6, ?_⟩
  rintro ⟨⟨n0, hn0⟩, ⟨n1, hn1⟩⟩
  have hM : (M : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have key : ∀ i, ∀ n : ℤ, (n : ℚ) = c * toQ M x i → x i = 0 := by
    intro i n hn
    simp only [toQ] at hn
    have h2 : n * (M : ℤ) = ((c * (x i).val : ℕ) : ℤ) := by
      have h3 : (n : ℚ) * M = c * (x i).val := by rw [hn]; field_simp
      exact_mod_cast h3
    have hdvd : (M : ℤ) ∣ ((c * (x i).val : ℕ) : ℤ) := ⟨n, by rw [← h2]; ring⟩
    have hdvd' : M ∣ c * (x i).val := Int.natCast_dvd_natCast.mp hdvd
    have hv : M ∣ (x i).val := Nat.Coprime.dvd_of_dvd_mul_left hc.symm hdvd'
    have hlt : (x i).val < M := ZMod.val_lt _
    have h0 : (x i).val = 0 := Nat.eq_zero_of_dvd_of_lt hv hlt
    exact (ZMod.val_eq_zero _).mp h0
  apply hx
  funext i
  fin_cases i
  · exact key 0 n0 hn0
  · exact key 1 n1 hn1

private theorem neBot : (Filter.codiscreteWithin Hs).NeBot := by
  have hI : Complex.I ∈ Hs := by simp [Hs]
  have hopen : IsOpen Hs := by
    show IsOpen {z : ℂ | 0 < z.im}
    exact isOpen_lt continuous_const Complex.continuous_im
  have hnb : (nhdsWithin Complex.I (Hs \ {Complex.I})).NeBot := by
    rw [Set.diff_eq, nhdsWithin_inter_of_mem
      (mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds hI))]
    infer_instance
  refine hnb.mono ?_
  exact le_iSup₂ (f := fun x (_ : x ∈ Hs) => nhdsWithin x (Hs \ {x})) Complex.I hI

private theorem mob_dg (k : ℕ) (hk : 0 < k) (z : ℂ) : mob (dg k) z = k * z := by
  simp [mob, dg, toGQ, ent, Matrix.det_fin_two, hk, Matrix.GeneralLinearGroup.mk']

private theorem prod_siegel {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε)
    (c k : ℕ) (x : Fin 2 → ℚ) (hA : GlobalTheory.Sieg.admitted c x) (hk : 0 < k) (hc : Nat.Coprime c k) :
    ∏ j ∈ Finset.range k, siegel X c ![x 0, (x 1 + j) / k] = X.sl (dg k) (siegel X c x) := by
  haveI := neBot
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  have hAj : ∀ j ∈ Finset.range k, GlobalTheory.Sieg.admitted c ![x 0, (x 1 + j) / k] := by
    intro j _
    obtain ⟨h1, h6, hn⟩ := hA
    refine ⟨h1, h6, ?_⟩
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    apply hn
    have ha' : (a : ℚ) = c * x 0 := by simpa using ha
    have hb' : (b : ℚ) = c * ((x 1 + j) / k) := by simpa using hb
    refine ⟨⟨a, ha'⟩, ⟨b * k - c * j, ?_⟩⟩
    push_cast
    rw [hb']
    field_simp
    ring
  apply X.an.injective
  rw [map_prod, Finset.prod_congr rfl (fun j hj => GlobalTheory.T.siegelUnitInTower_an_eq_siegelUnitOnComplex Ω ε X c _ (hAj j hj)),
    X.an_sl (dg k) _ (sgC c x) (GlobalTheory.T.siegelUnitInTower_an_eq_siegelUnitOnComplex Ω ε X c x hA)]
  have hprod : ∏ j ∈ Finset.range k, (↑(sgC c ![x 0, (x 1 + j) / k]) : Mero) =
      ↑(∏ j ∈ Finset.range k, sgC c ![x 0, (x 1 + j) / k]) :=
    (map_prod (Filter.Germ.coeRingHom _) _ _).symm
  rw [hprod, Filter.Germ.coe_eq]
  filter_upwards [Filter.self_mem_codiscreteWithin Hs] with z hz
  have hz' : 0 < z.im := hz
  have hkz : 0 < ((k : ℂ) * z).im := by
    simpa [Complex.mul_im] using mul_pos (Nat.cast_pos.mpr hk : (0 : ℝ) < k) hz'
  simp only [Finset.prod_apply]
  show _ = sgC c x (mob (dg k) z)
  rw [mob_dg k hk]
  simp only [sgC, UpperHalfPlane.ofComplex_apply_of_im_pos hz', UpperHalfPlane.ofComplex_apply_of_im_pos hkz]
  exact prod_sg c k x ⟨z, hz'⟩ ⟨k * z, hkz⟩ hk hc rfl

end UpperTheory.V.Z.Kato.Sym.SiegelIsogeny

open UpperTheory.V.Z.Kato.Sym.SiegelIsogeny in
theorem UpperTheory.V.Z.Kato.Sym.sgIsog :
    UpperTheory.V.Z.Kato.Sym.SgIsog := by
  intro Ω _ _ _ ε X c k M _ h1 h6 hc x hx
  have hkM : k * M ≠ 0 := NeZero.ne _
  have hk : 0 < k := Nat.pos_of_ne_zero (left_ne_zero_of_mul hkM)
  have hM : 0 < M := Nat.pos_of_ne_zero (right_ne_zero_of_mul hkM)
  haveI : NeZero M := ⟨hM.ne'⟩
  have hck : c.Coprime k := Nat.Coprime.coprime_dvd_right (dvd_mul_right k M) hc
  have hcM : c.Coprime M := Nat.Coprime.coprime_dvd_right (dvd_mul_left M k) hc
  have hx0 : (x 0).val < M := ZMod.val_lt _
  have hx1 : (x 1).val < M := ZMod.val_lt _
  have hlt0 : k * (x 0).val < k * M := by nlinarith
  have hlt1 : ∀ j, j < k → (x 1).val + j * M < k * M := by
    intro j hj
    nlinarith [Nat.zero_le M]
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hkq : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  simp only [UpperTheory.V.Z.Kato.Sym.sg]
  rw [← prod_siegel X c k (toQ M x) (siegel_admissible_to_rat c M h1 h6 hcM x hx) hk hck]
  symm
  refine Finset.prod_nbij'
    (i := fun j => ![((k * (x 0).val : ℕ) : ZMod (k * M)), (((x 1).val + j * M : ℕ) : ZMod (k * M))])
    (j := fun x' => (x' 1).val / M) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨rfl, ?_⟩
    show ZMod.castHom _ (ZMod M) (((x 1).val + j * M : ℕ) : ZMod (k * M)) = x 1
    rw [map_natCast, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, add_zero,
      ZMod.natCast_zmod_val]
  · intro x' hx'
    rw [Finset.mem_range]
    have hv : (x' 1).val < k * M := ZMod.val_lt _
    exact (Nat.div_lt_iff_lt_mul hM).mpr hv
  · intro j hj
    have hj' : j < k := Finset.mem_range.mp hj
    show (((x 1).val + j * M : ℕ) : ZMod (k * M)).val / M = j
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (hlt1 j hj'), Nat.add_mul_div_right _ _ hM,
      Nat.div_eq_of_lt hx1, zero_add]
  · intro x' hx'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx'
    obtain ⟨h0, h1'⟩ := hx'
    have h2 : ((x' 1).val : ZMod M) = x 1 := by
      rw [← h1']
      show _ = ZMod.castHom _ (ZMod M) (x' 1)
      rw [ZMod.castHom_apply, ZMod.cast_eq_val]
    have hmod : (x' 1).val % M = (x 1).val := by
      have h3 := congrArg ZMod.val h2
      rwa [ZMod.val_natCast] at h3
    funext i
    fin_cases i
    · exact h0.symm
    · show (((x 1).val + (x' 1).val / M * M : ℕ) : ZMod (k * M)) = x' 1
      rw [← hmod, Nat.mod_add_div', ZMod.natCast_zmod_val]
  · intro j hj
    have hj' : j < k := Finset.mem_range.mp hj
    congr 1
    funext i
    fin_cases i
    · show ((x 0).val : ℚ) / M =
        ((((k * (x 0).val : ℕ) : ZMod (k * M)).val : ℕ) : ℚ) / ((k * M : ℕ) : ℚ)
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt0]
      push_cast
      field_simp <;> ring
    · show (((x 1).val : ℚ) / M + j) / k =
        (((((x 1).val + j * M : ℕ) : ZMod (k * M)).val : ℕ) : ℚ) / ((k * M : ℕ) : ℚ)
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (hlt1 j hj')]
      push_cast
      field_simp <;> ring
end

noncomputable section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4

namespace UpperTheory.V.Z.Kato.Sym

private theorem mul_eq_up (k M : ℕ) [NeZero k] [NeZero M] (x : Row M) (i : Fin 2) (z : ZMod (k * M))
    (h : ZMod.castHom (dvd_mul_left M k) (ZMod M) z = x i) : up k M x i = (k : ZMod (k * M)) * z := by
  haveI : NeZero (k * M) := ⟨mul_ne_zero (NeZero.ne k) (NeZero.ne M)⟩
  obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective z
  rw [map_natCast] at h
  simp only [up]
  rw [← h, ZMod.val_natCast, ← Nat.cast_mul, ZMod.natCast_eq_natCast_iff]
  exact (Nat.mod_modEq n M).mul_left' k

private theorem cast_eq_zero_of (k M : ℕ) [NeZero k] [NeZero M] (z : ZMod (k * M))
    (h : (k : ZMod (k * M)) * z = 0) : ZMod.castHom (dvd_mul_left M k) (ZMod M) z = 0 := by
  haveI : NeZero (k * M) := ⟨mul_ne_zero (NeZero.ne k) (NeZero.ne M)⟩
  obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective z
  rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at h
  rw [map_natCast, ZMod.natCast_eq_zero_iff]
  exact Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero (NeZero.ne k)) h

private def InF (k M : ℕ) (x : Row M) (x' : Row (k * M)) : Prop := x' 0 = up k M x 0 ∧ dn k M x' 1 = x 1

private theorem lift_ex (k M : ℕ) (w : ZMod M) : ∃ z : ZMod (k * M), ZMod.castHom (dvd_mul_left M k) (ZMod M) z = w :=
  ZMod.castHom_surjective _ w

private theorem inF_ex (k M : ℕ) (x : Row M) : ∃ x', InF k M x x' := by
  obtain ⟨z, hz⟩ := lift_ex k M (x 1)
  exact ⟨![up k M x 0, z], rfl, hz⟩

private theorem inF_two (k M : ℕ) [NeZero k] [NeZero M] (x : Row M) (x' : Row (k * M)) (h : InF k M x x')
    (hx : (2 : ZMod M) • x ≠ 0) : (2 : ZMod (k * M)) • x' ≠ 0 := by
  intro h0
  apply hx
  obtain ⟨z, hz⟩ := lift_ex k M (x 0)
  have a0 : (2 : ZMod (k * M)) * x' 0 = 0 := congrFun h0 0
  have a1 : (2 : ZMod (k * M)) * x' 1 = 0 := congrFun h0 1
  have b0 : (2 : ZMod M) * x 0 = 0 := by
    rw [h.1, mul_eq_up k M x 0 z hz, mul_left_comm] at a0
    have := cast_eq_zero_of k M _ a0
    rwa [map_mul, hz, map_ofNat] at this
  have b1 : (2 : ZMod M) * x 1 = 0 := by
    have := congrArg (ZMod.castHom (dvd_mul_left M k) (ZMod M)) a1
    rw [map_mul, map_ofNat, map_zero] at this
    rw [← h.2]; exact this
  funext i
  fin_cases i
  · exact b0
  · exact b1

private theorem rt_zero {M : ℕ} (x : Row M) (γ : SL(2, ℤ)) : rt x γ 0 = x 0 * (γ.1 0 0 : ℤ) + x 1 * (γ.1 1 0 : ℤ) := by
  simp [rt, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

private theorem rt_one' {M : ℕ} (x : Row M) (γ : SL(2, ℤ)) : rt x γ 1 = x 0 * (γ.1 0 1 : ℤ) + x 1 * (γ.1 1 1 : ℤ) := by
  simp [rt, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

private theorem rt_rt {M : ℕ} (x : Row M) (γ δ : SL(2, ℤ)) : rt (rt x γ) δ = rt x (γ * δ) := by
  simp only [rt, Matrix.vecMul_vecMul, Matrix.SpecialLinearGroup.coe_mul, Matrix.map_mul]

private theorem rt_id {M : ℕ} (x : Row M) : rt x 1 = x := by
  simp [rt]

private theorem inF_rt (k M : ℕ) [NeZero k] [NeZero M] (γ γ' : SL(2, ℤ))
    (hg : !![(k : ℤ), 0; 0, 1] * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * !![(k : ℤ), 0; 0, 1])
    (x : Row M) (x' : Row (k * M)) (h : InF k M x x') : InF k M (rt x γ') (rt x' γ) := by
  have hk : (k : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne k
  have e00 : γ'.1 0 0 = γ.1 0 0 := by
    have := congrFun (congrFun hg 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this
    exact mul_left_cancel₀ hk (by linarith)
  have e01 : γ'.1 0 1 = k * γ.1 0 1 := by
    have := congrFun (congrFun hg 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this
    linarith
  have e10 : γ.1 1 0 = k * γ'.1 1 0 := by
    have := congrFun (congrFun hg 1) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this
    linarith
  have e11 : γ'.1 1 1 = γ.1 1 1 := by
    have := congrFun (congrFun hg 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this
    linarith
  obtain ⟨z, hz⟩ := lift_ex k M (x 0)
  have h0 : x' 0 = k * z := h.1.trans (mul_eq_up k M x 0 z hz)
  have h1 : ZMod.castHom (dvd_mul_left M k) (ZMod M) (x' 1) = x 1 := h.2
  constructor
  · rw [mul_eq_up k M (rt x γ') 0 (z * (γ'.1 0 0 : ℤ) + x' 1 * (γ'.1 1 0 : ℤ))
      (by rw [rt_zero, map_add (f := _), map_mul, map_mul, hz, h1, map_intCast, map_intCast]), rt_zero, h0, e00, e10]
    push_cast; ring
  · show ZMod.castHom (dvd_mul_left M k) (ZMod M) (rt x' γ 1) = _
    rw [rt_one', rt_one', h0, map_add (f := _), map_mul, map_mul, map_mul, hz, h1, map_intCast, map_intCast, map_natCast, e01, e11]
    push_cast; ring

private theorem rel_inv (k : ℕ) (γ γ' : SL(2, ℤ))
    (hg : !![(k : ℤ), 0; 0, 1] * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * !![(k : ℤ), 0; 0, 1]) :
    !![(k : ℤ), 0; 0, 1] * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      ((γ'⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * !![(k : ℤ), 0; 0, 1] := by
  have a : ((γ'⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * γ' = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have b : (γ : Matrix (Fin 2) (Fin 2) ℤ) * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  calc _ = (((γ'⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * γ') * !![(k : ℤ), 0; 0, 1] * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
        rw [a, one_mul]
    _ = _ := by rw [mul_assoc _ (γ' : Matrix (Fin 2) (Fin 2) ℤ), ← hg, mul_assoc, mul_assoc, b, mul_one]

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ}

private theorem inF_gr (k M : ℕ) [NeZero k] [NeZero M] (s : Ω ≃ₐ[ℚ] Ω)
    (x : Row M) (x' : Row (k * M)) (h : InF k M x x') : InF k M (gr M s x) (gr (k * M) s x') := by
  have H := (rowB Ω M (Nat.pos_of_ne_zero (NeZero.ne M))).2.2.2 k (Nat.pos_of_ne_zero (NeZero.ne k))
  refine ⟨h.1, ?_⟩
  rw [H.2.2.2.2.1 s x']
  show cyc M s * dn k M x' 1 = cyc M s * x 1
  rw [h.2]

private theorem mv_cancel (X : Tower Ω ε) (m : ℕ) (hm : 0 < m) (τ τ' : X.K ≃+* X.K) (s s' : Ω ≃ₐ[ℚ] Ω) (hτ : admitted X τ s)
    (hτ' : admitted X τ' s') (u v : X.K) (P Q R : Pt X m) (hP : IsPt X m u v P) (hQ : IsPt X m (τ u) (τ v) Q)
    (hR : IsPt X m (τ' (τ u)) (τ' (τ v)) R) (f : X.Kˣ) (h1 : Mv X m τ s P Q 1) (h2 : Mv X m (τ.trans τ') (s' * s) P R f) :
    Mv X m τ' s' Q R f := by
  have E := mvEx Ω ε X m hm τ' s' hτ' _ _ Q hQ
  obtain ⟨f0, -, h0⟩ := E.1 R hR
  have hc := mvComp Ω ε X m hm τ τ' s s' hτ hτ' u v P Q R hP hQ hR 1 f0 h1 h0
  rw [map_one, one_pow, one_mul] at hc
  have hA := (admB Ω ε X).2.2.2.1 τ s τ' s' hτ hτ'
  exact (E.2.2.2 R hR f0 f h0).2 (((mvEx Ω ε X m hm _ _ hA u v P hP).2.2.2 R hR f0 f hc).1 h2)

private theorem mv_swap (X : Tower Ω ε) (m : ℕ) (hm : 0 < m) (τ ρ ρ' : X.K ≃+* X.K) (s : Ω ≃ₐ[ℚ] Ω) (hτ : admitted X τ 1)
    (hρ : admitted X ρ s) (hρ' : admitted X ρ' s) (hc : ∀ f, ρ' (τ f) = τ (ρ f)) (u v u' v' : X.K) (hu : ρ u = u') (hv : ρ v = v')
    (P P' Q Q' : Pt X m) (hP : IsPt X m u v P) (hP' : IsPt X m u' v' P') (hQ : IsPt X m (τ u) (τ v) Q)
    (hQ' : IsPt X m (τ u') (τ v') Q') (h1 : Mv X m τ 1 P Q 1) (h2 : Mv X m τ 1 P' Q' 1) (f : X.Kˣ)
    (h3 : Mv X m ρ s P P' f) : Mv X m ρ' s Q Q' (unU X τ f) := by
  subst hu hv
  have h4 := mvComp Ω ε X m hm ρ τ s 1 hρ hτ u v P P' Q' hP hP' hQ' f 1 h3 h2
  have hA := (admB Ω ε X).2.2.2.1 ρ s τ 1 hρ hτ
  have h5 : Mv X m (ρ.trans τ) (1 * s) P Q' (unU X τ f) := by
    refine ((mvEx Ω ε X m hm _ _ hA u v P hP).2.2.2 Q' hQ' _ _ h4).2 ?_
    rw [((lgB Ω ε X m hm).2.2.2.2.2.2 1 1).2.1, mul_one]
    rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hm) with h | h
    · subst h
      exact ⟨_, by rw [pow_one]; exact (mul_inv_cancel_left _ _).symm⟩
    · haveI : Fact (1 < m) := ⟨h⟩
      exact ⟨1, by rw [ZMod.val_one, pow_one, one_pow, mul_one]⟩
  have e : ρ.trans τ = τ.trans ρ' := RingEquiv.ext fun f => (hc f).symm
  rw [e, one_mul, ← mul_one s] at h5
  refine mv_cancel X m hm τ ρ' 1 s hτ hρ' u v P Q Q' hP hQ ?_ _ h1 h5
  rw [hc, hc]; exact hQ'

open Classical in
theorem pIsog : PIsog := by
  intro Ω _ _ _ ε X m c d k M _ _ hm hc hd hc6 hd6 hL t w' w ht hw' hw
  haveI : NeZero (k * M) := ⟨mul_ne_zero (NeZero.ne k) (NeZero.ne M)⟩
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hcM : Nat.Coprime c M := hL.2.1.coprime_mul_left_right
  have hdM : Nat.Coprime d M := hL.2.2.coprime_mul_left_right
  have RB := rowB Ω M hM
  have RB' := rowB Ω (k * M) hL.1
  have AB := admB Ω ε X
  have GD := galDg Ω ε X k hk
  have Sc := sgB Ω ε X c M hc hc6 hM hcM
  have Sd := sgB Ω ε X d M hd hd6 hM hdM
  have Sc' := sgB Ω ε X c (k * M) hc hc6 hL.1 hL.2.1
  have Sd' := sgB Ω ε X d (k * M) hd hd6 hL.1 hL.2.2
  let fib : Row M → Finset (Row (k * M)) := fun x => Finset.univ.filter (fun x' => x' 0 = up k M x 0 ∧ dn k M x' 1 = x 1)
  have mf : ∀ x x', x' ∈ fib x ↔ InF k M x x' := fun x x' => by simp only [fib, InF, Finset.mem_filter, Finset.mem_univ, true_and]
  have ne : ∀ x, (fib x).Nonempty := fun x => (inF_ex k M x).imp fun x' h => (mf x x').2 h
  have ok : ∀ x y, Ok x y → ∀ i ∈ fib x, ∀ j ∈ fib y, Ok i j := fun x y h i hi j hj =>
    ⟨inF_two k M x i ((mf _ _).1 hi) h.1, inF_two k M y j ((mf _ _).1 hj) h.2⟩
  have nzc : ∀ x y, Ok x y → ∀ i ∈ fib x, i ≠ 0 := fun x y h i hi =>
    (RB'.2.1 _ _ (ok x y h i hi _ (ne y).choose_spec)).1
  have nzd : ∀ x y, Ok x y → ∀ j ∈ fib y, j ≠ 0 := fun x y h j hj =>
    (RB'.2.1 _ _ (ok x y h _ (ne x).choose_spec j hj)).2.1
  have T' := fun (x y : Row M) (h : Ok x y) i (hi : i ∈ fib x) j (hj : j ∈ fib y) =>
    ht _ _ (Sc' i (nzc x y h i hi)).1 (Sd' j (nzd x y h j hj)).1
  have T := fun (x y : Row M) (h : Ok x y) => ht _ _ (Sc x (RB.2.1 x y h).1).1 (Sd y (RB.2.1 x y h).2.1).1
  have gg : ∀ (N : ℕ) (hN : 0 < N) (s : Ω ≃ₐ[ℚ] Ω) (x : Row N), gr N s (gr N s⁻¹ x) = x ∧ gr N s⁻¹ (gr N s x) = x :=
    fun N hN s x => by
      have H := (rowB Ω N hN).1
      exact ⟨by rw [← (H _ _ x).1, mul_inv_cancel, (H 1 1 x).2], by rw [← (H _ _ x).1, inv_mul_cancel, (H 1 1 x).2]⟩
  have bg : ∀ (s : Ω ≃ₐ[ℚ] Ω) (x : Row M), Set.BijOn (gr (k * M) s⁻¹) (fib x) (fib (gr M s⁻¹ x)) := fun s x => by
    refine Set.InvOn.bijOn (f' := gr (k * M) s) ⟨fun i _ => (gg _ hL.1 s i).1, fun i _ => (gg _ hL.1 s i).2⟩
      (fun i hi => (mf _ _).2 (inF_gr k M _ x i ((mf _ _).1 hi))) fun i hi => (mf _ _).2 ?_
    have := inF_gr k M s _ i ((mf _ _).1 hi)
    rwa [(gg M hM s x).1] at this
  have rr : ∀ (N : ℕ) (γ : SL(2, ℤ)) (x : Row N), rt (rt x γ) γ⁻¹ = x ∧ rt (rt x γ⁻¹) γ = x := fun N γ x =>
    ⟨by rw [rt_rt, mul_inv_cancel, rt_id], by rw [rt_rt, inv_mul_cancel, rt_id]⟩
  have br : ∀ γ γ' : SL(2, ℤ),
      !![(k : ℤ), 0; 0, 1] * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * !![(k : ℤ), 0; 0, 1] →
      ∀ x : Row M, Set.BijOn (fun i : Row (k * M) => rt i γ⁻¹) (fib (rt x γ') : Set (Row (k * M))) (fib x : Set (Row (k * M))) := fun γ γ' hg x => by
    refine Set.InvOn.bijOn (s := (fib (rt x γ') : Set (Row (k * M)))) (t := (fib x : Set (Row (k * M)))) (f' := fun i => rt i γ) ⟨fun i _ => (rr _ γ i).2, fun i _ => (rr _ γ i).1⟩
      (fun i hi => ?_) fun i hi => ?_
    · refine (mf _ _).2 ?_
      have := inF_rt k M _ _ (rel_inv k γ γ' hg) _ i ((mf _ _).1 hi)
      rwa [(rr M γ' x).1] at this
    · exact (mf (rt x γ') (rt i γ)).2 (inF_rt k M γ γ' hg x i ((mf x i).1 hi))
  have hR : ∀ x y : Row M, ∃ R : Pt X m, Ok x y →
      IsSum X m (fib x) (fib y) (fun i j => t (sg X c (k * M) i) (sg X d (k * M) j)) R ∧
      IsPt X m (slR X (dg k) (sg X c M x)) (slR X (dg k) (sg X d M y)) R := fun x y => by
    by_cases h : Ok x y
    · have S := sumB Ω ε X m hm _ _ (fib x) (fib y) (sg X c (k * M)) (sg X d (k * M)) _ (ne x) (ne y)
        fun i hi j hj => (T' x y h i hi j hj).1
      obtain ⟨R, hR⟩ := S.1
      have h2 := S.2 R hR
      have e1 := sgIsog Ω ε X c k M hc hc6 hL.2.1 x (RB.2.1 x y h).1
      have e2 := sgIsog Ω ε X d k M hd hd6 hL.2.2 y (RB.2.1 x y h).2.1
      refine ⟨R, fun _ => ⟨hR, ?_⟩⟩
      convert h2 using 1
      · exact e1.symm.trans (by congr)
      · exact e2.symm.trans (by congr)
    · exact ⟨t 1 1, fun h' => absurd h' h⟩
  choose R hR using hR
  have hQ : ∀ x y : Row M, ∃ Q : Pt X m, Ok x y →
      IsPt X m (slR X (dg k) (sg X c M x)) (slR X (dg k) (sg X d M y)) Q ∧
      Mv X m (slR X (dg k)) 1 (t (sg X c M x) (sg X d M y)) Q 1 := fun x y => by
    by_cases h : Ok x y
    · obtain ⟨Q, hQ⟩ := (mvEx Ω ε X m hm _ _ (AB.1 (dg k)) _ _ _ (T x y h).1).2.1
      exact ⟨Q, fun _ => hQ⟩
    · exact ⟨t 1 1, fun h' => absurd h' h⟩
  choose Q hQ using hQ
  obtain ⟨a, ha, hb⟩ := cmp Ω ε X m M hm hM (fun x => slR X (dg k) (sg X c M x)) (fun y => slR X (dg k) (sg X d M y)) R Q
    (fun s => pushH X k M (w' s)) (fun s x y => slU X (toGQ !![(k : ℤ), 0; 0, 1]) (w s x y))
    (fun x y h => ⟨(hR x y h).2, (hQ x y h).1⟩) (fun s x y h => by
      have h0 := (RB.2.1 x y h).2.2.1 s⁻¹
      have eu : X.gal s (sg X c M (gr M s⁻¹ x)) = sg X c M x := by
        rw [(Sc _ (RB.2.1 _ _ h0).1).2.2.1, (gg M hM s x).1]
      have ev : X.gal s (sg X d M (gr M s⁻¹ y)) = sg X d M y := by
        rw [(Sd _ (RB.2.1 _ _ h0).2.1).2.2.1, (gg M hM s y).1]
      refine ⟨(GD.1 s _).trans (congrArg _ eu), (GD.1 s _).trans (congrArg _ ev), ?_, ?_⟩
      · have := sumMv Ω ε X m hm _ _ _ (fib x) _ (fib y) (sg X c (k * M)) (sg X c (k * M)) (sg X d (k * M)) (sg X d (k * M))
          _ _ _ _ _ _ (X.gal s) s (AB.2.1 s) (ne _) (ne _) (bg s x) (bg s y)
          (fun i hi j hj => (T' _ _ h0 i hi j hj).1) (fun i hi j hj => (T' _ _ h i hi j hj).1)
          (fun i hi => by rw [(Sc' _ (nzc _ _ h0 _ ((bg s x).mapsTo hi))).2.2.1, (gg _ hL.1 s i).1])
          (fun i hi => by rw [(Sd' _ (nzd _ _ h0 _ ((bg s y).mapsTo hi))).2.2.1, (gg _ hL.1 s i).1])
          (hR _ _ h0).1 (hR _ _ h).1 (w' s) (fun i hi j hj => (hw' s i j (ok x y h i hi j hj)).2)
        convert this using 1
        simp only [pushH, fib]
      · exact mv_swap X m hm (slR X (dg k)) (X.gal s) (X.gal s) s (AB.1 _) (AB.2.1 s) (AB.2.1 s) (GD.1 s) _ _ _ _ eu ev
          _ _ _ _ (T _ _ h0).1 (T _ _ h).1 (hQ _ _ h0).1 (hQ _ _ h).1 (hQ _ _ h0).2 (hQ _ _ h).2 _ (hw s x y h).2)
  refine ⟨a, fun x y h => ⟨(hb x y h).1, fun γ γ' hg => ?_⟩, ha⟩
  have h1 := (RB.2.1 x y h).2.2.2 γ'
  have eu := (Sc x (RB.2.1 x y h).1).2.1 γ'
  have ev := (Sd y (RB.2.1 x y h).2.1).2.1 γ'
  refine (hb x y h).2 (slR X (ofSL γ)) _ _ (AB.1 _) h1 ((GD.2.1 γ γ' hg _).trans (congrArg _ eu))
    ((GD.2.1 γ γ' hg _).trans (congrArg _ ev)) ?_ ?_
  · have ei : ∀ i ∈ fib (rt x γ'), sg X c (k * M) i = X.sl (ofSL γ) (sg X c (k * M) (rt i γ⁻¹)) := fun i hi => by
      rw [(Sc' _ (nzc _ _ h _ ((br γ γ' hg x).mapsTo hi))).2.1, (rr _ γ i).2]
    have ej : ∀ i ∈ fib (rt y γ'), sg X d (k * M) i = X.sl (ofSL γ) (sg X d (k * M) (rt i γ⁻¹)) := fun i hi => by
      rw [(Sd' _ (nzd _ _ h _ ((br γ γ' hg y).mapsTo hi))).2.1, (rr _ γ i).2]
    have := sumMv Ω ε X m hm _ _ (fib x) _ (fib y) _ (sg X c (k * M)) (sg X c (k * M)) (sg X d (k * M)) (sg X d (k * M))
      _ _ _ _ _ _ (slR X (ofSL γ)) 1 (AB.1 _) (ne _) (ne _) (br γ γ' hg x) (br γ γ' hg y)
      (fun i hi j hj => (T' _ _ h i hi j hj).1) (fun i hi j hj => (T' _ _ h1 i hi j hj).1) ei ej
      (hR _ _ h).1 (hR _ _ h1).1 (fun _ _ => 1) (fun i hi j hj => by
        have := (T' _ _ h _ ((br γ γ' hg x).mapsTo hi) _ ((br γ γ' hg y).mapsTo hj)).2 γ
        rwa [← ei i hi, ← ej j hj] at this)
    simpa only [Finset.prod_const_one] using this
  · have h3 := (T x y h).2 γ'
    rw [eu, ev] at h3
    have := mv_swap X m hm (slR X (dg k)) (slR X (ofSL γ')) (slR X (ofSL γ)) 1 (AB.1 _) (AB.1 _) (AB.1 _) (GD.2.1 γ γ' hg)
      _ _ _ _ eu ev _ _ _ _ (T _ _ h).1 (T _ _ h1).1 (hQ _ _ h).1 (hQ _ _ h1).1 (hQ _ _ h).2 (hQ _ _ h1).2 _ h3
    rwa [map_one] at this

end UpperTheory.V.Z.Kato.Sym

end

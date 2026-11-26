module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.CanonicalLiftUnpacking
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StalkMapInjectiveOfFlat

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPosZsmulMemRange
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory

section CosetMin
variable {X : Type} [AddCommGroup X] {Bf : X →+ X →+ ℤ} {Q : X → ℤ}

theorem quad_add_zsmul (hs : ∀ x y, Bf x y = Bf y x) (hQ : ∀ x, 2 * Q x = Bf x x)
    (y w : X) (t : ℤ) : Q (y + t • w) = Q y + t * Bf y w + t ^ 2 * Q w := by
  have h1 := hQ (y + t • w)
  have h2 := hQ y
  have h3 := hQ w
  have h4 := hs w y
  simp only [map_add (f := _), map_zsmul, AddMonoidHom.add_apply, AddMonoidHom.smul_apply, smul_eq_mul] at h1
  have h5 : 2 * Q (y + t • w) = 2 * (Q y + t * Bf y w + t ^ 2 * Q w) := by
    linear_combination h1 - h2 + t * h4 - t ^ 2 * h3
  exact mul_left_cancel₀ two_ne_zero h5

theorem quad_zero (hQ : ∀ x, 2 * Q x = Bf x x) : Q 0 = 0 := by
  have h := hQ 0
  simp only [map_zero] at h
  omega

theorem quad_nonneg (hQ : ∀ x, 2 * Q x = Bf x x) (hp : ∀ x, x ≠ 0 → 1 ≤ Q x) (x : X) :
    0 ≤ Q x := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact (quad_zero hQ).ge
  · exact le_trans zero_le_one (hp x hx)

private lemma exists_int_shift_within_bounds (q B N a : ℤ) (hq : 0 < q) (hN : 0 < N) :
    ∃ m : ℤ, -(N * q) ≤ 2 * q * (a + N * m) + B ∧ 2 * q * (a + N * m) + B ≤ N * q := by
  have hD : 0 < 2 * q * N := by positivity
  have h1 := Int.mul_ediv_add_emod (2 * q * a + B + N * q) (2 * q * N)
  have h2 := Int.emod_nonneg (2 * q * a + B + N * q) hD.ne'
  have h3 := Int.emod_lt_of_pos (2 * q * a + B + N * q) hD
  refine ⟨-((2 * q * a + B + N * q) / (2 * q * N)), ?_, ?_⟩
  · linarith
  · linarith

theorem quad_round_step (hs : ∀ x y, Bf x y = Bf y x) (hQ : ∀ x, 2 * Q x = Bf x x)
    (y w : X) (hw : 0 ≤ Q w) (N : ℤ) (hN : 0 < N) (a : ℤ) :
    ∃ m : ℤ, 4 * Q (y + (a + N * m) • w) ≤ 4 * Q y + N ^ 2 * Q w := by
  have key : ∀ t : ℤ, Q (y + t • w) = Q y + t * Bf y w + t ^ 2 * Q w :=
    fun t => quad_add_zsmul hs hQ y w t
  rcases hw.lt_or_eq with hq | hq
  · obtain ⟨m, hm1, hm2⟩ := exists_int_shift_within_bounds (Q w) (Bf y w) N a hq hN
    refine ⟨m, ?_⟩
    rw [key]
    set t := a + N * m
    have hsq : (2 * Q w * t + Bf y w) ^ 2 ≤ (N * Q w) ^ 2 := by
      nlinarith
    have hmul : Q w * (4 * (t * Bf y w + t ^ 2 * Q w)) ≤ Q w * (N ^ 2 * Q w) := by
      nlinarith [sq_nonneg (Bf y w)]
    have := le_of_mul_le_mul_left hmul hq
    linarith
  · by_cases hB : 0 ≤ Bf y w
    · refine ⟨-|a|, ?_⟩
      rw [key, ← hq]
      have h1 : a + N * -|a| ≤ 0 := by
        nlinarith [le_abs_self a, abs_nonneg a]
      nlinarith
    · refine ⟨|a|, ?_⟩
      rw [key, ← hq]
      have h1 : 0 ≤ a + N * |a| := by
        nlinarith [neg_abs_le a, abs_nonneg a]
      nlinarith

theorem quad_round_sum (hs : ∀ x y, Bf x y = Bf y x) (hQ : ∀ x, 2 * Q x = Bf x x)
    {ι : Type} [DecidableEq ι] (v : ι → X) (hv : ∀ j, 0 ≤ Q (v j)) (N : ℤ) (hN : 0 < N)
    (a : ι → ℤ) (s : Finset ι) :
    ∃ m : ι → ℤ, 4 * Q (∑ j ∈ s, (a j + N * m j) • v j) ≤ N ^ 2 * ∑ j ∈ s, Q (v j) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp [quad_zero hQ]⟩
  | insert i s hi ih =>
    obtain ⟨m, hm⟩ := ih
    obtain ⟨m0, h0⟩ :=
      quad_round_step hs hQ (∑ j ∈ s, (a j + N * m j) • v j) (v i) (hv i) N hN (a i)
    refine ⟨Function.update m i m0, ?_⟩
    have hs' : ∑ j ∈ s, (a j + N * Function.update m i m0 j) • v j
        = ∑ j ∈ s, (a j + N * m j) • v j := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Function.update_of_ne (fun h : j = i => hi (h ▸ hj))]
    rw [Finset.sum_insert hi, Finset.sum_insert hi, hs', Function.update_self, add_comm]
    nlinarith

theorem exists_pos_zsmul_mem_range {n : ℕ} (b : Module.Basis (Fin n) ℤ X) (φ : X →+ X)
    (hφ : Function.Injective φ) (x : X) : ∃ N : ℤ, 0 < N ∧ ∃ y, φ y = N • x := by
  have : Module.Free ℤ X := Module.Free.of_basis b
  have : Module.Finite ℤ X := Module.Finite.of_basis b
  set f : X →ₗ[ℤ] X := φ.toIntLinearMap with hf
  set M := LinearMap.toMatrix b b f
  have hinj : Function.Injective f := by
    simpa [hf, AddMonoidHom.coe_toIntLinearMap] using hφ
  have hdet : M.det ≠ 0 := by
    intro h
    rw [LinearMap.det_toMatrix, LinearMap.det_eq_zero_iff_ker_ne_bot] at h
    exact h (LinearMap.ker_eq_bot.mpr hinj)
  have e : Matrix.toLin b b M = f := Matrix.toLin_toMatrix b b f
  have key : f.comp (Matrix.toLin b b M.adjugate) = M.det • LinearMap.id := by
    calc f.comp (Matrix.toLin b b M.adjugate)
        = (Matrix.toLin b b M).comp (Matrix.toLin b b M.adjugate) := by rw [e]
      _ = Matrix.toLin b b (M * M.adjugate) := (Matrix.toLin_mul b b b M M.adjugate).symm
      _ = M.det • LinearMap.id := by rw [Matrix.mul_adjugate, map_smul, Matrix.toLin_one]
  refine ⟨M.det * M.det, mul_self_pos.mpr hdet, M.det • Matrix.toLin b b M.adjugate x, ?_⟩
  have hx : f (Matrix.toLin b b M.adjugate x) = M.det • x := by
    have := congrArg (fun g => g x) key
    simpa using this
  have : φ (M.det • Matrix.toLin b b M.adjugate x) = M.det • f (Matrix.toLin b b M.adjugate x) := by
    rw [map_zsmul]; rfl
  rw [this, hx, smul_smul]

end CosetMin

theorem exists_coset_minimiser :
    ∀ (X : Type) [AddCommGroup X] (Bf : X →+ X →+ ℤ) (Q : X → ℤ), (∀ x y, Bf x y = Bf y x) → (∀ x, 2 * Q x = Bf x x) → (∀ x, x ≠ 0 → 1 ≤ Q x) → ∀ (n : ℕ) (b : Module.Basis (Fin n) ℤ X) (Cc : ℝ), (∀ j, (Q (b j) : ℝ) ≤ Cc) → ∀ (φ : X →+ X) (g : ℕ), 1 ≤ g → (∀ x y, Bf (φ x) (φ y) = g * Bf x y) → ∀ x : X, ∃ χ : X, ((Q (x + φ χ) : ℝ) ≤ g * n * Cc / 4) ∧ ∀ (q : ℕ) (z : X), (q : ℤ) * (q - 1) * Q (φ z) ≤ Q (x + φ χ + q • φ z) - Q (x + φ χ) := by
  classical
  intro X _ Bf Q hs hQ hp n b Cc hC φ g hg hφ x
  have hQφ : ∀ z, Q (φ z) = g * Q z := by
    intro z
    have h : 2 * Q (φ z) = 2 * (g * Q z) := by
      rw [hQ, hφ, ← hQ z]; ring
    exact mul_left_cancel₀ two_ne_zero h
  have hinj : Function.Injective φ := by
    intro u v huv
    by_contra hne
    have h0 : φ (u - v) = 0 := by rw [map_sub, huv, sub_self]
    have h1 := hp (u - v) (sub_ne_zero.mpr hne)
    have h2 := hQφ (u - v)
    rw [h0, quad_zero hQ] at h2
    have : (1 : ℤ) ≤ g := by exact_mod_cast hg
    nlinarith
  obtain ⟨N, hN, y, hy⟩ := exists_pos_zsmul_mem_range b φ hinj x
  obtain ⟨m, hm⟩ := quad_round_sum hs hQ (fun j => φ (b j))
    (fun j => quad_nonneg hQ hp _) N hN (fun j => b.repr y j) Finset.univ
  set χ0 : X := ∑ j, m j • b j with hχ0
  have hNx : N • (x + φ χ0) = ∑ j, (b.repr y j + N * m j) • φ (b j) := by
    have hyφ : φ y = ∑ j, b.repr y j • φ (b j) := by
      calc φ y = φ (∑ j, b.repr y j • b j) := by rw [b.sum_repr]
        _ = ∑ j, b.repr y j • φ (b j) := by rw [map_sum]; simp only [map_zsmul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [smul_add, ← hy, hyφ, hχ0, map_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, smul_smul, add_smul]
  have hsc : ∀ z : X, Q (N • z) = N ^ 2 * Q z := by
    intro z
    have := quad_add_zsmul hs hQ 0 z N
    simp only [zero_add, quad_zero hQ, map_zero, AddMonoidHom.zero_apply, mul_zero] at this
    linarith
  have hbound : 4 * Q (x + φ χ0) ≤ g * ∑ j, Q (b j) := by
    have h1 : 4 * Q (N • (x + φ χ0)) ≤ N ^ 2 * ∑ j, Q (φ (b j)) := by
      rw [hNx]; exact hm
    rw [hsc] at h1
    simp only [hQφ, ← Finset.mul_sum] at h1
    have hN2 : 0 < N ^ 2 := by positivity
    have h2 : N ^ 2 * (4 * Q (x + φ χ0)) ≤ N ^ 2 * (g * ∑ j, Q (b j)) := by linarith
    exact le_of_mul_le_mul_left h2 hN2
  have hex : ∃ k : ℕ, ∃ χ : X, Q (x + φ χ) = k :=
    ⟨(Q (x + φ χ0)).toNat, χ0, (Int.toNat_of_nonneg (quad_nonneg hQ hp _)).symm⟩
  obtain ⟨χ, hχ⟩ := Nat.find_spec hex
  have hmin : ∀ χ' : X, Q (x + φ χ) ≤ Q (x + φ χ') := by
    intro χ'
    rw [hχ]
    have := Nat.find_min' hex ⟨χ', (Int.toNat_of_nonneg (quad_nonneg hQ hp (x + φ χ'))).symm⟩
    calc (Nat.find hex : ℤ) ≤ ((Q (x + φ χ')).toNat : ℤ) := by exact_mod_cast this
      _ = Q (x + φ χ') := Int.toNat_of_nonneg (quad_nonneg hQ hp _)
  refine ⟨χ, ?_, ?_⟩
  · have h1 : 4 * Q (x + φ χ) ≤ g * ∑ j, Q (b j) := by linarith [hmin χ0]
    have h2 : (∑ j, (Q (b j) : ℝ)) ≤ n * Cc := by
      calc (∑ j, (Q (b j) : ℝ)) ≤ ∑ _j : Fin n, Cc := Finset.sum_le_sum fun j _ => hC j
        _ = n * Cc := by simp
    have h3 : 4 * (Q (x + φ χ) : ℝ) ≤ g * ∑ j, (Q (b j) : ℝ) := by exact_mod_cast h1
    have hg' : (0 : ℝ) ≤ g := by positivity
    nlinarith
  · intro q z
    have hz := hmin (χ + z)
    rw [map_add (f := _), ← add_assoc] at hz
    have e1 := quad_add_zsmul hs hQ (x + φ χ) (φ z) 1
    have e2 := quad_add_zsmul hs hQ (x + φ χ) (φ z) q
    rw [one_smul] at e1
    rw [natCast_zsmul] at e2
    rw [e2]
    have hq0 : (0 : ℤ) ≤ q := by positivity
    nlinarith

end GlobalTheory
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open GlobalTheory GlobalTheory.FamGerm
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS FB ev Dof)
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DepthBound

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V] [IsDomain V]
  [IsDiscreteValuationRing V] {F : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (y : Pt1 E H V F)

theorem exists_transl_smul (hL : Laws) (q : ℕ) (hq : 1 ≤ q) (c : 𝓞 E) (s : Fam y.P.D.toPre F q) :
    ∃ u : F, y.v u = 0 ∧ y.Transl q c s (u • s) := by
  let _ := H.starRing
  have hG := hL.globalFns
  obtain ⟨f, hf1, -, -, hf4, -⟩ := y.tors F q hq
  obtain ⟨p0, hp0y, -, hp0a⟩ := CanonicalLiftUnpacking.exists_zero_qk (D := y.P.D.toPre) (F := F) y.P.D.tau_bimult q
  have hf0 : f p0 = 1 := by
    have := hf4 p0 p0 p0 ⟨p0, by rw [hp0y, add_zero], hp0a, qk_equiv_refl y.P.D.tau_bimult p0⟩
    exact mul_eq_left.1 this.symm
  obtain ⟨w, hw⟩ : ∃ w : LB.Gen (LB.LinComb y.P.D.toPre.P.L (DegPre.lineφ y.P.D.toPre F p0.g.b)
      (DegPre.lineε q)), w.IsGen := ClosedPointWeilPower.gen_local_linComb y.P.D.toPre.P.L y.P.D.toPre.P.isLB _ _
  obtain ⟨ζ, hζ, hfin⟩ := finOrdExists_of_laws hL V y.P.D F q hq p0 w hw
  obtain ⟨Φ, hΦ⟩ := phiFun_of_globalFns hG V _ y.P.D F q hq p0 w hw
  obtain ⟨w₂, hw₂, hc⟩ := ThetaMul.phi_mul_core hG p0 p0 p0 (by rw [hp0y, add_zero]) hp0a w w hw hw
  obtain ⟨e, he⟩ := ThetaFinOrd.exists_scalar hG p0 w₂ w hw₂ hw (Φ * Φ : Module.End F (Fam y.P.D.toPre F q)) Φ
    (fun s => hc s _ _ ((hΦ _ _).2 rfl) ((hΦ _ _).2 rfl)) (fun s => (hΦ _ _).2 rfl)
  obtain ⟨M, hM, hU⟩ := (ThetaFinOrd.finOrd_iff p0 w ζ Φ hΦ).1 hfin
  have hsc : ∀ t, Φ t = e • t := fun t => by
    obtain ⟨M, rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
    have h1 := LinearMap.congr_fun hU t
    rw [pow_succ', Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply] at h1
    have h2 := LinearMap.congr_fun he (((ζ • Φ : Module.End F (Fam y.P.D.toPre F q)) ^ M) t)
    rw [Module.End.mul_apply, LinearMap.smul_apply] at h2
    rw [← h1, map_smul, h2, smul_comm]
  have hT : y.Transl q c s ((ζ * e) • s) := by
    refine ⟨p0, 1, w, ζ, Φ s, (hf1 _ _).2 hf0.symm, ?_, hw, hζ, hfin, (hΦ _ _).2 rfl, ?_⟩
    · have := y.P.oA.hom c
      exact MonObj.one_comp _
    · rw [DVR.isSmul_iff, hsc, smul_smul]
  by_cases hs : s = 0
  · refine ⟨1, y.v.map_one, ?_⟩
    rw [hs, smul_zero] at hT ⊢
    exact hT
  · refine ⟨ζ * e, ?_, hT⟩
    have h1 : (ζ • Φ : Module.End F (Fam y.P.D.toPre F q)) = (ζ * e) • 1 := LinearMap.ext fun t => by
      rw [LinearMap.smul_apply, hsc, smul_smul]; rfl
    have h2 := LinearMap.congr_fun hU s
    rw [h1, smul_pow, one_pow, LinearMap.smul_apply, Module.End.one_apply] at h2
    have h3 : (ζ * e) ^ M = 1 := by
      have : ((ζ * e) ^ M - 1) • s = 0 := by rw [sub_smul, h2, one_smul, sub_self]
      exact sub_eq_zero.1 ((smul_eq_zero.1 this).resolve_right hs)
    have h4 := congrArg y.v h3
    rw [y.v.map_pow, y.v.map_one] at h4
    induction hx : y.v (ζ * e) using WithTop.recTopCoe with
    | top =>
      obtain ⟨M, rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
      rw [hx, succ_nsmul, add_top] at h4
      exact h4
    | coe x =>
      rw [hx, ← WithTop.coe_nsmul, WithTop.coe_eq_zero, smul_eq_zero] at h4
      rw [h4.resolve_left (by omega)]; rfl

variable [CharZero F] [Algebra V F] [IsScalarTower V (FractionRing V) F]

omit [IsAlgClosed F] [CharZero F] in
theorem fO_comp_eq : (algebraMap (TWO.Ov y.v) F).comp (TWO.fO y.v y.hϖ y.hv) = algebraMap V F :=
  (IsScalarTower.algebraMap_eq V (FractionRing V) F).symm

theorem exists_jet_column (hL : Laws) (hG : FamGerm.GermExSt) (hJ : JetsSt) (hP : PullGermSt) (r : ℕ)
    (bs : Module.Basis (Fin r) ℤ y.P.D.toPre.X) (Cc M₀ : ℝ) (hred : y.Red r bs Cc M₀) (a : 𝓞 E) (N k n : ℕ)
    (hN : 1 ≤ N) (haa : letI := H.starRing; a * star a = (N : 𝓞 E)) (hn : 4 * n + 4 ≤ k) (hM : (n : ℝ) * M₀ < k)
    (h : PS F 2 y.d) (hh : letI := H.starRing; y.B.IsCanonGauge F h) (ω : PS V 1 y.d)
    (hω : letI := H.starRing; FB.toK F ω =
      FB.expS F (ev (n := 1) ![y.B.actK F a] (y.B.hL F h H.w0) - (N : F) • y.B.hL F h H.w0))
    (g : PS F 1 y.d) (hg : ∀ mo, 0 ≤ y.v (MvPowerSeries.coeff mo g)) :
    letI := H.starRing
    ∃ (s : Fam y.P.D.toPre F k) (s' t : Fam y.P.D.toPre F (k * N)) (c : F) (f : PS F 1 y.d) (r₀ : ℚ),
      (NuGe y.P.D y.Q F y.v k s 0 ∧ PullAl y.P.D F y.P.oD a k N s s' ∧ y.Transl (k * N) (star a) s' t ∧
        y.Germ (k * N) t (MvPowerSeries.C c * (ev (n := 1) ![y.B.actK F a] f * FB.toK F ω ^ k))) ∧
      y.v c = (r₀ : ℚ) ∧ (r₀ : ℝ) ≤ (n : ℝ) ^ 2 * Cc / k ∧
      ∀ mo : Fin 1 × Fin y.d →₀ ℕ, mo.degree ≤ n → MvPowerSeries.coeff mo f = MvPowerSeries.coeff mo g := by
  let _ := H.starRing
  have hk1 : 1 ≤ k := by omega
  have hkN : 1 ≤ k * N := Nat.mul_pos hk1 hN
  obtain ⟨G, hGm⟩ := hG E H V F y (k * N) hkN
  obtain ⟨π, -, hπ⟩ := PullLin.exists_pull_linearMap hL V y.P.D F (𝓞 E) y.P.oD H.w0 y.P.w0 a N k hN hk1 haa
  obtain ⟨gm, h0, h1, h2⟩ := hJ E H V F y r bs Cc M₀ hred k n hn hM
  obtain ⟨s, f, h3, h4, -, h6⟩ := h2 g hg
  obtain ⟨w, κ, hw, hpull⟩ := hP E H V F y a N k hN (by omega) haa h hh
  obtain ⟨τ, hτ⟩ := ExactTerm.exists_val_eq_of_nonneg y.hv h0
  obtain ⟨u, hu, hT⟩ := exists_transl_smul y hL (k * N) hkN (star a) (π (τ • s))
  have hnu : NuGe y.P.D y.Q F y.v k (τ • s) 0 := by
    have := NuGe.smul y.Q (s' := τ • s) hτ.ge (fun _ _ => rfl) h3
    rwa [neg_add_cancel] at this
  have hκ : y.v (algebraMap V F κ) = 0 := by
    rw [← fO_comp_eq y]
    exact TWO.v_unit y.v (Units.map (TWO.fO y.v y.hϖ y.hv : V →* TWO.Ov y.v) κ)
  refine ⟨τ • s, π (τ • s), _, u * τ * algebraMap V F κ, f, gm, ⟨hnu, (hπ _ _).2 rfl, hT, (hGm _ _).2 ?_⟩, ?_, h1, h6⟩
  · rw [map_smul, map_smul, map_smul, ← (hGm _ _).1 (hpull s _ f ((hπ _ _).2 rfl) h4), hw.trans hω.symm,
      MvPowerSeries.smul_eq_C_mul, MvPowerSeries.smul_eq_C_mul]
    simp only [map_mul, _root_.mul_assoc]
  · rw [y.v.map_mul, y.v.map_mul, hu, hτ, hκ, zero_add, add_zero]

theorem exists_eigen_column (hL : Laws) (hTW : TwistBCSpanStatement) (hVR : TWM.VRatioGtStatement) (hUU : UUStatement)
    (hG : FamGerm.GermExSt) (hV : GermValSt) (hE : EigGermSt) (Dw : Datum H)
    (I : letI := H.starRing; TateIso Dw F (TFK (R := V) F ⟶ y.P.A.A) (fun a g => g ≫ y.P.oA.act a)
      (fun n g g' c => WeilIs y.P.A.A y.P.A.L n g g' (unitOn c))) (r : ℕ)
    (bs : Module.Basis (Fin r) ℤ y.P.D.toPre.X) (Cc M₀ : ℝ) (hred : y.Red r bs Cc M₀) (a : 𝓞 E) (p k : ℕ)
    (hp : p.Prime) (hk : 4 ≤ k) (haa : letI := H.starRing; a * star a = (p : 𝓞 E))
    (hcop : letI := H.starRing; ∃ u u' : 𝓞 E, u * a + u' * star a = 1) (hpk : Nat.Coprime p k)
    (Λ : Type) (e : Λ → Fin y.d → TWO.Ov y.v) (yy α : Λ → TWO.Ov y.v)
    (hα : ∀ l, α l ∈ Ideal.span {(p : TWO.Ov y.v)})
    (he : letI := H.starRing; ∀ l, (dAct F y.B a).mulVec (fun i => (e l i : F)) = (α l : F) • fun i => (e l i : F))
    (hc : y.CharAt a p e yy)
    (h : PS F 2 y.d) (hh : letI := H.starRing; y.B.IsCanonGauge F h) (ω : PS V 1 y.d)
    (hω1 : MvPowerSeries.constantCoeff ω = 1)
    (hω : letI := H.starRing; FB.toK F ω =
      FB.expS F (ev (n := 1) ![y.B.actK F a] (y.B.hL F h H.w0) - (p : F) • y.B.hL F h H.w0)) :
    letI := H.starRing
    ∃ (s : Fam y.P.D.toPre F k) (s' t : Fam y.P.D.toPre F (k * p)) (c : F) (f : PS (TWO.Ov y.v) 1 y.d) (r₀ : ℚ),
      (NuGe y.P.D y.Q F y.v k s 0 ∧ PullAl y.P.D F y.P.oD a k p s s' ∧ y.Transl (k * p) (star a) s' t ∧
        y.Germ (k * p) t (MvPowerSeries.C c * (FB.toK F f * FB.toK F ω ^ k))) ∧
      y.v c = (r₀ : ℚ) ∧ (r₀ : ℝ) ≤ r * Cc / (4 * k) ∧ y.v (MvPowerSeries.constantCoeff (FB.toK F f)) = 0 ∧
      ∀ l mo, y.v (p : F) ≤ y.v (MvPowerSeries.coeff mo (Dof (y.B.FK F) (fun i => (e l i : F)) (FB.toK F f) -
        MvPowerSeries.C (yy l : F) * FB.toK F f)) := by
  let _ := H.starRing
  have hk1 : 1 ≤ k := by omega
  have hN : 1 ≤ p := hp.pos
  have hkN : 1 ≤ k * p := Nat.mul_pos hk1 hN
  have haa' : star a * a = (p : 𝓞 E) := by rw [mul_comm, haa]
  have hQa := QuadraticAlgebraValuation.qAl_of hL V y.ϖ y.hϖ y.P.D y.Q y.hQ (𝓞 E) y.P.oD a p haa haa'
  obtain ⟨G, hGm⟩ := hG E H V F y (k * p) hkN
  obtain ⟨π, -, hπ⟩ := PullLin.exists_pull_linearMap hL V y.P.D F (𝓞 E) y.P.oD H.w0 y.P.w0 a p k hN hk1 haa
  obtain ⟨pt, x, hpt, hx, hE'⟩ := hE E H V F y a p k hp hk haa Λ e yy α hα he hc Dw I hpk hcop
  obtain ⟨w, hw⟩ : ∃ w : LB.Gen (LB.LinComb y.P.D.toPre.P.L (DegPre.lineφ y.P.D.toPre F pt.g.b)
      (DegPre.lineε (k * p))), w.IsGen := ClosedPointWeilPower.gen_local_linComb y.P.D.toPre.P.L y.P.D.toPre.P.isLB _ _
  obtain ⟨ζ, hζ, hfin⟩ := finOrdExists_of_laws hL V y.P.D F _ hkN pt w hw
  obtain ⟨Φ, hΦ⟩ := phiFun_of_globalFns hL.globalFns V _ y.P.D F _ hkN pt w hw
  obtain ⟨χ₀, hχ1, hχ2⟩ := exists_coset_minimiser y.P.D.toPre.X (QForm.bHom y.hϖ y.P.D y.hQ) y.Q
    (fun _ _ => QForm.bOf_comm y.P.D _ _) (QForm.two_Q_eq y.hϖ y.P.D y.hQ)
    (fun _ hx => QForm.Q_pos y.hϖ y.P.D y.hQ hx) r bs Cc hred.2.2.1 (DistribSMul.toAddMonoidHom _ (star a)) p hN
    (fun x x' => by
      simp only [QForm.bHom_apply, QForm.bOf, DistribSMul.toAddMonoidHom_apply, ← smul_add, hQa]
      ring) pt.y
  simp only [DistribSMul.toAddMonoidHom_apply] at hχ1 hχ2
  obtain ⟨s, hs, hex⟩ := ExactTerm.main hL hTW hVR hUU V y.ϖ y.hϖ y.P.D y.Q y.hQ F y.v y.hv (𝓞 E) y.P.oD H.w0 y.P.w0
    a p k hN hk haa pt w hw ζ hζ hfin χ₀
  have hsm : Fam.IsSmul y.P.D.toPre F ζ (Φ (π s)) (ζ • Φ (π s)) := (DVR.isSmul_iff _ _ _).2 rfl
  obtain ⟨hnu, hsupp, c, hc0, hcv⟩ := hex (π s) (Φ (π s)) _ ((hπ _ _).2 rfl) ((hΦ _ _).2 rfl) hsm
  set t := ζ • Φ (π s) with ht
  set r₀ : ℚ := (y.Q (star a • χ₀ + pt.y) : ℚ) / (k * p) with hr₀
  have hkp : (0 : ℚ) < k * p := by exact_mod_cast hkN
  have hother : ∀ β, β ≠ star a • χ₀ + pt.y → VGe y.P.D F y.v (k * p) β (t.s β) (r₀ + 1 / (k * p)) := by
    intro β hβ
    by_cases hz : ∃ z, β = pt.y + star a • χ₀ + k • star a • z
    · obtain ⟨z, rfl⟩ := hz
      refine (hnu _).mono ?_
      have hz0 : star a • z ≠ 0 := fun h0 => hβ (by rw [h0, smul_zero, add_zero, add_comm])
      have h1 := QForm.Q_pos y.hϖ y.P.D y.hQ hz0
      have h2 := hχ2 k z
      have h3 : (1 : ℤ) ≤ (k : ℤ) * (k - 1) * y.Q (star a • z) := by
        have : (4 : ℤ) ≤ k := by exact_mod_cast hk
        have h5 : (1 : ℤ) ≤ (k : ℤ) * (k - 1) := by nlinarith
        nlinarith
      have h4 : (y.Q (star a • χ₀ + pt.y) : ℚ) + 1 ≤ y.Q (pt.y + star a • χ₀ + k • star a • z) := by
        rw [add_comm (star a • χ₀)]
        exact_mod_cast (by linarith : y.Q (pt.y + star a • χ₀) + 1 ≤ y.Q (pt.y + star a • χ₀ + k • star a • z))
      rw [hr₀, zero_add, ← add_div, Nat.cast_mul]
      exact div_le_div_of_nonneg_right h4 hkp.le
    · exact vge_of_zero (hsupp β fun z e => hz ⟨z, e⟩) _
  have hall : ∀ β, VGe y.P.D F y.v (k * p) β (t.s β) r₀ := fun β => by
    by_cases hβ : β = star a • χ₀ + pt.y
    · subst hβ
      refine (hnu _).mono (le_of_eq ?_)
      rw [hr₀, zero_add, Nat.cast_mul]
    · exact (hother β hβ).mono (le_add_of_nonneg_right (by positivity))
  obtain ⟨hV1, hV2⟩ := hV E H V F y (k * p) hkN t (G t) ((hGm _ _).2 rfl)
  have hV1' := hV1 r₀ hall
  have hV2' := hV2 _ c r₀ _ hc0 hcv (lt_add_of_pos_right _ (by positivity)) hother
  have hcne : c ≠ 0 := fun h0 => by
    rw [h0, y.v.map_zero] at hcv
    exact WithTop.top_ne_coe hcv
  have hci : y.v c⁻¹ = ((-r₀ : ℚ) : WithTop ℚ) := by
    rw [y.v.map_inv, hcv]; rfl
  let f₀ : PS (TWO.Ov y.v) 1 y.d := fun mo => ⟨c⁻¹ * MvPowerSeries.coeff mo (G t), by
    rw [TWO.mem_Ov, y.v.map_mul, hci]
    refine le_trans (le_of_eq ?_) (add_le_add le_rfl (hV1' mo))
    rw [← WithTop.coe_add, neg_add_cancel]; rfl⟩
  have hf₀ : FB.toK F f₀ = MvPowerSeries.C c⁻¹ * G t := by
    ext mo
    rw [MvPowerSeries.coeff_C_mul]; rfl
  obtain ⟨ω', hω'⟩ := (MvPowerSeries.isUnit_iff_constantCoeff.2 (hω1 ▸ isUnit_one) : IsUnit ω).exists_left_inv
  have hω'1 : MvPowerSeries.constantCoeff ω' = 1 := by
    have := congrArg MvPowerSeries.constantCoeff hω'
    rwa [map_mul, hω1, _root_.mul_one, map_one] at this
  have hmap : FB.toK F (MvPowerSeries.map (TWO.fO y.v y.hϖ y.hv) ω') = FB.toK F ω' := by
    ext mo
    simp only [MvPowerSeries.coeff_map, ← fO_comp_eq y, RingHom.comp_apply]
  have hsp : FB.toK F (f₀ * MvPowerSeries.map (TWO.fO y.v y.hϖ y.hv) ω' ^ k) =
      MvPowerSeries.C c⁻¹ * G t * FB.toK F ω' ^ k := by
    rw [← hf₀, ← hmap]
    exact (map_mul _ _ _).trans (congrArg _ (map_pow _ _ _))
  have hωω : FB.toK F ω' * FB.toK F ω = 1 := by
    rw [FB.toK, FB.toK, ← map_mul, hω', map_one]
  have hf : FB.toK F (f₀ * MvPowerSeries.map (TWO.fO y.v y.hϖ y.hv) ω' ^ k) * FB.toK F ω ^ k =
      MvPowerSeries.C c⁻¹ * G t := by
    rw [hsp, _root_.mul_assoc, ← mul_pow, hωω, one_pow, _root_.mul_one]
  refine ⟨s, π s, t, c, f₀ * MvPowerSeries.map (TWO.fO y.v y.hϖ y.hv) ω' ^ k, r₀, ⟨hs, (hπ _ _).2 rfl,
    ⟨pt, x, w, ζ, _, hpt, hx, hw, hζ, hfin, (hΦ _ _).2 rfl, hsm⟩, (hGm _ _).2 ?_⟩, hcv, ?_, ?_, ?_⟩
  · rw [hf, ← _root_.mul_assoc, ← map_mul, mul_inv_cancel₀ hcne, map_one, _root_.one_mul]
  · have hkR : (0 : ℝ) < k := by exact_mod_cast hk1
    have hpR : (0 : ℝ) < p := by exact_mod_cast hN
    rw [hr₀, add_comm (star a • χ₀)]
    push_cast
    rw [div_le_iff₀ (by positivity)]
    refine hχ1.trans (le_of_eq ?_)
    field_simp
  · rw [hsp]
    simp only [FB.toK, map_mul, map_pow, MvPowerSeries.constantCoeff_C, MvPowerSeries.constantCoeff_map, hω'1, map_one,
      one_pow, _root_.mul_one]
    rw [y.v.map_mul, hci, hV2', ← WithTop.coe_add, neg_add_cancel]; rfl
  · have hct : (c⁻¹ * ζ) • Φ (π s) = c⁻¹ • t := by rw [ht, smul_smul]
    refine hE' w hw s (π s) (Φ (π s)) (c⁻¹ * ζ) ((hπ _ _).2 rfl) ((hΦ _ _).2 rfl) (fun χ => ?_) h ω hh hω _ ?_
    · rw [hct]
      have := (hall χ).smul (s' := (c⁻¹ • t).s χ) hci.ge (fun _ => rfl)
      rwa [add_neg_cancel] at this
    · rw [hct, hf, hGm, G.map_smul c⁻¹ t, MvPowerSeries.smul_eq_C_mul]

end GlobalTheory.DepthBound

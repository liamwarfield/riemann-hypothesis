module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HermitianSpaceGeometricEstimate

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.NsmulOrbitBoundedOfCompact
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.InfinitePlaceNormContinuity
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum

section
variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private theorem row_last (i : Fin a) (hi : i.val + 1 = a) (b k : GA E a)
    (hb : b ∈ Reduction.adelicBorel (K := E) (n := a)) (d : Fin a → (Ad E)ˣ) (j : Fin a) :
    (b * Reduction.diagUnits a d * k : GA E a).val i j = (d i : Ad E) * (b.val i i * k.val i j) := by
  have hb' : (b.val : Matrix (Fin a) (Fin a) (Ad E)).IsUpperTriangular := hb
  rw [Units.val_mul, Units.val_mul, Reduction.coe_diagUnits, Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [Matrix.mul_diagonal]; ring
  · intro l _ hl
    have hlt : l < i := by
      have h1 := l.2
      have h2 : l.val ≠ i.val := fun h => hl (Fin.ext h)
      rw [Fin.lt_def]; omega
    rw [Matrix.mul_diagonal, hb' hlt, zero_mul, zero_mul]
  · simp

private theorem row_map {R : Type} [CommRing R] (f : Ad E →+* R) (γ : GL (Fin a) E) (g : GA E a) (i j : Fin a) :
    ((fun l => f (algebraMap E (Ad E) (γ.val i l))) ᵥ* (GeneralLinearGroup.map f g).val) j =
      f ((ratGL E a γ * g).val i j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Units.val_mul, Matrix.mul_apply, map_sum, Matrix.vecMul, dotProduct]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul]
  rfl

variable [_root_.NumberField.IsTotallyComplex E]

private theorem norm_pInf (x : Ad E) (w : InfinitePlace E) : ‖pInf E x w‖ = ‖x.1 w‖ :=
  (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) (x.1 w)

private theorem cont_pInf : Continuous (pInf E) :=
  continuous_pi fun w => (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
    ((continuous_apply w).comp continuous_fst)

end

theorem UpperTheory.infinite_place_norm_continuity :
    SiegelRow := by
  intro E _ _ _ a ha
  obtain ⟨Ω, C, N, hΩ, hB, h⟩ := UpperTheory.height_bound_of_quasiHeight_le E a
  let i : Fin a := ⟨a - 1, by omega⟩
  have hi : i.val + 1 = a := by simp only [i]; omega
  let Φ : GA E a × GA E a → Fin a → Ad E := fun p j => p.1.val i i * p.2.val i j
  have hΦ : ∀ j, Continuous fun p => Φ p j := fun j =>
    ((Units.continuous_val.comp continuous_fst).matrix_elem i i).mul
      ((Units.continuous_val.comp continuous_snd).matrix_elem i j)
  have hS := hΩ.prod (Reduction.isCompact_maxCompact (K := E) (n := a))
  have hF : Continuous fun (p : GA E a × GA E a) (j : Fin a) => pFin E (Φ p j) :=
    continuous_pi fun j => continuous_snd.comp (hΦ j)
  have hI : Continuous fun p : GA E a × GA E a => qf fun j => pInf E (Φ p j) :=
    continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun w _ =>
      ((continuous_apply w).comp (cont_pInf.comp (hΦ j))).norm.pow 2
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn hI.continuousOn
  refine ⟨_, C * M ^ N, N, hS.image hF, fun g => ?_⟩
  obtain ⟨γ, b, k, ρ, hρ, hb, hk, e, hq⟩ := h g
  have hrow : ∀ j, (ratGL E a γ * g.1).val i j =
      ((Reduction.posIdele (K := E) (ρ i) (hρ i) : (Ad E)ˣ) : Ad E) * Φ (b, k) j := fun j => by
    rw [e]
    exact row_last i hi b k (hB b hb) _ j
  refine ⟨γ.val i, fun h0 => ?_, ⟨(b, k), ⟨hb, hk⟩, funext fun j => ?_⟩, ?_⟩
  · have h1 := congrFun (congrFun γ.mul_inv i) i
    simp [Matrix.mul_apply, h0] at h1
  · refine Eq.trans ?_ (row_map (pFin E) γ g.1 i j).symm
    have h1 : pFin E ((Reduction.posIdele (K := E) (ρ i) (hρ i) : (Ad E)ˣ) : Ad E) = 1 :=
      IsDedekindDomain.FiniteAdeleRing.ext _ fun v => Reduction.posIdele_finite (K := E) (ρ i) (hρ i) v
    rw [hrow, map_mul, h1, one_mul]
  · have h1 : qf (pt (E := E) (a := a) g.1 (γ.val i)) = ρ i ^ 2 * qf fun j => pInf E (Φ (b, k) j) := by
      unfold qf
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      have h2 : pt (E := E) (a := a) g.1 (γ.val i) j = _ := row_map (pInf E) γ g.1 i j
      rw [h2, hrow, map_mul, Pi.mul_apply, norm_mul, norm_pInf, Reduction.norm_posIdele_infinite, mul_pow]
    have h3 : (qf fun j => pInf E (Φ (b, k) j)) ≤ M := (Real.le_norm_self _).trans (hM (b, k) ⟨hb, hk⟩)
    have h4 : 0 ≤ qht (E := E) (a := a) g.1 := Real.iInf_nonneg fun _ => (AutomorphicForm.height_pos _).le
    have h5 := (hq i).1 hi
    have h6 : 0 ≤ qht (E := E) (a := a) g.1 * ρ i ^ (2 * N) := mul_nonneg h4 (pow_nonneg (hρ i).le _)
    rw [h1, mul_pow, ← pow_mul, ← mul_assoc]
    exact mul_le_mul h5 (pow_le_pow_left₀ (qf_nonneg _) h3 N) (pow_nonneg (qf_nonneg _) N) (h6.trans h5)
end

open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum Filter Topology

private theorem nsmul_mem_of_compact {E : Type} [Field E] [NumberField E] {a : ℕ} (L : AddSubgroup (Fin a → Af E))
    (hL : IsOpen (L : Set (Fin a → Af E))) {T : Set (Fin a → Af E)} (hT : IsCompact T) :
    ∃ M : ℕ, 0 < M ∧ ∀ x ∈ T, M • x ∈ L := by
  have hc : Continuous fun p : Af E × (Fin a → Af E) => p.1 • p.2 := continuous_fst.smul continuous_snd
  have hev : ∀ᶠ r in 𝓝 (0 : Af E), ∀ x ∈ T, r • x ∈ L := by
    refine hT.eventually_forall_of_forall_eventually fun x _ => ?_
    refine hc.continuousAt.preimage_mem_nhds (hL.mem_nhds ?_)
    show (0 : Af E) • x ∈ L
    rw [zero_smul]
    exact L.zero_mem
  obtain ⟨n, hn⟩ := ((GlobalTheory.AdelicFactorial.tendsto_factorial_finiteAdele E).eventually hev).exists
  refine ⟨n.factorial, n.factorial_pos, fun x hx => ?_⟩
  have h := hn x hx
  rwa [Nat.cast_smul_eq_nsmul] at h

theorem UpperTheory.nsmul_orbit_bounded_of_compact :
    ShortRow := by
  intro E _ _ _ a ha L hL
  obtain ⟨T, C, N, hT, hrow⟩ := UpperTheory.infinite_place_norm_continuity E a ha
  obtain ⟨M, hM, hML⟩ := nsmul_mem_of_compact L hL.isOpen hT
  refine ⟨((M : ℝ) ^ 2) ^ N * C, N, fun g => ?_⟩
  obtain ⟨-, hq, hF⟩ := (UpperTheory.rationalPoint_retraction_exists_cmDatum E a ha).2.1 g
  obtain ⟨v, hv, hvT, hvC⟩ := hrow (retractOne g)
  change ptF (rt g) v ∈ T at hvT
  change qht (rt g) * qf (pt (rt g) v) ^ N ≤ C at hvC
  rw [hF] at hvT
  rw [hq] at hvC
  refine ⟨M • v, ?_, ?_, ?_⟩
  · show ptF g (M • v) ∈ L
    rw [map_nsmul]
    exact hML _ hvT
  · rw [← Nat.cast_smul_eq_nsmul E]
    exact smul_ne_zero (Nat.cast_ne_zero.2 hM.ne') hv
  · rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, (UpperTheory.geometric_side_quadraticForm_identity E a).2.2.2.1, mul_pow, mul_left_comm]
    exact mul_le_mul_of_nonneg_left hvC (by positivity)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.GeometricSideLowerBound
open UpperTheory.V.Lit.Geo

theorem UpperTheory.geometric_side_lower_bound :
    ThetaLow := by
  classical
  intro A V _ _ _ φ hs v hv
  have ht : 0 < ‖φ v‖ := norm_pos_iff.mpr hv
  set t := ‖φ v‖ with htdef
  have hn : ∀ k : ℕ, ‖φ (k • v)‖ = k * t := by
    intro k
    rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, norm_smul, Real.norm_natCast]
  have hinj : Function.Injective (fun k : ℕ => k • v) := by
    intro k l h
    have h1 : (k : ℝ) * t = l * t := by
      rw [← hn k, ← hn l]
      exact congrArg (fun x => ‖φ x‖) h
    exact_mod_cast mul_right_cancel₀ ht.ne' h1
  set n := ⌊1 / t⌋₊ with hndef
  have h1 : 1 / t < n + 1 := Nat.lt_floor_add_one _
  have h2 : (n : ℝ) ≤ 1 / t := Nat.floor_le (by positivity)
  have h3 : ∑ x ∈ (Finset.range (n + 1)).image (fun k : ℕ => k • v), Real.exp (-Real.pi * ‖φ x‖ ^ 2) ≤
      ∑' x, Real.exp (-Real.pi * ‖φ x‖ ^ 2) :=
    hs.sum_le_tsum _ (fun _ _ => (Real.exp_pos _).le)
  rw [Finset.sum_image (fun a _ b _ h => hinj h)] at h3
  have h4 : ∑ _k ∈ Finset.range (n + 1), Real.exp (-Real.pi) ≤
      ∑ k ∈ Finset.range (n + 1), Real.exp (-Real.pi * ‖φ (k • v)‖ ^ 2) := by
    refine Finset.sum_le_sum fun k hk => Real.exp_le_exp.mpr ?_
    have hk' : (k : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have h5 : (k : ℝ) * t ≤ 1 := by
      have := hk'.trans h2
      rwa [le_div_iff₀ ht] at this
    have h6 : 0 ≤ (k : ℝ) * t := by positivity
    have h7 : ((k : ℝ) * t) ^ 2 ≤ 1 := by nlinarith
    rw [hn]
    nlinarith [Real.pi_pos]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h4
  push_cast at h4
  have h8 : 1 ≤ t * (n + 1) := by
    rw [div_lt_iff₀ ht] at h1
    linarith
  have h9 := mul_le_mul_of_nonneg_left (h4.trans h3) ht.le
  have h10 := mul_le_mul_of_nonneg_right h8 (Real.exp_pos (-Real.pi)).le
  calc Real.exp (-Real.pi) = 1 * Real.exp (-Real.pi) := (one_mul _).symm
    _ ≤ t * (n + 1) * Real.exp (-Real.pi) := h10
    _ = t * ((n + 1) * Real.exp (-Real.pi)) := by ring
    _ ≤ _ := h9
end

open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor

private theorem pt_ne_zero {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (g : GA E a)
    (v : Fin a → E) (hv : v ≠ 0) : pt g v ≠ 0 := by
  intro h
  apply hv
  have h1 : vInf v ᵥ* (GeneralLinearGroup.map (pInf E) g).val = 0 := h
  have h2 : vInf v = 0 := by
    have := congrArg (fun x => x ᵥ* ((GeneralLinearGroup.map (pInf E) g)⁻¹).val) h1
    simpa only [Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one, Matrix.zero_vecMul] using this
  funext i
  have h3 : ((pInf E : Ad E →+* Cinf E).comp (algebraMap E (Ad E))) (v i) = 0 := congrFun h2 i
  exact (map_eq_zero_iff _ (RingHom.injective _)).1 h3

private theorem log_bound {H q T C : ℝ} {N : ℕ} (hH : 1 ≤ H) (hT : 1 ≤ T) (hq : 0 < q)
    (h1 : H * (q ^ 2) ^ N ≤ C) (h2 : Real.exp (-Real.pi) ≤ q * T) :
    Real.log H ≤ (|Real.log C| + 2 * N * Real.pi + 2 * N) * (1 + Real.log T) := by
  have hH0 : 0 < H := by linarith
  have hT0 : 0 < T := by linarith
  have hl : 0 ≤ Real.log T := Real.log_nonneg hT
  have a1 := Real.log_le_log (by positivity) h1
  rw [Real.log_mul hH0.ne' (by positivity), Real.log_pow, Real.log_pow] at a1
  have a2 := Real.log_le_log (Real.exp_pos _) h2
  rw [Real.log_exp, Real.log_mul hq.ne' hT0.ne'] at a2
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have a3 := mul_le_mul_of_nonneg_left a2 hN
  have a4 := le_abs_self (Real.log C)
  have a5 := mul_nonneg (abs_nonneg (Real.log C)) hl
  have a6 := mul_nonneg (mul_nonneg hN Real.pi_pos.le) hl
  push_cast at a1
  nlinarith

theorem UpperTheory.hermitian_space_point_log_estimate :
    LeFn := by
  intro E _ _ _ a ha L hL
  obtain ⟨C, N, hC⟩ := UpperTheory.nsmul_orbit_bounded_of_compact E a ha L hL
  obtain ⟨M, hM⟩ := UpperTheory.geometry_of_numbers_lattice_estimate E a ha L hL
  have hT := (UpperTheory.hermitian_space_geometric_estimate E a ha L hL).1
  refine ⟨|Real.log C| + 2 * N * Real.pi + 2 * N, fun g => ?_⟩
  obtain ⟨v, hv, hv0, hb⟩ := hC g
  let φ : lat L g →+ EuclideanSpace ℂ (Fin a × InfinitePlace E) :=
    (euc.toLinearMap.toAddMonoidHom.comp (pt (rt g))).comp (lat L g).subtype
  have hφ : ∀ x : lat L g, ‖φ x‖ ^ 2 = qf (pt (rt g) x.1) := fun x => norm_euc_sq _
  have hs : Summable fun x => Real.exp (-Real.pi * ‖φ x‖ ^ 2) := by
    have := ((hM g).2 1 1 one_pos le_rfl).1
    simpa only [hφ, one_mul] using this
  have hne : φ ⟨v, hv⟩ ≠ 0 := fun h => pt_ne_zero (rt g) v hv0 (euc.injective (h.trans (map_zero euc).symm))
  have hlow := UpperTheory.geometric_side_lower_bound (lat L g) _ φ hs ⟨v, hv⟩ hne
  have hTh : ∑' x, Real.exp (-Real.pi * ‖φ x‖ ^ 2) = Th L g := by
    simp only [hφ]
    rfl
  rw [hTh] at hlow
  refine log_bound ((UpperTheory.V.Lit.Geo.qhtFacts E a).1 g) (hT g).1 (norm_pos_iff.2 hne) ?_ hlow
  rw [hφ]
  exact hb

module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogDetCuspFramePlurisubharmonic
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicSublatticeGramDeterminant
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.UniLatA

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PlurisubharmonicCones.CuspsLocallyFiniteFamily
section -- merged from Development.WeilBound.CoreStatements.PlurisubharmonicCones.FiniteSat
open Matrix Filter Topology

namespace LevelTowerAlt.LocFin

variable {Λ : Type} [AddCommGroup Λ] {N m : ℕ}

noncomputable def coords (e : Module.Basis (Fin N) ℤ Λ) (v : Fin m → Λ) : Matrix (Fin m) (Fin N) ℤ :=
  Matrix.of fun i k => e.repr (v i) k

theorem repr_sum (e : Module.Basis (Fin N) ℤ Λ) (v : Fin m → Λ) (y : Fin m → ℤ) :
    (fun k => e.repr (∑ i, y i • v i) k) = (coords e v)ᵀ *ᵥ y := by
  funext k
  set_option synthInstance.maxHeartbeats 100000 in
    simp [coords, mulVec, dotProduct, map_sum, Finsupp.finsetSum_apply, mul_comm]

theorem eq_of_repr (e : Module.Basis (Fin N) ℤ Λ) {x y : Λ}
    (h : (fun k => e.repr x k) = fun k => e.repr y k) : x = y :=
  e.repr.injective (Finsupp.ext fun k => congrFun h k)

theorem det_ne_zero (e : Module.Basis (Fin N) ℤ Λ) {v : Fin m → Λ} (hv : LinearIndependent ℤ v) :
    (coords e v * (coords e v)ᵀ).det ≠ 0 := by
  intro h
  obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  have h1 : ((coords e v)ᵀ *ᵥ y) ⬝ᵥ ((coords e v)ᵀ *ᵥ y) = 0 := by
    have : ((coords e v)ᵀ *ᵥ y) ⬝ᵥ ((coords e v)ᵀ *ᵥ y) = y ⬝ᵥ ((coords e v * (coords e v)ᵀ) *ᵥ y) := by
      rw [← mulVec_mulVec, dotProduct_mulVec y, ← mulVec_transpose]
    rw [this, hy, dotProduct_zero]
  have h2 : (coords e v)ᵀ *ᵥ y = 0 := dotProduct_self_eq_zero.1 h1
  have h3 : ∑ i, y i • v i = 0 := by
    apply eq_of_repr e
    rw [repr_sum, h2]
    funext k
    simp
  exact hy0 (funext (Fintype.linearIndependent_iff.1 hv y h3))

theorem exists_proj (e : Module.Basis (Fin N) ℤ Λ) {v : Fin m → Λ} {A : Set Λ}
    (hA : ∀ x, x ∈ A ↔ ∃ y : Fin m → ℤ, ∑ i, y i • v i = x)
    (hsat : ∀ (x : Λ) (n : ℤ), n ≠ 0 → n • x ∈ A → x ∈ A)
    (hd : 0 < (coords e v * (coords e v)ᵀ).det) :
    ∃ Q : Matrix (Fin N) (Fin N) ℤ, (∀ i j, |Q i j| ≤ (coords e v * (coords e v)ᵀ).det) ∧
      A = {x | Q *ᵥ (fun k => e.repr x k) = (coords e v * (coords e v)ᵀ).det • fun k => e.repr x k} := by
  obtain ⟨B, hB⟩ : ∃ B, B = coords e v := ⟨_, rfl⟩
  have hr := repr_sum e v
  rw [← hB] at hd hr ⊢
  obtain ⟨d, hdd⟩ : ∃ d, d = (B * Bᵀ).det := ⟨_, rfl⟩
  rw [← hdd] at hd ⊢
  have hQB : Bᵀ * (B * Bᵀ).adjugate * B * Bᵀ = d • Bᵀ := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, adjugate_mul, ← hdd, Matrix.mul_smul, Matrix.mul_one]
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = Bᵀ * (B * Bᵀ).adjugate * B := ⟨_, rfl⟩
  have hQQ : Q * Q = d • Q := by
    calc Q * Q = (Bᵀ * (B * Bᵀ).adjugate * B * Bᵀ) * ((B * Bᵀ).adjugate * B) := by
          rw [hQ]; simp only [Matrix.mul_assoc]
      _ = d • Q := by rw [hQB, hQ, Matrix.smul_mul, Matrix.mul_assoc]
  have hQt : Qᵀ = Q := by
    rw [hQ, transpose_mul, transpose_mul, transpose_transpose, adjugate_transpose, transpose_mul,
      transpose_transpose, Matrix.mul_assoc]
  refine ⟨Q, fun i j => ?_, ?_⟩
  · have h1 : ∑ k, Q i k ^ 2 = d * Q i i := by
      have := congrFun (congrFun hQQ i) i
      rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul] at this
      rw [← this]
      refine Finset.sum_congr rfl fun k _ => ?_
      have : Q k i = Q i k := by
        have := congrFun (congrFun hQt i) k
        rwa [transpose_apply] at this
      rw [this, sq]
    have h2 : ∀ k, Q i k ^ 2 ≤ d * Q i i := fun k => h1 ▸
      Finset.single_le_sum (f := fun k => Q i k ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ k)
    have h3 := h2 i
    have h4 := h2 j
    have h5 : Q i i ≤ d := by
      by_contra hc
      push Not at hc
      nlinarith
    have h6 : Q i j ^ 2 ≤ d ^ 2 := by nlinarith
    exact abs_le_of_sq_le_sq h6 hd.le
  · ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hx
      obtain ⟨y, rfl⟩ := (hA x).1 hx
      rw [hr, mulVec_mulVec, hQ, hQB, smul_mulVec]
    · intro hx
      refine hsat x d hd.ne' ((hA _).2 ⟨((B * Bᵀ).adjugate * B) *ᵥ (fun k => e.repr x k), ?_⟩)
      apply eq_of_repr e
      rw [hr, mulVec_mulVec, ← Matrix.mul_assoc, ← hQ, hx]
      funext k
      simp

theorem finite_sat (e : Module.Basis (Fin N) ℤ Λ) (T : ℤ) :
    {A : Set Λ | ∃ (m : ℕ) (v : Fin m → Λ), (∀ x, x ∈ A ↔ ∃ y : Fin m → ℤ, ∑ i, y i • v i = x) ∧
      (∀ (x : Λ) (n : ℤ), n ≠ 0 → n • x ∈ A → x ∈ A) ∧ 0 < (coords e v * (coords e v)ᵀ).det ∧
      (coords e v * (coords e v)ᵀ).det ≤ T}.Finite := by
  have h1 : {Q : Fin N → Fin N → ℤ | ∀ i, Q i ∈ {r : Fin N → ℤ | ∀ j, r j ∈ Set.Icc (-T) T}}.Finite :=
    Set.Finite.pi' fun _ => Set.Finite.pi' fun _ => Set.finite_Icc _ _
  have h2 := ((Set.finite_Icc 0 T).prod h1).image
    (fun p : ℤ × (Fin N → Fin N → ℤ) =>
      {x : Λ | (Matrix.of p.2) *ᵥ (fun k => e.repr x k) = p.1 • fun k => e.repr x k})
  refine h2.subset ?_
  rintro A ⟨m, v, hA, hsat, hd, hT⟩
  obtain ⟨Q, hQ, hAQ⟩ := exists_proj e hA hsat hd
  refine ⟨(_, Matrix.of.symm Q), ⟨⟨hd.le, hT⟩, fun i j => ?_⟩, hAQ.symm⟩
  exact abs_le.1 ((hQ i j).trans hT)

theorem unif_pos (S0 : Matrix (Fin N) (Fin N) ℝ) (h0 : ∀ x : Fin N → ℝ, x ≠ 0 → 0 < x ⬝ᵥ S0 *ᵥ x) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ S in 𝓝 S0, ∀ x : Fin N → ℝ, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ S *ᵥ x := by
  have hc : Continuous fun z : (ℝ × Matrix (Fin N) (Fin N) ℝ) × (Fin N → ℝ) =>
      z.2 ⬝ᵥ z.1.2 *ᵥ z.2 - z.1.1 * (z.2 ⬝ᵥ z.2) :=
    (continuous_snd.dotProduct ((continuous_snd.comp continuous_fst).matrix_mulVec continuous_snd)).sub
      ((continuous_fst.comp continuous_fst).mul (continuous_snd.dotProduct continuous_snd))
  have h1 := (isCompact_sphere (0 : Fin N → ℝ) 1).eventually_forall_of_forall_eventually
    (x₀ := ((0 : ℝ), S0)) (P := fun p x => 0 < x ⬝ᵥ p.2 *ᵥ x - p.1 * (x ⬝ᵥ x)) (fun y hy => by
      have hy0 : y ≠ 0 := by
        rintro rfl
        simp at hy
      refine hc.continuousAt.eventually (lt_mem_nhds ?_)
      simpa using h0 y hy0)
  have h2 : ∀ᶠ c in 𝓝[>] (0 : ℝ), ∀ᶠ S in 𝓝 S0, ∀ x ∈ Metric.sphere (0 : Fin N → ℝ) 1,
      0 < x ⬝ᵥ S *ᵥ x - c * (x ⬝ᵥ x) := h1.curry_nhds.filter_mono nhdsWithin_le_nhds
  obtain ⟨c, hc1, hc0⟩ := (h2.and self_mem_nhdsWithin).exists
  refine ⟨c, hc0, hc1.mono fun S hS x => ?_⟩
  by_cases hx : x = 0
  · simp [hx]
  have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
  have h3 := hS (‖x‖⁻¹ • x) (by simp [norm_smul, hn.ne'])
  simp only [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at h3
  have h4 : 0 < ‖x‖⁻¹ * ‖x‖⁻¹ * (x ⬝ᵥ S *ᵥ x - c * (x ⬝ᵥ x)) := by linarith
  have h5 := (mul_pos_iff_of_pos_left (by positivity)).1 h4
  linarith

theorem det_bound (B : Matrix (Fin m) (Fin N) ℤ) (hB : (B * Bᵀ).det ≠ 0) (S : Matrix (Fin N) (Fin N) ℝ)
    (hS : Sᵀ = S) {c : ℝ} (hc : 0 < c) (h : ∀ x : Fin N → ℝ, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ S *ᵥ x) :
    0 < (B * Bᵀ).det ∧ c ^ m * ((B * Bᵀ).det : ℝ) ≤
      (B.map (Int.castRingHom ℝ) * S * (B.map (Int.castRingHom ℝ))ᵀ).det := by
  obtain ⟨Br, hBr⟩ : ∃ Br, Br = B.map (Int.castRingHom ℝ) := ⟨_, rfl⟩
  have hdet : ((B * Bᵀ).det : ℝ) = (Br * Brᵀ).det := by
    have := (Int.castRingHom ℝ).map_det (B * Bᵀ)
    rw [RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.transpose_map, ← hBr] at this
    exact this
  rw [← hBr]
  have hpsd : (Br * Brᵀ).PosSemidef := by
    have := posSemidef_self_mul_conjTranspose Br
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  have hne : (Br * Brᵀ).det ≠ 0 := by
    rw [← hdet]; exact_mod_cast hB
  have hpd : (Br * Brᵀ).PosDef :=
    hpsd.posDef_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hne))
  have hpos : 0 < (Br * Brᵀ).det := hpd.det_pos
  refine ⟨by rw [← hdet] at hpos; exact_mod_cast hpos, ?_⟩
  have h1 : (S - c • (1 : Matrix (Fin N) (Fin N) ℝ)).PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
    · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_sub, hS, transpose_smul, transpose_one]
    · have := h x
      simp only [star_trivial, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
      linarith
  have h2 := h1.mul_mul_conjTranspose_same Br
  rw [conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mul] at h2
  have h3 := ReciprocityTheory.L2DbarEstimates.Y.uniLat_det_le_of_sub (hpd.smul hc) h2
  rwa [det_smul, Fintype.card_fin, ← hdet] at h3

end LevelTowerAlt.LocFin
end

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace LevelTowerAlt.LocFin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

noncomputable def rg (R : RiemLat E g Λ) {N : ℕ} (e : Fin N → Λ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun k l => (R.ip (R.P (e k)) (R.P (e l))).re

theorem conj_ip (R : RiemLat E g Λ) (x y : Fin g → ℂ) : star (R.ip y x) = R.ip x y := by
  show star (x ⬝ᵥ R.Hm *ᵥ star y) = y ⬝ᵥ R.Hm *ᵥ star x
  rw [← star_dotProduct_star, star_mulVec, star_star, R.herm.eq, dotProduct_mulVec]

theorem rg_symm (R : RiemLat E g Λ) {N : ℕ} (e : Fin N → Λ) : (rg R e)ᵀ = rg R e := by
  ext k l
  simp only [rg, transpose_apply, of_apply]
  rw [← conj_ip R (R.P (e l)) (R.P (e k))]
  simp

theorem ip_sum (R : RiemLat E g Λ) {N : ℕ} (u : Fin N → Fin g → ℂ) (x y : Fin N → ℝ) :
    (R.ip (∑ k, (x k : ℂ) • u k) (∑ l, (y l : ℂ) • u l)).re = ∑ k, ∑ l, x k * (R.ip (u k) (u l)).re * y l := by
  have : R.ip (∑ k, (x k : ℂ) • u k) (∑ l, (y l : ℂ) • u l) =
      ∑ k, ∑ l, (x k : ℂ) * R.ip (u k) (u l) * (y l : ℂ) := by
    unfold RiemLat.ip
    rw [star_sum, mulVec_sum, dotProduct_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sum_dotProduct]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [star_smul, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
    rw [show star (x k : ℂ) = (x k : ℂ) from Complex.conj_ofReal _]
    ring
  rw [this, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp

theorem rg_pos (R : RiemLat E g Λ) {N : ℕ} (e : Module.Basis (Fin N) ℤ Λ) (x : Fin N → ℝ) (hx : x ≠ 0) :
    0 < x ⬝ᵥ rg R e *ᵥ x := by
  have h1 : x ⬝ᵥ rg R e *ᵥ x =
      (R.ip (∑ k, (x k : ℂ) • R.P (e k)) (∑ l, (x l : ℂ) • R.P (e l))).re := by
    rw [ip_sum]
    simp only [dotProduct, mulVec, rg, of_apply, Finset.mul_sum, mul_assoc]
  rw [h1]
  refine R.pos _ fun h0 => hx ?_
  funext k
  obtain ⟨w, hw⟩ := R.unimod.2 (e.coord k)
  have h2 : ∀ l, R.form (e l) w = -(if l = k then 1 else 0) := by
    intro l
    have ha := R.alt (e l + w)
    simp only [map_add (f := _), LinearMap.add_apply, R.alt] at ha
    have hb : R.form w (e l) = if l = k then 1 else 0 := by
      rw [hw]; simp [Finsupp.single_apply]
    linarith
  have h3 : ((∑ l, (x l : ℂ) • R.P (e l)) ⬝ᵥ R.Hm *ᵥ star (R.P w)).im = ∑ l, x l * (R.form (e l) w : ℝ) := by
    rw [sum_dotProduct, Complex.im_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_dotProduct, smul_eq_mul, Complex.im_ofReal_mul, R.im]
  rw [h0] at h3
  simp only [h2] at h3
  simpa using h3

theorem rg_coords (R : RiemLat E g Λ) {N m : ℕ} (e : Module.Basis (Fin N) ℤ Λ) (v : Fin m → Λ) :
    rg R v = (coords e v).map (Int.castRingHom ℝ) * rg R e * ((coords e v).map (Int.castRingHom ℝ))ᵀ := by
  have h : ∀ i, R.P (v i) = ∑ k, (((e.repr (v i) k : ℤ) : ℝ) : ℂ) • R.P (e k) := by
    intro i
    conv_lhs => rw [← e.sum_repr (v i)]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul, Complex.ofReal_intCast, Int.cast_smul_eq_zsmul]
  ext i j
  have : rg R v i j = ∑ k, ∑ l, ((e.repr (v i) k : ℤ) : ℝ) * (R.ip (R.P (e k)) (R.P (e l))).re *
      ((e.repr (v j) l : ℤ) : ℝ) := by
    rw [← ip_sum, ← h, ← h]
    rfl
  rw [this, Finset.sum_comm]
  simp only [Matrix.mul_apply, Finset.sum_mul, map_apply, transpose_apply, coords, rg, of_apply, eq_intCast]

end LevelTowerAlt.LocFin

open LevelTowerAlt.LocFin in
theorem LevelTowerAlt.cusps_locally_finite_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (n : ℕ) (U : Set (Fin n → ℂ)) (R : (Fin n → ℂ) → RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (m : ℕ), IsOpen U → IsHolFam U R → IsCMFam σ → (∀ t ∈ U, (R t).HasRank σ m) → ∀ t₀ ∈ U, ∃ (ε : ℝ) (F : Finset (Submodule (𝓞 E) Λ)), 0 < ε ∧ ∀ t ∈ U ∩ Metric.ball t₀ ε, (∀ I ∈ F, (R t).IsCusp I) ∧ ∀ I, (R t).IsCusp I → (R t).nz σ I ≤ 1 → I ∈ F := by
  intro E _ _ _ g Λ _ _ Ψ _ n U R σ m hU hHol hCM _ t₀ ht₀
  classical
  haveI := (R t₀).free
  haveI := (R t₀).fin
  let e := Module.finBasis ℤ Λ
  have hHm : ∀ i j, ContinuousOn (fun t => (R t).Hm i j) U := by
    intro i j
    obtain ⟨h1, h2⟩ := (GlobalTheory.T.holomorphic_family_smooth_entries E g Λ Ψ n U R hU hHol).1 i j
    have e : (fun t => (R t).Hm i j) = fun t => (((R t).Hm i j).re : ℂ) + (((R t).Hm i j).im : ℂ) * Complex.I := by
      funext t; exact (Complex.re_add_im _).symm
    rw [e]
    exact (Complex.continuous_ofReal.comp_continuousOn h1.continuousOn).add
      ((Complex.continuous_ofReal.comp_continuousOn h2.continuousOn).mul continuousOn_const)
  have hip : ∀ x y, ContinuousOn (fun t => (R t).ip ((R t).P x) ((R t).P y)) U := by
    intro x y
    unfold RiemLat.ip
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
    refine continuousOn_finsetSum _ fun i _ => ((continuousOn_pi.1 (hHol.2 y).continuousOn i)).mul ?_
    refine continuousOn_finsetSum _ fun j _ => (hHm i j).mul ?_
    exact (continuous_star.comp_continuousOn (continuousOn_pi.1 (hHol.2 x).continuousOn j))
  have hS : ContinuousOn (fun t => rg (R t) e) U :=
    continuousOn_pi.2 fun k => continuousOn_pi.2 fun l =>
      Complex.continuous_re.comp_continuousOn (hip (e k) (e l))
  obtain ⟨c, hc, hev⟩ := unif_pos (rg (R t₀) e) (rg_pos (R t₀) e)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1
    ((hS.continuousAt (hU.mem_nhds ht₀)).eventually hev)
  obtain ⟨Dk, hDk⟩ : ∃ Dk : ℝ, Dk = |(discr E : ℝ)| ^ (1 / (Module.finrank ℚ E : ℝ)) := ⟨_, rfl⟩
  have hD0 : 0 ≤ Dk := hDk ▸ Real.rpow_nonneg (abs_nonneg _) _
  have hfin := (finite_sat e ⌈(max 1 (Dk / c)) ^ Module.finrank ℤ Λ⌉).preimage
    (SetLike.coe_injective (A := Submodule (𝓞 E) Λ)).injOn
  have hcusp : ∀ t ∈ U, ∀ t' ∈ U, ∀ I, (R t).IsCusp I → (R t').IsCusp I := fun t ht t' ht' I h =>
    ⟨h.1, h.2.1, hHol.1 t ht t' ht' ▸ h.2.2⟩
  refine ⟨ε, hfin.toFinset.filter fun I => (R t₀).IsCusp I, hε, fun t ht =>
    ⟨fun I hI => hcusp t₀ ht₀ t ht.1 I (Finset.mem_filter.1 hI).2, fun I hI hnz => ?_⟩⟩
  refine Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 ?_, hcusp t ht.1 t₀ ht₀ I hI⟩
  have hinj : Function.Injective (I.subtype.toAddMonoidHom.toIntLinearMap) := Subtype.val_injective
  haveI : Module.Finite ℤ I := Module.Finite.of_injective _ hinj
  haveI : Module.IsTorsionFree ℤ I := Function.Injective.moduleIsTorsionFree _ hinj (fun _ _ => map_smul _ _ _)
  haveI : Module.Free ℤ I := Module.free_of_finite_type_torsion_free'
  let b := Module.finBasis ℤ I
  have hli : LinearIndependent ℤ fun i => (b i : Λ) :=
    b.linearIndependent.map' (I.subtype.toAddMonoidHom.toIntLinearMap) (LinearMap.ker_eq_bot.2 hinj)
  obtain ⟨hm, hdet⟩ := GlobalTheory.T.isotropic_sublattice_gram_determinant E g Λ Ψ (R t) σ I hCM hI.2.2 hI.1 _ b
  obtain ⟨⟨r, v, hv⟩, hN⟩ := GlobalTheory.T.isotropic_sublattice_covolume_positive E g Λ Ψ (R t) σ I hCM hI.2.2 hI.1
  have hnz0 := (hN r v hv).2.1
  obtain ⟨hd0, hd1⟩ := det_bound (coords e fun i => (b i : Λ)) (det_ne_zero e hli) (rg (R t) e)
    (rg_symm _ _) hc (hball t ht.2)
  rw [← rg_coords] at hd1
  have hle : Module.finrank ℤ I ≤ Module.finrank ℤ Λ := by
    simpa using hli.fintype_card_le_finrank
  refine ⟨_, fun i => (b i : Λ), fun x => ⟨fun hx => ⟨fun i => b.repr ⟨x, hx⟩ i, ?_⟩, ?_⟩,
    fun x k hk hx => hI.2.1 x k hk hx, hd0, ?_⟩
  · have := congrArg (I.subtype.toAddMonoidHom.toIntLinearMap) (b.sum_repr ⟨x, hx⟩)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at this
    simpa using this
  · rintro ⟨y, rfl⟩
    exact I.sum_mem fun i _ => zsmul_mem (b i).2 _
  · have h1 : (rg (R t) fun i => (b i : Λ)).det ≤ Dk ^ Module.finrank ℤ I := by
      refine hdet.le.trans ?_
      rw [← hDk, hm, mul_assoc, mul_comm 2, pow_mul Dk _ 2]
      have h0 : 0 ≤ Dk ^ (Fintype.card Ψ * Module.finrank (𝓞 E) I) := pow_nonneg hD0 _
      exact pow_le_pow_left₀ (mul_nonneg hnz0.le h0) (mul_le_of_le_one_left h0 hnz) 2
    have h2 : (((coords e fun i => (b i : Λ)) * (coords e fun i => (b i : Λ))ᵀ).det : ℝ) ≤
        (Dk / c) ^ Module.finrank ℤ I := by
      rw [div_pow, le_div_iff₀ (pow_pos hc _), mul_comm]
      exact hd1.trans h1
    have h3 : (Dk / c) ^ Module.finrank ℤ I ≤ (max 1 (Dk / c)) ^ Module.finrank ℤ Λ :=
      (pow_le_pow_left₀ (div_nonneg hD0 hc.le) (le_max_right _ _) _).trans
        (pow_le_pow_right₀ (le_max_left _ _) hle)
    exact_mod_cast (h2.trans h3).trans (Int.le_ceil _)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.CuspSubmodulesLocallyFinite
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.CuspSubmodulesLocallyFinite
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.cusp_submodules_locally_finite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (n : ℕ) (U : Set (Fin n → ℂ)) (R : (Fin n → ℂ) → RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (m : ℕ), IsOpen U → IsHolFam U R → IsCMFam σ → (∀ t ∈ U, (R t).HasRank σ m) → ∀ t₀ ∈ U, ∃ (ε : ℝ) (F : Finset (Submodule (𝓞 E) Λ)), 0 < ε ∧ ∀ t ∈ U ∩ Metric.ball t₀ ε, (∀ I ∈ F, (R t).IsCusp I) ∧ ∀ I, (R t).IsCusp I → (R t).nz σ I ≤ 1 → I ∈ F := by
  first | exact @LevelTowerAlt.cusps_locally_finite_family | exact LevelTowerAlt.cusps_locally_finite_family
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.CuspSubmodulesLocallyFiniteStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_submodules_locally_finite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (n : ℕ) (U : Set (Fin n → ℂ)) (R : (Fin n → ℂ) → RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (m : ℕ), IsOpen U → IsHolFam U R → IsCMFam σ → (∀ t ∈ U, (R t).HasRank σ m) → ∀ t₀ ∈ U, ∃ (ε : ℝ) (F : Finset (Submodule (𝓞 E) Λ)), 0 < ε ∧ ∀ t ∈ U ∩ Metric.ball t₀ ε, (∀ I ∈ F, (R t).IsCusp I) ∧ ∀ I, (R t).IsCusp I → (R t).nz σ I ≤ 1 → I ∈ F := by
  first | exact @GlobalTheory.CompanionTheory.Relay.cusp_submodules_locally_finite | exact GlobalTheory.CompanionTheory.Relay.cusp_submodules_locally_finite | (intros; apply GlobalTheory.CompanionTheory.Relay.cusp_submodules_locally_finite <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogDetEigenFramePlurisubharmonic
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Corr

open ReciprocityTheory.AnForm.A (IsPsh)

theorem psh_add {d : ℕ} {U : Set (Fin d → ℂ)} {φ ψ : (Fin d → ℂ) → ℝ} (hφ : IsPsh U φ) (hψ : IsPsh U ψ) :
    IsPsh U (fun z => φ z + ψ z) := by
  refine ⟨hφ.1.add hψ.1, fun z w hd => ?_⟩
  obtain ⟨h1, h2⟩ := hφ.2 z w hd
  obtain ⟨h3, h4⟩ := hψ.2 z w hd
  refine ⟨h1.add h3, ?_⟩
  rw [Real.circleAverage_fun_add h1 h3]
  exact add_le_add h2 h4

theorem psh_const {d : ℕ} (U : Set (Fin d → ℂ)) (c : ℝ) : IsPsh U (fun _ => c) := by
  refine ⟨upperSemicontinuousOn_const, fun z w _ => ⟨circleIntegrable_const c 0 1, ?_⟩⟩
  rw [Real.circleAverage_const]

theorem psh_sum {d : ℕ} {U : Set (Fin d → ℂ)} {ι : Type} (S : Finset ι) {f : ι → (Fin d → ℂ) → ℝ}
    (h : ∀ i ∈ S, IsPsh U (f i)) : IsPsh U (fun z => ∑ i ∈ S, f i z) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using psh_const U 0
  | insert a S ha ih =>
    simp only [Finset.sum_insert ha]
    exact psh_add (h a (Finset.mem_insert_self a S)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem psh_congr {d : ℕ} {U : Set (Fin d → ℂ)} {φ ψ : (Fin d → ℂ) → ℝ} (h : ∀ z ∈ U, φ z = ψ z)
    (hφ : IsPsh U φ) : IsPsh U ψ := by
  refine ⟨fun z hz y hy => ?_, fun z w hd => ?_⟩
  · have h1 : ∀ᶠ x in nhdsWithin z U, φ x < y := hφ.1 z hz y (by show φ z < y; rw [h z hz]; exact hy)
    filter_upwards [h1, self_mem_nhdsWithin] with x hx hxU
    rwa [← h x hxU]
  · obtain ⟨h1, h2⟩ := hφ.2 z w hd
    have e : ∀ θ : ℝ, φ (z + circleMap 0 1 θ • w) = ψ (z + circleMap 0 1 θ • w) := fun θ =>
      h _ (hd _ (by simp))
    have hz : z ∈ U := by simpa using hd 0 (by simp)
    refine ⟨?_, ?_⟩
    · unfold CircleIntegrable at h1 ⊢
      simpa only [e] using h1
    · rw [← h z hz]
      simpa only [Real.circleAverage_def, e] using h2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
  {Ψ : Type} [Fintype Ψ]

noncomputable def term (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (F : Finset (Submodule (𝓞 E) Λ)) :
    Option F → ℝ
  | none => 0
  | some I => -Real.log (R.nz σ I.1)

theorem cuspW_eq (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (F : Finset (Submodule (𝓞 E) Λ))
    (h1 : ∀ I ∈ F, R.IsCusp I) (h2 : ∀ I, R.IsCusp I → R.nz σ I ≤ 1 → I ∈ F) :
    R.cuspW σ = Finset.univ.sup' Finset.univ_nonempty (term R σ F) := by
  have h0 : 0 ≤ Finset.univ.sup' Finset.univ_nonempty (term R σ F) :=
    Finset.le_sup' (term R σ F) (Finset.mem_univ none)
  have hb : ∀ x ∈ {x | ∃ I, R.IsCusp I ∧ x = -Real.log (R.nz σ I)},
      x ≤ Finset.univ.sup' Finset.univ_nonempty (term R σ F) := by
    rintro x ⟨I, hI, rfl⟩
    by_cases h : R.nz σ I ≤ 1
    · exact Finset.le_sup' (term R σ F) (Finset.mem_univ (some ⟨I, h2 I hI h⟩))
    · have := Real.log_nonneg (not_le.1 h).le
      linarith
  unfold RiemLat.cuspW
  refine le_antisymm (max_le h0 (Real.sSup_le hb h0)) (Finset.sup'_le _ _ fun o _ => ?_)
  cases o with
  | none => exact le_max_left _ _
  | some I => exact le_max_of_le_right (le_csSup ⟨_, hb⟩ ⟨I.1, h1 I.1 I.2, rfl⟩)

theorem add_sup {ι : Type} [Fintype ι] [Nonempty ι] (a : ℝ) (f : ι → ℝ) :
    Finset.univ.sup' Finset.univ_nonempty (fun j => a + f j) = a + Finset.univ.sup' Finset.univ_nonempty f := by
  refine le_antisymm (Finset.sup'_le _ _ fun j hj => ?_) ?_
  · have := Finset.le_sup' f hj
    linarith
  · obtain ⟨j, hj, e⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := ι)) f
    rw [e]
    exact Finset.le_sup' (fun j => a + f j) hj

end GlobalTheory.CompanionTheory.Ar.Cusp.Corr

open GlobalTheory.CompanionTheory.Ar.Cusp.Corr in
theorem _root_.GlobalTheory.CompanionTheory.Relay.log_det_eigen_frame_plurisubharmonic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (n : ℕ) (U : Set (Fin n → ℂ)) (R : (Fin n → ℂ) → RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (m : ℕ) (b : Ψ → Fin m → (Fin n → ℂ) → Fin g → ℂ), IsOpen U → IsHolFam U R → IsCMFam σ → IsEigFrames U (fun t => (R t).B) σ b → ReciprocityTheory.AnForm.A.IsPsh U (fun t => (R t).logDet (fun τ i => b τ i t)) ∧ ReciprocityTheory.AnForm.A.IsPsh U (fun t => (R t).logDet (fun τ i => b τ i t) + (R t).cuspW σ) ∧ ContinuousOn (fun t => (R t).cuspW σ) U := by
  intro E _ _ _ g Λ _ _ Ψ _ n U R σ m b hU hH hσ hb
  have hrank : ∀ t ∈ U, (R t).HasRank σ m := by
    intro t ht τ
    have h := hb.2 t ht τ
    have e : Module.finrank ℂ (Submodule.span ℂ (Set.range fun i => b τ i t)) = m := by
      rw [finrank_span_eq_card h.1, Fintype.card_fin]
    rw [h.2] at e
    exact e
  have hL : ReciprocityTheory.AnForm.A.IsPsh U (fun t => (R t).logDet (fun τ i => b τ i t)) :=
    psh_sum Finset.univ fun τ _ =>
      (GlobalTheory.CompanionTheory.Relay.holomorphic_family_smooth_entries E g Λ Ψ n U R hU hH).2.2 m (b τ) (hb.1 τ) (fun t ht => (hb.2 t ht τ).1)
  have hloc : ∀ t₀ ∈ U, ∃ W : Set (Fin n → ℂ), IsOpen W ∧ t₀ ∈ W ∧
      ReciprocityTheory.AnForm.A.IsPsh (U ∩ W) (fun t => (R t).logDet (fun τ i => b τ i t) + (R t).cuspW σ) ∧
      ContinuousOn (fun t => (R t).cuspW σ) (U ∩ W) := by
    intro t₀ ht₀
    obtain ⟨ε, F, hε, hF⟩ := GlobalTheory.T.cusp_submodules_locally_finite E g Λ Ψ n U R σ m hU hH hσ hrank t₀ ht₀
    have hVo : IsOpen (U ∩ Metric.ball t₀ ε) := hU.inter Metric.isOpen_ball
    have hVU : U ∩ Metric.ball t₀ ε ⊆ U := Set.inter_subset_left
    have hphi := fun I : F => GlobalTheory.T.log_det_cusp_frame_plurisubharmonic E g Λ Ψ n (U ∩ Metric.ball t₀ ε) R σ m b I.1 hVo
      ⟨fun t ht t' ht' => hH.1 t ht.1 t' ht'.1, fun x => (hH.2 x).mono hVU⟩ hσ
      ⟨fun τ i => (hb.1 τ i).mono hVU, fun t ht => hb.2 t ht.1⟩ (fun t ht => (hF t ht).1 I.1 I.2)
    have heq : ∀ t ∈ U ∩ Metric.ball t₀ ε,
        (R t).cuspW σ = Finset.univ.sup' Finset.univ_nonempty (term (R t) σ F) :=
      fun t ht => cuspW_eq (R t) σ F (hF t ht).1 (hF t ht).2
    refine ⟨Metric.ball t₀ ε, Metric.isOpen_ball, Metric.mem_ball_self hε, ?_, ?_⟩
    · have hs := ReciprocityTheory.AnForm.A.isPsh_sup_thm n (Option F) (U ∩ Metric.ball t₀ ε)
        (fun o t => (R t).logDet (fun τ i => b τ i t) + term (R t) σ F o) hVo (fun o => by
          cases o with
          | none =>
            exact psh_congr (fun z _ => (add_zero _).symm) (GlobalTheory.CompanionTheory.AnForm.PshLocal.isPsh_mono hVU hL)
          | some I => exact psh_congr (fun z _ => sub_eq_add_neg _ _) (hphi I).1)
      refine psh_congr (fun t ht => ?_) hs
      rw [heq t ht]
      exact add_sup _ _
    · have hc : ∀ o : Option F, ContinuousOn (fun t => term (R t) σ F o) (U ∩ Metric.ball t₀ ε) := by
        intro o
        cases o with
        | none => exact continuousOn_const
        | some I =>
          refine ContinuousOn.neg ((hphi I).2.log fun t ht => ?_)
          have hI := (hF t ht).1 I.1 I.2
          obtain ⟨⟨r, v, hv⟩, h2⟩ := GlobalTheory.T.isotropic_sublattice_covolume_positive E g Λ Ψ (R t) σ I.1 hσ hI.2.2 hI.1
          exact (h2 r v hv).2.1.ne'
      have hs : ContinuousOn (fun t => Finset.univ.sup' Finset.univ_nonempty (fun o => term (R t) σ F o))
          (U ∩ Metric.ball t₀ ε) :=
        ContinuousOn.finset_sup'_apply Finset.univ_nonempty fun o _ => hc o
      exact hs.congr heq
  refine ⟨hL, GlobalTheory.CompanionTheory.AnForm.PshLocal.isPsh_of_locally n U _ hU fun z hz => ?_,
    continuousOn_of_locally_continuousOn fun z hz => ?_⟩
  · obtain ⟨W, h1, h2, h3, -⟩ := hloc z hz
    exact ⟨U ∩ W, hU.inter h1, ⟨hz, h2⟩, h3⟩
  · obtain ⟨W, h1, h2, -, h4⟩ := hloc z hz
    exact ⟨W, h1, h2, h4⟩
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogDetEigenFramePlurisubharmonicStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_det_eigen_frame_plurisubharmonic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (n : ℕ) (U : Set (Fin n → ℂ)) (R : (Fin n → ℂ) → RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (m : ℕ) (b : Ψ → Fin m → (Fin n → ℂ) → Fin g → ℂ), IsOpen U → IsHolFam U R → IsCMFam σ → IsEigFrames U (fun t => (R t).B) σ b → ReciprocityTheory.AnForm.A.IsPsh U (fun t => (R t).logDet (fun τ i => b τ i t)) ∧ ReciprocityTheory.AnForm.A.IsPsh U (fun t => (R t).logDet (fun τ i => b τ i t) + (R t).cuspW σ) ∧ ContinuousOn (fun t => (R t).cuspW σ) U := by
  first | exact @GlobalTheory.CompanionTheory.Relay.log_det_eigen_frame_plurisubharmonic | exact GlobalTheory.CompanionTheory.Relay.log_det_eigen_frame_plurisubharmonic | (intros; apply GlobalTheory.CompanionTheory.Relay.log_det_eigen_frame_plurisubharmonic <;> assumption)
end

module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.HeckeDoubleCosets.PHeckeFormal

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.HeckeDoubleCosets.Assemble
noncomputable section

open NumberField NumberField.InfinitePlace Matrix UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.AffineStabilizerVanishing

open PositivityTheory.KB

theorem toK_injective (L : Type) [Field L] [NumberField L] (N : ℕ) : Function.Injective (toK L N) := by
  intro a b h
  apply Units.ext
  ext i j
  have h2 := congrArg (fun g : GL (Fin N) L => (g : Matrix (Fin N) (Fin N) L) i j) h
  simp [toK] at h2
  exact_mod_cast h2

theorem dC_addS {Y : Type} {m : ℕ} (F F' : (Fin (m + 1) → Y) → ℝ) (c : ℝ) :
    dC (F + c • F') = dC F + c • dC F' := by
  funext y
  simp only [dC, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem dC_zeroS {Y : Type} {m : ℕ} : dC (0 : (Fin (m + 1) → Y) → ℝ) = 0 := by
  funext y
  simp [dC]

theorem hecke_zero {G H K Y : Type} [Group G] [Group H] [Group K] [MulAction H Y] (ρ : G →* K) (τ : K →* H)
    (q : K) : hecke ρ τ q (0 : Y → ℝ) = 0 := by
  funext y
  simp [hecke]

section
variable {G H Y : Type} [Group G] [Group H] [MulAction H Y]

theorem ev_fadd1 (ρ : G →* H) {m : ℕ} (F F' : (Fin (m + 1) → Y) → ℝ) (y : Y) (z : Chn G m) :
    ev ρ (F + F') y z = ev ρ F y z + ev ρ F' y z := by
  unfold ev
  simp only [Pi.add_apply, mul_add]
  exact Finsupp.sum_add

theorem ev_fsmul (ρ : G →* H) {m : ℕ} (F : (Fin (m + 1) → Y) → ℝ) (c : ℝ) (y : Y) (z : Chn G m) :
    ev ρ (c • F) y z = c * ev ρ F y z := by
  unfold ev
  rw [Finsupp.mul_sum]
  exact Finsupp.sum_congr fun g _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring

end

def invCoc (L : Type) [Field L] [NumberField L] (n k : ℕ) : Submodule ℝ ((Fin (k + 2) → GK L n) → ℝ) where
  carrier := {G | Inv (toK L n) G ∧ dC G = 0}
  add_mem' := fun {F F'} hF hF' => ⟨fun g y => by
      simp only [Pi.add_apply]
      rw [hF.1, hF'.1], by
      have h := dC_addS F F' 1
      rw [one_smul, one_smul] at h
      rw [h, hF.2, hF'.2, add_zero]⟩
  zero_mem' := ⟨fun _ _ => rfl, dC_zeroS⟩
  smul_mem' := fun c F hF => ⟨fun g y => by
      simp only [Pi.smul_apply]
      rw [hF.1], by
      have h := dC_addS 0 F c
      rw [zero_add, dC_zeroS, zero_add] at h
      rw [h, hF.2, smul_zero]⟩

def resF (L : Type) [Field L] [NumberField L] (n r k : ℕ) (G : (Fin (k + 2) → GK L (n + r)) → ℝ) :
    (Fin (k + 2) → GK L n) → ℝ :=
  fun y => G fun j => stab L n (n + r) (Nat.le_add_right n r) (y j)

private theorem lift_map_comp {V ι : Type} [AddCommGroup V] [Module ℝ V] [Fintype ι]
    (P Q : V →ₗ[ℝ] (ι → ℝ)) (h : ∀ v, P v = 0 → Q v = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v, ‖Q v‖ ≤ K * ‖P v‖ := by
  have hk : LinearMap.ker P ≤ LinearMap.ker Q := fun v hv => h v hv
  obtain ⟨M, hM⟩ := LinearMap.exists_extend (((LinearMap.ker P).liftQ Q hk).comp
    (P.quotKerEquivRange.symm : LinearMap.range P →ₗ[ℝ] V ⧸ LinearMap.ker P))
  refine ⟨‖LinearMap.toContinuousLinearMap M‖, norm_nonneg _, fun v => ?_⟩
  have hv : Q v = M (P v) := by
    have := LinearMap.congr_fun hM ⟨P v, LinearMap.mem_range_self P v⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
    rw [this, LinearEquiv.coe_coe, LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  rw [hv]
  exact (LinearMap.toContinuousLinearMap M).le_opNorm (P v)

private theorem eq_zero_of_mem_all_maximalIdeal_pow {G : Type} [Group G] {k : ℕ} (E : Chn G (k + 1) →ₗ[ℝ] ℝ)
    (s : Finset (Chn G (k + 1)))
    (hs : ∀ z, IsCyc z → ∃ z' ∈ Submodule.span ℝ (s : Set (Chn G (k + 1))), IsBd (z - z'))
    (hbd : ∀ z, IsBd z → E z = 0) (h0 : ∀ z ∈ s, E z = 0) : ∀ z, IsCyc z → E z = 0 := by
  intro z hz
  obtain ⟨z', hz', hb⟩ := hs z hz
  have h1 : z' ∈ LinearMap.ker E :=
    (Submodule.span_le (p := LinearMap.ker E)).2 (fun w hw => h0 w hw) hz'
  have h2 := hbd _ hb
  rw [map_sub, LinearMap.mem_ker.1 h1, sub_zero] at h2
  exact h2

private theorem ev_resF_eq_ev_cmap_stab (L : Type) [Field L] [NumberField L] (n r k : ℕ)
    (hc : ∀ c : Gm L n, toK L (n + r) (stab (𝓞 L) n (n + r) (Nat.le_add_right n r) c) =
      stab L n (n + r) (Nat.le_add_right n r) (toK L n c))
    (G : (Fin (k + 2) → GK L (n + r)) → ℝ) (z : Chn (Gm L n) (k + 1)) :
    ev (toK L n) (resF L n r k G) 1 z =
      ev (toK L (n + r)) G 1 (cmap (stab (𝓞 L) n (n + r) (Nat.le_add_right n r)) (k + 1) z) := by
  unfold ev cmap
  rw [Finsupp.lmapDomain_apply, Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by ring)]
  refine Finsupp.sum_congr fun g _ => ?_
  simp only [resF, smul_eq_mul, mul_one, ← map_partialProd, hc]

private theorem exists_linearMap_eq_ev {G : Type} [Group G] {H Y : Type} [Group H] [MulAction H Y] (ρ : G →* H)
    {m : ℕ} (F : (Fin (m + 1) → Y) → ℝ) (y : Y) :
    ∃ E : Chn G m →ₗ[ℝ] ℝ, ∀ z, E z = ev ρ F y z := by
  refine ⟨Finsupp.lsum ℝ fun g => LinearMap.id.smulRight (F fun j => ρ (Fin.partialProd g j) • y),
    fun z => ?_⟩
  rw [Finsupp.lsum_apply]
  unfold ev
  refine Finsupp.sum_congr fun g _ => ?_
  simp [smul_eq_mul]

theorem assemble (hCh : SChain) (hEv : SEv) (hSt : SStab) (hFin : SFin) (hAff : SAff) (hKey : PKey)
    (hF : PHeckeFormal) (hK : PHeckeKer) (hI : PIndex) (hSK : PStabK) : SHecke := by
  unfold SHecke
  intro L _ _ hL k hk π hπ
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hCh' := hCh
  obtain ⟨_, hcm, _, _⟩ := hCh
  have hbdmap : ∀ {G H : Type} [Group G] [Group H] (f : G →* H) (w : Chn G (k + 1)), IsBd w →
      IsBd (cmap f (k + 1) w) := by
    intro G H _ _ f w hw
    obtain ⟨v, rfl⟩ := hw
    exact ⟨cmap f (k + 2) v, hcm G H f (k + 1) v⟩
  have hcycmap : ∀ {G H : Type} [Group G] [Group H] (f : G →* H) (w : Chn G (k + 1)), IsCyc w →
      IsCyc (cmap f (k + 1) w) := by
    intro G H _ _ f w hw
    unfold IsCyc at *
    rw [hcm, hw, map_zero]
  set n := 2 * (k + 1) + 4 with hn_def
  have hn1 : 1 ≤ n := by omega
  obtain ⟨s, hs1, hs2⟩ := hFin L hL n k
  have hfinn := (hI L n π hπ).1
  let P : invCoc L n k →ₗ[ℝ] (↥s → ℝ) :=
    { toFun := fun H z₀ => ev (toK L n) (H : (Fin (k + 2) → GK L n) → ℝ) 1 z₀.1
      map_add' := fun H H' => by
        funext z₀
        simp only [Submodule.coe_add, ev_fadd1, Pi.add_apply]
      map_smul' := fun c H => by
        funext z₀
        simp only [Submodule.coe_smul, ev_fsmul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] }
  let Q : invCoc L n k →ₗ[ℝ] (↥s → ℝ) :=
    { toFun := fun H z₀ => ev (toK L n) (hecke (toK L n) (MonoidHom.id (GK L n)) (qel L n π hπ0)
        (H : (Fin (k + 2) → GK L n) → ℝ)) 1 z₀.1
      map_add' := fun H H' => by
        funext z₀
        have h1 := (hF _ _ (toK L n) _ hfinn (k + 1) H H' 1 H.2.1).2.2
        rw [one_smul, one_smul] at h1
        simp only [Submodule.coe_add, h1, ev_fadd1, Pi.add_apply]
      map_smul' := fun c H => by
        funext z₀
        have h1 := (hF _ _ (toK L n) _ hfinn (k + 1) 0 H c (fun _ _ => rfl)).2.2
        rw [zero_add, hecke_zero, zero_add] at h1
        simp only [Submodule.coe_smul, h1, ev_fsmul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] }
  have hPQ : ∀ H, P H = 0 → Q H = 0 := by
    intro H hH
    have hvan : ∀ z : Chn (Gm L n) (k + 1), IsCyc z → ev (toK L n) (H : (Fin (k + 2) → GK L n) → ℝ) 1 z = 0 := by
      obtain ⟨E, hE⟩ := exists_linearMap_eq_ev (toK L n) (H : (Fin (k + 2) → GK L n) → ℝ) (1 : GK L n)
      intro z hz
      rw [← hE]
      refine eq_zero_of_mem_all_maximalIdeal_pow E s hs2 (fun w hw => ?_) (fun w hw => ?_) z hz
      · rw [hE]
        exact (hEv _ _ _ (toK L n) k _ H.2.1 H.2.2).1 1 w hw
      · rw [hE]
        exact congrFun hH ⟨w, hw⟩
    funext z₀
    exact hK hEv _ _ (toK L n) (toK_injective L n) _ hfinn k _ H.2.1 H.2.2 hvan z₀.1 (hs1 _ z₀.2)
  obtain ⟨K, hK0, hKb⟩ := lift_map_comp P Q hPQ
  set i0 : ℝ := ((Gq (toK L n) (qel L n π hπ0)).index : ℝ) with hi0_def
  refine ⟨n + 1 + ⌈5 * (1 + K) * i0⌉₊, fun N hN F hFi hFc hdec z hz => ?_⟩
  obtain ⟨r, rfl⟩ : ∃ r, N = n + r := ⟨N - n, by omega⟩
  have hr : 1 ≤ r := by omega
  have hfinN := hI L (n + r) π hπ
  set iN : ℝ := ((Gq (toK L (n + r)) (qel L (n + r) π hπ0)).index : ℝ) with hiN_def
  have hiN : ((n + r : ℕ) : ℝ) ≤ iN := Nat.cast_le.2 hfinN.2
  have hi0 : 0 ≤ i0 := Nat.cast_nonneg _
  have hceil : 5 * (1 + K) * i0 ≤ iN := by
    have h1 := Nat.le_ceil (5 * (1 + K) * i0)
    have h2 : ((n + 1 + ⌈5 * (1 + K) * i0⌉₊ : ℕ) : ℝ) ≤ ((n + r : ℕ) : ℝ) := by exact_mod_cast hN
    push_cast at h2 hiN
    linarith
  have hiNpos : 0 < iN := by
    have h1 : (1 : ℝ) ≤ ((n + r : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n + r)
    linarith
  set a : ℝ := i0 / iN with ha
  have ha0 : 0 ≤ a := div_nonneg hi0 hiNpos.le
  have haK : a * (1 + K) ≤ 1 / 5 := by
    rw [ha, div_mul_eq_mul_div, div_le_iff₀ hiNpos]
    linarith
  have ha15 : a ≤ 1 / 5 := by nlinarith [mul_nonneg ha0 hK0]
  set TN : ((Fin (k + 2) → GK L (n + r)) → ℝ) → ((Fin (k + 2) → GK L (n + r)) → ℝ) := hecke (toK L (n + r)) (MonoidHom.id (GK L (n + r))) (qel L (n + r) π hπ0) with hTN
  have hit : ∀ j, Inv (toK L (n + r)) (TN^[j] F) ∧ dC (TN^[j] F) = 0 := by
    intro j
    induction j with
    | zero => exact ⟨hFi, hFc⟩
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      obtain ⟨h1, h2, _⟩ := hF _ _ (toK L (n + r)) _ hfinN.1 (k + 1) (TN^[j] F) 0 0 ih.1
      refine ⟨h1, ?_⟩
      rw [h2, ih.2, hecke_zero]
  have hc := (hSK L π hπ0 n r hn1).1
  have hres : ∀ G : (Fin (k + 2) → GK L (n + r)) → ℝ, Inv (toK L (n + r)) G → dC G = 0 →
      resF L n r k G ∈ invCoc L n k := by
    intro G hGi hGc
    refine ⟨fun g y => ?_, ?_⟩
    · have h1 := hGi (stab (𝓞 L) n (n + r) (Nat.le_add_right n r) g)
        (fun j => stab L n (n + r) (Nat.le_add_right n r) (y j))
      rw [hc] at h1
      simp only [resF, smul_eq_mul, map_mul] at h1 ⊢
      exact h1
    · funext y
      have h1 := congrFun hGc (fun j => stab L n (n + r) (Nat.le_add_right n r) (y j))
      simpa [dC, resF] using h1
  let x : ℕ → (↥s → ℝ) := fun j z₀ => ev (toK L (n + r)) (TN^[j] F) 1
    (cmap (stab (𝓞 L) n (n + r) (Nat.le_add_right n r)) (k + 1) z₀.1)
  have hstep : ∀ j, (4 / 5 : ℝ) * ‖x j‖ ≤ ‖x (j + 1)‖ := by
    intro j
    have hy : ‖Q ⟨resF L n r k (TN^[j] F), hres _ (hit j).1 (hit j).2⟩‖ ≤ K * ‖x j‖ := by
      have hP : P ⟨resF L n r k (TN^[j] F), hres _ (hit j).1 (hit j).2⟩ = x j :=
        funext fun z₀ => ev_resF_eq_ev_cmap_stab L n r k hc _ z₀.1
      rw [← hP]
      exact hKb _
    have hxy : (1 - a) • x j = x (j + 1) - a • Q ⟨resF L n r k (TN^[j] F), hres _ (hit j).1 (hit j).2⟩ := by
      funext z₀
      have h1' : x (j + 1) z₀ = (1 - a) * x j z₀ +
          a * Q ⟨resF L n r k (TN^[j] F), hres _ (hit j).1 (hit j).2⟩ z₀ := by
        have h1 := hKey hCh' hEv hAff L hL k hk π hπ n r hn1 hr (TN^[j] F) (hit j).1 (hit j).2 z₀.1
          (hs1 _ z₀.2)
        simp only [x, Function.iterate_succ_apply']
        exact h1
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rw [h1']
      ring
    have h1 := norm_sub_le (x (j + 1)) (a • Q ⟨resF L n r k (TN^[j] F), hres _ (hit j).1 (hit j).2⟩)
    rw [← hxy, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha0,
      abs_of_nonneg (by linarith)] at h1
    have h2 := mul_le_mul_of_nonneg_left hy ha0
    have h3 := mul_le_mul_of_nonneg_right haK (norm_nonneg (x j))
    nlinarith [norm_nonneg (x j)]
  have hlow : ∀ j, (4 / 5 : ℝ) ^ j * ‖x 0‖ ≤ ‖x j‖ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ]
      nlinarith [hstep j, ih]
  have hdec' : ∀ z₀ : ↥s, ∃ C : ℝ, ∀ j, |x j z₀| ≤ C * (3 / 5) ^ j :=
    fun z₀ => hdec _ (hcycmap _ _ (hs1 _ z₀.2))
  choose C hC using hdec'
  have hup : ∀ j, ‖x j‖ ≤ (∑ z₀, |C z₀|) * (3 / 5) ^ j := by
    intro j
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun z₀ => ?_
    rw [Real.norm_eq_abs]
    calc |x j z₀| ≤ C z₀ * (3 / 5) ^ j := hC z₀ j
      _ ≤ |C z₀| * (3 / 5) ^ j := by gcongr; exact le_abs_self _
      _ ≤ (∑ z₀, |C z₀|) * (3 / 5) ^ j := by
        gcongr
        exact Finset.single_le_sum (f := fun z => |C z|) (fun _ _ => abs_nonneg _) (Finset.mem_univ z₀)
  have hx0 : ‖x 0‖ = 0 := by
    set D := ∑ z₀, |C z₀|
    have hb : ∀ j, ‖x 0‖ ≤ D * (3 / 4) ^ j := by
      intro j
      have h1 := (hlow j).trans (hup j)
      have hp : (0 : ℝ) < (4 / 5) ^ j := by positivity
      have h2 : (3 / 5 : ℝ) ^ j = (3 / 4) ^ j * (4 / 5) ^ j := by rw [← mul_pow]; norm_num
      rw [h2] at h1
      have h3 : (4 / 5 : ℝ) ^ j * ‖x 0‖ ≤ (4 / 5) ^ j * (D * (3 / 4) ^ j) := by linarith
      exact le_of_mul_le_mul_left h3 hp
    have ht : Filter.Tendsto (fun j : ℕ => D * (3 / 4 : ℝ) ^ j) Filter.atTop (nhds 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 3 / 4)
        (by norm_num)).const_mul D
    exact le_antisymm (ge_of_tendsto' ht hb) (norm_nonneg _)
  have hx0' : ∀ z₀ ∈ s, ev (toK L (n + r)) F 1
      (cmap (stab (𝓞 L) n (n + r) (Nat.le_add_right n r)) (k + 1) z₀) = 0 := by
    intro z₀ hz₀
    exact congrFun (norm_eq_zero.1 hx0) ⟨z₀, hz₀⟩
  obtain ⟨E, hE⟩ := exists_linearMap_eq_ev (toK L (n + r)) F (1 : GK L (n + r))
  have hall := eq_zero_of_mem_all_maximalIdeal_pow (E.comp (cmap (stab (𝓞 L) n (n + r) (Nat.le_add_right n r)) (k + 1))) s hs2
    (fun w hw => by
      rw [LinearMap.comp_apply, hE]
      exact (hEv _ _ _ _ k F hFi hFc).1 1 _ (hbdmap _ w hw))
    (fun w hw => by
      rw [LinearMap.comp_apply, hE]
      exact hx0' w hw)
  obtain ⟨z₀, hz₀, hb⟩ := (hSt (𝓞 L) k n (n + r) (Nat.le_add_right n r) (le_refl _)).2 z hz
  have h1 := (hEv _ _ _ _ k F hFi hFc).1 1 _ hb
  have h2 := hall z₀ hz₀
  rw [← hE, map_sub] at h1
  rw [LinearMap.comp_apply] at h2
  rw [← hE]
  linarith

end PositivityTheory.KB.AffineStabilizerVanishing

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.HeckeDoubleCosets.Formal
noncomputable section

open UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.AffineStabilizerVanishing

open PositivityTheory.KB

section

variable {G K : Type} [Group G] [Group K]

theorem mem_Gq {ρ : G →* K} {q : K} {δ : G} : δ ∈ Gq ρ q ↔ ∃ γ, q⁻¹ * ρ γ * q = ρ δ := by
  unfold Gq
  simp [MulAut.conj_apply]

theorem F_rep {m : ℕ} (ρ : G →* K) (q : K) (F : (Fin (m + 1) → K) → ℝ) (hF : Inv ρ F) (a b : G)
    (h : b * a⁻¹ ∈ Gq ρ q) (y : Fin (m + 1) → K) :
    F (fun j => q * ρ b * y j) = F (fun j => q * ρ a * y j) := by
  obtain ⟨γ, hγ⟩ := mem_Gq.mp h
  have hρ : ρ γ = q * ρ b * (ρ a)⁻¹ * q⁻¹ := by
    rw [map_mul, map_inv] at hγ
    calc ρ γ = q * (q⁻¹ * ρ γ * q) * q⁻¹ := by group
      _ = q * ρ b * (ρ a)⁻¹ * q⁻¹ := by rw [hγ]; group
  have key : (fun j => q * ρ b * y j) = fun j => ρ γ • (q * ρ a * y j) := by
    funext j
    rw [smul_eq_mul, hρ]
    group
  rw [key]
  exact hF γ _

theorem rel_out_mul (s : Subgroup G) (c : Quotient (QuotientGroup.rightRel s)) (g : G) :
    (c.out * g) * (Quotient.mk'' (c.out * g) : Quotient (QuotientGroup.rightRel s)).out⁻¹ ∈ s := by
  have hx := Quotient.mk_out (s := QuotientGroup.rightRel s) (c.out * g)
  exact QuotientGroup.rightRel_apply.mp hx

def actQ (s : Subgroup G) (c : Quotient (QuotientGroup.rightRel s)) (g : G) : Quotient (QuotientGroup.rightRel s) :=
  Quotient.mk'' (c.out * g)

theorem actQ_one (s : Subgroup G) (c : Quotient (QuotientGroup.rightRel s)) : actQ s c 1 = c := by
  simp [actQ]

theorem actQ_mul (s : Subgroup G) (c : Quotient (QuotientGroup.rightRel s)) (g h : G) :
    actQ s c (g * h) = actQ s (actQ s c g) h := by
  unfold actQ
  apply Quotient.sound'
  apply QuotientGroup.rightRel_apply.mpr
  convert s.inv_mem (rel_out_mul s c g) using 1
  group

theorem actQ_bij (s : Subgroup G) (g : G) : Function.Bijective fun c => actQ s c g := by
  refine Function.bijective_iff_has_inverse.2 ⟨fun c => actQ s c g⁻¹, fun c => ?_, fun c => ?_⟩
  · show actQ s (actQ s c g) g⁻¹ = c
    rw [← actQ_mul, mul_inv_cancel, actQ_one]
  · show actQ s (actQ s c g⁻¹) g = c
    rw [← actQ_mul, inv_mul_cancel, actQ_one]

theorem hecke_apply {m : ℕ} (ρ : G →* K) (q : K) (F : (Fin (m + 1) → K) → ℝ) (y : Fin (m + 1) → K) :
    hecke ρ (MonoidHom.id K) q F y =
      ((Gq ρ q).index : ℝ)⁻¹ * ∑ᶠ c : Quotient (QuotientGroup.rightRel (Gq ρ q)), F (fun j => q * ρ c.out * y j) :=
  rfl

end

theorem pHeckeFormal : PHeckeFormal := by
  intro G K _ _ ρ q hfin m F F' c hF
  haveI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel (Gq ρ q)))
  refine ⟨?_, ?_, ?_⟩
  · intro g y
    rw [hecke_apply, hecke_apply]
    congr 1
    refine Eq.trans ?_ (finsum_comp_equiv (Equiv.ofBijective _ (actQ_bij (Gq ρ q) g)))
    apply finsum_congr
    intro c'
    simp only [Equiv.ofBijective_apply]
    rw [← F_rep ρ q F hF (actQ (Gq ρ q) c' g).out (c'.out * g) (rel_out_mul _ c' g) y]
    congr 1
    funext j
    rw [smul_eq_mul, map_mul]
    group
  · funext y
    rw [hecke_apply]
    unfold dC
    simp only [hecke_apply, finsum_eq_sum_of_fintype, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun i _ => ?_))
    ring
  · funext y
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hecke_apply, finsum_eq_sum_of_fintype,
      Finset.sum_add_distrib, ← Finset.mul_sum]
    ring

theorem bd_cmap {G H : Type} [Group G] [Group H] (f : G →* H) (m : ℕ) (z : Chn G (m + 1)) :
    bd H m (cmap f (m + 1) z) = cmap f m (bd G m z) := by
  have hc : ∀ (j : Fin (m + 1)) (g : Fin (m + 1) → G),
      (fun i => f (Fin.contractNth j (· * ·) g i)) = Fin.contractNth j (· * ·) (fun i => f (g i)) :=
    fun j g => Fin.comp_contractNth _ _ (map_mul f) j g
  have key : (bd H m).comp (cmap f (m + 1)) = (cmap f m).comp (bd G m) := by
    apply Finsupp.lhom_ext
    intro g r
    set_option synthInstance.maxHeartbeats 100000 in
      simp [bd, cmap, Finsupp.mapDomain_single, map_sum, Finsupp.mapDomain_add, Finsupp.mapDomain_smul, hc]
    rw [Finsupp.mapDomain_finsetSum]
    simp only [Finsupp.mapDomain_single, hc]
  exact LinearMap.congr_fun key z

theorem pHeckeKer (hT : PTransfer) (hE : PEvDC) : PHeckeKer := by
  intro hSEv G K _ _ ρ hρ q hfin m F hF hdF hcyc z hz
  haveI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel (Gq ρ q)))
  have heq : ∀ (c : Quotient (QuotientGroup.rightRel (Gq ρ q))) (g : G) (y : Fin (m + 2) → G),
      ((Gq ρ q).index : ℝ)⁻¹ * F (fun j => q * ρ (actQ (Gq ρ q) c g).out * ρ (y j)) =
        ((Gq ρ q).index : ℝ)⁻¹ * F (fun j => q * ρ c.out * ρ (g * y j)) := by
    intro c g y
    have e := F_rep ρ q F hF (actQ (Gq ρ q) c g).out (c.out * g) (rel_out_mul _ c g) (fun j => ρ (y j))
    rw [← e]
    congr 1
    congr 1
    funext j
    rw [map_mul, map_mul]
    group
  have hcoc : ∀ c : Quotient (QuotientGroup.rightRel (Gq ρ q)),
      dC (fun y : Fin (m + 2) → G => ((Gq ρ q).index : ℝ)⁻¹ * F (fun j => q * ρ c.out * ρ (y j))) = 0 := by
    intro c
    funext y
    have h := congrFun hdF (fun j => q * ρ c.out * ρ (y j))
    unfold dC at h ⊢
    simp only [Pi.zero_apply] at h ⊢
    rw [← mul_zero (((Gq ρ q).index : ℝ)⁻¹), ← h, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  have hpp : ∀ {S T : Type} [Group S] [Group T] (φ : S →* T) {n : ℕ} (g : Fin n → S) (j : Fin (n + 1)),
      Fin.partialProd (fun i => φ (g i)) j = φ (Fin.partialProd g j) := by
    intro S T _ _ φ n g j
    refine Fin.inductionOn j ?_ ?_
    · simp
    · intro j ih
      rw [Fin.partialProd_succ, Fin.partialProd_succ, ih, map_mul]
  have hstab : ∀ (c : Quotient (QuotientGroup.rightRel (Gq ρ q)))
      (w : Chn (stabR (actQ (Gq ρ q)) (actQ_one _) (actQ_mul _) c) (m + 1)), IsCyc w →
      ev (stabR (actQ (Gq ρ q)) (actQ_one _) (actQ_mul _) c).subtype
        (fun y : Fin (m + 2) → G => ((Gq ρ q).index : ℝ)⁻¹ * F (fun j => q * ρ c.out * ρ (y j))) 1 w = 0 := by
    intro c w hw
    have hmem : ∀ h : stabR (actQ (Gq ρ q)) (actQ_one _) (actQ_mul _) c,
        q * ρ c.out * ρ h * (q * ρ c.out)⁻¹ ∈ ρ.range := by
      intro h
      have h1 : actQ (Gq ρ q) c h = c := h.2
      have h3 : (Quotient.mk'' (c.out * (h : G)) : Quotient (QuotientGroup.rightRel (Gq ρ q))) =
          Quotient.mk'' c.out := by
        rw [Quotient.out_eq']
        exact h1
      have h2 : c.out * (c.out * (h : G))⁻¹ ∈ Gq ρ q := QuotientGroup.rightRel_apply.mp (Quotient.exact' h3)
      obtain ⟨γ, hγ⟩ := mem_Gq.mp h2
      refine ⟨γ⁻¹, ?_⟩
      rw [map_inv]
      rw [map_mul, map_inv, map_mul] at hγ
      calc (ρ γ)⁻¹ = (q * (q⁻¹ * ρ γ * q) * q⁻¹)⁻¹ := by group
        _ = _ := by rw [hγ]; group
    let ψ : (stabR (actQ (Gq ρ q)) (actQ_one _) (actQ_mul _) c) →* K :=
      (MulAut.conj (q * ρ c.out)).toMonoidHom.comp (ρ.comp (stabR (actQ (Gq ρ q)) (actQ_one _) (actQ_mul _) c).subtype)
    have hψ : ∀ h, ψ h ∈ ρ.range := fun h => by
      convert hmem h using 1
      simp only [ψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_subtype]
      done
    let φ := (MonoidHom.ofInjective hρ).symm.toMonoidHom.comp (ψ.codRestrict ρ.range hψ)
    have hφ : ∀ h, ρ (φ h) = q * ρ c.out * ρ h * (q * ρ c.out)⁻¹ := by
      intro h
      rw [← MonoidHom.ofInjective_apply hρ (x := φ h)]
      simp [φ, ψ, MulAut.conj_apply]
      group
    have hz' : IsCyc (cmap φ (m + 1) w) := by
      unfold IsCyc at hw ⊢
      rw [bd_cmap, hw, map_zero]
    have hsev := (hSEv G K K ρ m F hF hdF).2 (q * ρ c.out) 1 _ hz'
    have hcalc : ev (stabR (actQ (Gq ρ q)) (actQ_one _) (actQ_mul _) c).subtype
        (fun y : Fin (m + 2) → G => ((Gq ρ q).index : ℝ)⁻¹ * F (fun j => q * ρ c.out * ρ (y j))) 1 w =
        ((Gq ρ q).index : ℝ)⁻¹ * ev ρ F (q * ρ c.out) (cmap φ (m + 1) w) := by
      unfold ev cmap
      rw [Finsupp.lmapDomain_apply, Finsupp.sum_mapDomain_index (by intro b; simp) (by intro b r1 r2; ring),
        Finsupp.mul_sum]
      apply Finsupp.sum_congr
      intro g _
      simp only [hpp, hφ, smul_eq_mul, Subgroup.coe_subtype, mul_one, inv_mul_cancel_right]
      ring
    rw [hcalc, hsev, hcyc _ hz', mul_zero]
  have hfinal := hT G (Quotient (QuotientGroup.rightRel (Gq ρ q))) (actQ (Gq ρ q)) (actQ_one _) (actQ_mul _) m
    (fun c y => ((Gq ρ q).index : ℝ)⁻¹ * F (fun j => q * ρ c.out * ρ (y j))) heq hcoc hstab z hz
  refine Eq.trans ?_ hfinal
  unfold ev
  apply Finsupp.sum_congr
  intro g _
  congr 1
  simp only [hecke_apply, finsum_eq_sum_of_fintype, Finset.mul_sum, smul_eq_mul, mul_one, MonoidHom.id_apply]

end PositivityTheory.KB.AffineStabilizerVanishing

end
end

noncomputable section

open UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.AffineStabilizerVanishing

open PositivityTheory.KB

section
variable {Γn ΓN Kn KN : Type} [Group Γn] [Group ΓN] [Group Kn] [Group KN]
  {ρn : Γn →* Kn} {ρN : ΓN →* KN} {sO : Γn →* ΓN} {sL : Kn →* KN} {qn : Kn} {q : KN}

private theorem ev_one_eq_finsupp_sum {G K : Type} [Group G] [Group K] (ρ : G →* K) {m : ℕ}
    (Ψ : (Fin (m + 2) → K) → ℝ) (z : Chn G (m + 1)) :
    ev ρ Ψ 1 z = Finsupp.sum (α := Fin (m + 1) → G) z
      (fun g r => r * Ψ (fun j => ρ (Fin.partialProd g j))) := by
  unfold ev
  simp only [smul_eq_mul, mul_one]

private theorem partialProd_map_monoidHom {G G' : Type} [Group G] [Group G'] (s : G' →* G) {n : ℕ} (g : Fin n → G')
    (j : Fin (n + 1)) : Fin.partialProd (fun i => s (g i)) j = s (Fin.partialProd g j) := by
  unfold Fin.partialProd
  rw [map_list_prod, List.map_take, List.map_ofFn]
  rfl

private theorem ev_one_cmap_eq_finsupp_sum {G K G' : Type} [Group G] [Group K] [Group G'] (ρ : G →* K)
    (s : G' →* G) {m : ℕ} (Ψ : (Fin (m + 2) → K) → ℝ) (z : Chn G' (m + 1)) :
    ev ρ Ψ 1 (cmap s (m + 1) z) = Finsupp.sum (α := Fin (m + 1) → G') z
      (fun g r => r * Ψ (fun j => ρ (s (Fin.partialProd g j)))) := by
  rw [ev_one_eq_finsupp_sum]
  unfold cmap
  rw [Finsupp.lmapDomain_apply, Finsupp.sum_mapDomain_index]
  · congr 1
    funext g r
    congr 2
    funext j
    congr 1
    exact partialProd_map_monoidHom s g j
  · intro _
    simp
  · intro _ _ _
    ring

private theorem ev_sub_hecke_double_cosets {G H Y : Type} [Group G] [Group H] [MulAction H Y] (ρ : G →* H) {m : ℕ}
    (f g : (Fin (m + 1) → Y) → ℝ) (y : Y) (w : Chn G m) :
    ev ρ (fun t => f t - g t) y w = ev ρ f y w - ev ρ g y w := by
  unfold ev
  simp only [mul_sub]
  exact Finsupp.sum_sub

private theorem coset_lemma_4 {G K : Type} [Group G] [Group K] (ρ : G →* K) (q : K) {m : ℕ}
    (F : (Fin (m + 2) → K) → ℝ) (hF : Inv ρ F) {c c' : G} (h : c' * c⁻¹ ∈ Gq ρ q)
    (w : Fin (m + 2) → K) :
    F (fun j => q * ρ c' * w j) = F (fun j => q * ρ c * w j) := by
  unfold Gq at h
  rw [Subgroup.mem_comap, Subgroup.mem_map] at h
  obtain ⟨a, ha1, ha⟩ := h
  obtain ⟨g', rfl⟩ := MonoidHom.mem_range.mp ha1
  simp at ha
  have hc' : ρ c' = q⁻¹ * ρ g' * q * ρ c := by
    rw [ha]
    group
  have e : (fun j => q * ρ c' * w j) = fun j => ρ g' • (q * ρ c * w j) := by
    funext j
    rw [hc', smul_eq_mul]
    group
  rw [e]
  exact hF g' _

private theorem hecke_apply_eq_index_inv_mul_finsum_rightRel {G K : Type} [Group G] [Group K] (ρ : G →* K) (q : K) {m : ℕ}
    (Ψ : (Fin (m + 2) → K) → ℝ) (y : Fin (m + 2) → K) :
    hecke ρ (MonoidHom.id K) q Ψ y = ((Gq ρ q).index : ℝ)⁻¹ *
      ∑ᶠ c : Quotient (QuotientGroup.rightRel (Gq ρ q)), Ψ (fun j => q * ρ c.out * y j) := by
  unfold hecke
  rfl

private theorem quotient_mk_rightRel_eq_iff_mul_inv_mem {G : Type} [Group G] (S : Subgroup G) (a b : G) :
    Quotient.mk (QuotientGroup.rightRel S) a = Quotient.mk (QuotientGroup.rightRel S) b ↔
      b * a⁻¹ ∈ S := by
  rw [Quotient.eq]
  exact QuotientGroup.rightRel_apply

private theorem index_eq_card_quotient_rightRel {G : Type} [Group G] (S : Subgroup G)
    [Fintype (Quotient (QuotientGroup.rightRel S))] :
    (S.index : ℝ) = Fintype.card (Quotient (QuotientGroup.rightRel S)) := by
  rw [Subgroup.index_eq_card, ← Nat.card_eq_fintype_card,
    Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel S)]

theorem keyGen (hT : PTransfer) (hcomm : ∀ c, ρN (sO c) = sL (ρn c)) (hq : q = sL qn)
    (hGS : ∀ c, sO c ∈ Gq ρN q ↔ c ∈ Gq ρn qn)
    [Finite (Quotient (QuotientGroup.rightRel (Gq ρN q)))] [Finite (Quotient (QuotientGroup.rightRel (Gq ρn qn)))]
    (m : ℕ) (F : (Fin (m + 2) → KN) → ℝ) (hFinv : Inv ρN F) (hFcoc : dC F = 0)
    (hvan : ∀ c : ΓN, (∀ c' : Γn, c * (sO c')⁻¹ ∉ Gq ρN q) → ∀ H : Subgroup Γn,
      (∀ h ∈ H, c * sO h * c⁻¹ ∈ Gq ρN q) → ∀ w : Chn H (m + 1), IsCyc w →
        ev H.subtype (fun y => F fun j => q * ρN c * ρN (sO (y j))) 1 w =
          ev H.subtype (fun y => F fun j => ρN (sO (y j))) 1 w)
    (z : Chn Γn (m + 1)) (hz : IsCyc z) :
    ev ρN (hecke ρN (MonoidHom.id KN) q F) 1 (cmap sO (m + 1) z) =
      (1 - ((Gq ρn qn).index : ℝ) / (Gq ρN q).index) * ev ρN F 1 (cmap sO (m + 1) z) +
        ((Gq ρn qn).index : ℝ) / (Gq ρN q).index *
          ev ρn (hecke ρn (MonoidHom.id Kn) qn (fun y => F fun j => sL (y j))) 1 z := by
  classical
  rw [ev_one_cmap_eq_finsupp_sum, ev_one_cmap_eq_finsupp_sum, ev_one_eq_finsupp_sum]
  simp only [hecke_apply_eq_index_inv_mul_finsum_rightRel]
  have hT' := hT
  unfold PTransfer at hT'
  let X := {x : Quotient (QuotientGroup.rightRel (Gq ρN q)) //
    ∀ a : Γn, Quotient.mk (QuotientGroup.rightRel (Gq ρN q)) (sO a) ≠ x}
  have hmem : ∀ (x : X) (g : Γn) (a : Γn), Quotient.mk (QuotientGroup.rightRel (Gq ρN q)) (sO a) ≠
      Quotient.mk (QuotientGroup.rightRel (Gq ρN q)) (x.1.out * sO g) := by
    intro x g a ha
    rw [quotient_mk_rightRel_eq_iff_mul_inv_mem] at ha
    apply x.2 (a * g⁻¹)
    rw [← Quotient.out_eq x.1, quotient_mk_rightRel_eq_iff_mul_inv_mem]
    convert ha using 1
    rw [map_mul, map_inv]
    group
  obtain ⟨act, hact⟩ : ∃ act : X → Γn → X, ∀ x g,
      (act x g).1 = Quotient.mk (QuotientGroup.rightRel (Gq ρN q)) (x.1.out * sO g) :=
    ⟨fun x g => ⟨_, hmem x g⟩, fun _ _ => rfl⟩
  have hrep : ∀ (x : X) (g : Γn), (act x g).1.out * (x.1.out * sO g)⁻¹ ∈ Gq ρN q := by
    intro x g
    rw [← quotient_mk_rightRel_eq_iff_mul_inv_mem, Quotient.out_eq, hact]
  have h1 : ∀ x, act x 1 = x := by
    intro x
    apply Subtype.ext
    rw [hact, map_one, mul_one, Quotient.out_eq]
  have hm : ∀ x g h, act x (g * h) = act (act x g) h := by
    intro x g h
    apply Subtype.ext
    rw [hact, hact, quotient_mk_rightRel_eq_iff_mul_inv_mem]
    convert hrep x g using 1
    rw [map_mul]
    group
  let Φ : X → (Fin (m + 2) → Γn) → ℝ := fun x y =>
    F (fun j => q * ρN x.1.out * ρN (sO (y j))) - F (fun j => ρN (sO (y j)))
  have hΦ1 : ∀ x g y, Φ (act x g) y = Φ x (fun j => g * y j) := by
    intro x g y
    simp only [Φ]
    rw [coset_lemma_4 ρN q F hFinv (hrep x g) (fun j => ρN (sO (y j)))]
    congr 1
    · congr 1
      funext j
      simp [map_mul, mul_assoc]
    · rw [show (fun j => ρN (sO (g * y j))) = fun j => ρN (sO g) • ρN (sO (y j)) from
        funext fun j => by simp]
      exact (hFinv _ _).symm
  have hΦ2 : ∀ x, dC (Φ x) = 0 := by
    intro x
    funext y
    have e1 := congrFun hFcoc (fun j => q * ρN x.1.out * ρN (sO (y j)))
    have e2 := congrFun hFcoc (fun j => ρN (sO (y j)))
    simp only [dC, Pi.zero_apply, Φ] at e1 e2 ⊢
    simp only [mul_sub, Finset.sum_sub_distrib, e1, e2, sub_zero]
  have hΦ3 : ∀ x (w : Chn (stabR act h1 hm x) (m + 1)), IsCyc w →
      ev (stabR act h1 hm x).subtype (Φ x) 1 w = 0 := by
    intro x w hw
    have hx : ∀ c' : Γn, x.1.out * (sO c')⁻¹ ∉ Gq ρN q := by
      intro c' hc
      apply x.2 c'
      rw [← Quotient.out_eq x.1, quotient_mk_rightRel_eq_iff_mul_inv_mem]
      exact hc
    have hst : ∀ h ∈ stabR act h1 hm x, x.1.out * sO h * x.1.out⁻¹ ∈ Gq ρN q := by
      intro h hh
      have hh' : act x h = x := hh
      have e := congrArg Subtype.val hh'
      rw [hact] at e
      conv at e => rhs; rw [← Quotient.out_eq x.1]
      exact (quotient_mk_rightRel_eq_iff_mul_inv_mem _ _ _).mp e.symm
    have e := hvan x.1.out hx _ hst w hw
    show ev _ (fun t => F (fun j => q * ρN x.1.out * ρN (sO (t j))) - F (fun j => ρN (sO (t j)))) 1 w = 0
    rw [ev_sub_hecke_double_cosets, e, sub_self]
  haveI : Finite X := Subtype.finite
  have hz0 := hT' Γn X act h1 hm m Φ hΦ1 hΦ2 hΦ3 z hz
  rw [ev_one_eq_finsupp_sum] at hz0
  simp only [MonoidHom.id_apply] at hz0
  haveI : Fintype (Quotient (QuotientGroup.rightRel (Gq ρN q))) := Fintype.ofFinite _
  haveI : Fintype (Quotient (QuotientGroup.rightRel (Gq ρn qn))) := Fintype.ofFinite _
  haveI : Fintype X := Fintype.ofFinite _
  have himg : Finset.univ.filter (fun c : Quotient (QuotientGroup.rightRel (Gq ρN q)) =>
      ¬ ∀ a : Γn, Quotient.mk (QuotientGroup.rightRel (Gq ρN q)) (sO a) ≠ c) =
      Finset.univ.image (fun d : Quotient (QuotientGroup.rightRel (Gq ρn qn)) =>
        Quotient.mk (QuotientGroup.rightRel (Gq ρN q)) (sO d.out)) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, not_forall, not_not]
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨Quotient.mk (QuotientGroup.rightRel (Gq ρn qn)) a, ?_⟩
      rw [← ha, quotient_mk_rightRel_eq_iff_mul_inv_mem, ← map_inv, ← map_mul, hGS, ← quotient_mk_rightRel_eq_iff_mul_inv_mem, Quotient.out_eq]
    · rintro ⟨d, hd⟩
      exact ⟨d.out, hd⟩
  have hinj : Function.Injective (fun d : Quotient (QuotientGroup.rightRel (Gq ρn qn)) =>
      Quotient.mk (QuotientGroup.rightRel (Gq ρN q)) (sO d.out)) := by
    intro d d' h
    simp only at h
    rw [quotient_mk_rightRel_eq_iff_mul_inv_mem, ← map_inv, ← map_mul, hGS, ← quotient_mk_rightRel_eq_iff_mul_inv_mem, Quotient.out_eq, Quotient.out_eq] at h
    exact h
  have hgen : ∀ f : Quotient (QuotientGroup.rightRel (Gq ρN q)) → ℝ,
      ∑ c, f c = ∑ x : X, f x.1 +
        ∑ d : Quotient (QuotientGroup.rightRel (Gq ρn qn)),
          f (Quotient.mk (QuotientGroup.rightRel (Gq ρN q)) (sO d.out)) := by
    intro f
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun c => ∀ a : Γn, Quotient.mk (QuotientGroup.rightRel (Gq ρN q)) (sO a) ≠ c) f,
      himg, Finset.sum_image (fun x _ y _ h => hinj h), Finset.sum_subtype _ (fun x => Finset.mem_filter.trans (and_iff_right (Finset.mem_univ _)))]
  have hNpos : 0 < Fintype.card (Quotient (QuotientGroup.rightRel (Gq ρN q))) :=
    Fintype.card_pos_iff.mpr ⟨Quotient.mk _ 1⟩
  have hnpos : 0 < Fintype.card (Quotient (QuotientGroup.rightRel (Gq ρn qn))) :=
    Fintype.card_pos_iff.mpr ⟨Quotient.mk _ 1⟩
  have hcard := hgen (fun _ => 1)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hcard
  have hpt : ∀ y : Fin (m + 2) → Γn,
      ((Gq ρN q).index : ℝ)⁻¹ * ∑ᶠ c : Quotient (QuotientGroup.rightRel (Gq ρN q)),
          F (fun j => q * ρN c.out * ρN (sO (y j))) =
        (1 - ((Gq ρn qn).index : ℝ) / (Gq ρN q).index) * F (fun j => ρN (sO (y j))) +
          ((Gq ρn qn).index : ℝ) / (Gq ρN q).index * (((Gq ρn qn).index : ℝ)⁻¹ *
            ∑ᶠ c : Quotient (QuotientGroup.rightRel (Gq ρn qn)),
              F (fun j => sL (qn * ρn c.out * ρn (y j)))) +
          ((Gq ρN q).index : ℝ)⁻¹ * ∑ᶠ x : X, Φ x y := by
    intro y
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, index_eq_card_quotient_rightRel,
      index_eq_card_quotient_rightRel, hgen]
    have hd : ∀ d : Quotient (QuotientGroup.rightRel (Gq ρn qn)),
        F (fun j => q * ρN (Quotient.mk (QuotientGroup.rightRel (Gq ρN q)) (sO d.out)).out *
          ρN (sO (y j))) = F (fun j => sL (qn * ρn d.out * ρn (y j))) := by
      intro d
      rw [coset_lemma_4 ρN q F hFinv (c := sO d.out)
        (c' := (Quotient.mk (QuotientGroup.rightRel (Gq ρN q)) (sO d.out)).out)
        (by rw [← quotient_mk_rightRel_eq_iff_mul_inv_mem, Quotient.out_eq]) (fun j => ρN (sO (y j)))]
      congr 1
      funext j
      simp only [hq, hcomm, map_mul]
    simp only [hd, Φ, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [hcard]
    have h1' : (Fintype.card (Quotient (QuotientGroup.rightRel (Gq ρn qn))) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr hnpos.ne'
    have h2' : (Fintype.card X : ℝ) + Fintype.card (Quotient (QuotientGroup.rightRel (Gq ρn qn))) ≠ 0 := by
      positivity
    field_simp
    ring
  simp only [hpt]
  rw [← sub_eq_zero]
  calc _ = ((Gq ρN q).index : ℝ)⁻¹ *
        Finsupp.sum z (fun g r => r * ∑ᶠ x : X, Φ x (fun j => Fin.partialProd g j)) := by
        simp only [Finsupp.sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro g _
        ring
    _ = 0 := by rw [hz0, mul_zero]

end

end PositivityTheory.KB.AffineStabilizerVanishing

end

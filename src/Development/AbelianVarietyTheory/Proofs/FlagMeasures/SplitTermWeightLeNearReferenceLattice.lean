module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormCongruenceLiftSmallGroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarInvVolumeMiddleLayerEichlerLe

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerHermitianLatticeOfDeepStarCongruence
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImportsFurther
namespace GlobalTheory.ExistsSmulMemLattice

open NumberField

theorem exists_smul_mem {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]
    {M : Submodule (RingOfIntegers K) V} {v : V} (hv : v ∈ Submodule.span K (M : Set V)) :
    ∃ d : RingOfIntegers K, d ≠ 0 ∧ d • v ∈ M := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d₁, hd₁, h₁⟩ := hx
    obtain ⟨d₂, hd₂, h₂⟩ := hy
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact M.smul_mem _ h₁
    · rw [mul_smul]; exact M.smul_mem _ h₂
  | smul a x _ hx =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨⟨n, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors (RingOfIntegers K)) a
    have hs0 : (s : RingOfIntegers K) ≠ 0 := nonZeroDivisors.coe_ne_zero s
    refine ⟨(s : RingOfIntegers K) * d, mul_ne_zero hs0 hd, ?_⟩
    have key : ((s : RingOfIntegers K) * d) • (a • x) = n • (d • x) := by
      rw [← algebraMap_smul K ((s : RingOfIntegers K) * d), ← algebraMap_smul K n (d • x),
        ← algebraMap_smul K d x, smul_smul, smul_smul, map_mul]
      congr 1
      simp only at hs
      rw [← hs]; ring
    rw [key]; exact M.smul_mem _ h

end GlobalTheory.ExistsSmulMemLattice
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerHermitianLatticeOfDeepStarCongruence
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.Stab

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]


omit [NumberField K] in
theorem smul_eq (a : 𝓞 K) (v : V) : a • v = (a : K) • v := (algebraMap_smul K a v).symm

theorem cancel {J : Ideal (𝓞 K)} (hJ : J ≠ ⊥) {M : Submodule (𝓞 K) V} {v : V}
    (h : ∀ a ∈ J, a • v ∈ J • M) : v ∈ M := by
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  obtain ⟨J', hJ'⟩ : J ∣ Ideal.span {c} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hc)
  have h1 : J • Submodule.span (𝓞 K) {v} ≤ J • M := by
    refine Submodule.smul_le.2 fun a ha x hx => ?_
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [smul_comm]
    exact Submodule.smul_mem _ _ (h a ha)
  have h2 : Ideal.span {c} • Submodule.span (𝓞 K) {v} ≤ Ideal.span {c} • M := by
    rw [hJ', mul_comm, Submodule.mul_smul, Submodule.mul_smul]
    exact Submodule.smul_mono le_rfl h1
  have h3 := h2 (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self c)
    (Submodule.mem_span_singleton_self v))
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h3
  obtain ⟨m, hm, hmv⟩ := h3
  rw [smul_eq, smul_eq] at hmv
  have hc1 : (c : K) ≠ 0 := by exact_mod_cast hc0
  rwa [← smul_right_injective V hc1 hmv]

theorem exists_mul {M : Submodule (𝓞 K) V} {v : V} (hv : v ∈ Submodule.span K (M : Set V)) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • v ∈ M := by
  first
  | exact @_root_.GlobalTheory.ExistsSmulMemLattice.exists_smul_mem
  | exact _root_.GlobalTheory.ExistsSmulMemLattice.exists_smul_mem
  | (apply _root_.GlobalTheory.ExistsSmulMemLattice.exists_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.ExistsSmulMemLattice.exists_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ExistsSmulMemLattice.exists_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ExistsSmulMemLattice.exists_smul_mem ..)

variable [StarRing K]


omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem isom_of_mem {H : HermSpace K V} {r : ℕ} {F F' : FlagD H r} {s : V ≃ₗ[K] V}
    (hs : s ∈ Subgroup.closure {s : V ≃ₗ[K] V | F.InN (s : V →ₗ[K] V) ∧ F'.InN (s : V →ₗ[K] V)}) :
    s ∈ isomGrp H :=
  (Subgroup.closure_le (k := {t : V ≃ₗ[K] V | F.InN (t : V →ₗ[K] V) ∧ F'.InN (t : V →ₗ[K] V)}) (isomGrp H)).2 (fun t ht =>
    (mem_isomGrp H t).2 ht.1.1) hs


omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem le_perp_perp (H : HermSpace K V) (S : Submodule K V) : S ≤ perp H (perp H S) := by
  intro x hx
  rw [mem_perp_iff]
  intro y hy
  rw [← H.herm, (mem_perp_iff H S y).1 hy x hx, star_zero]

end GlobalTheory.DegCnt.Stab


open GlobalTheory.DegCnt.Stab in
theorem GlobalTheory.DegCnt.stab_of_deep_congruence : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → ∀ e : ℕ, N.Split Λ → N.Near (𝔠 ^ e) Λ → ∀ s ∈ N.Rs, (∀ x ∈ N.P0, s x - x ∈ 𝔠 ^ (3 * e + 10) • N.P0) → s • Λ = Λ := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hΛ 𝔠 h0 h1 h2 h3 e hsp hn s hs hcong
  have hkill := (GlobalTheory.T.hermFramePair_ideal_kills_discriminantModules K V H hK r N g Λ hg hΛ 𝔠 h0 h1 h2 h3).1
  have hcompl : IsCompl N.Wt N.Pi := (GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N).2.2.1
  have hiso := (mem_isomGrp H s).1 (isom_of_mem hs.1)
  have hfix : ∀ w ∈ N.Wt, s w = w := fun w hw =>
    (mem_fixingSubgroup_iff (V ≃ₗ[K] V)).1 hs.2 w hw
  have hdual : dual H Λ = Λ := hΛ.1.1.2
  have hspan : Submodule.span K (Λ : Set V) = ⊤ := hΛ.1.1.1.2
  have hint : ∀ x ∈ Λ, ∀ y ∈ Λ, H.B x y ∈ (1 : Submodule (𝓞 K) K) := fun x hx =>
    ((mem_dual_iff H Λ x).1 (hdual.symm ▸ hx)).2
  have hIP : II N.F N.F' ≤ N.Pi :=
    (inf_le_left.trans (le_sup_left.trans (le_sup_left.trans le_sup_left))).trans
      (le_perp_perp H (V0 N.F N.F' ⊔ N.Ist))
  have hle : ∀ x ∈ Λ, s x ∈ Λ := by
    intro x hx
    obtain ⟨w, hw, p, hp, rfl⟩ := Submodule.mem_sup.1
      (hcompl.sup_eq_top ▸ Submodule.mem_top : x ∈ N.Wt ⊔ N.Pi)
    have hpw : ∀ y ∈ N.Wt, H.B p y = 0 := (mem_perp_iff H N.Wt p).1 hp
    have hwd : w ∈ dual H (latTh N.F N.F' Λ) := by
      rw [hsp, mem_dual_iff]
      constructor
      · obtain ⟨d, hd, hdw⟩ := exists_mul (M := Λ) (v := w) (hspan ▸ Submodule.mem_top)
        have hd1 : (d : K) ≠ 0 := by exact_mod_cast hd
        have hw' : w = (d : K)⁻¹ • (d • w) := by rw [smul_eq, smul_smul, inv_mul_cancel₀ hd1, one_smul]
        rw [hw']
        refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
        exact Submodule.mem_sup_left ⟨hdw, (rs (𝓞 K) N.Wt).smul_mem d hw⟩
      · intro y hy
        obtain ⟨θ, hθ, i, hi, rfl⟩ := Submodule.mem_sup.1 hy
        have e1 : H.B w i = 0 := by
          rw [← H.herm, (mem_perp_iff H N.Wt i).1 (hIP hi) w hw, star_zero]
        have e2 := hint _ hx θ hθ.1
        rw [map_add (f := _), LinearMap.add_apply, hpw θ hθ.2, add_zero] at e2
        rw [map_add (f := _), e1, add_zero]
        exact e2
    have hap : ∀ a ∈ 𝔠 ^ 3, a • p ∈ Λ ⊓ rs (𝓞 K) N.Pi := by
      intro a ha
      have := hkill (Submodule.smul_mem_smul ha hwd)
      rw [hsp] at this
      obtain ⟨θ, hθ, i, hi, h⟩ := Submodule.mem_sup.1 this
      have hiW : i ∈ N.Wt := by
        have : i = a • w - θ := by rw [← h]; abel
        rw [this]
        exact (rs (𝓞 K) N.Wt).sub_mem ((rs (𝓞 K) N.Wt).smul_mem a hw) hθ.2
      have hi0 : i = 0 := (Submodule.disjoint_def.1 hcompl.disjoint) i hiW (hIP hi)
      refine ⟨?_, (rs (𝓞 K) N.Pi).smul_mem a hp⟩
      have : a • p = a • (w + p) - θ := by rw [smul_add, ← h, hi0]; abel
      rw [this]
      exact Λ.sub_mem (Λ.smul_mem a hx) hθ.1
    have hbp : ∀ b ∈ 𝔠 ^ (e + 3), b • p ∈ N.P0 := by
      intro b hb
      rw [pow_add] at hb
      refine Submodule.mul_induction_on hb (fun m hm n hn' => ?_) (fun m n hm hn' => ?_)
      · rw [mul_smul]
        exact hn.2 (Submodule.smul_mem_smul hm (hap n hn'))
      · rw [add_smul]; exact N.P0.add_mem hm hn'
    have hsp' : s p - p ∈ 𝔠 ^ e • N.P0 := by
      refine cancel (pow_ne_zero (e + 3) h0) fun b hb => ?_
      have := hcong _ (hbp b hb)
      rw [smul_eq, map_smul, ← smul_sub, ← smul_eq] at this
      rw [← Submodule.mul_smul, ← pow_add]
      exact Submodule.smul_mono (Ideal.pow_le_pow_right (by omega)) le_rfl this
    have : s (w + p) = (w + p) + (s p - p) := by rw [map_add (f := _), hfix w hw]; abel
    rw [this]
    exact Λ.add_mem hx (hn.1 hsp').1
  apply le_antisymm
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists y s Λ).1 hy
    exact hle x hx
  · intro x hx
    refine (Submodule.mem_smul_pointwise_iff_exists x s Λ).2 ⟨s.symm x, ?_, s.apply_symm_apply x⟩
    rw [← hdual, mem_dual_iff]
    refine ⟨hspan ▸ Submodule.mem_top, fun y hy => ?_⟩
    rw [← hiso, s.apply_symm_apply]
    exact hint x hx _ (hle y hy)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerHermitianLatticeOfDeepStarCongruenceStatement
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabilizer_hermitianLattice_of_deep_star_congruence : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → ∀ e : ℕ, N.Split Λ → N.Near (𝔠 ^ e) Λ → ∀ s ∈ N.Rs, (∀ x ∈ N.P0, s x - x ∈ 𝔠 ^ (3 * e + 10) • N.P0) → s • Λ = Λ := by
  first | exact @GlobalTheory.DegCnt.stab_of_deep_congruence | exact GlobalTheory.DegCnt.stab_of_deep_congruence | (intros; apply GlobalTheory.DegCnt.stab_of_deep_congruence <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormInvVolSkewLayerLe
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormInvVolSkewLayerLe
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.WtSkew

theorem invVol_le_relIndex {G : Type} [Group G] (A B : Subgroup G) :
    GlobalTheory.HL.invVol A B ≤ (B.relIndex A : ℝ) := by
  unfold GlobalTheory.HL.invVol
  rcases Nat.eq_zero_or_pos (A.relIndex B) with h | h
  · simp [h]
  · exact div_le_self (Nat.cast_nonneg _) (by exact_mod_cast h)

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}

omit [NumberField K] [StarRing K] in
theorem line_le {A : Submodule (𝓞 K) K} {v : V} {S : Submodule K V} (h : v ∈ S) :
    line A v ≤ rs (𝓞 K) S := by
  rintro _ ⟨t, -, rfl⟩
  exact S.smul_mem t h

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem e_mem_X (F : FlagD H r) (a : Fin r) : F.e a.castSucc ∈ F.X :=
  Submodule.subset_span ⟨a, a.2, rfl⟩

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem lastVector_mem_jointSpan_left (F F' : FlagD H r) : F.z ∈ V0 F F' :=
  Submodule.mem_sup_right (Submodule.subset_span (by simp))

theorem normalForm_baseLattice_le_dualSpan_sup_line (N : NF H r) : N.P0 ≤ rs (𝓞 K) (V0 N.F N.F' ⊔ N.Ist) := by
  unfold NF.P0
  refine sup_le (sup_le (sup_le (iSup_le fun a => line_le ?_) (iSup_le fun a => iSup_le fun _ => line_le ?_))
    (line_le ?_)) (iSup_le fun a => iSup_le fun ha => line_le ?_)
  · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left (e_mem_X _ a)))
  · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right (e_mem_X _ a)))
  · exact Submodule.mem_sup_left (lastVector_mem_jointSpan_left _ _)
  · exact Submodule.mem_sup_right (Submodule.subset_span ⟨a, ha, rfl⟩)

theorem ref_inf_Pi (N : NF H r) (L : Submodule (𝓞 K) V) (hc : IsCompl N.Wt N.Pi)
    (hn : N.Wn = N.Wt ⊔ Submodule.span K {N.F.z}) (hp : N.Pi = V0 N.F N.F' ⊔ N.Ist)
    (hz : ∀ t : K, t • N.F.z ∈ L → t ∈ (1 : Submodule (𝓞 K) K)) :
    N.Ref L ⊓ rs (𝓞 K) N.Pi = N.P0 := by
  have h0 : N.P0 ≤ rs (𝓞 K) N.Pi := hp ▸ normalForm_baseLattice_le_dualSpan_sup_line N
  have hzP : N.F.z ∈ N.Pi := hp ▸ Submodule.mem_sup_left (lastVector_mem_jointSpan_left _ _)
  refine le_antisymm ?_ (le_inf le_sup_left h0)
  rintro x ⟨hx, hxP⟩
  obtain ⟨p, hpP, l, ⟨hlL, hlW⟩, rfl⟩ := Submodule.mem_sup.1 hx
  have hlW' : l ∈ N.Wt ⊔ Submodule.span K {N.F.z} := hn ▸ hlW
  obtain ⟨w, hw, y, hy, rfl⟩ := Submodule.mem_sup.1 hlW'
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hy
  have hxP' : p + (w + t • N.F.z) ∈ N.Pi := hxP
  have hpP' : p ∈ N.Pi := h0 hpP
  have hwP : w ∈ N.Pi := by
    have := N.Pi.sub_mem (N.Pi.sub_mem hxP' hpP') (N.Pi.smul_mem t hzP)
    simpa using this
  have hw0 : w = 0 := (Submodule.disjoint_def.1 hc.disjoint) w hw hwP
  subst hw0
  rw [zero_add] at hlL ⊢
  refine N.P0.add_mem hpP ?_
  unfold NF.P0
  exact Submodule.mem_sup_left (Submodule.mem_sup_right ⟨t, hz t hlL, rfl⟩)

theorem invVol_skew_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → ∀ e : ℕ, N.Split Λ → N.Near (𝔠 ^ e) Λ → GlobalTheory.HL.invVol (N.Gam (N.Ref (latL N.F N.F' Λ)) ⊓ N.ZI) (N.Gam Λ ⊓ N.ZI) ≤ (Ideal.absNorm 𝔠 : ℝ) ^ ((3 * e + 11) * (2 * r + 1) ^ 2) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hT 𝔠 h0 hst hdT hD e hS hN
  obtain ⟨-, -, hc, hdim, hn, -, -, -, -, -, -, hp⟩ := GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N
  obtain ⟨hR, -⟩ := GlobalTheory.T.hermFramePairCommonUnipotentStabiliser_summary K V H hK r N
  obtain ⟨-, -, hz, -, hlat, -⟩ := GlobalTheory.T.hermFramePair_innerLattices_unimodular_primitive K V H hK r N g Λ hg hT
  have hstab := GlobalTheory.T.stabilizer_hermitianLattice_of_deep_star_congruence K V H hK r N g Λ hg hT 𝔠 h0 hst hdT hD e hS hN
  have hP := ref_inf_Pi N (latL N.F N.F' Λ) hc hn hp (fun t ht => (hz t).1 ht)
  have hfg : N.P0.FG := by
    refine Submodule.FG.of_le hlat.fg ?_
    rw [← hP]; exact inf_le_left
  have hmap : ∀ s ∈ N.Gam (N.Ref (latL N.F N.F' Λ)) ⊓ N.ZI, ∀ x ∈ N.P0, s x ∈ N.P0 := by
    rintro s ⟨⟨hsR, hsS⟩, -, hsW⟩ x hx
    rw [← hP] at hx ⊢
    have hsS' : s • N.Ref (latL N.F N.F' Λ) = N.Ref (latL N.F N.F' Λ) := hsS
    refine ⟨?_, ?_⟩
    · rw [← hsS']
      exact Submodule.smul_mem_pointwise_smul _ _ _ hx.1
    · have hx2 : x ∈ perp H N.Wt := hx.2
      change s x ∈ perp H N.Wt
      rw [mem_perp_iff] at hx2 ⊢
      intro w hw
      have hw' : s w = w := (mem_fixingSubgroup_iff _).1 hsW w hw
      have := ((hR s).1 hsR).1.1 x w
      simp only [LinearEquiv.coe_coe, hw'] at this
      rw [this]; exact hx2 w hw
  have hfix : ∀ s ∈ N.Gam (N.Ref (latL N.F N.F' Λ)) ⊓ N.ZI, s • N.P0 = N.P0 := by
    intro s hs
    refine le_antisymm ?_ ?_
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy
      exact hmap s hs x hx
    · intro y hy
      refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨s⁻¹ y, hmap _ (inv_mem hs) y hy, ?_⟩
      exact s.apply_symm_apply y
  have hm : 𝔠 ^ (3 * e + 10) ≠ ⊥ := pow_ne_zero _ h0
  obtain ⟨-, hle⟩ := GlobalTheory.T.relIndex_congruence_subgroup_le_absNorm_pow K V (N.Gam (N.Ref (latL N.F N.F' Λ)) ⊓ N.ZI) N.P0 (𝔠 ^ (3 * e + 10))
    (N.Gam Λ ⊓ N.ZI) hfg hm hfix (fun s hs hx =>
      ⟨⟨hs.1.1, hstab s ⟨hs.1.1, hs.2.2⟩ hx⟩, hs.2⟩)
  have hrk : Module.finrank K (Submodule.span K (N.P0 : Set V)) ≤ 2 * r + 1 := by
    have h1 : Submodule.span K (N.P0 : Set V) ≤ N.Pi := by
      rw [Submodule.span_le, ← hP]
      exact fun x hx => hx.2
    have h2 := Submodule.finrank_mono h1
    have h3 := Submodule.finrank_add_eq_of_isCompl hc
    omega
  have hpos : 1 ≤ Ideal.absNorm 𝔠 := Nat.one_le_iff_ne_zero.2 (fun h => h0 (Ideal.absNorm_eq_zero_iff.1 h))
  refine (invVol_le_relIndex _ _).trans ?_
  have : (N.Gam Λ ⊓ N.ZI).relIndex (N.Gam (N.Ref (latL N.F N.F' Λ)) ⊓ N.ZI) ≤
      Ideal.absNorm 𝔠 ^ ((3 * e + 11) * (2 * r + 1) ^ 2) := by
    refine hle.trans ?_
    rw [map_pow, ← pow_mul]
    exact Nat.pow_le_pow_right hpos (Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left hrk 2))
  exact_mod_cast this

end GlobalTheory.DegCnt.WtSkew
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormInvVolSkewLayerLeStatement
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermFramePairNormalForm_invVol_skew_layer_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → ∀ e : ℕ, N.Split Λ → N.Near (𝔠 ^ e) Λ → GlobalTheory.HL.invVol (N.Gam (N.Ref (latL N.F N.F' Λ)) ⊓ N.ZI) (N.Gam Λ ⊓ N.ZI) ≤ (Ideal.absNorm 𝔠 : ℝ) ^ ((3 * e + 11) * (2 * r + 1) ^ 2) := by
  first | exact @GlobalTheory.DegCnt.WtSkew.invVol_skew_le | exact GlobalTheory.DegCnt.WtSkew.invVol_skew_le | (intros; apply GlobalTheory.DegCnt.WtSkew.invVol_skew_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormInvVolTopLayerLe
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormInvVolTopLayerLe
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt

section
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}

theorem inN_map_mem_of_le (F : FlagD H r) {g : V →ₗ[K] V} (hg : F.InN g) {S : Submodule K V} (hX : F.X ≤ S)
    (hz : F.z ∈ S) : (∀ x ∈ F.X, g x ∈ S) ∧ g F.z ∈ S := by
  have hXa : ∀ a : Fin r, F.Xa a ≤ F.X := fun a =>
    Submodule.span_mono (Set.image_mono fun b _ => b.isLt)
  have he : ∀ a : Fin r, F.e a.castSucc ∈ F.X := fun a => Submodule.subset_span ⟨a, a.isLt, rfl⟩
  constructor
  · have : F.X ≤ S.comap g := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨a, -, rfl⟩
      have := S.add_mem (hX (hXa a (hg.2.2.1 a))) (hX (he a))
      simpa using this
    exact fun x hx => this hx
  · have := S.add_mem (hX (hg.2.2.2 F.z F.zperp)) hz
    simpa using this

theorem unipotent_map_mem_V0 (F F' : FlagD H r) {g : V →ₗ[K] V} (hg : F.InN g) (hg' : F'.InN g) :
    ∀ x ∈ V0 F F', g x ∈ V0 F F' := by
  have h1 := inN_map_mem_of_le F hg (S := V0 F F') (le_sup_left.trans le_sup_left)
    (Submodule.mem_sup_right (Submodule.subset_span (by simp)))
  have h2 := inN_map_mem_of_le F' hg' (S := V0 F F') (le_sup_right.trans le_sup_left)
    (Submodule.mem_sup_right (Submodule.subset_span (by simp)))
  have : V0 F F' ≤ (V0 F F').comap g := by
    refine sup_le (sup_le h1.1 h2.1) (Submodule.span_le.2 ?_)
    rintro _ (rfl | rfl)
    · exact h1.2
    · exact h2.2
  exact fun x hx => this hx

end

theorem star_stable_pow {K : Type} [Field K] [StarRing K] (𝔠 : Ideal (𝓞 K))
    (h : ∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) (n : ℕ) :
    ∀ x ∈ 𝔠 ^ (n + 1), ∃ y ∈ 𝔠 ^ (n + 1), (y : K) = star (x : K) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    intro x hx
    rw [pow_succ] at hx ⊢
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      obtain ⟨a', ha', ea⟩ := ih a ha
      obtain ⟨b', hb', eb⟩ := h b hb
      refine ⟨a' * b', Ideal.mul_mem_mul ha' hb', ?_⟩
      show (a' : K) * (b' : K) = star ((a : K) * (b : K))
      rw [ea, eb, star_mul']
    · rintro a b ⟨a', ha', ea⟩ ⟨b', hb', eb⟩
      refine ⟨a' + b', add_mem ha' hb', ?_⟩
      show (a' : K) + (b' : K) = star ((a : K) + (b : K))
      rw [ea, eb, star_add]

theorem invVol_top_layer_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → ∀ e : ℕ, N.Split Λ → N.Near (𝔠 ^ e) Λ → GlobalTheory.HL.invVol (N.Gam (N.Ref (latL N.F N.F' Λ)) ⊔ N.R1) (N.Gam Λ ⊔ N.R1) ≤ (Ideal.absNorm 𝔠 : ℝ) ^ ((3 * e + 11) * (2 * r + 1) ^ 2) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hΛ 𝔠 hc0 hcs hcT hcD e hsp hnear
  obtain ⟨hR, -⟩ := GlobalTheory.T.hermFramePairCommonUnipotentStabiliser_summary K V H hK r N
  obtain ⟨hNF, -⟩ := GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N
  obtain ⟨-, -, -, -, hlat, hint⟩ := GlobalTheory.T.hermFramePair_innerLattices_unimodular_primitive K V H hK r N g Λ hg hΛ
  set L := N.Ref (latL N.F N.F' Λ) with hL
  set M := N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F') with hM
  have hMfg : M.FG := by
    rw [← hint]
    exact Submodule.FG.of_le hlat.fg inf_le_left
  have hstab : ∀ A : Subgroup (V ≃ₗ[K] V), (∀ s ∈ A, ∀ x ∈ M, s x ∈ M) →
      A ≤ MulAction.stabilizer (V ≃ₗ[K] V) M := by
    intro A hA s hs
    rw [MulAction.mem_stabilizer_iff]
    apply le_antisymm
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
      exact hA s hs y hy
    · intro x hx
      refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨s⁻¹ • x, hA _ (A.inv_mem hs) x hx, ?_⟩
      rw [smul_inv_smul]
  have hG : N.Gam L ⊔ N.R1 ≤ MulAction.stabilizer (V ≃ₗ[K] V) M := by
    refine sup_le (hstab _ ?_) (hstab _ ?_)
    · intro s hs x hx
      rw [← hint] at hx ⊢
      refine ⟨?_, unipotent_map_mem_V0 N.F N.F' ((hR s).1 hs.1).1 ((hR s).1 hs.1).2 x hx.2⟩
      have h1 : s • L = L := hs.2
      have h2 := Submodule.smul_mem_pointwise_smul x s L hx.1
      rw [h1] at h2
      exact h2
    · intro s hs x hx
      have h1 : s • x = x := (mem_fixingSubgroup_iff _).1 hs.2 x hx.2
      have h2 : s x = x := h1
      rw [h2]
      exact hx
  have hGR : N.Gam L ⊔ N.R1 ≤ N.R := sup_le inf_le_left inf_le_left
  have hle : 𝔠 ^ (3 * e + 11) ≤ Ideal.span {(N.T : 𝓞 K)} * 𝔠 ^ (3 * e + 10) := by
    rw [show 3 * e + 11 = (3 * e + 10) + 1 from rfl, pow_succ']
    exact Ideal.mul_mono_left fun x hx => Ideal.mem_span_singleton.2 (hcT x hx)
  obtain ⟨h0, hidx⟩ := GlobalTheory.T.relIndex_congruence_subgroup_le_absNorm_pow K V (N.Gam L ⊔ N.R1) M (𝔠 ^ (3 * e + 11)) (N.Gam Λ ⊔ N.R1) hMfg
    (pow_ne_zero _ hc0) (fun s hs => hG hs) (by
      intro s hs hcong
      obtain ⟨s', hs', hV, hP⟩ := GlobalTheory.T.hermFramePairNormalForm_congruence_lift_smallGroup K V H hK r N (𝔠 ^ (3 * e + 10))
        (star_stable_pow 𝔠 hcs (3 * e + 9)) s (hGR hs)
        (fun x hx => Submodule.smul_mono_left hle (hcong x hx))
      have hfix := GlobalTheory.T.stabilizer_hermitianLattice_of_deep_star_congruence K V H hK r N g Λ hg hΛ 𝔠 hc0 hcs hcT hcD e hsp hnear s' hs' hP
      have h1 : s' ∈ N.Gam Λ := ⟨hs'.1, hfix⟩
      have h2 : s'⁻¹ * s ∈ N.R1 := by
        refine ⟨N.R.mul_mem (N.R.inv_mem hs'.1) (hGR hs), (mem_fixingSubgroup_iff _).2 fun y hy => ?_⟩
        have h3 : s • y = s' • y := (hV y hy).symm
        rw [mul_smul, h3, inv_smul_smul]
      have h4 := mul_mem (Subgroup.mem_sup_left h1 : s' ∈ N.Gam Λ ⊔ N.R1) (Subgroup.mem_sup_right h2)
      rwa [mul_inv_cancel_left] at h4)
  have hd : Module.finrank K (Submodule.span K (M : Set V)) ≤ 2 * r + 1 := by
    have h1 : Submodule.span K (M : Set V) ≤ V0 N.F N.F' := Submodule.span_le.2 fun x hx => hx.2
    have h2 := Submodule.finrank_mono h1
    have h3 := hNF.2.2.2.2.1
    have h4 := N.j_le
    omega
  have hn : 1 ≤ Ideal.absNorm 𝔠 := Nat.one_le_iff_ne_zero.2 (fun h => hc0 (Ideal.absNorm_eq_zero_iff.1 h))
  have hfin : (N.Gam Λ ⊔ N.R1).relIndex (N.Gam L ⊔ N.R1) ≤
      Ideal.absNorm 𝔠 ^ ((3 * e + 11) * (2 * r + 1) ^ 2) := by
    refine hidx.trans ?_
    rw [map_pow, ← pow_mul]
    exact Nat.pow_le_pow_right hn (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hd 2))
  have hdiv : ∀ a b : ℕ, (a : ℝ) / (b : ℝ) ≤ a := by
    intro a b
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp
    · exact div_le_self (Nat.cast_nonneg a) (by exact_mod_cast hb)
  unfold GlobalTheory.HL.invVol
  refine (hdiv _ _).trans ?_
  exact_mod_cast hfin

end GlobalTheory.DegCnt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormInvVolTopLayerLeStatement
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermFramePairNormalForm_invVol_top_layer_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → ∀ e : ℕ, N.Split Λ → N.Near (𝔠 ^ e) Λ → GlobalTheory.HL.invVol (N.Gam (N.Ref (latL N.F N.F' Λ)) ⊔ N.R1) (N.Gam Λ ⊔ N.R1) ≤ (Ideal.absNorm 𝔠 : ℝ) ^ ((3 * e + 11) * (2 * r + 1) ^ 2) := by
  first | exact @GlobalTheory.DegCnt.invVol_top_layer_le | exact GlobalTheory.DegCnt.invVol_top_layer_le | (intros; apply GlobalTheory.DegCnt.invVol_top_layer_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitTermWeightLeNearReferenceLattice
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.Weight

theorem invVol_three {G : Type} [Group G] (R M Z A B : Subgroup G) (hM : M ≤ R) (hZ : Z ≤ M) (hA : A ≤ R) (hB : B ≤ R)
    (nM : ∀ s ∈ R, ∀ t ∈ M, s * t * s⁻¹ ∈ M) (nZ : ∀ s ∈ R, ∀ t ∈ Z, s * t * s⁻¹ ∈ Z)
    (h1 : A.relIndex B ≠ 0) (h2 : B.relIndex A ≠ 0)
    (h3 : (A ⊓ M).relIndex (B ⊓ M) ≠ 0) (h4 : (B ⊓ M).relIndex (A ⊓ M) ≠ 0) :
    GlobalTheory.HL.invVol A B = GlobalTheory.HL.invVol (A ⊓ Z) (B ⊓ Z) * GlobalTheory.HL.invVol ((A ⊓ M) ⊔ Z) ((B ⊓ M) ⊔ Z) *
      GlobalTheory.HL.invVol (A ⊔ M) (B ⊔ M) := by
  rw [(GlobalTheory.IndexProd.invVol_eq_inf_mul_sup_and_mono G R M A B hM hA hB nM h1 h2).1,
    (GlobalTheory.IndexProd.invVol_eq_inf_mul_sup_and_mono G M Z (A ⊓ M) (B ⊓ M) hZ inf_le_right inf_le_right
      (fun s hs t ht => nZ s (hM hs) t ht) h3 h4).1,
    inf_assoc, inf_assoc, inf_eq_right.mpr hZ]

theorem invVol_nonneg {G : Type} [Group G] (A B : Subgroup G) : 0 ≤ GlobalTheory.HL.invVol A B := by
  unfold GlobalTheory.HL.invVol
  positivity

theorem om_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → ∀ e : ℕ, N.Split Λ → N.Near (𝔠 ^ e) Λ → N.om Λ ≤ (N.bI Λ : ℝ) ^ Module.finrank K N.Wt * N.Del ^ r * (Ideal.absNorm 𝔠 : ℝ) ^ (2 * (3 * e + 11) * (2 * r + 1) ^ 2) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hT 𝔠 hc hs hTd hD e hSp hNe
  obtain ⟨-, -, nM, nZ, hnil⟩ := GlobalTheory.UnipStab.common_unipotent_stabiliser K V H hK r N
  obtain ⟨-, -, -, -, hRef, -⟩ := GlobalTheory.T.hermFramePair_innerLattices_unimodular_primitive K V H hK r N g Λ hg hT
  obtain ⟨-, hg0, hi0, -, hgi, -⟩ := GlobalTheory.T.flagPairDefiniteThetaLattice_le_fixed_index_bound K V H hK r N g Λ hg hT
  have hTop := GlobalTheory.T.hermFramePairNormalForm_invVol_top_layer_le K V H hK r N g Λ hg hT 𝔠 hc hs hTd hD e hSp hNe
  have hBot := GlobalTheory.T.hermFramePairNormalForm_invVol_skew_layer_le K V H hK r N g Λ hg hT 𝔠 hc hs hTd hD e hSp hNe
  have hMid := GlobalTheory.T.haarInvVolume_middleLayer_eichler_le K V H hK r N g Λ hg hT hSp
  have hΛ : Submodule.IsFullLattice K Λ := by
    have h := hT.1.1.1
    unfold IsLatMod at h
    obtain ⟨⟨M, hM, hE⟩, hsp⟩ := h
    have hfg : Λ.FG := by
      rw [hE, rs, Submodule.restrictScalars_bot, sup_bot_eq]
      exact hM
    letI : Submodule.IsLattice K Λ := Submodule.IsLattice.of_fg K hfg
    exact ⟨hsp⟩
  have hRefFull : Submodule.IsFullLattice K (N.Ref (latL N.F N.F' Λ)) := by
    letI := hRef
    obtain ⟨_, _, hC, _, hWn, hUp, _, _, _, _, _, hPi⟩ :=
      GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N
    have hspan : Submodule.span K (N.Ref (latL N.F N.F' Λ) : Set V) = ⊤ := by
      apply eq_top_iff.mpr
      rw [← hC.sup_eq_top]
      apply sup_le
      · intro w hw
        obtain ⟨c, hc, hcΛ⟩ := GlobalTheory.DegCnt.InnerLat.exists_mult hΛ.span_eq_top w
        have hwN : w ∈ N.Wn := by rw [hWn]; exact Submodule.mem_sup_left hw
        have hwU : w ∈ uPerp N.F N.F' := by rw [hUp]; exact Submodule.mem_sup_left hwN
        rw [← Submodule.smul_mem_iff _ hc]
        apply Submodule.subset_span
        exact Submodule.mem_sup_right ⟨⟨(uPerp N.F N.F').smul_mem c hwU,
          Submodule.mem_sup_left hcΛ⟩, N.Wn.smul_mem c hwN⟩
      · rw [hPi, ← GlobalTheory.DegCnt.InnerLat.span_hermFramePair_lattice_eq_sup N]
        exact Submodule.span_mono (show (N.P0 : Set V) ⊆ N.Ref (latL N.F N.F' Λ) from
          fun _ hx => Submodule.mem_sup_left hx)
    exact ⟨hspan⟩
  have hR1 : N.R1 ≤ N.R := inf_le_left
  have hZ : N.ZI ≤ N.R1 := inf_le_left
  have key : ∀ L : Submodule (𝓞 K) V, N.Gam L ⊓ N.R1 = N.R1 ⊓ MulAction.stabilizer (V ≃ₗ[K] V) L := by
    intro L
    unfold NF.Gam
    rw [inf_right_comm, inf_eq_right.mpr hR1]
  have hnil1 : ∀ s ∈ N.R1, ((s : V →ₗ[K] V) - 1) ^ (2 * r + 1) = 0 := fun s hs => hnil s (hR1 hs)
  have h3 := (GlobalTheory.DegCnt.Unimod.invVol_smul K V N.R1 _ hnil1 _ _ hRefFull hΛ).1
  have h4 := (GlobalTheory.DegCnt.Unimod.invVol_smul K V N.R1 _ hnil1 _ _ hΛ hRefFull).1
  rw [← key, ← key] at h3 h4
  have hprod := invVol_three N.R N.R1 N.ZI (N.Gam (N.Ref (latL N.F N.F' Λ))) (N.Gam Λ) hR1 hZ inf_le_left inf_le_left
    nM nZ (GlobalTheory.DegCnt.Unimod.invVol_smul K V N.R _ hnil _ _ hRefFull hΛ).1
    (GlobalTheory.DegCnt.Unimod.invVol_smul K V N.R _ hnil _ _ hΛ hRefFull).1 h3 h4
  have h1 : (1 : ℝ) ≤ (N.gI g Λ : ℝ) * N.iI g Λ := by
    have : 1 ≤ N.gI g Λ * N.iI g Λ := Nat.mul_pos hg0 hi0
    exact_mod_cast this
  have hpow : ((N.gI g Λ : ℝ) * N.iI g Λ) ^ (r - N.j) ≤ N.Del ^ r :=
    (pow_le_pow_right₀ h1 (Nat.sub_le _ _)).trans (pow_le_pow_left₀ (by linarith) hgi r)
  have hMid' := hMid.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
  have hDel : (0 : ℝ) ≤ N.Del := by linarith
  unfold NF.om
  rw [hprod]
  calc _ ≤ (Ideal.absNorm 𝔠 : ℝ) ^ ((3 * e + 11) * (2 * r + 1) ^ 2) *
        ((N.bI Λ : ℝ) ^ Module.finrank K N.Wt * N.Del ^ r) *
        (Ideal.absNorm 𝔠 : ℝ) ^ ((3 * e + 11) * (2 * r + 1) ^ 2) :=
        mul_le_mul (mul_le_mul hBot hMid' (invVol_nonneg _ _) (by positivity)) hTop (invVol_nonneg _ _) (by positivity)
    _ = _ := by rw [mul_assoc 2, two_mul ((3 * e + 11) * _), pow_add]; ring

end GlobalTheory.DegCnt.Weight
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitTermWeightLeNearReferenceLatticeStatement
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitTermWeight_le_near_referenceLattice : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → ∀ e : ℕ, N.Split Λ → N.Near (𝔠 ^ e) Λ → N.om Λ ≤ (N.bI Λ : ℝ) ^ Module.finrank K N.Wt * N.Del ^ r * (Ideal.absNorm 𝔠 : ℝ) ^ (2 * (3 * e + 11) * (2 * r + 1) ^ 2) := by
  first | exact @GlobalTheory.DegCnt.Weight.om_le | exact GlobalTheory.DegCnt.Weight.om_le | (intros; apply GlobalTheory.DegCnt.Weight.om_le <;> assumption)
end

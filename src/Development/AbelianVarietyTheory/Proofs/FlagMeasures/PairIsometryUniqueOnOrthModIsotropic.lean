module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemOfPerpPerp
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LinearFormsBoundedRepresentatives

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDenominatorOfFg
open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal

namespace GlobalTheory

theorem exists_denominator_of_fg {V : Type} [AddCommGroup V] (B : V →ₗ[ℤ] V →ₗ[ℤ] ℚ)
    (M : Submodule ℤ V) (hM : M.FG) :
    ∃ d : ℕ, 0 < d ∧ ∀ x ∈ M, ∀ y ∈ M, ∃ n : ℤ, (d : ℚ) * B x y = n := by
  obtain ⟨s, hs⟩ := Submodule.FG.map₂ B hM hM
  refine ⟨∏ a ∈ s, a.den, Finset.prod_pos fun a _ => a.den_pos, ?_⟩
  have key : ∀ r ∈ Submodule.span ℤ (s : Set ℚ), ∃ n : ℤ, ((∏ a ∈ s, a.den : ℕ) : ℚ) * r = n := by
    intro r hr
    induction hr using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun a : ℚ => a.den) (Finset.mem_coe.mp ha)
      refine ⟨c * a.num, ?_⟩
      rw [hc]
      push_cast
      rw [← Rat.den_mul_eq_num]; ring
    | zero => exact ⟨0, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨m, hm⟩ := ha
      obtain ⟨n, hn⟩ := hb
      exact ⟨m + n, by rw [mul_add, hm, hn]; push_cast; ring⟩
    | smul c a _ ha =>
      obtain ⟨m, hm⟩ := ha
      exact ⟨c * m, by rw [zsmul_eq_mul, mul_left_comm, hm]; push_cast; ring⟩
  intro x hx y hy
  exact key _ (hs ▸ Submodule.apply_mem_map₂ B hx hy)

theorem isom_sub_mem_of_congr : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (U X : Submodule K V) (M : Submodule (𝓞 K) V) (γ : V ≃ₗ[K] V) (g : ℕ), h.IsSymm → X ≤ U → (∀ x ∈ X, ∀ y ∈ U, h x y = 0) → (∀ x ∈ U, x ∉ X → 0 < Algebra.trace ℚ K (h x x)) → M.FG → (∀ x ∈ M, x ∈ U) → γ ∈ Formalism.HermitianLatticesTheory.isom h → (∀ x ∈ X, γ x ∈ X) → 3 ≤ g → (∀ x ∈ M, ∃ y ∈ M, γ x - x - (g : K) • y ∈ X) → ∀ x ∈ M, γ x - x ∈ X := by
  intro K V _ _ _ _ _ _ _ _ h U X M γ g hs hXU hrad hpos hM hMU hγ hγX hg hcong
  have hiso : ∀ x y, h (γ x) (γ y) = h x y := hγ
  have hrad' : ∀ y ∈ U, ∀ x ∈ X, h y x = 0 := fun y hy x hx => by
    rw [← hs.eq x y, hrad x hx y hy, map_zero]
  let B : V →ₗ[ℤ] V →ₗ[ℤ] ℚ := LinearMap.mk₂ ℤ (fun x y => Algebra.trace ℚ K (h x y))
    (fun a b c => by simp) (fun c a b => by rw [map_zsmul h, LinearMap.smul_apply, map_zsmul])
    (fun a b c => by simp)
    (fun c a b => by rw [map_zsmul (h a), map_zsmul])
  have hB : ∀ x y, B x y = Algebra.trace ℚ K (h x y) := fun _ _ => rfl
  obtain ⟨d, hd, hden⟩ := exists_denominator_of_fg B (M.restrictScalars ℤ) (hM.restrictScalars)
  have hnn : ∀ x ∈ U, 0 ≤ B x x := fun x hx => by
    by_cases hxX : x ∈ X
    · rw [hB, hrad x hxX x hx, map_zero]
    · exact (hpos x hx hxX).le
  have main : ∀ n : ℕ, ∀ x ∈ M, (d : ℚ) * B x x < n → γ x - x ∈ X := by
    intro n
    induction n with
    | zero =>
      intro x hx hlt
      have := hnn x (hMU x hx)
      have : (0 : ℚ) ≤ d * B x x := by positivity
      simp at hlt
      linarith
    | succ n ih =>
      intro x hx hlt
      by_cases hxX : x ∈ X
      · exact X.sub_mem (hγX x hxX) hxX
      obtain ⟨y, hy, hu⟩ := hcong x hx
      set u := γ x - x - (g : K) • y with hu_def
      set z := γ x - x with hz_def
      have hz : z = (g : K) • y + u := by rw [hu_def]; abel
      have hxU := hMU x hx
      have hyU := hMU y hy
      have hzU : z ∈ U := hz ▸ U.add_mem (U.smul_mem _ hyU) (hXU hu)
      have hγx : γ x = x + z := by rw [hz_def]; abel
      have hγxU : γ x ∈ U := hγx ▸ U.add_mem hxU hzU
      have h1 : B z z = (g : ℚ) ^ 2 * B y y := by
        have e1 : B u z = 0 := by rw [hB, hrad u hu z hzU, map_zero]
        have e2 : B y u = 0 := by rw [hB, hrad' y hyU u hu, map_zero]
        have hz' : z = (g : ℤ) • y + u := by rw [hz, natCast_zsmul, Nat.cast_smul_eq_nsmul]
        calc B z z = B ((g : ℤ) • y + u) z := by rw [← hz']
          _ = (g : ℤ) • B y z := by rw [map_add (f := _), LinearMap.add_apply, e1, map_smul]; simp
          _ = (g : ℤ) • B y ((g : ℤ) • y + u) := by rw [← hz']
          _ = _ := by rw [map_add (f := _), e2, map_smul]; simp; ring
      have h2 : B z z + B (γ x + x) (γ x + x) = 4 * B x x := by
        have e : B (γ x) (γ x) = B x x := by rw [hB, hB, hiso]
        rw [hz_def]
        simp only [map_add (f := _), map_sub, LinearMap.add_apply, LinearMap.sub_apply, e]
        ring
      have h3 := hnn _ (U.add_mem hγxU hxU)
      have hxp : 0 < B x x := hpos x hxU hxX
      have hyn := hnn y hyU
      have hg' : (9 : ℚ) ≤ (g : ℚ) ^ 2 := by
        have : (3 : ℚ) ≤ g := by exact_mod_cast hg
        nlinarith
      have hlt' : B y y < B x x := by nlinarith
      have hd' : (0 : ℚ) < d := by exact_mod_cast hd
      obtain ⟨a, ha⟩ := hden x hx x hx
      obtain ⟨b, hb⟩ := hden y hy y hy
      have hab : b < a := by
        have : (b : ℚ) < a := by rw [← ha, ← hb]; exact mul_lt_mul_of_pos_left hlt' hd'
        exact_mod_cast this
      have han : a < n + 1 := by
        rw [ha] at hlt
        exact_mod_cast hlt
      have hyX : γ y - y ∈ X := ih y hy (by
        rw [hb]
        have : b < n := by omega
        exact_mod_cast this)
      have hw : γ z - z ∈ X := by
        have : γ z - z = (g : K) • (γ y - y) + (γ u - u) := by
          rw [hz, map_add (f := _), map_smul, smul_sub]; abel
        rw [this]
        exact X.add_mem (X.smul_mem _ hyX) (X.sub_mem (hγX u hu) hu)
      have hzz : h z z = 0 := by
        have e := hiso x z
        have e2 : h (γ x) (γ z - z) = 0 := hrad' _ hγxU _ hw
        rw [map_sub, e, hγx, map_add (f := _), LinearMap.add_apply] at e2
        linear_combination -e2
      by_contra hzX
      have := hpos z hzU hzX
      rw [hzz, map_zero] at this
      exact lt_irrefl _ this
  intro x hx
  obtain ⟨n, hn⟩ := exists_nat_gt ((d : ℚ) * B x x)
  exact main n x hx hn

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairIsometryUniqueOnOrthModIsotropic
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC.BetaUniq

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

theorem keeps_orth {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (P : Submodule E S.V)
    (hP : ∀ x ∈ P, γ x ∈ P) : ∀ x ∈ orth S P, γ x ∈ orth S P := by
  have hle : P.map (γ : S.V →ₗ[E] S.V) ≤ P := by
    rintro _ ⟨x, hx, rfl⟩
    exact hP x hx
  have heq : P.map (γ : S.V →ₗ[E] S.V) = P :=
    Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq γ P)
  have hiso : ∀ x y, S.hT (γ x) (γ y) = S.hT x y := hγ
  intro x hx
  rw [Formalism.MainNotions.mem_orth_iff] at hx ⊢
  intro y hy
  rw [← heq] at hy
  obtain ⟨y, hy, rfl⟩ := hy
  exact (hiso y x).trans (hx y hy)

theorem exists_of_mem_gsmul {Λ : Submodule (𝓞 E) S.V} {g : ℕ} {a : S.V}
    (h : a ∈ Ideal.span {(g : 𝓞 E)} • Λ) : ∃ l ∈ Λ, a = (g : E) • l := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h
  obtain ⟨b, hb, rfl⟩ := h
  refine ⟨b, hb, ?_⟩
  rw [← algebraMap_smul E (g : 𝓞 E) b, map_natCast]

theorem gsmul_mem {Λ : Submodule (𝓞 E) S.V} (g : ℕ) {l : S.V} (hl : l ∈ Λ) :
    (g : E) • l ∈ Ideal.span {(g : 𝓞 E)} • Λ := by
  rw [← map_natCast (algebraMap (𝓞 E) E) g, algebraMap_smul]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hl

theorem int_pair {Λ : Submodule (𝓞 E) S.V} (hu : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) :
    ∀ x ∈ Λ, ∀ y ∈ Λ, S.hT x y ∈ (1 : Submodule (𝓞 E) E) := fun x hx y hy => by
  rw [← hu, Formalism.HermitianLatticesTheory.dualBasic_mem_dual] at hy
  exact hy x hx

theorem exists_sub_smul_mem_orth {r : ℕ} {T' : E} (A : LFlag S r T') (hT : T' ≠ 0) :
    ∀ x ∈ orth S (Xsp A), ∃ a : E, x - a • A.fl.z ∈ orth S (Xplus A) := by
  intro x hx
  rw [Formalism.MainNotions.mem_orth_iff] at hx
  refine ⟨S.hT A.fl.z x / (-T'), ?_⟩
  rw [Formalism.MainNotions.mem_orth_iff]
  refine Formalism.MainNotions.hT_zero_of_mem_Xplus A.fl (fun a => ?_) ?_
  · rw [map_sub, map_smul, A.fl.z_orth, smul_zero, sub_zero]
    exact hx _ (Submodule.subset_span ⟨a, rfl⟩)
  · rw [map_sub, map_smul, A.fl.z_norm, smul_eq_mul, div_mul_cancel₀ _ (neg_ne_zero.2 hT), sub_self]

end GlobalTheory.LoopC.BetaUniq

namespace GlobalTheory.LoopC.BetaUniq

theorem main : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T T' : E)
    (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (F : LFlag S r T) (A B : LFlag S r T')
    (β₁ β₂ : S.V ≃ₗ[E] S.V), Submodule.IsLattice E Λ → Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ → 3 ≤ g → T' ≠ 0 →
    (∀ x ∈ orth S (Xplus A), x ∉ Xsp A → 0 < Algebra.trace ℚ E (S.hT x x)) →
    XLam Λ F ≤ Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ A →
    XLam Λ F ≤ Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ B →
    IsAutLam S Λ β₁ → (Xsp A).map (β₁ : S.V →ₗ[E] S.V) = Xsp B → β₁ A.fl.z - B.fl.z ∈ Xsp B →
    IotaCompat Λ F A B β₁ g →
    IsAutLam S Λ β₂ → (Xsp A).map (β₂ : S.V →ₗ[E] S.V) = Xsp B → β₂ A.fl.z - B.fl.z ∈ Xsp B →
    IotaCompat Λ F A B β₂ g → ∀ x ∈ orth S (Xsp A), β₁ x - β₂ x ∈ Xsp B := by
  intro E _ _ _ S r T T' Λ g F A B β₁ β₂ hΛ hu hg hT' hpos hFA hFB h1a h1X h1z h1ι h2a h2X h2z h2ι
  have hg0 : (g : E) ≠ 0 := by exact_mod_cast (show g ≠ 0 by omega)
  have hΛ₁ : ∀ x, β₁ x ∈ Λ ↔ x ∈ Λ := FrEqv.aut_mem_iff h1a
  have hΛ₂ : ∀ x, β₂ x ∈ Λ ↔ x ∈ Λ := FrEqv.aut_mem_iff h2a
  have hΛ₁' : ∀ x, β₁.symm x ∈ Λ ↔ x ∈ Λ := fun x => by
    rw [← hΛ₁ (β₁.symm x), LinearEquiv.apply_symm_apply]
  have hX₁ : ∀ x ∈ Xsp A, β₁ x ∈ Xsp B := fun x hx => h1X ▸ Submodule.mem_map_of_mem hx
  have hX₂ : ∀ x ∈ Xsp A, β₂ x ∈ Xsp B := fun x hx => h2X ▸ Submodule.mem_map_of_mem hx
  have hX₁' : ∀ y ∈ Xsp B, β₁.symm y ∈ Xsp A := fun y hy => by
    rw [← h1X] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    simpa using hx
  set δ : S.V ≃ₗ[E] S.V := β₁⁻¹ * β₂ with hδ_def
  have hδ_apply : ∀ x, δ x = β₁.symm (β₂ x) := fun x => by
    rw [hδ_def, LinearEquiv.mul_apply, LinearEquiv.coe_inv]
  have hδ : δ ∈ Formalism.HermitianLatticesTheory.isom S.hT := mul_mem (inv_mem h1a.1) h2a.1
  have hδX : ∀ x ∈ Xsp A, δ x ∈ Xsp A := fun x hx => by
    rw [hδ_apply]; exact hX₁' _ (hX₂ x hx)
  have hδz : δ A.fl.z - A.fl.z ∈ Xsp A := by
    have e : δ A.fl.z - A.fl.z = β₁.symm (β₂ A.fl.z - β₁ A.fl.z) := by
      rw [hδ_apply, map_sub, LinearEquiv.symm_apply_apply]
    rw [e]
    refine hX₁' _ ?_
    have := (Xsp B).sub_mem h2z h1z
    convert this using 1; abel
  have hδXp : ∀ x ∈ Xplus A, δ x ∈ Xplus A := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hb
    rw [map_add (f := _), map_smul]
    refine (Xplus A).add_mem (Submodule.mem_sup_left (hδX a ha)) ?_
    have e : c • δ A.fl.z = c • (δ A.fl.z - A.fl.z) + c • A.fl.z := by rw [← smul_add]; congr 1; abel
    rw [e]
    exact (Xplus A).add_mem (Submodule.mem_sup_left ((Xsp A).smul_mem c hδz))
      (Submodule.mem_sup_right (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)))
  set U : Submodule E S.V := orth S (Xplus A) with hU_def
  have hδU : ∀ x ∈ U, δ x ∈ U := keeps_orth hδ _ hδXp
  have hXU : Xsp A ≤ U := Formalism.MainNotions.X_le_orth_Xplus A.fl
  have hrad : ∀ x ∈ Xsp A, ∀ y ∈ U, S.hT x y = 0 := fun x hx y hy =>
    (Formalism.MainNotions.mem_orth_iff _ _).1 hy x (Submodule.mem_sup_left hx)
  have hrad' : ∀ y ∈ U, ∀ x ∈ Xsp A, S.hT y x = 0 := fun y hy x hx =>
    Formalism.MainNotions.hT_swap_zero (hrad x hx y hy)
  set M : Submodule (𝓞 E) S.V := Λ ⊓ toO S U with hM_def
  have hM : ∀ x, x ∈ M ↔ x ∈ Λ ∧ x ∈ U := fun x => Iff.rfl
  haveI : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.mpr hΛ.fg
  have hMfg : M.FG := Submodule.FG.of_le_of_isNoetherian (T := Λ) inf_le_left
  have hint := int_pair hu
  have hUXA : U ≤ orth S (Xsp A) := fun y hy => by
    rw [Formalism.MainNotions.mem_orth_iff] at hy ⊢
    exact fun x hx => hy x (Submodule.mem_sup_left hx)

  have hcong : ∀ x ∈ M, ∃ y ∈ M, δ x - x - (g : E) • y ∈ Xsp A := by
    intro x hx
    obtain ⟨hxΛ, hxU⟩ := (hM x).1 hx

    obtain ⟨l', hl'Λ, hl'⟩ := GlobalTheory.Mass.RowPerp.exists_sub_mem S.herm S.nondeg hΛ hu (orth S (Xsp F))
      ((g : E)⁻¹ • x) (fun y hyΛ hy => by
        have hyX : y ∈ Xsp F := GlobalTheory.Mass.RowPerp.mem_of_perp_perp S.nondeg (Xsp F) y fun w hw =>
          Formalism.MainNotions.hT_swap_zero (hy w ((Formalism.MainNotions.mem_orth_iff _ _).2 hw))
        obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (hFA (Submodule.mem_inf.2 ⟨hyΛ, hyX⟩))
        obtain ⟨l, hlΛ, rfl⟩ := exists_of_mem_gsmul ha
        obtain ⟨t, ht⟩ := Submodule.mem_one.1 (hint x hxΛ l hlΛ)
        refine Submodule.mem_one.2 ⟨t, ?_⟩
        rw [LinearMap.map_smulₛₗ S.hT, LinearMap.smul_apply, map_add (f := _), map_smul,
          hrad' x hxU b (Submodule.mem_inf.1 hb).2, add_zero, starRingEnd_apply, star_inv₀, star_natCast,
          smul_eq_mul, smul_eq_mul, ht, inv_mul_cancel_left₀ hg0])
    set l : S.V := x - (g : E) • l' with hl_def
    have hlΛ : l ∈ Λ := by
      rw [hl_def, ← map_natCast (algebraMap (𝓞 E) E) g, algebraMap_smul]
      exact Λ.sub_mem hxΛ (Λ.smul_mem _ hl'Λ)
    have hlF : l ∈ Lrep Λ F := by
      refine Submodule.mem_inf.2 ⟨hlΛ, ?_⟩
      have e : l = (g : E) • ((g : E)⁻¹ • x - l') := by
        rw [hl_def, smul_sub, smul_smul, mul_inv_cancel₀ hg0, one_smul]
      rw [e]
      exact (orth S (Xsp F)).smul_mem _ hl'
    have hlx : l - x ∈ NgX Λ g F A := by
      have e : l - x = (g : E) • (-l') := by rw [hl_def, smul_neg]; abel
      rw [e]
      exact Submodule.mem_sup_left (Submodule.mem_sup_left (gsmul_mem g (Λ.neg_mem hl'Λ)))
    have hxA : x ∈ Lrep Λ A := Submodule.mem_inf.2 ⟨hxΛ, hUXA hxU⟩
    have hb1 : l - β₁ x ∈ NgX Λ g F B := (h1ι x hxA l hlF).1 hlx
    have hb2 : l - β₂ x ∈ NgX Λ g F B := (h2ι x hxA l hlF).1 hlx
    have hdiff : β₂ x - β₁ x ∈ Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ B := by
      have hle : NgX Λ g F B ≤ Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ B :=
        sup_le (sup_le le_sup_left hFB) le_sup_right
      have := (NgX Λ g F B).sub_mem hb1 hb2
      refine hle ?_
      convert this using 1; abel
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hdiff
    obtain ⟨lam, hlam, rfl⟩ := exists_of_mem_gsmul ha
    have hbA : β₁.symm b ∈ Xsp A := hX₁' b (Submodule.mem_inf.1 hb).2
    have key : δ x - x - (g : E) • β₁.symm lam = β₁.symm b := by
      have e : b = (β₂ x - β₁ x) - (g : E) • lam := by rw [← hab]; abel
      rw [e, map_sub, map_sub, map_smul, LinearEquiv.symm_apply_apply, hδ_apply]
    refine ⟨β₁.symm lam, (hM _).2 ⟨(hΛ₁' lam).2 hlam, ?_⟩, ?_⟩
    · have e : β₁.symm lam = (g : E)⁻¹ • (δ x - x - β₁.symm b) := by
        rw [← key, sub_sub_cancel, smul_smul, inv_mul_cancel₀ hg0, one_smul]
      rw [e]
      exact U.smul_mem _ (U.sub_mem (U.sub_mem (hδU x hxU) hxU) (hXU hbA))
    · rw [key]; exact hbA
  have hmain : ∀ x ∈ M, δ x - x ∈ Xsp A :=
    GlobalTheory.isom_sub_mem_of_congr E S.V S.hT U (Xsp A) M δ g S.herm hXU hrad hpos hMfg
      (fun x hx => ((hM x).1 hx).2) hδ hδX hg hcong

  have hext : ∀ x ∈ orth S (Xsp A), δ x - x ∈ Xsp A := by
    intro x hx
    obtain ⟨a, hy⟩ := exists_sub_smul_mem_orth A hT' x hx
    set y := x - a • A.fl.z with hy_def
    have hfull : Submodule.IsFullLattice E Λ :=
      { toIsLattice := hΛ, span_eq_top := GlobalTheory.LoopC.FunIdx.span_eq_top_of_unimodular Λ hΛ hu }
    obtain ⟨d, hd0, hd⟩ := GlobalTheory.Mass.RowPerp.exists_smul_mem hfull y
    have hdM : d • y ∈ M := (hM _).2 ⟨hd, by
      rw [← algebraMap_smul E d y]; exact U.smul_mem _ hy⟩
    have h1 := hmain _ hdM
    rw [← algebraMap_smul E d y, map_smul, ← smul_sub] at h1
    have hyX : δ y - y ∈ Xsp A :=
      (Submodule.smul_mem_iff _ ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hd0)).1 h1
    have e : δ x - x = a • (δ A.fl.z - A.fl.z) + (δ y - y) := by
      rw [hy_def, map_sub, map_smul, smul_sub]; abel
    rw [e]
    exact (Xsp A).add_mem ((Xsp A).smul_mem a hδz) hyX
  intro x hx
  have e : β₁ x - β₂ x = -(β₁ (δ x - x)) := by
    rw [hδ_apply, map_sub, LinearEquiv.apply_symm_apply, neg_sub]
  rw [e]
  exact (Xsp B).neg_mem (hX₁ _ (hext x hx))

end GlobalTheory.LoopC.BetaUniq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairIsometryUniqueOnOrthModIsotropicStatement
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_isometry_unique_on_orth_mod_isotropic : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T T' : E) (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (F : LFlag S r T) (A B : LFlag S r T') (β₁ β₂ : S.V ≃ₗ[E] S.V), Submodule.IsLattice E Λ → Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ → 3 ≤ g → T' ≠ 0 → (∀ x ∈ orth S (Xplus A), x ∉ Xsp A → 0 < Algebra.trace ℚ E (S.hT x x)) → XLam Λ F ≤ Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ A → XLam Λ F ≤ Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ B → IsAutLam S Λ β₁ → (Xsp A).map (β₁ : S.V →ₗ[E] S.V) = Xsp B → β₁ A.fl.z - B.fl.z ∈ Xsp B → IotaCompat Λ F A B β₁ g → IsAutLam S Λ β₂ → (Xsp A).map (β₂ : S.V →ₗ[E] S.V) = Xsp B → β₂ A.fl.z - B.fl.z ∈ Xsp B → IotaCompat Λ F A B β₂ g → ∀ x ∈ orth S (Xsp A), β₁ x - β₂ x ∈ Xsp B := by
  first | exact @GlobalTheory.LoopC.BetaUniq.main | exact GlobalTheory.LoopC.BetaUniq.main | (intros; apply GlobalTheory.LoopC.BetaUniq.main <;> assumption)
end

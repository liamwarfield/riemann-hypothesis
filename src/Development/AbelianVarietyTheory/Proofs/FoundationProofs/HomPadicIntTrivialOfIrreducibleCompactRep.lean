module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormLeOneOfIsIntegralPadicInt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAugmentationCombinationEqIdTracelessIrredu

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisHomZlLipschitzOfKerLeLinearGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicHomSmallOnDeepCongruenceSubgroups
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicHomSmallOnDeepCongruenceSubgroups
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem GlobalTheory.lam_small_of_deep_congruence : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] (r : Γ →* GL (Fin 2) (Qbar l)) (lam : Γ →* Multiplicative ℤ_[l]), Continuous r → Continuous lam → r.ker ≤ lam.ker → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ g : Γ, (∀ i j, ‖((r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j‖ ≤ ‖((l : ℕ) : Qbar l) ^ N‖) → ‖(lam g).toAdd‖ ≤ ε := by
  intro l _ Γ _ _ _ r lam hr hlam hker ε hε
  have hl : ‖((l:ℕ) : Qbar l)‖ = (l:ℝ)⁻¹ := by
    have : ((l:ℕ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) (l : ℚ_[l]) := by simp
    rw [this, norm_algebraMap']
    simp [Padic.norm_p]
  have hl1 : ‖((l:ℕ) : Qbar l)‖ < 1 := by
    rw [hl]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  by_contra hcon
  push_neg at hcon
  set F : ℕ → Set Γ := fun N => {g | ∀ i j, ‖((r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j‖ ≤ ‖((l : ℕ) : Qbar l) ^ N‖} ∩ {g | ε ≤ ‖(lam g).toAdd‖} with hF
  have hcm : Continuous fun g => ((r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) := (Units.continuous_val.comp hr).sub continuous_const
  have hclosed : ∀ N, IsClosed (F N) := by
    intro N
    refine IsClosed.inter ?_ ?_
    · have : {g | ∀ i j, ‖((r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j‖ ≤ ‖((l : ℕ) : Qbar l) ^ N‖} = ⋂ i, ⋂ j, {g | ‖((r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j‖ ≤ ‖((l : ℕ) : Qbar l) ^ N‖} := by
        ext g; simp
      rw [this]
      refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
      exact isClosed_le (continuous_norm.comp ((continuous_apply j).comp ((continuous_apply i).comp hcm))) continuous_const
    · exact isClosed_le continuous_const (continuous_norm.comp (continuous_toAdd.comp hlam))
  have hmono : ∀ N, F (N+1) ⊆ F N := by
    intro N g hg
    refine ⟨fun i j => (hg.1 i j).trans ?_, hg.2⟩
    rw [norm_pow, norm_pow]
    exact pow_le_pow_of_le_one (norm_nonneg _) hl1.le (Nat.le_succ N)
  have hne : ∀ N, (F N).Nonempty := by
    intro N
    obtain ⟨g, hg1, hg2⟩ := hcon N
    exact ⟨g, hg1, hg2.le⟩
  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed F hmono hne (hclosed 0).isCompact hclosed
  rw [Set.mem_iInter] at hg
  have hzero : ∀ i j, ((r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j = 0 := by
    intro i j
    by_contra hx
    have hpos : 0 < ‖((r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j‖ := norm_pos_iff.mpr hx
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hpos hl1
    have := (hg N).1 i j
    rw [norm_pow] at this
    linarith
  have hrg : r g = 1 := by
    apply Units.ext
    have : (r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1 = 0 := by
      ext i j; exact hzero i j
    simpa [sub_eq_zero] using this
  have hlg : lam g = 1 := hker (MonoidHom.mem_ker.mpr hrg)
  have h2 : ε ≤ ‖(lam g).toAdd‖ := (hg 0).2
  rw [hlg] at h2
  simp at h2
  linarith
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicHomSmallOnDeepCongruenceSubgroupsStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicHom_small_on_deep_congruence_subgroups : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] (r : Γ →* GL (Fin 2) (Qbar l)) (lam : Γ →* Multiplicative ℤ_[l]), Continuous r → Continuous lam → r.ker ≤ lam.ker → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ g : Γ, (∀ i j, ‖((r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j‖ ≤ ‖((l : ℕ) : Qbar l) ^ N‖) → ‖(lam g).toAdd‖ ≤ ε := by
  first | exact @GlobalTheory.lam_small_of_deep_congruence | exact GlobalTheory.lam_small_of_deep_congruence | (intros; apply GlobalTheory.lam_small_of_deep_congruence <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LipschitzPadicHomOfContractionPerLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LipschitzPadicHomOfContractionPerLevel
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem GlobalTheory.lipschitz_of_contraction_per_level : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (P : ℕ → Γ → Prop) (lam : Γ →* Multiplicative ℤ_[l]), (∀ m g, P (m + 1) g → P m g) → (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ g, P N g → ‖(lam g).toAdd‖ ≤ ε) → (∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ g, P (m + 1) g → ∃ h g' : Γ, P m h ∧ P (m + 2) g' ∧ g = h ^ l * g') → ∃ C : ℝ, ∀ (m : ℕ) (g : Γ), P m g → ‖(lam g).toAdd‖ ≤ C * ((l : ℝ)⁻¹) ^ m := by
  intro l hl Γ _ P lam hmono hsmall hdec
  obtain ⟨m₀, hdec⟩ := hdec
  have hmono' : ∀ a b g, P (a + b) g → P a g := by
    intro a b g h
    induction b with
    | zero => simpa using h
    | succ b ih => exact ih (hmono _ _ h)
  have hlpos : (0:ℝ) < l := by exact_mod_cast hl.out.pos
  have key : ∀ x y : Γ, ‖(lam (x ^ l * y)).toAdd‖ ≤
      max ((l:ℝ)⁻¹ * ‖(lam x).toAdd‖) ‖(lam y).toAdd‖ := by
    intro x y
    rw [map_mul, map_pow, toAdd_mul, toAdd_pow]
    refine (PadicInt.nonarchimedean _ _).trans (le_of_eq ?_)
    rw [nsmul_eq_mul, norm_mul, PadicInt.norm_p]
  have step : ∀ m, m₀ ≤ m → ∀ t : ℝ, 0 ≤ t → (∀ g, P m g → ‖(lam g).toAdd‖ ≤ t) →
      ∀ g, P (m + 1) g → ‖(lam g).toAdd‖ ≤ (l:ℝ)⁻¹ * t := by
    intro m hm t ht hyp g hg
    have chain : ∀ k : ℕ, ∃ g', P (m + 1 + k) g' ∧
        ‖(lam g).toAdd‖ ≤ max ((l:ℝ)⁻¹ * t) ‖(lam g').toAdd‖ := by
      intro k
      induction k with
      | zero => exact ⟨g, by simpa using hg, le_max_right _ _⟩
      | succ k ih =>
        obtain ⟨g', hg', hle⟩ := ih
        have hg'2 : P (m + k + 1) g' := by
          rw [show m + k + 1 = m + 1 + k by omega]; exact hg'
        obtain ⟨h, g'', hh, hg'', rfl⟩ := hdec (m + k) (by omega) g' hg'2
        refine ⟨g'', ?_, hle.trans (max_le (le_max_left _ _) ((key h g'').trans
          (max_le_max ?_ le_rfl)))⟩
        · rw [show m + 1 + (k + 1) = m + k + 2 by omega]; exact hg''
        · exact mul_le_mul_of_nonneg_left (hyp h (hmono' m k h hh)) (inv_nonneg.2 hlpos.le)
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨N, hN⟩ := hsmall ε hε
    obtain ⟨g', hg', hle⟩ := chain N
    have hsm := hN g' (hmono' N (m + 1) g' (by rw [show N + (m + 1) = m + 1 + N by omega]; exact hg'))
    exact hle.trans (max_le (le_add_of_nonneg_right hε.le)
      (hsm.trans (le_add_of_nonneg_left (mul_nonneg (inv_nonneg.2 hlpos.le) ht))))
  have levels : ∀ j : ℕ, ∀ g, P (m₀ + j) g → ‖(lam g).toAdd‖ ≤ ((l:ℝ)⁻¹) ^ j := by
    intro j
    induction j with
    | zero => intro g _; rw [pow_zero]; exact PadicInt.norm_le_one _
    | succ j ih =>
      intro g hg
      rw [pow_succ']
      exact step (m₀ + j) (by omega) _ (pow_nonneg (inv_nonneg.2 hlpos.le) _) ih g hg
  refine ⟨(l:ℝ) ^ m₀, fun m g hg => ?_⟩
  rcases le_or_gt m₀ m with h | h
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
    calc ‖(lam g).toAdd‖ ≤ ((l:ℝ)⁻¹) ^ j := levels j g hg
      _ = (l:ℝ) ^ m₀ * ((l:ℝ)⁻¹) ^ (m₀ + j) := by
        rw [pow_add, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hlpos.ne', one_pow, one_mul]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt h
    have e : (l:ℝ) ^ (m + j + 1) * ((l:ℝ)⁻¹) ^ m = (l:ℝ) ^ (j + 1) := by
      rw [show m + j + 1 = m + (j + 1) by omega, pow_add, mul_comm ((l:ℝ) ^ m), mul_assoc,
        ← mul_pow, mul_inv_cancel₀ hlpos.ne', one_pow, mul_one]
    rw [e]
    exact (PadicInt.norm_le_one _).trans (one_le_pow₀ (by exact_mod_cast hl.out.one_lt.le))
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LipschitzPadicHomOfContractionPerLevelStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lipschitz_padicHom_of_contraction_per_level : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (P : ℕ → Γ → Prop) (lam : Γ →* Multiplicative ℤ_[l]), (∀ m g, P (m + 1) g → P m g) → (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ g, P N g → ‖(lam g).toAdd‖ ≤ ε) → (∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ g, P (m + 1) g → ∃ h g' : Γ, P m h ∧ P (m + 2) g' ∧ g = h ^ l * g') → ∃ C : ℝ, ∀ (m : ℕ) (g : Γ), P m g → ‖(lam g).toAdd‖ ≤ C * ((l : ℝ)⁻¹) ^ m := by
  first | exact @GlobalTheory.lipschitz_of_contraction_per_level | exact GlobalTheory.lipschitz_of_contraction_per_level | (intros; apply GlobalTheory.lipschitz_of_contraction_per_level <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPrimePowMulDeepCongruenceLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPrimePowMulDeepCongruenceLevel
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.DeepLevel

variable {l : ℕ} [Fact l.Prime]

theorem norm_natCast_l : ‖((l : ℕ) : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
  have : ((l : ℕ) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
  rw [this, norm_algebraMap', Padic.norm_p]

theorem eO_toNat_pos (c : Coef l) : 1 ≤ (UpperTheory.V.Base.eO l c.O).toNat := by
  obtain ⟨-, -, -, -, -, he0, -, hev, -⟩ := UpperTheory.V.Base.dvrFacts l c.O
  have hl0 : ((l : ℕ) : c.O) ≠ 0 := by
    intro h
    have h' : (((l : ℕ) : c.O) : PadicAlgCl l) = 0 := by rw [h]; rfl
    have : ((l : ℕ) : PadicAlgCl l) = 0 := by simpa using h'
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) this
  have htop : UpperTheory.V.Base.eO l c.O ≠ ⊤ := by
    rw [hev, Ne, IsDiscreteValuationRing.addVal_eq_top_iff]; exact hl0
  have : (UpperTheory.V.Base.eO l c.O).toNat ≠ 0 := by
    intro h; exact he0 ((ENat.toNat_eq_zero).1 h |>.resolve_right htop)
  omega

theorem norm_le_one (c : Coef l) (y : c.O) : ‖(y : PadicAlgCl l)‖ ≤ 1 := by
  by_cases hy : y = 0
  · simp [hy]
  have h := UpperTheory.V.Base.normO l c.O y hy
  have he := eO_toNat_pos c
  have hl : (0 : ℝ) ≤ (l : ℝ)⁻¹ := by positivity
  have hl1 : (l : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt.le)
  have : ‖(y : PadicAlgCl l)‖ ^ (UpperTheory.V.Base.eO l c.O).toNat ≤ 1 := by
    rw [h]; exact pow_le_one₀ hl hl1
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) (by omega)).1 this

end GlobalTheory.DeepLevel

namespace GlobalTheory.DeepLevel

variable {l : ℕ} [Fact l.Prime]

theorem norm_le_iff_dvd (c : Coef l) (x : c.O) (k : ℕ) :
    ‖(x : PadicAlgCl l)‖ ≤ ‖((l : ℕ) : PadicAlgCl l) ^ k‖ ↔ ((l : ℕ) : c.O) ^ k ∣ x := by
  constructor
  · intro hx
    by_cases hx0 : x = 0
    · rw [hx0]; exact dvd_zero _
    obtain ⟨-, -, -, -, -, -, -, hev, -⟩ := UpperTheory.V.Base.dvrFacts l c.O
    have h := UpperTheory.V.Base.normO l c.O x hx0
    have he := eO_toNat_pos c
    set e := (UpperTheory.V.Base.eO l c.O).toNat with he_def
    set v := (IsDiscreteValuationRing.addVal c.O x).toNat with hv_def
    have hq0 : (0 : ℝ) < (l : ℝ)⁻¹ := by
      have := (Fact.out : l.Prime).pos; positivity
    have hq1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
    rw [norm_pow, norm_natCast_l] at hx
    have h2 : ‖(x : PadicAlgCl l)‖ ^ e ≤ ((l : ℝ)⁻¹ ^ k) ^ e := pow_le_pow_left₀ (norm_nonneg _) hx e
    rw [h, ← pow_mul] at h2
    have h3 : k * e ≤ v := (pow_le_pow_iff_right_of_lt_one₀ hq0 hq1).1 h2
    have hl0 : ((l : ℕ) : c.O) ≠ 0 := by
      intro h0
      have h' : (((l : ℕ) : c.O) : PadicAlgCl l) = 0 := by rw [h0]; rfl
      have : ((l : ℕ) : PadicAlgCl l) = 0 := by simpa using h'
      exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) this
    have htl : IsDiscreteValuationRing.addVal c.O ((l : ℕ) : c.O) ≠ ⊤ := by
      rw [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]; exact hl0
    have htx : IsDiscreteValuationRing.addVal c.O x ≠ ⊤ := by
      rw [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]; exact hx0
    rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, IsDiscreteValuationRing.addVal_pow,
      ← ENat.coe_toNat htl, ← ENat.coe_toNat htx, ← hev, ← he_def, ← hv_def]
    rw [nsmul_eq_mul]
    exact_mod_cast h3
  · rintro ⟨y, rfl⟩
    have : (((l : ℕ) : c.O) ^ k * y : c.O) = ((l : ℕ) : PadicAlgCl l) ^ k * (y : PadicAlgCl l) := by simp
    rw [this, norm_mul]
    calc _ ≤ ‖((l : ℕ) : PadicAlgCl l) ^ k‖ * 1 := mul_le_mul_of_nonneg_left (norm_le_one c y) (norm_nonneg _)
      _ = _ := mul_one _

end GlobalTheory.DeepLevel

namespace GlobalTheory.DeepLevel

theorem pow_expand {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (t : R) (m : ℕ) (hm : 2 ≤ m) (B : Matrix n n R) (N : ℕ) :
    ∃ C : Matrix n n R, (1 + t ^ m • B) ^ N = 1 + ((N : R) * t ^ m) • B + t ^ (m + 2) • C := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  induction N with
  | zero => exact ⟨0, by simp⟩
  | succ N ih =>
    obtain ⟨C, hC⟩ := ih
    refine ⟨((N : R) * t ^ k) • (B * B) + C + t ^ (k + 2) • (C * B), ?_⟩
    rw [pow_succ, hC]
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_one, one_mul, smul_add]
    push_cast
    module

end GlobalTheory.DeepLevel

namespace GlobalTheory.DeepLevel

variable {l : ℕ} [Fact l.Prime]

def intRep (c : Coef l) {Γ : Type} [Group Γ] (r : Γ →* GL (Fin 2) (PadicAlgCl l))
    (hint : ∀ g i j, (r g : Matrix (Fin 2) (Fin 2) (PadicAlgCl l)) i j ∈ c.O) :
    Γ →* Matrix (Fin 2) (Fin 2) c.O where
  toFun g := Matrix.of fun i j => ⟨_, hint g i j⟩
  map_one' := by
    ext i j
    simp only [map_one, Units.val_one, Matrix.of_apply]
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> rfl
  map_mul' g h := by
    apply Matrix.map_injective (f := (c.O.val : c.O →+* PadicAlgCl l)) Subtype.val_injective
    dsimp only
    rw [Matrix.map_mul]
    ext i j
    simp only [Matrix.map_apply, Matrix.of_apply, map_mul, Units.val_mul]
    rfl

theorem intRep_map (c : Coef l) {Γ : Type} [Group Γ] (r : Γ →* GL (Fin 2) (PadicAlgCl l))
    (hint : ∀ g i j, (r g : Matrix (Fin 2) (Fin 2) (PadicAlgCl l)) i j ∈ c.O) (g : Γ) (i j : Fin 2) :
    ((((r g : Matrix (Fin 2) (Fin 2) (PadicAlgCl l)) - 1) i j) : PadicAlgCl l) =
      ((((intRep c r hint g) - 1) i j : c.O) : PadicAlgCl l) := by
  simp only [Matrix.sub_apply]
  rw [Subalgebra.coe_sub]
  congr 1
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem level_iff (c : Coef l) {Γ : Type} [Group Γ] (r : Γ →* GL (Fin 2) (PadicAlgCl l))
    (hint : ∀ g i j, (r g : Matrix (Fin 2) (Fin 2) (PadicAlgCl l)) i j ∈ c.O) (g : Γ) (k : ℕ) :
    (∀ i j, ‖((r g : Matrix (Fin 2) (Fin 2) (PadicAlgCl l)) - 1) i j‖ ≤ ‖((l : ℕ) : PadicAlgCl l) ^ k‖) ↔
      ∃ B : Matrix (Fin 2) (Fin 2) c.O, intRep c r hint g = 1 + (((l : ℕ) : c.O) ^ k) • B := by
  simp only [intRep_map c r hint, norm_le_iff_dvd]
  constructor
  · intro h
    choose B hB using h
    refine ⟨Matrix.of B, ?_⟩
    ext i j
    have := hB i j
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, ← this, Matrix.sub_apply]
    ring_nf
  · rintro ⟨B, hB⟩ i j
    exact ⟨B i j, by rw [hB]; simp⟩

end GlobalTheory.DeepLevel

namespace GlobalTheory.DeepLevel

variable {l : ℕ} [Fact l.Prime]

theorem pow_step (c : Coef l) (A B : Matrix (Fin 2) (Fin 2) c.O) (m : ℕ) (hm : 2 ≤ m)
    (hA : A = 1 + (((l : ℕ) : c.O) ^ m) • B) :
    ∃ B' : Matrix (Fin 2) (Fin 2) c.O, A ^ l = 1 + (((l : ℕ) : c.O) ^ (m + 1)) • B' ∧
      B'.map (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : c.O)})) =
        B.map (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : c.O)})) := by
  obtain ⟨C, hC⟩ := pow_expand ((l : ℕ) : c.O) m hm B l
  refine ⟨B + ((l : ℕ) : c.O) • C, ?_, ?_⟩
  · rw [hA, hC, smul_add, smul_smul, show ((l : ℕ) : c.O) * ((l : ℕ) : c.O) ^ m = ((l : ℕ) : c.O) ^ (m + 1) by ring,
      show ((l : ℕ) : c.O) ^ (m + 2) = ((l : ℕ) : c.O) ^ (m + 1) * ((l : ℕ) : c.O) by ring]
    abel
  · ext i j
    have h0 : Ideal.Quotient.mk (Ideal.span {((l : ℕ) : c.O)}) ((l : ℕ) : c.O) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
    simp [Matrix.map_apply, h0]

def img (c : Coef l) {Γ : Type} [Group Γ] (ρ : Γ →* Matrix (Fin 2) (Fin 2) c.O) (m : ℕ) :
    Set (Matrix (Fin 2) (Fin 2) (c.O ⧸ Ideal.span {((l : ℕ) : c.O)})) :=
  {X | ∃ g B, ρ g = 1 + (((l : ℕ) : c.O) ^ m) • B ∧ B.map (Ideal.Quotient.mk _) = X}

theorem img_mono (c : Coef l) {Γ : Type} [Group Γ] (ρ : Γ →* Matrix (Fin 2) (Fin 2) c.O) (m : ℕ) (hm : 2 ≤ m) :
    img c ρ m ⊆ img c ρ (m + 1) := by
  rintro X ⟨g, B, hg, rfl⟩
  obtain ⟨B', h1, h2⟩ := pow_step c (ρ g) B m hm hg
  exact ⟨g ^ l, B', by rw [map_pow, h1], h2⟩

theorem exists_pow_mul_of_deep_level : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (Γ : Type) [Group Γ] (r : Γ →* GL (Fin 2) (Qbar l)), (∀ g i j, (r g : Matrix (Fin 2) (Fin 2) (Qbar l)) i j ∈ c.O) → ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ g : Γ, (∀ i j, ‖((r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j‖ ≤ ‖((l : ℕ) : Qbar l) ^ (m + 1)‖) → ∃ h g' : Γ, (∀ i j, ‖((r h : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j‖ ≤ ‖((l : ℕ) : Qbar l) ^ m‖) ∧ (∀ i j, ‖((r g' : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j‖ ≤ ‖((l : ℕ) : Qbar l) ^ (m + 2)‖) ∧ g = h ^ l * g' := by
  intro l _ c Γ _ r hint
  set ρ := intRep c r hint with hρ
  have hl0 : ((l : ℕ) : c.O) ≠ 0 := by
    intro h0
    have h' : (((l : ℕ) : c.O) : PadicAlgCl l) = 0 := by rw [h0]; rfl
    have : ((l : ℕ) : PadicAlgCl l) = 0 := by simpa using h'
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) this
  haveI : Finite (c.O ⧸ Ideal.span {((l : ℕ) : c.O)}) :=
    (UpperTheory.V.X.So.levFacts l c.O ((l : ℕ) : c.O) hl0 _ ⟨LinearEquiv.refl _ _⟩).1
  haveI : Finite (Matrix (Fin 2) (Fin 2) (c.O ⧸ Ideal.span {((l : ℕ) : c.O)})) :=
    inferInstanceAs (Finite (Fin 2 → Fin 2 → _))
  let F : ℕ →o Set (Matrix (Fin 2) (Fin 2) (c.O ⧸ Ideal.span {((l : ℕ) : c.O)})) :=
    ⟨fun n => img c ρ (n + 2), monotone_nat_of_le_succ fun n => img_mono c ρ (n + 2) (by omega)⟩
  obtain ⟨n, hn⟩ := WellFoundedGT.monotone_chain_condition F
  refine ⟨n + 2, fun m hm g hg => ?_⟩
  have hS : img c ρ (m + 1) ⊆ img c ρ m := by
    have e1 := hn (m - 2) (by omega)
    have e2 := hn (m - 1) (by omega)
    have h1 : F (m - 2) = img c ρ m := by
      show img c ρ (m - 2 + 2) = _; congr 1; omega
    have h2 : F (m - 1) = img c ρ (m + 1) := by
      show img c ρ (m - 1 + 2) = _; congr 1; omega
    rw [← h1, ← h2, ← e1, ← e2]
  obtain ⟨B, hB⟩ := (level_iff c r hint g (m + 1)).1 hg
  obtain ⟨h, B₁, hh, hB₁⟩ := hS ⟨g, B, hB, rfl⟩
  obtain ⟨B₂, hh2, hB₂⟩ := pow_step c (ρ h) B₁ m (by omega) hh
  have hD : ∀ i j, ∃ d : c.O, B i j - B₂ i j = ((l : ℕ) : c.O) * d := by
    intro i j
    have := congrFun (congrFun (hB₁.symm.trans hB₂.symm) i) j
    simp only [Matrix.map_apply] at this
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 this)
    exact ⟨d, by rw [← hd]; ring⟩
  choose D hDD using hD
  refine ⟨h, (h ^ l)⁻¹ * g, (level_iff c r hint h m).2 ⟨B₁, hh⟩, (level_iff c r hint _ (m + 2)).2
    ⟨ρ (h ^ l)⁻¹ * Matrix.of D, ?_⟩, (mul_inv_cancel_left _ _).symm⟩
  have hBB : B = B₂ + ((l : ℕ) : c.O) • Matrix.of D := by
    ext i j
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, ← hDD]
    ring_nf
  have hinv : ρ (h ^ l)⁻¹ * ρ (h ^ l) = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hpow : ρ (h ^ l) = 1 + (((l : ℕ) : c.O) ^ (m + 1)) • B₂ := by rw [map_pow, hh2]
  have hg' : ρ g = ρ (h ^ l) + (((l : ℕ) : c.O) ^ (m + 2)) • Matrix.of D := by
    rw [hB, hpow, hBB, smul_add, smul_smul, ← pow_succ]
    abel
  rw [map_mul, hg', mul_add, hinv, Matrix.mul_smul]

end GlobalTheory.DeepLevel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPrimePowMulDeepCongruenceLevelStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_pow_mul_deep_congruenceLevel : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (Γ : Type) [Group Γ] (r : Γ →* GL (Fin 2) (Qbar l)), (∀ g i j, (r g : Matrix (Fin 2) (Fin 2) (Qbar l)) i j ∈ c.O) → ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ g : Γ, (∀ i j, ‖((r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j‖ ≤ ‖((l : ℕ) : Qbar l) ^ (m + 1)‖) → ∃ h g' : Γ, (∀ i j, ‖((r h : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j‖ ≤ ‖((l : ℕ) : Qbar l) ^ m‖) ∧ (∀ i j, ‖((r g' : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j‖ ≤ ‖((l : ℕ) : Qbar l) ^ (m + 2)‖) ∧ g = h ^ l * g' := by
  first | exact @GlobalTheory.DeepLevel.exists_pow_mul_of_deep_level | exact GlobalTheory.DeepLevel.exists_pow_mul_of_deep_level | (intros; apply GlobalTheory.DeepLevel.exists_pow_mul_of_deep_level <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisHomZlLipschitzOfKerLeLinearGroup
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem norm_natPrime_pow (l : ℕ) [Fact l.Prime] (m : ℕ) : ‖((l : ℕ) : Qbar l) ^ m‖ = ((l : ℝ)⁻¹) ^ m := by
  rw [norm_pow]
  congr 1
  have : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) (l : ℚ_[l]) := by simp
  rw [this, norm_algebraMap', Padic.norm_p]

theorem hom_lipschitz_of_ker_le : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (r : Γ →* GL (Fin 2) (Qbar l)) (lam : Γ →* Multiplicative ℤ_[l]), Continuous r → (∀ g i j, (r g : Matrix (Fin 2) (Fin 2) (Qbar l)) i j ∈ c.O) → Continuous lam → r.ker ≤ lam.ker → ∃ C : ℝ, ∀ (m : ℕ) (g : Γ), (∀ i j, ‖((r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j‖ ≤ ‖((l : ℕ) : Qbar l) ^ m‖) → ‖(lam g).toAdd‖ ≤ C * ‖((l : ℕ) : Qbar l) ^ m‖ := by
  intro l _ c Γ _ _ _ _ r lam hr hO hlam hker
  obtain ⟨C, hC⟩ := GlobalTheory.T.lipschitz_padicHom_of_contraction_per_level l Γ
    (fun m g => ∀ i j, ‖((r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j‖ ≤ ‖((l : ℕ) : Qbar l) ^ m‖) lam
    (fun m g h i j => (h i j).trans (by
      rw [norm_natPrime_pow, norm_natPrime_pow, pow_succ]
      have h1 : (0 : ℝ) ≤ (l : ℝ)⁻¹ := by positivity
      have h2 : (l : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt.le)
      exact mul_le_of_le_one_right (pow_nonneg h1 _) h2))
    (GlobalTheory.T.padicHom_small_on_deep_congruence_subgroups l Γ r lam hr hlam hker) (GlobalTheory.T.exists_prime_pow_mul_deep_congruenceLevel l c Γ r hO)
  exact ⟨C, fun m g hg => by rw [norm_natPrime_pow]; exact hC m g hg⟩

end GlobalTheory.Ord2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisHomZlLipschitzOfKerLeLinearGroupStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisHom_zl_lipschitz_of_ker_le_linearGroup : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (r : Γ →* GL (Fin 2) (Qbar l)) (lam : Γ →* Multiplicative ℤ_[l]), Continuous r → (∀ g i j, (r g : Matrix (Fin 2) (Fin 2) (Qbar l)) i j ∈ c.O) → Continuous lam → r.ker ≤ lam.ker → ∃ C : ℝ, ∀ (m : ℕ) (g : Γ), (∀ i j, ‖((r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j‖ ≤ ‖((l : ℕ) : Qbar l) ^ m‖) → ‖(lam g).toAdd‖ ≤ C * ‖((l : ℕ) : Qbar l) ^ m‖ := by
  first | exact @GlobalTheory.Ord2.hom_lipschitz_of_ker_le | exact GlobalTheory.Ord2.hom_lipschitz_of_ker_le | (intros; apply GlobalTheory.Ord2.hom_lipschitz_of_ker_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormNatCastLeOne
noncomputable section

open Formalism.ConjugateSelfDual
open scoped Matrix

namespace GlobalTheory.SmallMat

variable {l : ℕ} [Fact l.Prime]

def Sm (ε : ℝ) (M : Matrix (Fin 2) (Fin 2) (Qbar l)) : Prop := ∀ i j, ‖M i j‖ ≤ ε

theorem Sm.mono {ε δ : ℝ} {M : Matrix (Fin 2) (Fin 2) (Qbar l)} (h : Sm ε M) (hεδ : ε ≤ δ) : Sm δ M :=
  fun i j => (h i j).trans hεδ

theorem Sm.add {ε : ℝ} {M N : Matrix (Fin 2) (Fin 2) (Qbar l)} (hM : Sm ε M) (hN : Sm ε N) : Sm ε (M + N) := fun i j => by
  simp only [Matrix.add_apply]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hM i j) (hN i j))

theorem Sm.neg {ε : ℝ} {M : Matrix (Fin 2) (Fin 2) (Qbar l)} (hM : Sm ε M) : Sm ε (-M) := fun i j => by
  simpa using hM i j

theorem Sm.sub {ε : ℝ} {M N : Matrix (Fin 2) (Fin 2) (Qbar l)} (hM : Sm ε M) (hN : Sm ε N) : Sm ε (M - N) := by
  rw [sub_eq_add_neg]; exact hM.add hN.neg

theorem sm_zero {ε : ℝ} (hε : 0 ≤ ε) : Sm (l := l) ε 0 := fun i j => by simpa using hε

theorem Sm.mul {ε δ : ℝ} {M N : Matrix (Fin 2) (Fin 2) (Qbar l)} (hM : Sm ε M) (hN : Sm δ N) (hε : 0 ≤ ε) :
    Sm (ε * δ) (M * N) := fun i j => by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_) <;> rw [norm_mul] <;>
    exact mul_le_mul (hM _ _) (hN _ _) (norm_nonneg _) hε

theorem Sm.smul {ε : ℝ} {M : Matrix (Fin 2) (Fin 2) (Qbar l)} (hM : Sm ε M) (a : Qbar l) : Sm (‖a‖ * ε) (a • M) :=
  fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul]; exact mul_le_mul_of_nonneg_left (hM i j) (norm_nonneg _)

theorem Sm.smul_le {ε : ℝ} {M : Matrix (Fin 2) (Fin 2) (Qbar l)} (hM : Sm ε M) (hε : 0 ≤ ε) {a : Qbar l} (ha : ‖a‖ ≤ 1) :
    Sm ε (a • M) :=
  (hM.smul a).mono (by simpa using mul_le_mul_of_nonneg_right ha hε)

theorem sm_scalar {ε : ℝ} {a : Qbar l} (ha : ‖a‖ ≤ ε) (hε : 0 ≤ ε) : Sm ε (a • (1 : Matrix (Fin 2) (Fin 2) (Qbar l))) :=
  fun i j => by
    by_cases h : i = j
    · subst h; simpa using ha
    · simpa [Matrix.one_apply_ne h] using hε

theorem Sm.sum {ι : Type*} (s : Finset ι) {ε : ℝ} (hε : 0 ≤ ε) (M : ι → Matrix (Fin 2) (Fin 2) (Qbar l))
    (h : ∀ i ∈ s, Sm ε (M i)) : Sm ε (∑ i ∈ s, M i) := fun a b => by
  rw [Matrix.sum_apply]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hε fun i hi => h i hi a b

theorem norm_natCast_le_one (b : ℕ) : ‖(b : Qbar l)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ b

theorem Sm.det {ε : ℝ} {M : Matrix (Fin 2) (Fin 2) (Qbar l)} (hM : Sm ε M) (hε : 0 ≤ ε) : ‖M.det‖ ≤ ε ^ 2 := by
  rw [Matrix.det_fin_two, sq, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_) <;> simp only [norm_neg, norm_mul] <;>
    exact mul_le_mul (hM _ _) (hM _ _) (norm_nonneg _) hε

end GlobalTheory.SmallMat

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HomPadicIntTrivialOfIrreducibleCompactRep
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2

open GlobalTheory.SmallMat

theorem noab_inv_det_one {K : Type} [Field K] (A : GL (Fin 2) K) (h : (A : Matrix (Fin 2) (Fin 2) K).det = 1) :
    ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = (A : Matrix (Fin 2) (Fin 2) K).trace • 1 - A := by
  rw [Matrix.coe_units_inv, Matrix.inv_def, h, Ring.inverse_one, one_smul, Matrix.adjugate_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.trace_fin_two]

theorem noab_trace_eq {K : Type} [Field K] (Z : Matrix (Fin 2) (Fin 2) K) (h : (1 + Z).det = 1) : Z.trace = - Z.det := by
  rw [Matrix.det_fin_two] at h
  rw [Matrix.det_fin_two, Matrix.trace_fin_two]
  simp [Matrix.add_apply, Matrix.one_apply] at h
  linear_combination h

theorem noab_norm_two (l : ℕ) [Fact l.Prime] : ‖((l : ℕ) : Qbar l)‖ ≤ ‖(2 : Qbar l)‖ := by
  have e : ∀ m : ℕ, ‖((m : ℕ) : Qbar l)‖ = ‖((m : ℕ) : ℚ_[l])‖ := fun m => by
    rw [← map_natCast (algebraMap ℚ_[l] (Qbar l)), norm_algebraMap']
  have e2 : (2 : Qbar l) = ((2 : ℕ) : Qbar l) := by norm_num
  rw [e2, e, e]
  by_cases h2 : l = 2
  · subst h2; exact le_rfl
  · rw [Padic.norm_natCast_eq_one_iff.2 ((Nat.coprime_primes (Fact.out) Nat.prime_two).2 h2), Padic.norm_p]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt.le)

theorem noab_pow : ∀ (l : ℕ) [Fact l.Prime] (ε : ℝ) (Z : Matrix (Fin 2) (Fin 2) (Qbar l)), 0 ≤ ε → ε ≤ 1 →
    GlobalTheory.SmallMat.Sm ε Z → ∀ b : ℕ, GlobalTheory.SmallMat.Sm (ε ^ 2) ((1 + Z) ^ b - 1 - (b : Qbar l) • Z) := by
  intro l _ ε Z hε0 hε1 hZ b
  have hε2 : ε ^ 2 * ε ≤ ε ^ 2 := by simpa using mul_le_mul_of_nonneg_left hε1 (sq_nonneg ε)
  induction b with
  | zero => simpa using GlobalTheory.SmallMat.sm_zero (l := l) (sq_nonneg ε)
  | succ b ih =>
    have e : (1 + Z) ^ (b + 1) - 1 - ((b + 1 : ℕ) : Qbar l) • Z = ((1 + Z) ^ b - 1 - (b : Qbar l) • Z)
        + ((1 + Z) ^ b - 1 - (b : Qbar l) • Z) * Z + (b : Qbar l) • (Z * Z) := by
      simp only [pow_succ, Nat.cast_succ, add_smul, one_smul, mul_add, add_mul, sub_mul, mul_one, one_mul,
        Matrix.smul_mul]
      abel
    rw [e]
    refine (ih.add ((ih.mul hZ (sq_nonneg ε)).mono hε2)).add ?_
    refine ((hZ.mul hZ hε0).smul_le (mul_nonneg hε0 hε0) (GlobalTheory.SmallMat.norm_natCast_le_one b)).mono (le_of_eq (sq ε).symm)

theorem noab_sum_list : ∀ (l : ℕ) [Fact l.Prime] (ε : ℝ) (L : List (Matrix (Fin 2) (Fin 2) (Qbar l))), 0 ≤ ε →
    (∀ M ∈ L, GlobalTheory.SmallMat.Sm ε (M - 1)) → GlobalTheory.SmallMat.Sm ε ((L.map (fun M => M - 1)).sum) := by
  intro l _ ε L hε0 hL
  induction L with
  | nil => simpa using GlobalTheory.SmallMat.sm_zero (l := l) hε0
  | cons M L ih =>
    rw [List.map_cons, List.sum_cons]
    exact (hL M (by simp)).add (ih fun N hN => hL N (by simp [hN]))

theorem noab_prod : ∀ (l : ℕ) [Fact l.Prime] (ε : ℝ) (L : List (Matrix (Fin 2) (Fin 2) (Qbar l))), 0 ≤ ε → ε ≤ 1 →
    (∀ M ∈ L, GlobalTheory.SmallMat.Sm ε (M - 1)) →
    GlobalTheory.SmallMat.Sm (ε ^ 2) (L.prod - 1 - (L.map (fun M => M - 1)).sum) := by
  intro l _ ε L hε0 hε1 hL
  have hε2 : ε ^ 2 ≤ ε := by simpa [sq] using mul_le_mul_of_nonneg_left hε1 hε0
  induction L with
  | nil => simpa using GlobalTheory.SmallMat.sm_zero (l := l) (sq_nonneg ε)
  | cons M L ih =>
    have hL' : ∀ N ∈ L, GlobalTheory.SmallMat.Sm ε (N - 1) := fun N hN => hL N (by simp [hN])
    have hM : GlobalTheory.SmallMat.Sm ε (M - 1) := hL M (by simp)
    have ih' := ih hL'
    have hS := noab_sum_list l ε L hε0 hL'
    have hP : GlobalTheory.SmallMat.Sm ε (L.prod - 1) := by
      have := (ih'.mono hε2).add hS; rwa [sub_add_cancel] at this
    have e : (M :: L).prod - 1 - ((M :: L).map (fun M => M - 1)).sum =
        (M - 1) * (L.prod - 1) + (L.prod - 1 - (L.map (fun M => M - 1)).sum) := by
      rw [List.prod_cons, List.map_cons, List.sum_cons]
      simp only [sub_mul, mul_sub, one_mul, mul_one]
      abel
    rw [e]
    exact ((hM.mul hP hε0).mono (le_of_eq (sq ε).symm)).add ih'

theorem noab_denom : ∀ (l : ℕ) [Fact l.Prime] (N : ℕ) (a : Fin N → ℚ_[l]), ∃ s : ℕ, ∀ i, ‖((l : ℕ) : ℚ_[l]) ^ s * a i‖ ≤ 1 := by
  intro l _ N a
  have hρ : ‖((l : ℕ) : ℚ_[l])‖ < 1 := Padic.norm_p_lt_one
  have hex : ∀ i, ∃ s : ℕ, ‖((l : ℕ) : ℚ_[l])‖ ^ s * ‖a i‖ ≤ 1 := fun i => by
    by_cases h : a i = 0
    · exact ⟨0, by simp [h]⟩
    · obtain ⟨s, hs⟩ := exists_pow_lt_of_lt_one (inv_pos.2 (norm_pos_iff.2 h)) hρ
      refine ⟨s, ?_⟩
      rw [← le_div_iff₀ (norm_pos_iff.2 h), one_div]
      exact hs.le
  choose f hf using hex
  refine ⟨∑ i, f i, fun i => ?_⟩
  rw [norm_mul, norm_pow]
  exact le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (norm_nonneg _) hρ.le
    (Finset.single_le_sum (fun j _ => Nat.zero_le (f j)) (Finset.mem_univ i))) (norm_nonneg _)) (hf i)

theorem noab_comm : ∀ (l : ℕ) [Fact l.Prime] (ε : ℝ) (A A' Z Z' : Matrix (Fin 2) (Fin 2) (Qbar l)) (β : ℕ), 0 ≤ ε → ε ≤ 1 →
    A * A' = 1 → GlobalTheory.SmallMat.Sm 1 A → GlobalTheory.SmallMat.Sm 1 A' → GlobalTheory.SmallMat.Sm ε Z → GlobalTheory.SmallMat.Sm (ε ^ 2) (Z' + Z) →
    GlobalTheory.SmallMat.Sm (ε ^ 2) (A * (1 + Z) ^ β * A' * (1 + Z') ^ β - 1 - (β : Qbar l) • (A * Z * A' - Z)) := by
  intro l _ ε A A' Z Z' β hε0 hε1 hAA' hA hA' hZ hZZ
  have hε2 : ε ^ 2 ≤ ε := by simpa [sq] using mul_le_mul_of_nonneg_left hε1 hε0
  have hZ' : GlobalTheory.SmallMat.Sm ε Z' := by
    have := (hZZ.mono hε2).sub hZ; rwa [add_sub_cancel_right] at this
  have hE := noab_pow l ε Z hε0 hε1 hZ β
  have hE' := noab_pow l ε Z' hε0 hε1 hZ' β
  have hU : GlobalTheory.SmallMat.Sm ε ((1 + Z) ^ β - 1) := by
    have := (hE.mono hε2).add (hZ.smul_le hε0 (GlobalTheory.SmallMat.norm_natCast_le_one β)); rwa [sub_add_cancel] at this
  have hV : GlobalTheory.SmallMat.Sm ε ((1 + Z') ^ β - 1) := by
    have := (hE'.mono hε2).add (hZ'.smul_le hε0 (GlobalTheory.SmallMat.norm_natCast_le_one β)); rwa [sub_add_cancel] at this
  have e : A * (1 + Z) ^ β * A' * (1 + Z') ^ β - 1 - (β : Qbar l) • (A * Z * A' - Z) =
      A * ((1 + Z) ^ β - 1 - (β : Qbar l) • Z) * A' + ((1 + Z') ^ β - 1 - (β : Qbar l) • Z') + (β : Qbar l) • (Z' + Z)
      + (A * ((1 + Z) ^ β - 1) * A') * ((1 + Z') ^ β - 1) := by
    generalize (1 + Z) ^ β = P
    generalize (1 + Z') ^ β = P'
    simp only [mul_sub, sub_mul, mul_one, one_mul, Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_sub, mul_assoc,
      ← mul_assoc A A', hAA']
    abel
  rw [e]
  have h1 : GlobalTheory.SmallMat.Sm (ε ^ 2) (A * ((1 + Z) ^ β - 1 - (β : Qbar l) • Z) * A') := by
    have := (hA.mul hE zero_le_one).mul hA' (by positivity); rwa [one_mul, mul_one] at this
  have h3 : GlobalTheory.SmallMat.Sm (ε ^ 2) ((β : Qbar l) • (Z' + Z)) :=
    hZZ.smul_le (sq_nonneg ε) (GlobalTheory.SmallMat.norm_natCast_le_one β)
  have h4 : GlobalTheory.SmallMat.Sm (ε ^ 2) ((A * ((1 + Z) ^ β - 1) * A') * ((1 + Z') ^ β - 1)) := by
    have := ((hA.mul hU zero_le_one).mul hA' (by positivity)).mul hV (by positivity)
    rwa [one_mul, mul_one, ← sq] at this
  exact ((h1.add hE').add h3).add h4

theorem noab_congr_pow : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] (r : Γ →* GL (Fin 2) (Qbar l)), Continuous r →
    (∀ g i j, (r g : Matrix (Fin 2) (Fin 2) (Qbar l)) i j ∈ c.O) →
    (∀ g, (r g : Matrix (Fin 2) (Fin 2) (Qbar l)).det ^ 2 = 1) → ∀ g : Γ, ∃ k : ℕ, 0 < k ∧
      (r (g ^ k) : Matrix (Fin 2) (Fin 2) (Qbar l)).det = 1 ∧
      GlobalTheory.SmallMat.Sm ‖((l : ℕ) : Qbar l)‖ ((r (g ^ k) : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) := by
  intro l _ c Γ _ _ _ _ r hr hint hdet g
  set R : Γ →* Matrix (Fin 2) (Fin 2) (Qbar l) := (Units.coeHom _).comp r with hRdef
  have hRint : ∀ x, Sm 1 (R x) := fun x i j => commHt_norm_le_one_of_mem c _ (hint x i j)
  set ρ : ℝ := ‖((l : ℕ) : Qbar l)‖ with hρ
  have hρeq : ρ = (l : ℝ)⁻¹ := by
    rw [hρ, ← map_natCast (algebraMap ℚ_[l] (Qbar l)), norm_algebraMap', Padic.norm_p]
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hρ0 : 0 < ρ := by rw [hρeq]; positivity
  have hρ1 : ρ < 1 := by rw [hρeq]; exact inv_lt_one_of_one_lt₀ hl1
  have hρρ : ρ * ρ ≤ ρ := by simpa using mul_le_mul_of_nonneg_left hρ1.le hρ0.le
  let U : Subgroup Γ :=
    { carrier := {x | (R x).det = 1 ∧ Sm ρ (R x - 1)}
      one_mem' := by
        refine ⟨by simp, ?_⟩
        rw [map_one, sub_self]; exact sm_zero hρ0.le
      mul_mem' := by
        rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
        refine ⟨by rw [map_mul, Matrix.det_mul, hx1, hy1, one_mul], ?_⟩
        have e : R (x * y) - 1 = (R x - 1) + (R y - 1) + (R x - 1) * (R y - 1) := by
          rw [map_mul]; simp only [sub_mul, mul_sub, one_mul, mul_one]; abel
        rw [e]
        exact (hx2.add hy2).add ((hx2.mul hy2 hρ0.le).mono hρρ)
      inv_mem' := by
        rintro x ⟨hx1, hx2⟩
        have hinv : R x⁻¹ = (R x).trace • 1 - R x := by
          simp only [hRdef, MonoidHom.coe_comp, Function.comp_apply, map_inv, Units.coeHom_apply]
          exact noab_inv_det_one (r x) hx1
        refine ⟨?_, ?_⟩
        · have h := Matrix.det_mul (R x⁻¹) (R x)
          rw [← map_mul, inv_mul_cancel, map_one, Matrix.det_one, hx1, mul_one] at h
          exact h.symm
        · set Z := R x - 1 with hZ
          have hRx : R x = 1 + Z := by rw [hZ, add_sub_cancel]
          have htr : Z.trace = - Z.det := noab_trace_eq Z (by rw [← hRx]; exact hx1)
          have e : R x⁻¹ - 1 = Z.trace • (1 : Matrix (Fin 2) (Fin 2) (Qbar l)) - Z := by
            rw [hinv, hRx, Matrix.trace_add, Matrix.trace_one, Fintype.card_fin]; module
          rw [e]
          refine (sm_scalar ?_ hρ0.le).sub hx2
          rw [htr, norm_neg]
          exact (hx2.det hρ0.le).trans (by rw [sq]; exact hρρ) }
  have hRc : Continuous R := Units.continuous_val.comp hr
  have hdeq : ∀ x, (R x).det = 1 ↔ (R x).det ≠ -1 := fun x => by
    constructor
    · intro h; rw [h]; norm_num
    · intro h
      have h2 := hdet x
      rw [sq] at h2
      exact (mul_self_eq_one_iff.1 h2).resolve_right h
  have hU : IsOpen (U : Set Γ) := by
    have hset : (U : Set Γ) = {x | (R x).det ≠ -1} ∩
        ⋂ i, ⋂ j, (fun x => (R x - 1) i j) ⁻¹' Metric.closedBall 0 ρ := by
      ext x
      rw [show x ∈ (U : Set Γ) ↔ ((R x).det = 1 ∧ Sm ρ (R x - 1)) from Iff.rfl, hdeq x]
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right,
        Set.mem_setOf_eq]
      rfl
    rw [hset]
    refine (isOpen_ne_fun (hRc.matrix_det) continuous_const).inter
      (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_)
    exact (IsUltrametricDist.isOpen_closedBall 0 hρ0.ne').preimage ((hRc.sub continuous_const).matrix_elem i j)
  haveI : Finite (Γ ⧸ U) := Subgroup.quotient_finite_of_isOpen U hU
  obtain ⟨k, hk0, -, hk⟩ := Subgroup.exists_pow_mem_of_index_ne_zero (Subgroup.index_ne_zero_of_finite (H := U)) g
  exact ⟨k, hk0, hk.1, hk.2⟩

theorem hom_padicInt_trivial : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (Γ : Type) [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [CompactSpace Γ] (r : Γ →* GL (Fin 2) (Qbar l)) (lam : Γ →* Multiplicative ℤ_[l]),
    Continuous r → (∀ g i j, (r g : Matrix (Fin 2) (Fin 2) (Qbar l)) i j ∈ c.O) →
    (∀ g, (r g : Matrix (Fin 2) (Fin 2) (Qbar l)).det ^ 2 = 1) → IsIrr r → Continuous lam → r.ker ≤ lam.ker →
    lam = 1 := by
  intro l _ c Γ _ _ _ _ r lam hr hint hdet hirr hlam hker
  set R : Γ →* Matrix (Fin 2) (Fin 2) (Qbar l) := (Units.coeHom _).comp r with hRdef
  have hRint : ∀ x, Sm 1 (R x) := fun x i j => commHt_norm_le_one_of_mem c _ (hint x i j)
  set ρ : ℝ := ‖((l : ℕ) : Qbar l)‖ with hρ
  have hρeq : ρ = (l : ℝ)⁻¹ := by
    rw [hρ, ← map_natCast (algebraMap ℚ_[l] (Qbar l)), norm_algebraMap', Padic.norm_p]
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hρ0 : 0 < ρ := by rw [hρeq]; positivity
  have hρ1 : ρ < 1 := by rw [hρeq]; exact inv_lt_one_of_one_lt₀ hl1
  have hρZ : ‖((l : ℕ) : ℤ_[l])‖ = ρ := by rw [PadicInt.norm_p, hρeq]
  by_contra hne
  obtain ⟨g, hg⟩ : ∃ g, lam g ≠ 1 := by
    by_contra h; push_neg at h; exact hne (MonoidHom.ext fun x => by simpa using h x)
  obtain ⟨k, hk0, hkdet, hksm⟩ := noab_congr_pow l c Γ r hr hint hdet g
  set h0 := g ^ k with hh0
  set v0 : ℤ_[l] := Multiplicative.toAdd (lam h0) with hv0def
  have hv0 : v0 ≠ 0 := by
    have hg' : Multiplicative.toAdd (lam g) ≠ 0 := fun h => hg (by simpa using congrArg Multiplicative.ofAdd h)
    rw [hv0def, hh0, map_pow, toAdd_pow, nsmul_eq_mul]
    exact mul_ne_zero (Nat.cast_ne_zero.2 hk0.ne') hg'
  have hpow : ∀ n : ℕ, (R (h0 ^ l ^ n)).det = 1 ∧ Sm (ρ ^ (n + 1)) (R (h0 ^ l ^ n) - 1) := by
    intro n
    induction n with
    | zero => simpa using ⟨hkdet, hksm⟩
    | succ n ih =>
      have he : R (h0 ^ l ^ (n + 1)) = R (h0 ^ l ^ n) ^ l := by rw [pow_succ, pow_mul, map_pow]
      refine ⟨by rw [he, Matrix.det_pow, ih.1, one_pow], ?_⟩
      have h1 := noab_pow l (ρ ^ (n + 1)) (R (h0 ^ l ^ n) - 1) (by positivity) (pow_le_one₀ hρ0.le hρ1.le) ih.2 l
      rw [add_sub_cancel] at h1
      have h2 := ih.2.smul ((l : ℕ) : Qbar l)
      have e : R (h0 ^ l ^ (n + 1)) - 1 =
          (R (h0 ^ l ^ n) ^ l - 1 - ((l : ℕ) : Qbar l) • (R (h0 ^ l ^ n) - 1)) + ((l : ℕ) : Qbar l) • (R (h0 ^ l ^ n) - 1) := by
        rw [he]; abel
      rw [e]
      refine (h1.mono ?_).add (h2.mono ?_)
      · rw [← pow_mul]; exact pow_le_pow_of_le_one hρ0.le hρ1.le (by omega)
      · rw [← hρ, pow_succ' ρ (n + 1)]
  obtain ⟨N, γ, a, haug⟩ := GlobalTheory.T.exists_augmentation_combination_eq_id_traceless_irreducible l c Γ r hint hirr
  obtain ⟨s, hs⟩ := noab_denom l N a
  set b : Fin N → ℤ_[l] := fun i => ⟨((l : ℕ) : ℚ_[l]) ^ s * a i, hs i⟩ with hbdef
  obtain ⟨C, hC⟩ := GlobalTheory.T.galoisHom_zl_lipschitz_of_ker_le_linearGroup l c Γ r lam hr hint hlam hker
  have key : ∀ n : ℕ, ρ ^ (s + n) * ‖v0‖ ≤ C * ρ ^ (2 * n + 1) := by
    intro n

    set h := h0 ^ l ^ n with hhdef
    set Z := R h - 1 with hZdef
    set Z' := R h⁻¹ - 1 with hZ'def
    set ε : ℝ := ρ ^ (n + 1) with hεdef
    set τ : ℝ := ρ ^ (2 * n + 1) with hτdef
    obtain ⟨hdet1, hZ⟩ := hpow n
    have hε0 : 0 ≤ ε := by positivity
    have hε1 : ε ≤ 1 := pow_le_one₀ hρ0.le hρ1.le
    have hτ0 : 0 ≤ τ := by positivity
    have hεε : ε ^ 2 ≤ τ := by rw [← pow_mul]; exact pow_le_pow_of_le_one hρ0.le hρ1.le (by omega)
    have hτε : τ ≤ ε := pow_le_pow_of_le_one hρ0.le hρ1.le (by omega)
    have hε2ε : ε ^ 2 ≤ ε := hεε.trans hτε
    have hRh : R h = 1 + Z := by rw [hZdef, add_sub_cancel]
    have hRh' : R h⁻¹ = 1 + Z' := by rw [hZ'def, add_sub_cancel]
    have htr : Z.trace = - Z.det := noab_trace_eq Z (by rw [← hRh]; exact hdet1)
    have htrn : ‖Z.trace‖ ≤ ε ^ 2 := by rw [htr, norm_neg]; exact hZ.det hε0
    have hZ'Z : Z' + Z = Z.trace • (1 : Matrix (Fin 2) (Fin 2) (Qbar l)) := by
      have hinv : R h⁻¹ = (R h).trace • 1 - R h := by
        simp only [hRdef, MonoidHom.coe_comp, Function.comp_apply, map_inv, Units.coeHom_apply]
        exact noab_inv_det_one (r h) hdet1
      rw [hZ'def, hinv, hRh, Matrix.trace_add, Matrix.trace_one, Fintype.card_fin]
      module
    have hZ'Zs : Sm (ε ^ 2) (Z' + Z) := by rw [hZ'Z]; exact sm_scalar htrn (by positivity)
    have hZ' : Sm ε Z' := by
      have := (hZ'Zs.mono hε2ε).sub hZ
      rwa [add_sub_cancel_right] at this
    set β : Fin N → ℕ := fun i => (b i).appr (2 * n + 1) with hβdef
    set A : Fin N → Matrix (Fin 2) (Fin 2) (Qbar l) := fun i => R (γ i) with hAdef
    set A' : Fin N → Matrix (Fin 2) (Fin 2) (Qbar l) := fun i => R (γ i)⁻¹ with hA'def
    have hAA' : ∀ i, A i * A' i = 1 := fun i => by simp only [hAdef, hA'def, ← map_mul, mul_inv_cancel, map_one]
    set D : Fin N → Matrix (Fin 2) (Fin 2) (Qbar l) := fun i => A i * Z * A' i - Z with hDdef
    set F : Fin N → Matrix (Fin 2) (Fin 2) (Qbar l) := fun i => A i * (1 + Z) ^ β i * A' i * (1 + Z') ^ β i with hFdef
    have hE3 : ∀ i, Sm (ε ^ 2) (F i - 1 - (β i : Qbar l) • D i) := fun i =>
      noab_comm l ε (A i) (A' i) Z Z' (β i) hε0 hε1 (hAA' i) (hRint _) (hRint _) hZ hZ'Zs
    have hD : ∀ i, Sm ε (D i) := fun i => by
      have h1 := ((hRint (γ i)).mul hZ zero_le_one).mul (hRint (γ i)⁻¹) (by positivity)
      rw [one_mul, mul_one] at h1
      exact h1.sub hZ
    have hF : ∀ i, Sm ε (F i - 1) := fun i => by
      have := ((hE3 i).mono hε2ε).add ((hD i).smul_le hε0 (norm_natCast_le_one (β i)))
      rwa [sub_add_cancel] at this
    set P : Γ := (h⁻¹) ^ (l ^ s) * (List.ofFn fun i => γ i * h ^ β i * (γ i)⁻¹ * (h⁻¹) ^ β i).prod with hPdef
    have hRP : R P = (1 + Z') ^ (l ^ s) * (List.ofFn F).prod := by
      rw [hPdef, map_mul, map_pow, map_list_prod, List.map_ofFn, hRh']
      refine congrArg (fun L => _ * List.prod L) (congrArg List.ofFn (funext fun i => ?_))
      simp only [Function.comp_apply, map_mul, map_pow, hFdef, hAdef, hA'def, hRh, hRh']
    have hlamP : ‖Multiplicative.toAdd (lam P)‖ = ρ ^ (s + n) * ‖v0‖ := by
      have hfac : ∀ i, lam (γ i * h ^ β i * (γ i)⁻¹ * (h⁻¹) ^ β i) = 1 := fun i => by
        simp only [map_mul, map_pow, map_inv]
        rw [mul_comm (lam (γ i)) _, mul_assoc, mul_assoc, mul_inv_cancel_left, inv_pow, mul_inv_cancel]
      have hprod : lam (List.ofFn fun i => γ i * h ^ β i * (γ i)⁻¹ * (h⁻¹) ^ β i).prod = 1 := by
        rw [map_list_prod, List.map_ofFn, List.prod_ofFn]
        exact Finset.prod_eq_one fun i _ => hfac i
      have e : Multiplicative.toAdd (lam P) = -(((l ^ s : ℕ) : ℤ_[l]) * (((l ^ n : ℕ) : ℤ_[l]) * v0)) := by
        rw [hPdef, map_mul lam, hprod, mul_one, map_pow lam, map_inv lam, hhdef, map_pow lam]
        simp only [toAdd_pow, toAdd_inv, nsmul_eq_mul, hv0def]
        ring
      rw [e, norm_neg, norm_mul, norm_mul, Nat.cast_pow, Nat.cast_pow, norm_pow, norm_pow, hρZ, pow_add]
      ring
    have hsm : Sm τ (R P - 1) := by
      set ls : Qbar l := ((l ^ s : ℕ) : Qbar l) with hlsdef
      have hls : ‖ls‖ ≤ 1 := norm_natCast_le_one _
      set t := Z.trace with htdef
      set aQ : Fin N → Qbar l := fun i => algebraMap ℚ_[l] (Qbar l) (a i) with haQ
      set bQ : Fin N → Qbar l := fun i => ls * aQ i with hbQ
      set Q1 := (1 + Z') ^ (l ^ s) with hQ1
      set Q2 := (List.ofFn F).prod with hQ2
      have hE1 : Sm (ε ^ 2) (Q1 - 1 - ls • Z') := noab_pow l ε Z' hε0 hε1 hZ' (l ^ s)
      have hE2 : Sm (ε ^ 2) (Q2 - 1 - ∑ i, (F i - 1)) := by
        have := noab_prod l ε (List.ofFn F) hε0 hε1 (fun M hM => by
          obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hM; exact hF i)
        convert this using 2
        rw [List.map_ofFn, List.sum_ofFn]; rfl
      have hβb : ∀ i, ‖(β i : Qbar l) - bQ i‖ ≤ τ := fun i => by
        have hsp := PadicInt.appr_spec (2 * n + 1) (b i)
        rw [← PadicInt.norm_le_pow_iff_mem_span_pow] at hsp
        have e : (β i : Qbar l) - bQ i = - algebraMap ℚ_[l] (Qbar l) ((b i - (β i : ℤ_[l]) : ℤ_[l]) : ℚ_[l]) := by
          rw [PadicInt.coe_sub, PadicInt.coe_natCast, map_sub, map_natCast]
          simp only [hβdef, hbQ, haQ, hlsdef, hbdef, map_mul, map_pow, map_natCast, Nat.cast_pow]
          ring
        rw [e, norm_neg, norm_algebraMap', ← PadicInt.norm_def]
        refine hsp.trans (le_of_eq ?_)
        rw [hτdef, hρeq, zpow_neg, zpow_natCast, inv_pow]
      set X := Z - (t / 2) • (1 : Matrix (Fin 2) (Fin 2) (Qbar l)) with hXdef
      have hXtr : X.trace = 0 := by
        rw [hXdef, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, ← htdef]
        simp only [smul_eq_mul, Nat.cast_ofNat]
        ring
      have hsumD : ∑ i, aQ i • D i = X := by
        conv_rhs => rw [haug X hXtr]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [haQ, algebraMap_smul]
        congr 1
        have hA'i : (((r (γ i))⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) = A' i := by
          simp [hA'def, hRdef, map_inv]
        have hAi : ((r (γ i) : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) = A i := rfl
        rw [hA'i, hAi, hDdef, hXdef]
        simp only [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, mul_one, hAA' i]
        abel
      have hsumB : ∑ i, bQ i • D i = ls • X := by
        rw [← hsumD, Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [hbQ]; exact mul_smul _ _ _
      have hiden : R P - 1 = (Q1 - 1 - ls • Z') + (Q2 - 1 - ∑ i, (F i - 1)) + ∑ i, (F i - 1 - (β i : Qbar l) • D i)
          + ∑ i, ((β i : Qbar l) - bQ i) • D i + (Q1 - 1) * (Q2 - 1)
          + (ls * (t / 2)) • (1 : Matrix (Fin 2) (Fin 2) (Qbar l)) := by
        have e1 : ∑ i, (F i - 1 - (β i : Qbar l) • D i) = ∑ i, (F i - 1) - ∑ i, (β i : Qbar l) • D i :=
          Finset.sum_sub_distrib _ _
        have e2 : ∑ i, ((β i : Qbar l) - bQ i) • D i = ∑ i, (β i : Qbar l) • D i - ls • X := by
          rw [← hsumB, ← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun i _ => sub_smul _ _ _
        have e3 : Z' = t • 1 - Z := eq_sub_of_add_eq hZ'Z
        rw [e1, e2, hRP, e3, hXdef]
        simp only [sub_mul, mul_sub, one_mul, mul_one]
        module
      have hQ1s : Sm ε (Q1 - 1) := by
        have := (hE1.mono hε2ε).add (hZ'.smul_le hε0 hls); rwa [sub_add_cancel] at this
      have hSF : Sm ε (∑ i, (F i - 1)) := Sm.sum _ hε0 _ fun i _ => hF i
      have hQ2s : Sm ε (Q2 - 1) := by
        have := (hE2.mono hε2ε).add hSF; rwa [sub_add_cancel] at this
      have hlast : Sm τ ((ls * (t / 2)) • (1 : Matrix (Fin 2) (Fin 2) (Qbar l))) := by
        refine sm_scalar ?_ hτ0
        rw [norm_mul, norm_div]
        have h2n := noab_norm_two l
        calc ‖ls‖ * (‖t‖ / ‖(2 : Qbar l)‖) ≤ 1 * (ε ^ 2 / ρ) :=
              mul_le_mul hls (div_le_div₀ (by positivity) htrn hρ0 h2n) (by positivity) zero_le_one
          _ = τ := by
            rw [one_mul, hεdef, hτdef, ← pow_mul, div_eq_iff hρ0.ne', ← pow_succ]; congr 1; ring
      rw [hiden]
      refine (((((hE1.mono hεε).add (hE2.mono hεε)).add (Sm.sum _ hτ0 _ fun i _ => (hE3 i).mono hεε)).add
        (Sm.sum _ hτ0 _ fun i _ => ?_)).add ((hQ1s.mul hQ2s hε0).mono ?_)).add hlast
      · exact ((hD i).smul _).mono ((mul_le_mul (hβb i) hε1 hε0 hτ0).trans (le_of_eq (mul_one τ)))
      · rw [← sq]; exact hεε
    have := hC (2 * n + 1) P (fun i j => by rw [norm_pow]; exact hsm i j)
    rw [hlamP, norm_pow] at this
    exact this

  have hbound : ∀ m : ℕ, ‖v0‖ ≤ C * ρ ^ (m + 1) := by
    intro m
    have h := key (s + m)
    have e : ρ ^ (2 * (s + m) + 1) = ρ ^ (s + (s + m)) * ρ ^ (m + 1) := by rw [← pow_add]; congr 1; omega
    rw [e, mul_left_comm] at h
    exact le_of_mul_le_mul_left h (by positivity)
  have ht : Filter.Tendsto (fun m : ℕ => C * ρ ^ (m + 1)) Filter.atTop (nhds (C * 0)) :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1).comp (Filter.tendsto_add_atTop_nat 1)).const_mul C
  have h0' : ‖v0‖ ≤ C * 0 := ge_of_tendsto' ht hbound
  rw [mul_zero] at h0'
  exact hv0 (norm_le_zero_iff.1 h0')

end GlobalTheory.Ord2

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HomPadicIntTrivialOfIrreducibleCompactRepStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hom_padicInt_trivial_of_irreducible_compact_rep : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (r : Γ →* GL (Fin 2) (Qbar l)) (lam : Γ →* Multiplicative ℤ_[l]), Continuous r → (∀ g i j, (r g : Matrix (Fin 2) (Fin 2) (Qbar l)) i j ∈ c.O) → (∀ g, (r g : Matrix (Fin 2) (Fin 2) (Qbar l)).det ^ 2 = 1) → IsIrr r → Continuous lam → r.ker ≤ lam.ker → lam = 1 := by
  first | exact @GlobalTheory.Ord2.hom_padicInt_trivial | exact GlobalTheory.Ord2.hom_padicInt_trivial | (intros; apply GlobalTheory.Ord2.hom_padicInt_trivial <;> assumption)
end

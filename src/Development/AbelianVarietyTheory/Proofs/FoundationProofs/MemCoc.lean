module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsLocallyConstantCycMod
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowMulMemAdd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsQuotientMapToGSProd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormLeOneOfIsIntegralPadicInt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemCoc
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

namespace GlobalTheory.InertCoh

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

def cob (W : R2 Ω l) (c : Coef l) (I : Subgroup (G ℚ Ω)) : Submodule c.O (G ℚ Ω → Fin 2 → Qbar l) where
  carrier := {z | ∃ v : Fin 2 → Qbar l, ∀ s ∈ I, z s = mat W s *ᵥ v - v}
  zero_mem' := ⟨0, fun s _ => by simp⟩
  add_mem' := by
    rintro a b ⟨v, hv⟩ ⟨w, hw⟩
    refine ⟨v + w, fun s hs => ?_⟩
    simp only [Pi.add_apply, hv s hs, hw s hs, Matrix.mulVec_add]
    abel
  smul_mem' := by
    rintro k a ⟨v, hv⟩
    refine ⟨k • v, fun s hs => ?_⟩
    simp only [Pi.smul_apply, hv s hs, Matrix.mulVec_smul, smul_sub]

def coc (W : R2 Ω l) (c : Coef l) (I : Subgroup (G ℚ Ω)) : Submodule c.O (G ℚ Ω → Fin 2 → Qbar l) where
  carrier := {z | (∀ i, Continuous fun s => z s i) ∧ (∀ s i, z s i ∈ c.O) ∧
    ∀ s ∈ I, ∀ t ∈ I, z (s * t) = z s + mat W s *ᵥ z t}
  zero_mem' := ⟨fun i => continuous_const, fun s i => c.O.zero_mem, fun s _ t _ => by simp⟩
  add_mem' := by
    rintro a b ⟨ha1, ha2, ha3⟩ ⟨hb1, hb2, hb3⟩
    refine ⟨fun i => (ha1 i).add (hb1 i), fun s i => c.O.add_mem (ha2 s i) (hb2 s i), fun s hs t ht => ?_⟩
    simp only [Pi.add_apply, ha3 s hs t ht, hb3 s hs t ht, Matrix.mulVec_add]
    abel
  smul_mem' := by
    rintro k a ⟨ha1, ha2, ha3⟩
    refine ⟨fun i => ?_, fun s i => ?_, fun s hs t ht => ?_⟩
    · simp only [Pi.smul_apply, Subalgebra.smul_def, smul_eq_mul]
      exact continuous_const.mul (ha1 i)
    · simp only [Pi.smul_apply, Subalgebra.smul_def, smul_eq_mul]
      exact c.O.mul_mem k.2 (ha2 s i)
    · simp only [Pi.smul_apply, ha3 s hs t ht, Matrix.mulVec_smul, smul_add]

theorem mem_cob {W : R2 Ω l} {c : Coef l} {I : Subgroup (G ℚ Ω)} {z : G ℚ Ω → Fin 2 → Qbar l} :
    z ∈ cob W c I ↔ ∃ v : Fin 2 → Qbar l, ∀ s ∈ I, z s = mat W s *ᵥ v - v := Iff.rfl

theorem mem_coc {W : R2 Ω l} {c : Coef l} {I : Subgroup (G ℚ Ω)} {z : G ℚ Ω → Fin 2 → Qbar l} :
    z ∈ coc W c I ↔ (∀ i, Continuous fun s => z s i) ∧ (∀ s i, z s i ∈ c.O) ∧
      ∀ s ∈ I, ∀ t ∈ I, z (s * t) = z s + mat W s *ᵥ z t := Iff.rfl

end GlobalTheory.InertCoh

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqZeroOfForallNormLe
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormLeOneOfMemCoef
theorem UpperTheory.Reformulated.B.Rf3.norm_le_one_of_mem_coef :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] (c : UpperTheory.V.HV.Coef l)
    {x : Formalism.ConjugateSelfDual.Qbar l},
    x ∈ c.O →
      ‖x‖ ≤
        (1 :
          ℝ) := by
  intro l inst c x hx
  let v : Valuation (PadicAlgCl l) NNReal := NormedField.valuation
  have hv : ∀ y, y ∈ v.integer ↔ ‖y‖ ≤ 1 := fun y => Iff.rfl
  have h1 : IsIntegral ℤ_[l] x :=
    (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val
  have h2 : ∀ a : ℤ_[l], algebraMap ℤ_[l] (PadicAlgCl l) a ∈ v.integer := fun a => by
    rw [hv, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), PadicAlgCl.norm_extends]
    exact a.2
  have h3 : IsIntegral v.integer x :=
    h1.map_of_comp_eq ((algebraMap ℤ_[l] (PadicAlgCl l)).codRestrict v.integer h2) (RingHom.id _) rfl
  exact (hv x).1 ((Valuation.integer.integers v).mem_of_integral h3)
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2

variable {l : ℕ} [Fact l.Prime]

theorem norm_le_one_of_mem_coef (c : Coef l) {x : Qbar l} (hx : x ∈ c.O) : ‖x‖ ≤ 1 :=
  _root_.UpperTheory.Reformulated.B.Rf3.norm_le_one_of_mem_coef c hx

theorem norm_natCast_l : ‖((l : ℕ) : Qbar l)‖ = (l : ℝ)⁻¹ := by
  have : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
  rw [this, norm_algebraMap', Padic.norm_p]

theorem norm_natCast_l_lt_one : ‖((l : ℕ) : Qbar l)‖ < 1 := by
  rw [norm_natCast_l]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)

theorem tendsto_norm_l_pow :
    Filter.Tendsto (fun n : ℕ => ‖((l : ℕ) : Qbar l) ^ n‖) Filter.atTop (nhds 0) := by
  simp only [norm_pow]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) norm_natCast_l_lt_one

theorem eq_zero_of_forall_norm_le (x : Qbar l) (h : ∀ n : ℕ, ‖x‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖) : x = 0 := by
  have h0 : ‖x‖ ≤ 0 := ge_of_tendsto' tendsto_norm_l_pow h
  exact norm_le_zero_iff.1 h0

theorem cg_symm {n : ℕ} {a b : Qbar l} (h : Cg n a b) : Cg n b a := by
  unfold Cg at *; rwa [norm_sub_rev]

theorem cg_trans {n : ℕ} {a b d : Qbar l} (h : Cg n a b) (h' : Cg n b d) : Cg n a d := by
  unfold Cg at *
  have e : a - d = (a - b) + (b - d) := by ring
  rw [e]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h h')

theorem cv_symm {n : ℕ} {a b : Fin 2 → Qbar l} (h : Cv n a b) : Cv n b a := fun i => cg_symm (h i)

theorem cv_trans {n : ℕ} {a b d : Fin 2 → Qbar l} (h : Cv n a b) (h' : Cv n b d) : Cv n a d :=
  fun i => cg_trans (h i) (h' i)

theorem eq_of_forall_cg {a b : Qbar l} (h : ∀ n, Cg n a b) : a = b :=
  sub_eq_zero.1 (eq_zero_of_forall_norm_le _ h)

end GlobalTheory.Ord2

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormIntCastLeOfDvd
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

namespace GlobalTheory.PowCong

variable {l : ℕ} [Fact l.Prime]

theorem norm_intCast_eq (k : ℤ) : ‖(k : Qbar l)‖ = ‖(k : ℚ_[l])‖ := by
  rw [show (k : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) (k : ℚ_[l]) from (map_intCast _ k).symm]
  exact PadicAlgCl.norm_extends l _

theorem norm_natCast_eq (n : ℕ) : ‖(n : Qbar l)‖ = ‖(n : ℚ_[l])‖ := by
  have := norm_intCast_eq (l := l) (n : ℤ)
  simpa using this

theorem norm_l_pow (r : ℕ) : ‖((l : ℕ) : Qbar l) ^ r‖ = (l : ℝ) ^ (-(r : ℤ)) := by
  rw [norm_pow, norm_natCast_eq, Padic.norm_p, zpow_neg, zpow_natCast, inv_pow]

theorem norm_intCast_le_of_dvd (r : ℕ) (k : ℤ) (h : ((l : ℤ) ^ r) ∣ k) : ‖(k : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
  rw [norm_intCast_eq, norm_l_pow]
  exact (Padic.norm_int_le_pow_iff_dvd k r).mpr h

theorem norm_natCast_eq_one {n : ℕ} (h : ¬ l ∣ n) : ‖(n : Qbar l)‖ = 1 := by
  rw [norm_natCast_eq, Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr h

theorem key (r e a b : ℕ) (ha : ¬ l ∣ a) (hb : b = a % l ^ r) (hb' : 1 ≤ r → ¬ l ∣ b) :
    ‖((a : Qbar l) ^ e)⁻¹ - ((b : Qbar l) ^ e)⁻¹‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ ∧
      ‖(a : Qbar l) ^ e - (b : Qbar l) ^ e‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
  have hcong : ((l : ℤ) ^ r) ∣ (((a ^ e : ℕ) : ℤ) - ((b ^ e : ℕ) : ℤ)) := by
    have h1 := (Nat.mod_modEq a (l ^ r)).pow e
    have h2 := (Nat.modEq_iff_dvd.mp h1)
    rw [hb]
    push_cast at h2 ⊢
    exact h2
  have hsub : ‖(a : Qbar l) ^ e - (b : Qbar l) ^ e‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
    have := norm_intCast_le_of_dvd (l := l) r _ hcong
    push_cast at this
    exact this
  refine ⟨?_, hsub⟩
  have hna : ‖(a : Qbar l)‖ = 1 := norm_natCast_eq_one ha
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    have hb0 : b = 0 := by rw [hb, pow_zero, Nat.mod_one]
    subst hb0
    rcases Nat.eq_zero_or_pos e with he | he
    · subst he; simp
    · rw [Nat.cast_zero, zero_pow he.ne', inv_zero, sub_zero, norm_inv, norm_pow, hna]
      simp
  · have hnb : ‖(b : Qbar l)‖ = 1 := norm_natCast_eq_one (hb' hr)
    have ha0 : ((a : Qbar l) ^ e) ≠ 0 := by
      intro h; have := congrArg norm h; rw [norm_pow, hna] at this; simp at this
    have hb0 : ((b : Qbar l) ^ e) ≠ 0 := by
      intro h; have := congrArg norm h; rw [norm_pow, hnb] at this; simp at this
    rw [inv_sub_inv ha0 hb0, norm_div, norm_mul, norm_pow, norm_pow, hna, hnb, one_pow, mul_one, div_one,
      norm_sub_rev]
    exact hsub

theorem powCong : ∀ (l : ℕ) [Fact l.Prime] (e r : ℕ) (x : (ZMod (l ^ (r + 1)))ˣ), ‖(((x : ZMod (l ^ (r + 1))).val : Qbar l) ^ e)⁻¹ - (((((Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) x : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val : Qbar l) ^ e)⁻¹‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ ∧ ‖((x : ZMod (l ^ (r + 1))).val : Qbar l) ^ e - ((((Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) x : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val : Qbar l) ^ e‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
  intro l hl e r x
  have hp : l.Prime := hl.out
  haveI : NeZero (l ^ (r + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have notdvd : ∀ {k : ℕ}, 1 ≤ k → (u : (ZMod (l ^ k))ˣ) → ¬ l ∣ (u : ZMod (l ^ k)).val := by
    intro k hk u hd
    have hc := ZMod.val_coe_unit_coprime u
    have : l ∣ Nat.gcd (u : ZMod (l ^ k)).val (l ^ k) := Nat.dvd_gcd hd (dvd_pow_self l (by omega))
    rw [hc] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  refine key (l := l) r e _ _ (notdvd (by omega) x) ?_ (fun hr => notdvd hr _)
  rw [Units.coe_map]
  simp only [MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, ZMod.castHom_apply]
  rw [ZMod.cast_eq_val, ZMod.val_natCast]

end GlobalTheory.PowCong
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoboundaryInertiaIndependent
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormAlgebraMapPadicIntLeOne
namespace GlobalTheory.PadicIntegralNormLeOne

open Polynomial

theorem norm_algebraMap_padicInt_le_one {l : ℕ} [Fact (Nat.Prime l)] (a : ℤ_[l]) :
    ‖algebraMap ℤ_[l] (PadicAlgCl l) a‖ ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l),
    PadicAlgCl.norm_extends]
  exact PadicInt.norm_le_one a

theorem norm_le_one_of_isIntegral {l : ℕ} [Fact (Nat.Prime l)] (x : PadicAlgCl l)
    (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ (1 : ℝ) := by
  obtain ⟨f, hmon, hf⟩ := hx
  by_contra h
  push_neg at h
  have hsum := hf
  rw [eval₂_eq_sum_range, Finset.sum_range_succ, Polynomial.coeff_natDegree, hmon.leadingCoeff,
    map_one, one_mul] at hsum
  set n := f.natDegree
  set S := ∑ i ∈ Finset.range n, algebraMap ℤ_[l] (PadicAlgCl l) (f.coeff i) * x ^ i
  have hxn : x ^ n = -S := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact hsum
  rcases Nat.eq_zero_or_pos n with hn | hn
  · have : S = 0 := by simp [S, hn]
    rw [this, hn, pow_zero, neg_zero] at hxn
    exact one_ne_zero hxn
  · have hx1 : (1 : ℝ) ≤ ‖x‖ := h.le
    have hS : ‖S‖ ≤ ‖x‖ ^ (n - 1) := by
      apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
      intro i hi
      rw [Finset.mem_range] at hi
      rw [norm_mul, norm_pow]
      calc ‖algebraMap ℤ_[l] (PadicAlgCl l) (f.coeff i)‖ * ‖x‖ ^ i ≤ 1 * ‖x‖ ^ i := by
            gcongr; exact norm_algebraMap_padicInt_le_one _
        _ = ‖x‖ ^ i := one_mul _
        _ ≤ ‖x‖ ^ (n - 1) := pow_le_pow_right₀ hx1 (by omega)
    have hlt : ‖x‖ ^ (n - 1) < ‖x‖ ^ n := pow_lt_pow_right₀ h (by omega)
    have : ‖x ^ n‖ = ‖S‖ := by rw [hxn, norm_neg]
    rw [norm_pow] at this
    linarith

end GlobalTheory.PadicIntegralNormLeOne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoboundaryInertiaIndependent
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.CobConj

variable {l : ℕ} [Fact l.Prime]

theorem norm_le_one_of_isIntegral (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.PadicIntegralNormLeOne.norm_le_one_of_isIntegral
  | exact _root_.GlobalTheory.PadicIntegralNormLeOne.norm_le_one_of_isIntegral
  | (apply _root_.GlobalTheory.PadicIntegralNormLeOne.norm_le_one_of_isIntegral <;> assumption)
  | (intros; apply _root_.GlobalTheory.PadicIntegralNormLeOne.norm_le_one_of_isIntegral <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PadicIntegralNormLeOne.norm_le_one_of_isIntegral <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PadicIntegralNormLeOne.norm_le_one_of_isIntegral ..)

theorem norm_le_one_of_memO (c : Coef l) {x : Qbar l} (hx : x ∈ c.O) : ‖x‖ ≤ 1 := by
  have hi : IsIntegral ℤ_[l] (⟨x, hx⟩ : c.O) := Algebra.IsIntegral.isIntegral _
  exact norm_le_one_of_isIntegral x (hi.map c.O.val)

def Sm (n : ℕ) (v : Fin 2 → Qbar l) : Prop := ∀ i, ‖v i‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖

theorem sm_add {n : ℕ} {a b : Fin 2 → Qbar l} (ha : Sm n a) (hb : Sm n b) : Sm n (a + b) := fun i =>
  (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha i) (hb i))

theorem sm_neg {n : ℕ} {a : Fin 2 → Qbar l} (ha : Sm n a) : Sm n (-a) := fun i => by
  simpa using ha i

theorem sm_sub {n : ℕ} {a b : Fin 2 → Qbar l} (ha : Sm n a) (hb : Sm n b) : Sm n (a - b) := by
  rw [sub_eq_add_neg]; exact sm_add ha (sm_neg hb)

theorem sm_mulVec (c : Coef l) {n : ℕ} {M : Matrix (Fin 2) (Fin 2) (Qbar l)} (hM : ∀ i j, M i j ∈ c.O)
    {a : Fin 2 → Qbar l} (ha : Sm n a) : Sm n (M *ᵥ a) := fun i => by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_) <;> rw [norm_mul] <;>
    exact (mul_le_mul (norm_le_one_of_memO c (hM _ _)) (ha _) (norm_nonneg _) zero_le_one).trans (by rw [one_mul])

theorem cv_iff {n : ℕ} {a b : Fin 2 → Qbar l} : Cv n a b ↔ Sm n (a - b) := Iff.rfl

theorem key_identity (Mσ Ms Mτ : Matrix (Fin 2) (Fin 2) (Qbar l)) (hτσ : Mτ * Mσ = 1)
    (zs' zσ zsτ zs zτ z1 x : Fin 2 → Qbar l) :
    zs' - ((Mσ * Ms * Mτ) *ᵥ (Mσ *ᵥ x - zσ) - (Mσ *ᵥ x - zσ)) =
      (zs' - (zσ + Mσ *ᵥ zsτ)) + Mσ *ᵥ (zsτ - (zs + Ms *ᵥ zτ)) + Mσ *ᵥ (zs - (Ms *ᵥ x - x))
        - Mσ *ᵥ (Ms *ᵥ (z1 - (z1 + (1 : Matrix (Fin 2) (Fin 2) (Qbar l)) *ᵥ z1)))
        - Mσ *ᵥ (Ms *ᵥ (z1 - (zτ + Mτ *ᵥ zσ))) := by
  simp only [Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.one_mulVec, Matrix.mul_assoc, hτσ,
    Matrix.mul_one]
  abel

theorem cob_conj : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (c : Coef l) (n : ℕ) (z : G ℚ Ω → Fin 2 → Qbar l) (q : Pl) (B B' : ValuationSubring Ω), (∀ s i j, mat W s i j ∈ c.O) → Coc1 c n W ⊤ z → IsPlaceOver B q → IsPlaceOver B' q → Cob1 c n W (Ine (F := ℚ) B) z → Cob1 c n W (Ine (F := ℚ) B') z := by
  intro l _ Ω _ _ _ W c n z q B B' hW hC hB hB' hcob
  obtain ⟨x, hxO, hx⟩ := hcob
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hB hB'
  have hcoc : ∀ a b : G ℚ Ω, Sm n (z (a * b) - (z a + mat W a *ᵥ z b)) := fun a b =>
    hC.2.2 a (Subgroup.mem_top a) b (Subgroup.mem_top b)
  have hτσ : mat W σ⁻¹ * mat W σ = 1 := by
    simp only [mat, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have h1 : mat W 1 = 1 := by simp [mat]
  refine ⟨mat W σ *ᵥ x - z σ, fun i => ?_, fun s' hs' => ?_⟩
  · simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    exact c.O.sub_mem (c.O.add_mem (c.O.mul_mem (hW _ _ _) (hxO _)) (c.O.mul_mem (hW _ _ _) (hxO _))) (hC.2.1 σ i)
  set s := σ⁻¹ * s' * σ with hsdef
  have hs : s ∈ Ine (F := ℚ) B := GlobalTheory.ParamRepCompare.conj_mem_Ine_of_smul_eq hσ hs'
  have e : s' = σ * (s * σ⁻¹) := by rw [hsdef]; group
  have hM : mat W s' = mat W σ * mat W s * mat W σ⁻¹ := by
    rw [e]; simp only [mat, map_mul, Units.val_mul, Matrix.mul_assoc]
  rw [cv_iff, hM, key_identity _ _ _ hτσ (z s') (z σ) (z (s * σ⁻¹)) (z s) (z σ⁻¹) (z 1) x]
  have hA : Sm n (z s' - (z σ + mat W σ *ᵥ z (s * σ⁻¹))) := by
    have := hcoc σ (s * σ⁻¹); rwa [← e] at this
  have hD : Sm n (z 1 - (z 1 + (1 : Matrix (Fin 2) (Fin 2) (Qbar l)) *ᵥ z 1)) := by
    have := hcoc 1 1; rwa [mul_one, h1] at this
  have hE : Sm n (z 1 - (z σ⁻¹ + mat W σ⁻¹ *ᵥ z σ)) := by
    have := hcoc σ⁻¹ σ; rwa [inv_mul_cancel] at this
  exact sm_sub (sm_sub (sm_add (sm_add hA (sm_mulVec c (hW σ) (hcoc s σ⁻¹))) (sm_mulVec c (hW σ) (hx s hs)))
    (sm_mulVec c (hW σ) (sm_mulVec c (hW s) hD))) (sm_mulVec c (hW σ) (sm_mulVec c (hW s) hE))

end GlobalTheory.Ord2.CobConj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoboundaryInertiaIndependentStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coboundary_inertia_independent : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (c : Coef l) (n : ℕ) (z : G ℚ Ω → Fin 2 → Qbar l) (q : Pl) (B B' : ValuationSubring Ω), (∀ s i j, mat W s i j ∈ c.O) → Coc1 c n W ⊤ z → IsPlaceOver B q → IsPlaceOver B' q → Cob1 c n W (Ine (F := ℚ) B) z → Cob1 c n W (Ine (F := ℚ) B') z := by
  first | exact @GlobalTheory.Ord2.CobConj.cob_conj | exact GlobalTheory.Ord2.CobConj.cob_conj | (intros; apply GlobalTheory.Ord2.CobConj.cob_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralTwoCocycleReciprocityTrivialAtLastPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralTwoCocycleReciprocityTrivialAtLastPlace
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.Rec

open GlobalTheory.Published.PoitouTate

variable {l : ℕ} [Fact l.Prime] {c : Coef l}
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {n : ℕ} {S : Finset Pl}
  {ξ : G ℚ Ω → G ℚ Ω → Qbar l}

def zcl {μ : GS Ω (S : Set Pl) →* (ZMod (l ^ n))ˣ} (hμ : μ.comp (toGS Ω _) = cycMod ℚ Ω l n)
    (hξ : Coc2 c n S ξ) (i : Ix c) : H2 (charRep μ) :=
  Submodule.Quotient.mk ⟨zc c n S ξ i, zc_mem hμ hξ i⟩

theorem res_zcl_eq_zero {μ : GS Ω (S : Set Pl) →* (ZMod (l ^ n))ˣ}
    (hμ : μ.comp (toGS Ω _) = cycMod ℚ Ω l n) (hξ : Coc2 c n S ξ) (Av : S → ValuationSubring Ω) (v : S)
    (hcob : Cob2 c n (Dec (F := ℚ) (Av v)) ξ) (i : Ix c) :
    resH2 (charRep μ) (locFam S Av v) (continuous_locFam S Av v) (zcl hμ hξ i) = 0 := by
  obtain ⟨u, hu, huO, hcu⟩ := hcob
  unfold zcl resH2
  rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype,
    separated_dvr_second_cohomology_mem]
  refine ⟨fun g => crd c n i (u g), continuous_crd hu.domRestrict (fun g => huO _) n i, ?_⟩
  funext ⟨g, h⟩
  rw [d1_apply, restrictCocycles2_apply]
  change _ = zc c n S ξ i (((g : G ℚ Ω) : GS Ω (S : Set Pl)), ((h : G ℚ Ω) : GS Ω (S : Set Pl)))
  rw [zc_mk hξ, MonoidHom.coe_comp, Function.comp_apply, charRep_apply]
  have hμg : ((μ (locFam S Av v g) : ZMod (l ^ n))) = PadicInt.toZModPow n (cycZ ℚ Ω l g : ℤ_[l]) :=
    congrArg Units.val (DFunLike.congr_fun hμ (g : G ℚ Ω))
  rw [hμg]
  have hc := (cg_iff (hξ.int g h) (c.O.add_mem (c.O.sub_mem (algebraMap_mul_mem _ (huO h)) (huO _)) (huO g))).1
    (hcu g g.2 h h.2) i
  rw [crd_add i (c.O.sub_mem (algebraMap_mul_mem _ (huO h)) (huO _)) (huO g),
    crd_sub i (algebraMap_mul_mem _ (huO h)) (huO _), crd_algebraMap_mul i _ (huO h)] at hc
  rw [hc]; rfl

theorem cob_of_res_zcl_eq_zero {μ : GS Ω (S : Set Pl) →* (ZMod (l ^ n))ˣ}
    (hμ : μ.comp (toGS Ω _) = cycMod ℚ Ω l n) (hξ : Coc2 c n S ξ) (Av : S → ValuationSubring Ω) (v : S)
    (h0 : ∀ i, resH2 (charRep μ) (locFam S Av v) (continuous_locFam S Av v) (zcl hμ hξ i) = 0) :
    Cob2 c n (Dec (F := ℚ) (Av v)) ξ := by
  have hb : ∀ i, ∃ ci : Dec (F := ℚ) (Av v) → ZMod (l ^ n), Continuous ci ∧
      d1 ((charRep μ).comp (locFam S Av v)) ci =
        fun p => zc c n S ξ i (((p.1 : G ℚ Ω) : GS Ω (S : Set Pl)), ((p.2 : G ℚ Ω) : GS Ω (S : Set Pl))) := by
    intro i
    have := h0 i
    unfold zcl resH2 at this
    rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype,
      separated_dvr_second_cohomology_mem] at this
    exact this
  choose ci hci hd using hb
  classical
  refine ⟨fun s => if hs : s ∈ Dec (F := ℚ) (Av v) then lft c n (fun i => ci i ⟨s, hs⟩) else 0, ?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have : (Set.domRestrict (Dec (F := ℚ) (Av v) : Set (G ℚ Ω))
        fun s => if hs : s ∈ Dec (F := ℚ) (Av v) then lft c n (fun i => ci i ⟨s, hs⟩) else 0) =
        fun g => lft c n (fun i => ci i g) := by
      funext g; exact dif_pos g.2
    rw [this]
    exact Continuous.comp (g := lft c n) (f := fun g i => ci i g) continuous_of_discreteTopology
      (continuous_pi fun i => hci i)
  · intro s
    dsimp only
    split_ifs
    · exact lft_mem _ _
    · exact c.O.zero_mem
  · intro s hs t ht
    dsimp only
    rw [dif_pos ht, dif_pos ((Dec (F := ℚ) (Av v)).mul_mem hs ht), dif_pos hs]
    have hm : ∀ a, lft c n a ∈ c.O := lft_mem n
    refine (cg_iff (hξ.int s t) (c.O.add_mem (c.O.sub_mem (algebraMap_mul_mem _ (hm _)) (hm _)) (hm _))).2
      fun i => ?_
    rw [crd_add i (c.O.sub_mem (algebraMap_mul_mem _ (hm _)) (hm _)) (hm _),
      crd_sub i (algebraMap_mul_mem _ (hm _)) (hm _), crd_algebraMap_mul i _ (hm _), crd_lft, crd_lft, crd_lft]
    have e := congrFun (hd i) (⟨s, hs⟩, ⟨t, ht⟩)
    rw [zc_mk hξ, d1_apply, MonoidHom.coe_comp, Function.comp_apply, charRep_apply] at e
    have hμg : ((μ (locFam S Av v ⟨s, hs⟩) : ZMod (l ^ n))) = PadicInt.toZModPow n (cycZ ℚ Ω l s : ℤ_[l]) :=
      congrArg Units.val (DFunLike.congr_fun hμ s)
    rw [hμg] at e
    rw [← e]; rfl

end GlobalTheory.Ord2.Rec

namespace GlobalTheory.Ord2.Rec

open GlobalTheory.Published.PoitouTate

theorem reciprocity : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ) (S : Finset Pl) (ξ : G ℚ Ω → G ℚ Ω → Qbar l) (v₀ : Pl),
    l ≠ 2 → ContainsAbove S l → Coc2 c n S ξ → v₀ ∈ S →
    (∀ v ∈ S, v ≠ v₀ → ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧ Cob2 c n (Dec (F := ℚ) B) ξ) →
    ∀ B : ValuationSubring Ω, IsPlaceOver B v₀ → Cob2 c n (Dec (F := ℚ) B) ξ := by
  intro hL l _ Ω _ _ _ c n S ξ v₀ hl hS hξ hv₀ hloc B hB
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨fun _ => 0, continuousOn_const, fun _ => c.O.zero_mem, fun s _ t _ => ?_⟩
    unfold Cg
    simp only [mul_zero, sub_zero, add_zero, pow_zero, norm_one]
    exact norm_le_one_of_mem (hξ.int s t)
  obtain ⟨ζ, hζ⟩ := GlobalTheory.Published.exists_primitiveRoot_pow ℚ Ω l n
  obtain ⟨inv, hinv, hPT⟩ := hL.pt ℚ Ω l n (Or.inl hl) hn ζ hζ
  classical
  let Av : S → ValuationSubring Ω := fun v =>
    if h : v.1 = v₀ then B else Classical.choose (hloc v.1 v.2 h)
  have hAv : ∀ v, IsPlaceOver (Av v) v.1 := by
    intro v
    by_cases h : v.1 = v₀
    · simp only [Av, dif_pos h]; rw [h]; exact hB
    · simp only [Av, dif_neg h]; exact (Classical.choose_spec (hloc v.1 v.2 h)).1
  obtain ⟨μ, hμ⟩ := exists_lift_cycMod (F := ℚ) (Ω := Ω) (r := n) hS
  have hNT := (hPT S hS Av hAv μ hμ (ZMod (l ^ n)) (charRep μ) (contAction_charRep hμ)).1
  have hres : ∀ i, resH2 (charRep μ) (locFam S Av ⟨v₀, hv₀⟩) (continuous_locFam S Av _)
      (zcl hμ hξ i) = 0 := by
    intro i
    have hsum := hNT.sum_eq_zero (zcl hμ hξ i)
    rw [Finset.sum_eq_single ⟨v₀, hv₀⟩] at hsum
    · have hinj : Function.Injective (invAt S Av μ hμ inv ⟨v₀, hv₀⟩) :=
        (hinv _ _ (hAv ⟨v₀, hv₀⟩)).1.1.comp (toMuLoc_bijective S Av μ hμ _).1
      exact hinj (by rw [hsum, map_zero])
    · intro v _ hv
      have hne : v.1 ≠ v₀ := fun h => hv (Subtype.ext h)
      have hcob : Cob2 c n (Dec (F := ℚ) (Av v)) ξ := by
        simp only [Av, dif_neg hne]; exact (Classical.choose_spec (hloc v.1 v.2 hne)).2
      rw [res_zcl_eq_zero hμ hξ Av v hcob i, map_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hcob := cob_of_res_zcl_eq_zero hμ hξ Av ⟨v₀, hv₀⟩ hres
  have hA : Av ⟨v₀, hv₀⟩ = B := dif_pos rfl
  rw [hA] at hcob
  exact hcob

end GlobalTheory.Ord2.Rec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralTwoCocycleReciprocityTrivialAtLastPlaceStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralTwoCocycle_reciprocity_trivial_at_last_place : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ) (S : Finset Pl) (ξ : G ℚ Ω → G ℚ Ω → Qbar l) (v₀ : Pl), l ≠ 2 → ContainsAbove S l → Coc2 c n S ξ → v₀ ∈ S → (∀ v ∈ S, v ≠ v₀ → ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧ Cob2 c n (Dec (F := ℚ) B) ξ) → ∀ B : ValuationSubring Ω, IsPlaceOver B v₀ → Cob2 c n (Dec (F := ℚ) B) ξ := by
  first | exact @GlobalTheory.Ord2.Rec.reciprocity | exact GlobalTheory.Ord2.Rec.reciprocity | (intros; apply GlobalTheory.Ord2.Rec.reciprocity <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CocyclePairingLocallyConstant
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CocyclePairingLocallyConstant
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.XiCoc

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem norm_le_one_of_int (x : Qbar l) (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.PadicIntegralNorm.norm_le_one_of_isIntegral_padicInt
  | exact _root_.GlobalTheory.PadicIntegralNorm.norm_le_one_of_isIntegral_padicInt
  | (apply _root_.GlobalTheory.PadicIntegralNorm.norm_le_one_of_isIntegral_padicInt <;> assumption)
  | (intros; apply _root_.GlobalTheory.PadicIntegralNorm.norm_le_one_of_isIntegral_padicInt <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PadicIntegralNorm.norm_le_one_of_isIntegral_padicInt <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PadicIntegralNorm.norm_le_one_of_isIntegral_padicInt ..)

theorem norm_le_one (c : Coef l) {x : Qbar l} (hx : x ∈ c.O) : ‖x‖ ≤ 1 := by
  haveI := c.fin
  have : Algebra.IsIntegral ℤ_[l] c.O := Algebra.IsIntegral.of_finite ℤ_[l] c.O
  exact norm_le_one_of_int x ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val)

theorem eps_mem (c : Coef l) (s : G ℚ Ω) : eps l s ∈ c.O := by
  have h : eps l s = algebraMap ℤ_[l] (Qbar l) ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) := by
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l)]; rfl
  rw [h]; exact c.O.algebraMap_mem _

theorem eps_cont : Continuous fun s : G ℚ Ω => eps l s :=
  (continuous_algebraMap ℚ_[l] (Qbar l)).comp
    (continuous_subtype_val.comp ((Units.continuous_val (M := ℤ_[l])).comp (continuous_cycZ ℚ Ω l)))

theorem eps_mul (r s : G ℚ Ω) : eps l (r * s) = eps l r * eps l s := by
  simp [eps, map_mul]

theorem mat_mul (W : R2 Ω l) (r s : G ℚ Ω) : mat W (r * s) = mat W r * mat W s := by
  simp [mat, map_mul]

theorem dt_val (W : R2 Ω l) (s : G ℚ Ω) : ((dt W s : (Qbar l)ˣ) : Qbar l) = (mat W s).det := by
  simp [dt, mat]

theorem dt_inv (W : R2 Ω l) (h2 : dt W ^ 2 = 1) (s : G ℚ Ω) : (dt W s)⁻¹ = dt W s := by
  have h := congrArg (fun f => f s) h2
  simp only [MonoidHom.pow_apply, MonoidHom.one_apply] at h
  exact inv_eq_of_mul_eq_one_right (by rw [← sq]; exact h)

theorem det_sq (W : R2 Ω l) (h2 : dt W ^ 2 = 1) (s : G ℚ Ω) : (mat W s).det * (mat W s).det = 1 := by
  have h := congrArg (fun f => f s) h2
  simp only [MonoidHom.pow_apply, MonoidHom.one_apply] at h
  rw [← dt_val, ← Units.val_mul, ← sq, h, Units.val_one]

theorem matD (W : R2 Ω l) (h2 : dt W ^ 2 = 1) (s : G ℚ Ω) :
    mat (dual1 W) s = (eps l s * (mat W s).det) • mat W s := by
  have := dt_inv W h2 s
  simp [dual1, Af.tw, mat, eps, Matrix.GeneralLinearGroup.scalar, this, ← dt_val]
  exact (Matrix.smul_eq_diagonal_mul _ _).symm

theorem sm_add {x y : Qbar l} {B : ℝ} (hx : ‖x‖ ≤ B) (hy : ‖y‖ ≤ B) : ‖x + y‖ ≤ B :=
  (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)

theorem sm_sub {x y : Qbar l} {B : ℝ} (hx : ‖x‖ ≤ B) (hy : ‖y‖ ≤ B) : ‖x - y‖ ≤ B := by
  rw [sub_eq_add_neg]; exact sm_add hx (by rwa [norm_neg])

theorem sm_mul {a x : Qbar l} {B : ℝ} (ha : ‖a‖ ≤ 1) (hx : ‖x‖ ≤ B) : ‖a * x‖ ≤ B := by
  rw [norm_mul]
  calc ‖a‖ * ‖x‖ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right ha (norm_nonneg _)
    _ = ‖x‖ := one_mul _
    _ ≤ B := hx

theorem om_sm {e v : Fin 2 → Qbar l} {B : ℝ} (he : ∀ i, ‖e i‖ ≤ B) (hv : ∀ i, ‖v i‖ ≤ 1) : ‖om e v‖ ≤ B := by
  unfold om
  exact sm_sub (by rw [mul_comm]; exact sm_mul (hv 1) (he 0)) (by rw [mul_comm]; exact sm_mul (hv 0) (he 1))

theorem mulVec_sm {M : Matrix (Fin 2) (Fin 2) (Qbar l)} {v : Fin 2 → Qbar l} {B : ℝ} (hM : ∀ i j, ‖M i j‖ ≤ 1)
    (hv : ∀ i, ‖v i‖ ≤ B) (i : Fin 2) : ‖(M *ᵥ v) i‖ ≤ B := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  exact sm_add (sm_mul (hM i 0) (hv 0)) (sm_mul (hM i 1) (hv 1))

theorem mulVec_mem (c : Coef l) {M : Matrix (Fin 2) (Fin 2) (Qbar l)} {v : Fin 2 → Qbar l} (hM : ∀ i j, M i j ∈ c.O)
    (hv : ∀ i, v i ∈ c.O) (i : Fin 2) : (M *ᵥ v) i ∈ c.O := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  exact add_mem (mul_mem (hM i 0) (hv 0)) (mul_mem (hM i 1) (hv 1))

theorem psi_sm (n : ℕ) (ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n))) (r s : G ℚ Ω) :
    ‖(((ψ (r * s)).toAdd.val : ℕ) : Qbar l) - ((ψ r).toAdd.val : ℕ) - ((ψ s).toAdd.val : ℕ)‖ ≤
      ‖((l : ℕ) : Qbar l) ^ n‖ := by
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have e1 : (ψ (r * s)).toAdd = (ψ r).toAdd + (ψ s).toAdd := by rw [map_mul, toAdd_mul]
  rw [e1, ZMod.val_add]
  set m := (ψ r).toAdd.val + (ψ s).toAdd.val
  have e2 : ((m % l ^ n : ℕ) : Qbar l) = (m : Qbar l) - ((l : ℕ) : Qbar l) ^ n * ((m / l ^ n : ℕ) : Qbar l) := by
    have := Nat.mod_add_div m (l ^ n)
    rw [eq_sub_iff_add_eq, ← Nat.cast_pow, ← Nat.cast_mul, ← Nat.cast_add, this]
  have e3 : ((m % l ^ n : ℕ) : Qbar l) - ((ψ r).toAdd.val : ℕ) - ((ψ s).toAdd.val : ℕ) =
      -(((l : ℕ) : Qbar l) ^ n * ((m / l ^ n : ℕ) : Qbar l)) := by
    rw [e2]; simp only [m, Nat.cast_add]; ring
  rw [e3, norm_neg, norm_mul]
  calc _ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ * 1 :=
        mul_le_mul_of_nonneg_left (IsUltrametricDist.norm_natCast_le_one _ _) (norm_nonneg _)
    _ = _ := mul_one _

theorem ident (Ar As : Matrix (Fin 2) (Fin 2) (Qbar l)) (er es Pp pr ps prs ut us ust cyz : Qbar l)
    (dr ds drs ys zs zt : Fin 2 → Qbar l) (hdet : Ar.det * Ar.det = 1)
    (hcyz : cyz = om ys (((es * As.det) • As) *ᵥ zt)) :
    er * (om ds (((es * As.det) • As) *ᵥ zt) - ps * Pp * es * ut) +
        (om dr (((er * Ar.det) • Ar) *ᵥ (zs + ((es * As.det) • As) *ᵥ zt)) - pr * Pp * er * ust) -
      ((om drs (((er * es * (Ar.det * As.det)) • (Ar * As)) *ᵥ zt) - prs * Pp * (er * es) * ut) +
        (om dr (((er * Ar.det) • Ar) *ᵥ zs) - pr * Pp * er * us)) =
    -om (drs - (dr + Ar *ᵥ ds + (pr * Pp) • (Ar *ᵥ ys))) (((er * es * (Ar.det * As.det)) • (Ar * As)) *ᵥ zt) +
      Pp * (er * es) * ut * (prs - pr - ps) - Pp * pr * er * (cyz - (es * ut - ust + us)) := by
  have key : er * (om ds (((es * As.det) • As) *ᵥ zt) - ps * Pp * es * ut) +
        (om dr (((er * Ar.det) • Ar) *ᵥ (zs + ((es * As.det) • As) *ᵥ zt)) - pr * Pp * er * ust) -
      ((om drs (((er * es * (Ar.det * As.det)) • (Ar * As)) *ᵥ zt) - prs * Pp * (er * es) * ut) +
        (om dr (((er * Ar.det) • Ar) *ᵥ zs) - pr * Pp * er * us)) -
    (-om (drs - (dr + Ar *ᵥ ds + (pr * Pp) • (Ar *ᵥ ys))) (((er * es * (Ar.det * As.det)) • (Ar * As)) *ᵥ zt) +
      Pp * (er * es) * ut * (prs - pr - ps) - Pp * pr * er * (cyz - (es * ut - ust + us))) =
    -(er * om ds (((es * As.det) • As) *ᵥ zt) + pr * Pp * er * cyz) * (Ar.det * Ar.det - 1) := by
    subst hcyz
    simp only [om, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.smul_apply, Matrix.mul_apply, Pi.add_apply,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.det_fin_two]
    ring
  linear_combination key + (-(er * om ds (((es * As.det) • As) *ᵥ zt) + pr * Pp * er * cyz)) * hdet

end GlobalTheory.Ord2.XiCoc


open GlobalTheory.Ord2.XiCoc in
theorem GlobalTheory.Ord2.cup_product_two_cocycle : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ) (S : Finset Pl) (W : R2 Ω l) (y z d : G ℚ Ω → Fin 2 → Qbar l) (u : G ℚ Ω → Qbar l) (P : Qbar l) (ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n))), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → dt W ^ 2 = 1 → (toGS Ω (S : Set Pl)).ker ≤ N0g W ⊓ ψ.ker → IsLocallyConstant ψ → P ∈ c.O → y ∈ Z1 (Loc.colRep W) → z ∈ Z1 (Loc.colRep (dual1 W)) → (∀ s i, y s i ∈ c.O) → (∀ s i, z s i ∈ c.O) → (∀ a ∈ (toGS Ω (S : Set Pl)).ker, y a = 0 ∧ z a = 0 ∧ Cv n (d a) 0) → Continuous u → (∀ s, u s ∈ c.O) → (∀ s, ∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cg n (u (s * a)) (u s)) → (∀ s t, Cg n (cup W y z s t) (eps l s * u t - u (s * t) + u s)) → Continuous d → (∀ s i, d s i ∈ c.O) → (∀ s t, Cv n (d (s * t)) (d s + mat W s *ᵥ d t + ((((ψ s).toAdd.val : ℕ) : Qbar l) * P) • (mat W s *ᵥ y t))) → Coc2 c n S (fun s t => cup W d z s t - (((ψ s).toAdd.val : ℕ) : Qbar l) * P * eps l s * u t) := by
  intro l _ Ω _ _ _ c n S W y z d u P ψ hW hWO hdt hker hψ hP hy hz hyO hzO hyz0 hu huO huS hcup hd hdO hdrec
  set B : ℝ := ‖((l : ℕ) : Qbar l) ^ n‖
  have nO : ∀ x ∈ c.O, ‖x‖ ≤ 1 := fun x hx => norm_le_one c hx
  have detO : ∀ s, (mat W s).det ∈ c.O := fun s => by
    rw [Matrix.det_fin_two]; exact sub_mem (mul_mem (hWO _ _ _) (hWO _ _ _)) (mul_mem (hWO _ _ _) (hWO _ _ _))
  have DO : ∀ s i j, mat (dual1 W) s i j ∈ c.O := fun s i j => by
    rw [matD W hdt, Matrix.smul_apply, smul_eq_mul]; exact mul_mem (mul_mem (eps_mem c s) (detO s)) (hWO _ _ _)
  have psiO : ∀ s, ((((ψ s).toAdd.val : ℕ) : Qbar l)) ∈ c.O := fun s => natCast_mem c.O _
  have zrec : ∀ s t, z (s * t) = z s + mat (dual1 W) s *ᵥ z t := fun s t => by
    have := hz.2 s t
    rw [this]; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    have hA : Continuous fun s => mat W s := Units.continuous_val.comp hW
    have hAij : ∀ i j, Continuous fun s => mat W s i j := fun i j =>
      (continuous_apply j).comp ((continuous_apply i).comp hA)
    have hdet : Continuous fun s => (mat W s).det := by
      simp_rw [Matrix.det_fin_two]
      exact ((hAij 0 0).mul (hAij 1 1)).sub ((hAij 0 1).mul (hAij 1 0))
    have hψc : Continuous fun s => (((ψ s).toAdd.val : ℕ) : Qbar l) :=
      (hψ.comp (fun x => ((x.toAdd.val : ℕ) : Qbar l))).continuous
    have hdi : ∀ i, Continuous fun s => d s i := fun i => (continuous_apply i).comp hd
    have hzi : ∀ i, Continuous fun s => z s i := fun i => (continuous_apply i).comp hz.1
    have he : Continuous fun s : G ℚ Ω => eps l s := eps_cont
    have hf : ∀ {f : G ℚ Ω → Qbar l}, Continuous f → Continuous fun p : G ℚ Ω × G ℚ Ω => f p.1 :=
      fun h => h.comp continuous_fst
    have hg : ∀ {f : G ℚ Ω → Qbar l}, Continuous f → Continuous fun p : G ℚ Ω × G ℚ Ω => f p.2 :=
      fun h => h.comp continuous_snd
    simp only [cup, om, matD W hdt, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul]
    have hD : ∀ i j, Continuous fun p : G ℚ Ω × G ℚ Ω => eps l p.1 * (mat W p.1).det * mat W p.1 i j :=
      fun i j => ((hf he).mul (hf hdet)).mul (hf (hAij i j))
    exact (((hf (hdi 0)).mul (((hD 1 0).mul (hg (hzi 0))).add ((hD 1 1).mul (hg (hzi 1))))).sub
      ((hf (hdi 1)).mul (((hD 0 0).mul (hg (hzi 0))).add ((hD 0 1).mul (hg (hzi 1)))))).sub
      ((((hf hψc).mul continuous_const).mul (hf he)).mul (hg hu))
  ·
    intro s t
    refine sub_mem ?_ (mul_mem (mul_mem (mul_mem (psiO s) hP) (eps_mem c s)) (huO t))
    unfold cup om
    exact sub_mem (mul_mem (hdO s 0) (mulVec_mem c (DO s) (hzO t) 1)) (mul_mem (hdO s 1) (mulVec_mem c (DO s) (hzO t) 0))
  ·
    intro r s t
    show ‖_ - _‖ ≤ B
    have key := ident (mat W r) (mat W s) (eps l r) (eps l s) P (((ψ r).toAdd.val : ℕ) : Qbar l)
      (((ψ s).toAdd.val : ℕ) : Qbar l) (((ψ (r * s)).toAdd.val : ℕ) : Qbar l) (u t) (u s) (u (s * t)) (cup W y z s t)
      (d r) (d s) (d (r * s)) (y s) (z s) (z t) (det_sq W hdt r) (by rw [cup, matD W hdt])
    simp only [cup, zrec, matD W hdt, mat_mul, eps_mul, Matrix.det_mul] at key ⊢
    rw [key]
    have hV : ∀ s' i j, ((eps l s' * (mat W s').det) • mat W s') i j ∈ c.O := fun s' i j => by
      rw [← matD W hdt]; exact DO s' i j
    have hVrs : ∀ i, ‖(((eps l r * eps l s * ((mat W r).det * (mat W s).det)) • (mat W r * mat W s)) *ᵥ z t) i‖ ≤ 1 := by
      intro i
      refine nO _ (mulVec_mem c (fun i j => ?_) (hzO t) i)
      have := hV (r * s) i j
      rwa [mat_mul, eps_mul, Matrix.det_mul] at this
    have hEu := hcup s t
    simp only [Cg, cup, matD W hdt] at hEu
    refine sm_sub (sm_add (by rw [norm_neg]; exact om_sm (fun i => hdrec r s i) hVrs)
      (sm_mul (nO _ (mul_mem (mul_mem hP (mul_mem (eps_mem c r) (eps_mem c s))) (huO t))) (psi_sm n ψ r s)))
      (sm_mul (nO _ (mul_mem (mul_mem hP (psiO r)) (eps_mem c r))) hEu)
  ·
    intro s t a ha b hb
    have ha' := hker ha
    simp only [N0g, Subgroup.mem_inf, MonoidHom.mem_ker] at ha'
    obtain ⟨⟨hca, hWa⟩, hψa⟩ := ha'
    have hAa : mat W a = 1 := by simp [mat, hWa]
    have hea : eps l a = 1 := by simp [eps, hca]
    have hAsa : mat W (s * a) = mat W s := by rw [mat_mul, hAa, mul_one]
    have hesa : eps l (s * a) = eps l s := by rw [eps_mul, hea, mul_one]
    have hψsa : ψ (s * a) = ψ s := by rw [map_mul, hψa, mul_one]
    have hztb : z (t * b) = z t := by rw [zrec, (hyz0 b hb).2.1]; simp
    show ‖_ - _‖ ≤ B
    simp only [cup, matD W hdt, hAsa, hesa, hψsa, hztb]
    have hE : ∀ i, ‖(d (s * a) - d s) i‖ ≤ B := by
      intro i
      have h1 := hdrec s a i
      simp only [Cg, (hyz0 a ha).1, Matrix.mulVec_zero, smul_zero, add_zero, Pi.add_apply, Pi.zero_apply] at h1
      have h2 : ‖(mat W s *ᵥ d a) i‖ ≤ B :=
        mulVec_sm (fun i j => nO _ (hWO s i j)) (fun j => by have h0 := (hyz0 a ha).2.2 j; simp only [Cg, Pi.zero_apply, sub_zero] at h0; exact h0) i
      have h3 : (d (s * a) - d s) i = (d (s * a) i - (d s i + (mat W s *ᵥ d a) i)) + (mat W s *ᵥ d a) i := by
        simp only [Pi.sub_apply]; ring
      rw [h3]; exact sm_add h1 h2
    have hVs : ∀ i, ‖(((eps l s * (mat W s).det) • mat W s) *ᵥ z t) i‖ ≤ 1 := by
      intro i
      refine nO _ (mulVec_mem c (fun i j => ?_) (hzO t) i)
      rw [← matD W hdt]; exact DO s i j
    have e : om (d (s * a)) (((eps l s * (mat W s).det) • mat W s) *ᵥ z t) -
          (((ψ s).toAdd.val : ℕ) : Qbar l) * P * eps l s * u (t * b) -
        (om (d s) (((eps l s * (mat W s).det) • mat W s) *ᵥ z t) -
          (((ψ s).toAdd.val : ℕ) : Qbar l) * P * eps l s * u t) =
        om (d (s * a) - d s) (((eps l s * (mat W s).det) • mat W s) *ᵥ z t) -
          ((((ψ s).toAdd.val : ℕ) : Qbar l) * P * eps l s) * (u (t * b) - u t) := by
      simp only [om, Pi.sub_apply]; ring
    rw [e]
    exact sm_sub (om_sm hE hVs) (sm_mul (nO _ (mul_mem (mul_mem (psiO s) hP) (eps_mem c s))) (huS t b hb))

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CocyclePairingLocallyConstantStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocycle_pairing_locally_constant : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ) (S : Finset Pl) (W : R2 Ω l) (y z d : G ℚ Ω → Fin 2 → Qbar l) (u : G ℚ Ω → Qbar l) (P : Qbar l) (ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n))), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → dt W ^ 2 = 1 → (toGS Ω (S : Set Pl)).ker ≤ N0g W ⊓ ψ.ker → IsLocallyConstant ψ → P ∈ c.O → y ∈ Z1 (Loc.colRep W) → z ∈ Z1 (Loc.colRep (dual1 W)) → (∀ s i, y s i ∈ c.O) → (∀ s i, z s i ∈ c.O) → (∀ a ∈ (toGS Ω (S : Set Pl)).ker, y a = 0 ∧ z a = 0 ∧ Cv n (d a) 0) → Continuous u → (∀ s, u s ∈ c.O) → (∀ s, ∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cg n (u (s * a)) (u s)) → (∀ s t, Cg n (cup W y z s t) (eps l s * u t - u (s * t) + u s)) → Continuous d → (∀ s i, d s i ∈ c.O) → (∀ s t, Cv n (d (s * t)) (d s + mat W s *ᵥ d t + ((((ψ s).toAdd.val : ℕ) : Qbar l) * P) • (mat W s *ᵥ y t))) → Coc2 c n S (fun s t => cup W d z s t - (((ψ s).toAdd.val : ℕ) : Qbar l) * P * eps l s * u t) := by
  first | exact @GlobalTheory.Ord2.cup_product_two_cocycle | exact GlobalTheory.Ord2.cup_product_two_cocycle | (intros; apply GlobalTheory.Ord2.cup_product_two_cocycle <;> assumption)
end
end

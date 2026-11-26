module

public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDefs

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowMulMemAdd
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

def MemE (c : Coef l) (x : Qbar l) : Prop := ∃ k : ℕ, (l : Qbar l) ^ k * x ∈ c.O

def VecE (c : Coef l) (y : Fin 2 → Qbar l) : Prop := ∃ k : ℕ, ∀ i, (l : Qbar l) ^ k * y i ∈ c.O

theorem natPow_mem (c : Coef l) (k : ℕ) : (l : Qbar l) ^ k ∈ c.O :=
  c.O.pow_mem (c.O.natCast_mem l) k

theorem pow_mul_mem_add (c : Coef l) {x : Qbar l} {k : ℕ} (h : (l : Qbar l) ^ k * x ∈ c.O) (j : ℕ) :
    (l : Qbar l) ^ (k + j) * x ∈ c.O := by
  rw [pow_add, mul_comm ((l : Qbar l) ^ k), mul_assoc]
  exact c.O.mul_mem (natPow_mem c j) h

theorem memE_add {c : Coef l} {x y : Qbar l} (hx : MemE c x) (hy : MemE c y) : MemE c (x + y) := by
  obtain ⟨k, hk⟩ := hx
  obtain ⟨j, hj⟩ := hy
  refine ⟨k + j, ?_⟩
  have h2 := pow_mul_mem_add c hj k
  rw [add_comm j k] at h2
  rw [mul_add]
  exact c.O.add_mem (pow_mul_mem_add c hk j) h2

theorem memE_neg {c : Coef l} {x : Qbar l} (hx : MemE c x) : MemE c (-x) := by
  obtain ⟨k, hk⟩ := hx
  exact ⟨k, by rw [mul_neg]; exact c.O.neg_mem hk⟩

theorem vecE_add {c : Coef l} {x y : Fin 2 → Qbar l} (hx : VecE c x) (hy : VecE c y) : VecE c (x + y) := by
  obtain ⟨k, hk⟩ := hx
  obtain ⟨j, hj⟩ := hy
  refine ⟨k + j, fun i => ?_⟩
  have h2 := pow_mul_mem_add c (hj i) k
  rw [add_comm j k] at h2
  rw [Pi.add_apply, mul_add]
  exact c.O.add_mem (pow_mul_mem_add c (hk i) j) h2

theorem vecE_neg {c : Coef l} {x : Fin 2 → Qbar l} (hx : VecE c x) : VecE c (-x) := by
  obtain ⟨k, hk⟩ := hx
  exact ⟨k, fun i => by rw [Pi.neg_apply, mul_neg]; exact c.O.neg_mem (hk i)⟩

def divSelCoc (c : Coef l) (W : R2 Ω l) (S : Finset Pl) (A : ValuationSubring Ω) :
    AddSubgroup (G ℚ Ω → Fin 2 → Qbar l) where
  carrier := {z | (∃ k : ℕ, ∀ s i, (l : Qbar l) ^ k * z s i ∈ c.O) ∧
    (∀ s t i, z (s * t) i - z s i - (mat W s *ᵥ z t) i ∈ c.O) ∧
    (∀ s, ∀ᶠ t in nhds s, ∀ i, z t i - z s i ∈ c.O) ∧
    (∀ a ∈ (toGS Ω (S : Set Pl)).ker, ∀ i, z a i ∈ c.O) ∧
    (∀ q ∈ S, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∀ B : ValuationSubring Ω, IsPlaceOver B q →
      ∃ y : Fin 2 → Qbar l, VecE c y ∧ ∀ s ∈ Ine (F := ℚ) B, ∀ i, z s i - (mat W s *ᵥ y - y) i ∈ c.O) ∧
    (∃ y : Qbar l, MemE c y ∧ ∀ s ∈ Dec (F := ℚ) A, z s 1 - (mat W s 1 1 * y - y) ∈ c.O)}
  add_mem' := by
    rintro z w ⟨⟨k, hk⟩, h2, h3, h4, h5, ⟨y, hy, h6⟩⟩ ⟨⟨k', hk'⟩, h2', h3', h4', h5', ⟨y', hy', h6'⟩⟩
    refine ⟨⟨k + k', fun s i => ?_⟩, fun s t i => ?_, fun s => ?_, fun a ha i => ?_, fun q hq hl B hB => ?_,
      ⟨y + y', memE_add hy hy', fun s hs => ?_⟩⟩
    · have h := pow_mul_mem_add c (hk' s i) k
      rw [add_comm k' k] at h
      rw [Pi.add_apply, Pi.add_apply, mul_add]
      exact c.O.add_mem (pow_mul_mem_add c (hk s i) k') h
    · have e : (z + w) (s * t) i - (z + w) s i - (mat W s *ᵥ (z + w) t) i =
          (z (s * t) i - z s i - (mat W s *ᵥ z t) i) + (w (s * t) i - w s i - (mat W s *ᵥ w t) i) := by
        simp only [Pi.add_apply, Matrix.mulVec_add]; ring
      rw [e]; exact c.O.add_mem (h2 s t i) (h2' s t i)
    · filter_upwards [h3 s, h3' s] with t ht ht' i
      have e : (z + w) t i - (z + w) s i = (z t i - z s i) + (w t i - w s i) := by
        simp only [Pi.add_apply]; ring
      rw [e]; exact c.O.add_mem (ht i) (ht' i)
    · rw [Pi.add_apply, Pi.add_apply]; exact c.O.add_mem (h4 a ha i) (h4' a ha i)
    · obtain ⟨u, hu, hu'⟩ := h5 q hq hl B hB
      obtain ⟨u', hv, hv'⟩ := h5' q hq hl B hB
      refine ⟨u + u', vecE_add hu hv, fun s hs i => ?_⟩
      have e : (z + w) s i - (mat W s *ᵥ (u + u') - (u + u')) i =
          (z s i - (mat W s *ᵥ u - u) i) + (w s i - (mat W s *ᵥ u' - u') i) := by
        simp only [Pi.add_apply, Pi.sub_apply, Matrix.mulVec_add]; ring
      rw [e]; exact c.O.add_mem (hu' s hs i) (hv' s hs i)
    · have e : (z + w) s 1 - (mat W s 1 1 * (y + y') - (y + y')) =
          (z s 1 - (mat W s 1 1 * y - y)) + (w s 1 - (mat W s 1 1 * y' - y')) := by
        simp only [Pi.add_apply]; ring
      rw [e]; exact c.O.add_mem (h6 s hs) (h6' s hs)
  zero_mem' := by
    refine ⟨⟨0, fun s i => by simp⟩, fun s t i => by simp, fun s => Filter.Eventually.of_forall fun t i => by simp,
      fun a _ i => by simp, fun q _ _ B _ => ⟨0, ⟨0, fun i => by simp⟩, fun s _ i => by simp⟩, ⟨0, ⟨0, by simp⟩, fun s _ => by simp⟩⟩
  neg_mem' := by
    rintro z ⟨⟨k, hk⟩, h2, h3, h4, h5, ⟨y, hy, h6⟩⟩
    refine ⟨⟨k, fun s i => ?_⟩, fun s t i => ?_, fun s => ?_, fun a ha i => ?_, fun q hq hl B hB => ?_,
      ⟨-y, memE_neg hy, fun s hs => ?_⟩⟩
    · rw [Pi.neg_apply, Pi.neg_apply, mul_neg]; exact c.O.neg_mem (hk s i)
    · have e : (-z) (s * t) i - (-z) s i - (mat W s *ᵥ (-z) t) i = -(z (s * t) i - z s i - (mat W s *ᵥ z t) i) := by
        simp only [Pi.neg_apply, Matrix.mulVec_neg]; ring
      rw [e]; exact c.O.neg_mem (h2 s t i)
    · filter_upwards [h3 s] with t ht i
      have e : (-z) t i - (-z) s i = -(z t i - z s i) := by simp only [Pi.neg_apply]; ring
      rw [e]; exact c.O.neg_mem (ht i)
    · rw [Pi.neg_apply, Pi.neg_apply]; exact c.O.neg_mem (h4 a ha i)
    · obtain ⟨u, hu, hu'⟩ := h5 q hq hl B hB
      refine ⟨-u, vecE_neg hu, fun s hs i => ?_⟩
      have e : (-z) s i - (mat W s *ᵥ (-u) - (-u)) i = -(z s i - (mat W s *ᵥ u - u) i) := by
        simp only [Pi.neg_apply, Pi.sub_apply, Matrix.mulVec_neg]; ring
      rw [e]; exact c.O.neg_mem (hu' s hs i)
    · have e : (-z) s 1 - (mat W s 1 1 * (-y) - (-y)) = -(z s 1 - (mat W s 1 1 * y - y)) := by
        simp only [Pi.neg_apply]; ring
      rw [e]; exact c.O.neg_mem (h6 s hs)

def divCob (c : Coef l) (W : R2 Ω l) : AddSubgroup (G ℚ Ω → Fin 2 → Qbar l) where
  carrier := {z | ∃ y : Fin 2 → Qbar l, VecE c y ∧ ∀ s i, z s i - (mat W s *ᵥ y - y) i ∈ c.O}
  add_mem' := by
    rintro z w ⟨u, hu, hu'⟩ ⟨u', hv, hv'⟩
    refine ⟨u + u', vecE_add hu hv, fun s i => ?_⟩
    have e : (z + w) s i - (mat W s *ᵥ (u + u') - (u + u')) i =
        (z s i - (mat W s *ᵥ u - u) i) + (w s i - (mat W s *ᵥ u' - u') i) := by
      simp only [Pi.add_apply, Pi.sub_apply, Matrix.mulVec_add]; ring
    rw [e]; exact c.O.add_mem (hu' s i) (hv' s i)
  zero_mem' := ⟨0, ⟨0, fun i => by simp⟩, fun s i => by simp⟩
  neg_mem' := by
    rintro z ⟨u, hu, hu'⟩
    refine ⟨-u, vecE_neg hu, fun s i => ?_⟩
    have e : (-z) s i - (mat W s *ᵥ (-u) - (-u)) i = -(z s i - (mat W s *ᵥ u - u) i) := by
      simp only [Pi.neg_apply, Pi.sub_apply, Matrix.mulVec_neg]; ring
    rw [e]; exact c.O.neg_mem (hu' s i)

abbrev DivSel (c : Coef l) (W : R2 Ω l) (S : Finset Pl) (A : ValuationSubring Ω) : Type :=
  ↥(divSelCoc c W S A) ⧸ (divCob c W).addSubgroupOf (divSelCoc c W S A)

theorem divSel_torsion (c : Coef l) (W : R2 Ω l) (S : Finset Pl) (A : ValuationSubring Ω) :
    ∀ x : DivSel c W S A, ∃ n : ℕ, l ^ n • x = 0 := by
  intro x
  induction x using QuotientAddGroup.induction_on with
  | H z =>
    obtain ⟨k, hk⟩ := z.2.1
    refine ⟨k, ?_⟩
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    refine ⟨0, ⟨0, fun i => by simp⟩, fun s i => ?_⟩
    simp only [AddSubgroup.coe_nsmul, Pi.smul_apply, nsmul_eq_mul, Matrix.mulVec_zero, sub_zero, Pi.zero_apply]
    push_cast
    exact hk s i

end GlobalTheory.Ord2

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SelNZero
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.GwCount

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

def SelN (c : Coef l) (n : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (V : R2 Ω l)
    (z : G ℚ Ω → Fin 2 → Qbar l) : Prop :=
  Coc1 c n V ⊤ z ∧ (∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cv n (z a) 0) ∧
    (∀ q ∈ S, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∃ B : ValuationSubring Ω, IsPlaceOver B q ∧
      Cob1 c n V (Ine (F := ℚ) B) z) ∧
    (∃ x ∈ c.O, ∀ s ∈ Dec (F := ℚ) A, Cg n (z s 1) (mat V s 1 1 * x - x))

end GlobalTheory.Ord2.GwCount
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EulerSystemTameClassScaleEnlargeCoefficients
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EulerSystemTameClassScaleEnlargeCoefficients
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem tame_scale : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (c c' : Coef l) (y : G ℚ Ω → Fin 2 → Qbar l) (n : ℕ) (w : Pl) (ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n))) (a : Qbar l), c.O ≤ c'.O → a ∈ c'.O → Tame c W y n w ψ → Tame c' W (fun s => a • y s) n w ψ := by
  intro l _ Ω _ _ _ W c c' y n w ψ a hle ha hT
  obtain ⟨Y, P, u, b, hY, hYO, hP, hu, hb, hco, hsum, hfr, htame⟩ := hT
  refine ⟨fun s x => a • Y s x, P, u, a • b, ?_, ?_, hle hP, hu, ?_, ?_, ?_, hfr, ?_⟩
  · exact hY.const_smul a
  · intro s x i
    simpa using c'.O.mul_mem ha (hle (hYO s x i))
  · intro i
    simpa using c'.O.mul_mem ha (hle (hb i))
  · intro s t x
    simp only [hco s t x, smul_add, Matrix.mulVec_smul]
  · intro s
    rw [finsum_eq_sum_of_fintype] at *
    rw [← Finset.smul_sum, ← finsum_eq_sum_of_fintype, hsum s]
    simp only [smul_add, smul_sub, Matrix.mulVec_smul, smul_comm a P]
  · intro q hq hl
    obtain ⟨B, hB, t, htO, ht⟩ := htame q hq hl
    refine ⟨B, hB, fun x => a • t x, ?_, ?_⟩
    · intro x i
      simpa using c'.O.mul_mem ha (hle (htO x i))
    · intro s hs x
      simp only [ht s hs x, smul_sub, Matrix.mulVec_smul]

end GlobalTheory.Ord2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EulerSystemTameClassScaleEnlargeCoefficientsStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eulerSystemTameClass_scale_enlarge_coefficients : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (c c' : Coef l) (y : G ℚ Ω → Fin 2 → Qbar l) (n : ℕ) (w : Pl) (ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n))) (a : Qbar l), c.O ≤ c'.O → a ∈ c'.O → Tame c W y n w ψ → Tame c' W (fun s => a • y s) n w ψ := by
  first | exact @GlobalTheory.Ord2.tame_scale | exact GlobalTheory.Ord2.tame_scale | (intros; apply GlobalTheory.Ord2.tame_scale <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormLePowIffDvd
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormLePowIffDvd
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem GlobalTheory.Coef.norm_le_norm_pow_iff_dvd :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (n : ℕ) (x : c.O),
      ‖((x : c.O) : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ ↔ ((l : ℕ) : c.O) ^ n ∣ x := by
  intro l _ c n x
  have hlnorm : ‖((l : ℕ) : Qbar l)‖ = (l : ℝ)⁻¹ := by
    have : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [this, norm_algebraMap', Padic.norm_p]
  obtain ⟨-, -, -, -, -, he0, -, he, -⟩ := UpperTheory.V.Base.dvrFacts l c.O
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hl0 : ((l : ℕ) : c.O) ≠ 0 := by
    intro h
    have h' : (((l : ℕ) : c.O) : PadicAlgCl l) = 0 := by rw [h]; rfl
    have : ((l : ℕ) : PadicAlgCl l) = 0 := by simpa using h'
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) this
  have key := UpperTheory.V.Base.normO l c.O x hx
  set e := (UpperTheory.V.Base.eO l c.O).toNat with he_def
  have hEtop : UpperTheory.V.Base.eO l c.O ≠ ⊤ := by
    rw [he]; exact fun h => hl0 (IsDiscreteValuationRing.addVal_eq_top_iff.1 h)
  have hEcast : UpperTheory.V.Base.eO l c.O = (e : ℕ∞) := (ENat.coe_toNat hEtop).symm
  have hepos : e ≠ 0 := by
    intro h0; apply he0; rw [hEcast, h0]; rfl
  have hxtop : IsDiscreteValuationRing.addVal c.O x ≠ ⊤ :=
    fun h => hx (IsDiscreteValuationRing.addVal_eq_top_iff.1 h)
  set v := (IsDiscreteValuationRing.addVal c.O x).toNat with hv_def
  have hvcast : IsDiscreteValuationRing.addVal c.O x = (v : ℕ∞) := (ENat.coe_toNat hxtop).symm
  have hlpos : (0 : ℝ) < (l : ℝ)⁻¹ := inv_pos.2 (Nat.cast_pos.2 (Fact.out : l.Prime).pos)
  have hllt : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (Nat.one_lt_cast.2 (Fact.out : l.Prime).one_lt)
  rw [norm_pow, hlnorm, ← IsDiscreteValuationRing.addVal_le_iff_dvd, IsDiscreteValuationRing.addVal_pow,
    ← he, hEcast, hvcast, ← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) hepos, key, ← pow_mul,
    pow_le_pow_iff_right_of_lt_one₀ hlpos hllt]
  rw [nsmul_eq_mul, ← Nat.cast_mul, Nat.cast_le]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormLePowIffDvdStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_le_pow_iff_dvd : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (n : ℕ) (x : c.O), ‖((x : c.O) : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ ↔ ((l : ℕ) : c.O) ^ n ∣ x := by
  first | exact @GlobalTheory.Coef.norm_le_norm_pow_iff_dvd | exact GlobalTheory.Coef.norm_le_norm_pow_iff_dvd | (intros; apply GlobalTheory.Coef.norm_le_norm_pow_iff_dvd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharpolySmulMap
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 CongruenceSubgroup
open scoped Matrix MatrixGroups ModularForm

noncomputable section

open Polynomial

namespace GlobalTheory.TwAtt

theorem normV_eq (v : HeightOneSpectrum (𝓞 ℚ)) : normV v = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl

theorem mem_iff (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) : (n : 𝓞 ℚ) ∈ v.asIdeal ↔ normV v ∣ n := by
  rw [normV_eq]
  refine ⟨fun h => ?_, ?_⟩
  · have h1 := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 h)
    rwa [Ideal.absNorm_span_natCast, RingOfIntegers.rank, Module.finrank_self, pow_one] at h1
  · rintro ⟨c, rfl⟩
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)

theorem normV_prime (v : HeightOneSpectrum (𝓞 ℚ)) : (normV v).Prime := by
  have h1 : 1 < normV v := by
    rw [normV_eq]
    exact NumberField.HeightOneSpectrum.one_lt_absNorm v
  refine Nat.prime_def.2 ⟨h1, fun m hm => ?_⟩
  obtain ⟨c, hc⟩ := hm
  have h2 := (mem_iff v _).2 dvd_rfl
  rw [hc, Nat.cast_mul] at h2
  rcases v.isPrime.mem_or_mem h2 with h | h
  · exact Or.inr (Nat.dvd_antisymm ⟨c, hc⟩ ((mem_iff v _).1 h))
  · have h3 := Nat.dvd_antisymm (Dvd.intro_left m hc.symm) ((mem_iff v _).1 h)
    rw [h3] at hc
    exact Or.inl (Nat.eq_of_mul_eq_mul_right (by omega) (hc.symm.trans (one_mul _).symm))

theorem eq_of_normV {v v' : HeightOneSpectrum (𝓞 ℚ)} (h : ((normV v : ℕ) : 𝓞 ℚ) ∈ v'.asIdeal) : v' = v := by
  have hle : v.asIdeal ≤ v'.asIdeal := by
    intro x hx
    obtain ⟨m, rfl⟩ : ∃ m : ℤ, (m : 𝓞 ℚ) = x := ⟨Rat.ringOfIntegersEquiv x, by
      apply Rat.ringOfIntegersEquiv.injective; simp⟩
    have key : ∀ I : Ideal (𝓞 ℚ), (m : 𝓞 ℚ) ∈ I ↔ ((m.natAbs : ℕ) : 𝓞 ℚ) ∈ I := fun I => by
      rcases Int.natAbs_eq m with e | e
      · conv_lhs => rw [e]
        rw [Int.cast_natCast]
      · conv_lhs => rw [e]
        rw [Int.cast_neg, Int.cast_natCast, neg_mem_iff]
    rw [key, mem_iff] at hx ⊢
    exact ((mem_iff _ _).1 h).trans hx
  exact (HeightOneSpectrum.ext (v.isMaximal.eq_of_le v'.isPrime.ne_top hle)).symm

theorem normV_injective : Function.Injective (normV : HeightOneSpectrum (𝓞 ℚ) → ℕ) := by
  intro v v' h
  refine (eq_of_normV (v := v') (v' := v) ?_)
  rw [← h]
  exact (mem_iff v _).2 dvd_rfl

end GlobalTheory.TwAtt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalConditionsIndependentOfPlaceOver
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalConditionsIndependentOfPlaceOver
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

open Pointwise

namespace GlobalTheory.Ord2

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem cocycle_mulVec {W : R2 Ω l} {z : G ℚ Ω → Fin 2 → Qbar l} (hz : z ∈ Z1 (Loc.colRep W)) (g h : G ℚ Ω) :
    z (g * h) = z g + mat W g *ᵥ z h :=
  hz.2 g h

theorem mat_mul' (W : R2 Ω l) (g h : G ℚ Ω) : mat W (g * h) = mat W g * mat W h := by
  simp [mat, map_mul, Units.val_mul]

theorem mat_one' (W : R2 Ω l) : mat W 1 = 1 := by
  simp [mat]

theorem cob_conj {W : R2 Ω l} {z : G ℚ Ω → Fin 2 → Qbar l} (hz : z ∈ Z1 (Loc.colRep W)) (γ t : G ℚ Ω)
    (x : Fin 2 → Qbar l) (ht : z t = mat W t *ᵥ x - x) :
    z (γ * t * γ⁻¹) = mat W (γ * t * γ⁻¹) *ᵥ (mat W γ *ᵥ x - z γ) - (mat W γ *ᵥ x - z γ) := by
  have h0 : z 1 = 0 := by
    have := cocycle_mulVec hz 1 1
    rw [mul_one, mat_one', Matrix.one_mulVec] at this
    simpa using this
  have h2 : z γ⁻¹ = -(mat W γ⁻¹ *ᵥ z γ) := by
    have := cocycle_mulVec hz γ⁻¹ γ
    rw [inv_mul_cancel, h0] at this
    exact eq_neg_of_add_eq_zero_left this.symm
  have hinv : mat W γ⁻¹ * mat W γ = 1 := by rw [← mat_mul', inv_mul_cancel, mat_one']
  rw [cocycle_mulVec hz, cocycle_mulVec hz, ht, h2, mat_mul', mat_mul', mat_mul']
  simp only [Matrix.mulVec_sub, Matrix.mulVec_neg, Matrix.mulVec_mulVec, Matrix.mul_assoc, hinv, Matrix.mul_one]
  abel

theorem cob_of_conj_le {W : R2 Ω l} {z : G ℚ Ω → Fin 2 → Qbar l} (hz : z ∈ Z1 (Loc.colRep W)) (γ : G ℚ Ω)
    (H H' : Subgroup (G ℚ Ω)) (hH : ∀ s ∈ H', γ⁻¹ * s * γ ∈ H)
    (h : ∃ x : Fin 2 → Qbar l, ∀ s ∈ H, z s = mat W s *ᵥ x - x) :
    ∃ x : Fin 2 → Qbar l, ∀ s ∈ H', z s = mat W s *ᵥ x - x := by
  obtain ⟨x, hx⟩ := h
  refine ⟨mat W γ *ᵥ x - z γ, fun s hs => ?_⟩
  have e : s = γ * (γ⁻¹ * s * γ) * γ⁻¹ := by group
  rw [e]
  exact cob_conj hz γ _ x (hx _ (hH s hs))

theorem place_indep : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l)
    (z : G ℚ Ω → Fin 2 → Qbar l), z ∈ Z1 (Loc.colRep W) → ∀ (w : Pl) (B B' : ValuationSubring Ω),
    IsPlaceOver B w → IsPlaceOver B' w →
    ((∃ x : Fin 2 → Qbar l, ∀ s ∈ Ine (F := ℚ) B, z s = mat W s *ᵥ x - x) →
      ∃ x : Fin 2 → Qbar l, ∀ s ∈ Ine (F := ℚ) B', z s = mat W s *ᵥ x - x) ∧ (Triv W B z → Triv W B' z) := by
  intro l _ Ω _ _ _ W z hz w B B' hB hB'
  obtain ⟨γ, hγ⟩ := exists_smul_eq_of_isPlaceOver hB hB'
  refine ⟨cob_of_conj_le hz γ _ _ (fun s hs => ?_), cob_of_conj_le hz γ _ _ (fun s hs => ?_)⟩
  · have := conj_mem_Ine_smul (F := ℚ) (A := B') (γ := γ⁻¹) (σ := s) hs
    rw [inv_inv, ← hγ, inv_smul_smul] at this
    exact this
  · have hs' : s • B' = B' := hs
    show (γ⁻¹ * s * γ) • B = B
    rw [mul_smul, mul_smul, hγ, hs', ← hγ, inv_smul_smul]

end GlobalTheory.Ord2
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalConditionsIndependentOfPlaceOverStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localConditions_independent_of_place_over : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (z : G ℚ Ω → Fin 2 → Qbar l), z ∈ Z1 (Loc.colRep W) → ∀ (w : Pl) (B B' : ValuationSubring Ω), IsPlaceOver B w → IsPlaceOver B' w → ((∃ x : Fin 2 → Qbar l, ∀ s ∈ Ine (F := ℚ) B, z s = mat W s *ᵥ x - x) → ∃ x : Fin 2 → Qbar l, ∀ s ∈ Ine (F := ℚ) B', z s = mat W s *ᵥ x - x) ∧ (Triv W B z → Triv W B' z) := by
  first | exact @GlobalTheory.Ord2.place_indep | exact GlobalTheory.Ord2.place_indep | (intros; apply GlobalTheory.Ord2.place_indep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCommutatorDetNonzero
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsComm
noncomputable section

open scoped Matrix

namespace GlobalTheory.CommutingExistence

variable {k : Type} [Field k]

theorem trace_two (A : Matrix (Fin 2) (Fin 2) k) (h1 : A.det = 1) (h2 : (A - 1).det = 0) :
    A 0 0 + A 1 1 = 2 := by
  rw [Matrix.det_fin_two] at h1 h2
  simp at h2
  linear_combination h1 - h2

theorem mul_nil (A B : Matrix (Fin 2) (Fin 2) k) (hA : A.det = 1) (hB : B.det = 1)
    (hA' : (A - 1).det = 0) (hB' : (B - 1).det = 0) (hAB : (A * B - 1).det = 0) :
    (A - 1) * (B - 1) = 0 := by
  have tA := trace_two A hA hA'
  have tB := trace_two B hB hB'
  have tAB := trace_two (A * B) (by rw [Matrix.det_mul, hA, hB, mul_one]) hAB
  rw [Matrix.det_fin_two] at hA hB
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at tAB
  obtain ⟨x, hx⟩ : ∃ x, A 0 0 = 1 + x := ⟨A 0 0 - 1, by ring⟩
  obtain ⟨a, ha⟩ : ∃ a, B 0 0 = 1 + a := ⟨B 0 0 - 1, by ring⟩
  have hx' : A 1 1 = 1 - x := by linear_combination tA - hx
  have ha' : B 1 1 = 1 - a := by linear_combination tB - ha
  rw [hx, hx'] at hA tAB
  rw [ha, ha'] at hB tAB
  have e1 : x ^ 2 + A 0 1 * A 1 0 = 0 := by linear_combination -hA
  have e2 : a ^ 2 + B 0 1 * B 1 0 = 0 := by linear_combination -hB
  have e3 : 2 * x * a + A 0 1 * B 1 0 + A 1 0 * B 0 1 = 0 := by linear_combination tAB
  have f00 : x * a + A 0 1 * B 1 0 = 0 := by
    apply pow_eq_zero_iff (two_ne_zero) |>.mp
    linear_combination a ^ 2 * e1 - A 0 1 * A 1 0 * e2 + A 0 1 * B 1 0 * e3
  have f01 : x * B 0 1 - A 0 1 * a = 0 := by
    apply pow_eq_zero_iff (two_ne_zero) |>.mp
    linear_combination B 0 1 ^ 2 * e1 + A 0 1 ^ 2 * e2 - A 0 1 * B 0 1 * e3
  have f10 : A 1 0 * a - x * B 1 0 = 0 := by
    apply pow_eq_zero_iff (two_ne_zero) |>.mp
    linear_combination B 1 0 ^ 2 * e1 + A 1 0 ^ 2 * e2 - A 1 0 * B 1 0 * e3
  have f11 : A 1 0 * B 0 1 + x * a = 0 := by
    linear_combination e3 - f00
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hx, hx', ha, ha']
  · linear_combination f00
  · linear_combination f01
  · linear_combination f10
  · linear_combination f11

theorem exists_comm [IsAlgClosed k] {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin 2) k) (H : Subgroup Γ)
    (hdet : ∀ s ∈ H, (ρ s : Matrix (Fin 2) (Fin 2) k).det = 1)
    (hirr : ∀ V : Submodule k (Fin 2 → k),
      (∀ g ∈ H, ∀ v ∈ V, (ρ g : Matrix (Fin 2) (Fin 2) k) *ᵥ v ∈ V) → V = ⊥ ∨ V = ⊤) :
    ∃ φ ∈ ⁅H, H⁆, ((ρ φ : Matrix (Fin 2) (Fin 2) k) - 1).det ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hle : ⁅H, H⁆ ≤ H := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)
  have hconj : ∀ g ∈ H, ∀ φ ∈ ⁅H, H⁆, g⁻¹ * φ * g ∈ ⁅H, H⁆ := by
    intro g hg φ hφ
    have := Subgroup.commutator_mem_commutator (H.inv_mem hg) (hle hφ)
    have h2 := Subgroup.mul_mem _ this hφ
    convert h2 using 1
    rw [commutatorElement_def]
    group
  let F : Submodule k (Fin 2 → k) :=
    { carrier := {v | ∀ φ ∈ ⁅H, H⁆, (ρ φ : Matrix (Fin 2) (Fin 2) k) *ᵥ v = v}
      add_mem' := by
        intro a b ha hb φ hφ
        rw [Matrix.mulVec_add, ha φ hφ, hb φ hφ]
      zero_mem' := by
        intro φ _
        simp
      smul_mem' := by
        intro c a ha φ hφ
        rw [Matrix.mulVec_smul, ha φ hφ] }
  have hF : ∀ v, v ∈ F ↔ ∀ φ ∈ ⁅H, H⁆, (ρ φ : Matrix (Fin 2) (Fin 2) k) *ᵥ v = v := fun _ => Iff.rfl
  have hFinv : ∀ g ∈ H, ∀ v ∈ F, (ρ g : Matrix (Fin 2) (Fin 2) k) *ᵥ v ∈ F := by
    intro g hg v hv
    rw [hF] at hv ⊢
    intro φ hφ
    have h1 := hv _ (hconj g hg φ hφ)
    have h2 : φ * g = g * (g⁻¹ * φ * g) := by group
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, h2, map_mul, Units.val_mul,
      ← Matrix.mulVec_mulVec, h1]
  have hFtop : ∀ v, v ∈ F := by
    rcases hirr F hFinv with h | h
    · intro w
      rw [hF]
      intro ψ hψ
      have : ((ρ ψ : Matrix (Fin 2) (Fin 2) k) - 1) *ᵥ w ∈ F := by
        rw [hF]
        intro φ hφ
        have h0 := mul_nil (ρ φ : Matrix (Fin 2) (Fin 2) k) (ρ ψ : Matrix (Fin 2) (Fin 2) k)
          (hdet _ (hle hφ)) (hdet _ (hle hψ)) (hcon _ hφ) (hcon _ hψ)
          (by rw [← Units.val_mul, ← map_mul]; exact hcon _ (Subgroup.mul_mem _ hφ hψ))
        rw [Matrix.mulVec_mulVec]
        congr 1
        rw [sub_mul, one_mul, sub_eq_zero] at h0
        exact h0
      rw [h, Submodule.mem_bot, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at this
      exact this
    · intro w
      rw [h]
      trivial
  have hcomm : ∀ g ∈ H, ∀ g' ∈ H, ∀ v, (ρ g : Matrix (Fin 2) (Fin 2) k) *ᵥ ((ρ g' : Matrix (Fin 2) (Fin 2) k) *ᵥ v) =
      (ρ g' : Matrix (Fin 2) (Fin 2) k) *ᵥ ((ρ g : Matrix (Fin 2) (Fin 2) k) *ᵥ v) := by
    intro g hg g' hg' v
    have h1 := (hF _).1 (hFtop ((ρ g' : Matrix (Fin 2) (Fin 2) k) *ᵥ ((ρ g : Matrix (Fin 2) (Fin 2) k) *ᵥ v))) _
      (Subgroup.commutator_mem_commutator hg hg')
    rw [← h1]
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul]
    congr 3
    rw [commutatorElement_def]
    group
  have hscal : ∀ g ∈ H, ∃ c : k, ∀ v, (ρ g : Matrix (Fin 2) (Fin 2) k) *ᵥ v = c • v := by
    intro g hg
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (Matrix.toLin' (ρ g : Matrix (Fin 2) (Fin 2) k))
    refine ⟨c, ?_⟩
    rcases hirr (Module.End.eigenspace (Matrix.toLin' (ρ g : Matrix (Fin 2) (Fin 2) k)) c) (by
      intro g' hg' v hv
      rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hv ⊢
      rw [hcomm g hg g' hg', hv, Matrix.mulVec_smul]) with h | h
    · exact absurd h (Module.End.hasEigenvalue_iff.1 hc)
    · intro v
      have : v ∈ Module.End.eigenspace (Matrix.toLin' (ρ g : Matrix (Fin 2) (Fin 2) k)) c := by
        rw [h]; trivial
      rwa [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at this
  rcases hirr (Submodule.span k {(![1, 0] : Fin 2 → k)}) (by
    intro g hg v hv
    obtain ⟨c, hc⟩ := hscal g hg
    rw [hc]
    exact Submodule.smul_mem _ _ hv) with h | h
  · rw [Submodule.span_singleton_eq_bot] at h
    have := congrFun h 0
    simp at this
  · have : (![0, 1] : Fin 2 → k) ∈ Submodule.span k {(![1, 0] : Fin 2 → k)} := by
      rw [h]; trivial
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 this
    have := congrFun hc 1
    simp at this

theorem main (l : ℕ) [Fact (Nat.Prime l)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ)
    (S : Finset GlobalTheory.Ord2.Pl) (A : ValuationSubring Ω) (W : GlobalTheory.Ord2.R2 Ω l) (h : GlobalTheory.Ord2.Nf e S A W) :
    ∃ φ ∈ ⁅GlobalTheory.Ord2.H0g W, GlobalTheory.Ord2.H0g W⁆,
      Matrix.det (GlobalTheory.Ord2.mat W φ - (1 : Matrix (Fin 2) (Fin 2) (Formalism.ConjugateSelfDual.Qbar l))) ≠ (0 : Formalism.ConjugateSelfDual.Qbar l) := by
  refine exists_comm W (GlobalTheory.Ord2.H0g W) ?_ ?_
  · intro s hs
    have h1 : GlobalTheory.Ord2.dt W s = 1 := hs.2
    have h2 := congrArg Units.val h1
    exact h2
  · intro V hV
    exact h.irr.2.2 V le_top (fun g v hv => hV g g.2 v hv)

end GlobalTheory.CommutingExistence

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCommutatorDetNonzero
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem commutator_H0_has_no_eigenvalue_one : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W →
    ∃ φ ∈ ⁅H0g W, H0g W⁆, (mat W φ - 1).det ≠ 0 := by
  first
  | exact @_root_.GlobalTheory.CommutingExistence.main
  | exact _root_.GlobalTheory.CommutingExistence.main
  | (apply _root_.GlobalTheory.CommutingExistence.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.CommutingExistence.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CommutingExistence.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CommutingExistence.main ..)

end GlobalTheory.Ord2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCommutatorDetNonzeroStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_commutator_det_nonzero : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∃ φ ∈ ⁅H0g W, H0g W⁆, (mat W φ - 1).det ≠ 0 := by
  first | exact @GlobalTheory.Ord2.commutator_H0_has_no_eigenvalue_one | exact GlobalTheory.Ord2.commutator_H0_has_no_eigenvalue_one | (intros; apply GlobalTheory.Ord2.commutator_H0_has_no_eigenvalue_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GreenbergOrdinaryOfVanishingOnCycloKernel
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GreenbergOrdinaryOfVanishingOnCycloKernel
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.GrOfKill

theorem exists_unit_one_add (l : ℕ) [Fact l.Prime] : ∃ u : ℤ_[l]ˣ, (u : ℤ_[l]) = ((1 + l : ℕ) : ℤ_[l]) := by
  have hu : IsUnit (((1 + l : ℕ) : ℤ_[l])) := by
    push_cast
    rw [← sub_neg_eq_add]
    exact IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ fun h =>
      PadicInt.irreducible_p.not_isUnit ((IsUnit.neg_iff _).1 h)
  exact ⟨hu.unit, rfl⟩

theorem gr_of_vanish_on_trivial : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ y ∈ Z1 (Loc.colRep W), (∀ g ∈ N0g W, y g = 0) → Gr W A y := by
  intro l _ Ω _ _ _ e S A W hW y hy hN
  set D := Dec (F := ℚ) A with hDdef
  have hup : ∀ s ∈ D, mat W s 1 0 = 0 := hW.upper
  have hmul : ∀ s t, mat W (s * t) = mat W s * mat W t := fun s t => by simp [mat]
  have hone : mat W 1 = 1 := by simp [mat]
  have h00 : ∀ s t, t ∈ D → mat W (s * t) 0 0 = mat W s 0 0 * mat W t 0 0 := by
    intro s t ht; rw [hmul, Matrix.mul_apply, Fin.sum_univ_two, hup t ht]; ring
  have h11 : ∀ s t, s ∈ D → mat W (s * t) 1 1 = mat W s 1 1 * mat W t 1 1 := by
    intro s t hs; rw [hmul, Matrix.mul_apply, Fin.sum_univ_two, hup s hs]; ring
  have h01 : ∀ s t, t ∈ D → mat W (s * t) 0 1 = mat W s 0 0 * mat W t 0 1 + mat W s 0 1 * mat W t 1 1 := by
    intro s t ht; rw [hmul, Matrix.mul_apply, Fin.sum_univ_two]
  have hcoc : ∀ s t, y (s * t) = y s + mat W s *ᵥ y t := fun s t => by
    have := hy.2 s t
    rw [this]; rfl
  have hy1 : y 1 = 0 := by
    have := hcoc 1 1
    simpa [hone] using this
  have hb : ∀ s t, s ∈ D → y (s * t) 1 = y s 1 + mat W s 1 1 * y t 1 := by
    intro s t hs; rw [hcoc]; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hup s hs]

  let P : G ℚ Ω → Prop := fun u => u ∈ D ∧ mat W u 0 0 = 1 ∧ mat W u 1 1 = 1 ∧ cycBar ℚ Ω l u = 1

  have hfac : ∀ u v, P u → P v → mat W u 0 1 = mat W v 0 1 → y u = y v := by
    rintro u v ⟨huD, hu0, hu1, huc⟩ ⟨hvD, hv0, hv1, hvc⟩ h
    have hm : mat W u = mat W v := by
      ext i j
      fin_cases i <;> fin_cases j
      · simp [hu0, hv0]
      · exact h
      · simp [hup u huD, hup v hvD]
      · simp [hu1, hv1]
    have hW' : W u = W v := Units.ext hm
    have hn : u⁻¹ * v ∈ N0g W := by
      refine ⟨?_, ?_⟩
      · simp [MonoidHom.mem_ker, map_mul, map_inv, huc, hvc]
      · simp [MonoidHom.mem_ker, map_mul, map_inv, hW']
    have e1 : v = u * (u⁻¹ * v) := by group
    rw [e1, hcoc, hN _ hn, Matrix.mulVec_zero, add_zero]
  have hPmul : ∀ u v, P u → P v → P (u * v) ∧ mat W (u * v) 0 1 = mat W u 0 1 + mat W v 0 1 ∧
      y (u * v) 1 = y u 1 + y v 1 := by
    rintro u v ⟨huD, hu0, hu1, huc⟩ ⟨hvD, hv0, hv1, hvc⟩
    refine ⟨⟨D.mul_mem huD hvD, ?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [h00 u v hvD, hu0, hv0, one_mul]
    · rw [h11 u v huD, hu1, hv1, one_mul]
    · rw [map_mul, huc, hvc, one_mul]
    · rw [h01 u v hvD, hu0, hv1]; ring
    · rw [hb u v huD, hu1, one_mul]
  have hPpow : ∀ u, P u → ∀ n : ℕ, P (u ^ n) ∧ mat W (u ^ n) 0 1 = n * mat W u 0 1 ∧
      y (u ^ n) 1 = n * y u 1 := by
    intro u hu n
    induction n with
    | zero =>
      refine ⟨⟨D.one_mem, by simp [hone], by simp [hone], by simp⟩, by simp [hone], by simp [hy1]⟩
    | succ n ih =>
      obtain ⟨h1, h2, h3⟩ := hPmul _ _ ih.1 hu
      rw [pow_succ]
      refine ⟨h1, ?_, ?_⟩
      · rw [h2, ih.2.1]; push_cast; ring
      · rw [h3, ih.2.2]; push_cast; ring

  have hv : A.valuation (l : Ω) < 1 := by
    obtain ⟨v, hA, hlv⟩ := hW.atL
    simpa using (hA _).2 hlv
  obtain ⟨u0, hu0⟩ := exists_unit_one_add l
  obtain ⟨t, htI, htu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hv u0
  have heps : eps l t = ((1 + l : ℕ) : Qbar l) := by
    simp [eps, cycBar, htu, hu0]
  obtain ⟨m, hm1, hm⟩ := hW.wt
  have htD : t ∈ D := Ine_le_Dec A htI
  have hpow00 : ∀ s ∈ D, ∀ n : ℕ, mat W (s ^ n) 0 0 = mat W s 0 0 ^ n := by
    intro s hs n
    induction n with
    | zero => simp [hone]
    | succ n ih => rw [pow_succ, h00 _ _ hs, ih, pow_succ]
  set T := t ^ (2 * m) with hTdef
  have hTD : T ∈ D := D.pow_mem htD _
  set Nq : ℕ := (1 + l) ^ (2 * (e * m)) with hNq
  have hT00 : mat W T 0 0 = (Nq : Qbar l) := by
    rw [hTdef, hpow00 t htD, pow_mul', hm t htI, heps, hNq]; push_cast; ring
  have hdet : mat W T 0 0 * mat W T 1 1 = 1 := by
    have h2 : dt W t ^ 2 = 1 := by
      have := congrArg (fun f => f t) hW.det2
      simpa using this
    have hdT : dt W T = 1 := by
      rw [hTdef, map_pow, pow_mul, h2, one_pow]
    have h3 : ((dt W T : (Qbar l)ˣ) : Qbar l) = (mat W T).det := rfl
    rw [hdT, Units.val_one, Matrix.det_fin_two, hup T hTD] at h3
    linear_combination -h3
  have hNqne : ∀ k : ℕ, 1 ≤ k → ((Nq ^ k : ℕ) : Qbar l) ≠ 1 := by
    intro k hk h
    have h' : Nq ^ k = 1 := by exact_mod_cast h
    have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
    have hpos : 2 * (e * m) ≠ 0 := by
      have := hW.e_pos; positivity
    have : 1 < Nq ^ k := by
      rw [hNq, ← pow_mul]
      exact Nat.one_lt_pow (by positivity) (by omega)
    omega
  have hTi : T * T⁻¹ = 1 := mul_inv_cancel T
  have hTiD : T⁻¹ ∈ D := D.inv_mem hTD
  have hTi11 : mat W T⁻¹ 1 1 = (Nq : Qbar l) := by
    have := h11 T T⁻¹ hTD
    rw [hTi, hone] at this
    rw [Matrix.one_apply_eq] at this
    linear_combination (-(mat W T⁻¹ 1 1)) * hdet - (mat W T 0 0) * this + hT00
  have hi11 : mat W T 1 1 * mat W T⁻¹ 1 1 = 1 := by
    have := h11 T T⁻¹ hTD
    rw [hTi, hone, Matrix.one_apply_eq] at this
    exact this.symm
  have hinvy : y T 1 + mat W T 1 1 * y T⁻¹ 1 = 0 := by
    have := hb T T⁻¹ hTD
    rw [hTi, hy1] at this
    simpa using this.symm

  have hPconj : ∀ u, P u → P (T * u * T⁻¹) ∧ mat W (T * u * T⁻¹) 0 1 = ((Nq * Nq : ℕ) : Qbar l) * mat W u 0 1 ∧
      y (T * u * T⁻¹) 1 = mat W T 1 1 * y u 1 := by
    rintro u ⟨huD, hu0', hu1, huc⟩
    have hTuD : T * u ∈ D := D.mul_mem hTD huD
    have hi00 : mat W T 0 0 * mat W T⁻¹ 0 0 = 1 := by
      have := h00 T T⁻¹ hTiD
      rw [hTi, hone, Matrix.one_apply_eq] at this
      exact this.symm
    have hi01 : mat W T 0 0 * mat W T⁻¹ 0 1 + mat W T 0 1 * mat W T⁻¹ 1 1 = 0 := by
      have := h01 T T⁻¹ hTiD
      rw [hTi, hone, Matrix.one_apply_ne (by decide)] at this
      exact this.symm
    refine ⟨⟨D.mul_mem hTuD hTiD, ?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [h00 _ _ hTiD, h00 _ _ huD, hu0', mul_one, hi00]
    · rw [h11 _ _ hTuD, h11 _ _ hTD, hu1, mul_one, hi11]
    · simp [map_mul, map_inv, huc]
    · rw [h01 _ _ hTiD, h01 _ _ huD, h00 _ _ huD, hu0', hu1]
      push_cast
      linear_combination hi01 + mat W u 0 1 * mat W T⁻¹ 1 1 * hT00 + mat W u 0 1 * (Nq : Qbar l) * hTi11
    · rw [mul_assoc, hb T _ hTD, hb u T⁻¹ huD, hu1]
      linear_combination hinvy

  have hvan : ∀ u, P u → y u 1 = 0 := by
    intro u hu
    obtain ⟨hc1, hc2, hc3⟩ := hPconj u hu
    obtain ⟨hp1, hp2, hp3⟩ := hPpow u hu (Nq * Nq)
    have h3 := hfac _ _ hc1 hp1 (by rw [hc2, hp2])
    have h4 : mat W T 1 1 * y u 1 = ((Nq * Nq : ℕ) : Qbar l) * y u 1 := by rw [← hc3, ← hp3, h3]
    have h5 : (((Nq ^ 3 : ℕ) : Qbar l) - 1) * y u 1 = 0 := by
      push_cast at h4 ⊢
      linear_combination (-(Nq : Qbar l)) * h4 + y u 1 * hdet - y u 1 * mat W T 1 1 * hT00
    rcases mul_eq_zero.1 h5 with h | h
    · exact absurd (sub_eq_zero.1 h) (hNqne 3 (by norm_num))
    · exact h

  have hT11ne : mat W T 1 1 - 1 ≠ 0 := by
    intro h
    have h' : mat W T 1 1 = 1 := sub_eq_zero.1 h
    rw [h', mul_one, hT00] at hdet
    exact hNqne 1 (by norm_num) (by simpa using hdet)
  refine ⟨y T 1 / (mat W T 1 1 - 1), fun s hs => ?_⟩
  have hsT : s * T ∈ D := D.mul_mem hs hTD
  have hTs : T * s ∈ D := D.mul_mem hTD hs
  have hsTi : (s * T)⁻¹ ∈ D := D.inv_mem hsT
  have hinv00 : mat W (s * T)⁻¹ 0 0 * mat W (s * T) 0 0 = 1 := by
    have := h00 (s * T)⁻¹ (s * T) hsT
    rw [inv_mul_cancel, hone, Matrix.one_apply_eq] at this
    exact this.symm
  have hinv11 : mat W (s * T)⁻¹ 1 1 * mat W (s * T) 1 1 = 1 := by
    have := h11 (s * T)⁻¹ (s * T) hsTi
    rw [inv_mul_cancel, hone, Matrix.one_apply_eq] at this
    exact this.symm
  have hcP : P ((s * T)⁻¹ * (T * s)) := by
    refine ⟨D.mul_mem hsTi hTs, ?_, ?_, ?_⟩
    · rw [h00 _ _ hTs, h00 _ _ hs]
      linear_combination hinv00 - mat W (s * T)⁻¹ 0 0 * h00 s T hTD
    · rw [h11 _ _ hsTi, h11 _ _ hTD]
      linear_combination hinv11 - mat W (s * T)⁻¹ 1 1 * h11 s T hs
    · have hcs : cycBar ℚ Ω l (T * s) = cycBar ℚ Ω l (s * T) := by rw [map_mul, map_mul, mul_comm]
      rw [map_mul, map_inv, hcs, inv_mul_cancel]
  have hyc := hvan _ hcP
  have e1 : (s * T) * ((s * T)⁻¹ * (T * s)) = T * s := by group
  have h6 := hb (s * T) ((s * T)⁻¹ * (T * s)) hsT
  rw [e1, hyc, mul_zero, add_zero, hb T s hTD, hb s T hs] at h6
  have hinv := mul_inv_cancel₀ hT11ne
  rw [div_eq_mul_inv]
  linear_combination (mat W T 1 1 - 1)⁻¹ * h6 - y s 1 * hinv

end GlobalTheory.Ord2.GrOfKill
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GreenbergOrdinaryOfVanishingOnCycloKernelStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.greenbergOrdinary_of_vanishing_on_cycloKernel : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ y ∈ Z1 (Loc.colRep W), (∀ g ∈ N0g W, y g = 0) → Gr W A y := by
  first | exact @GlobalTheory.Ord2.GrOfKill.gr_of_vanish_on_trivial | exact GlobalTheory.Ord2.GrOfKill.gr_of_vanish_on_trivial | (intros; apply GlobalTheory.Ord2.GrOfKill.gr_of_vanish_on_trivial <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.VanishOrdOfKatoUse
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.VanishKato

theorem cont_of_ker {Γ H : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] (f : Γ →* H) (U : Set Γ) (hU : IsOpen U) (h1 : 1 ∈ U)
    (h : ∀ s ∈ U, f s = 1) : Continuous f := by
  refine continuous_of_continuousAt_one f ?_
  refine (continuousAt_const (y := (1 : H))).congr ?_
  filter_upwards [hU.mem_nhds h1] with s hs
  exact (h s hs).symm

theorem cont_kills {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (M : ℕ) (hM : 1 ≤ M) (φ : G ℚ Ω →* (Qbar l)ˣ) (hφ : KillsMu M φ) : Continuous φ := by
  have hfin : {ζ : Ω | ζ ^ M = 1}.Finite := by
    classical
    refine (Polynomial.nthRoots M (1 : Ω)).toFinset.finite_toSet.subset fun ζ hζ => ?_
    simpa [Polynomial.mem_nthRoots hM] using hζ
  refine cont_of_ker φ (⋂ ζ ∈ {ζ : Ω | ζ ^ M = 1}, (MulAction.stabilizer (Ω ≃ₐ[ℚ] Ω) ζ : Set (Ω ≃ₐ[ℚ] Ω)))
    (hfin.isOpen_biInter fun ζ _ => stabilizer_isOpen_of_isIntegral ζ) ?_ ?_
  · simp only [Set.mem_iInter]
    exact fun ζ _ => Subgroup.one_mem _
  · intro s hs
    simp only [Set.mem_iInter] at hs
    exact hφ s fun ζ hζ => hs ζ hζ

end GlobalTheory.Ord2.VanishKato

namespace GlobalTheory.Ord2

end GlobalTheory.Ord2

end
end

module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlmostPurityOfNormalFiniteIndexSubgroup
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SetAverageProdFundamentalDomainPlaneLatticePow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingCyclotomicTowerLevel
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeAdelicMatrixIntegralTranslate
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGaloisInvariantValuationIntegersEqIntegral

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ApproxPthRootFixedFieldCyclotomicTower
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqUnitMulPowCyclotomicUniformizer
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqUnitMulPowCyclotomicUniformizer
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.K5.UnitPow

theorem eq_unit_mul_pow : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω), ∀ b ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq), b ≠ 0 → ∃ (n k : ℕ), 1 ≤ n ∧ ∃ u ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq), ∃ u' ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq), u * u' = 1 ∧ b = u * (T.ζ n - 1) ^ k := by
  intro p _ Ω _ _ hclo T b hb hb0
  obtain ⟨n, ι, w, hn, hemb, hw, hmem⟩ := GlobalTheory.T.exists_level_emb_of_mem_adjoin_zeta_qq p Ω hclo T b hb
  obtain ⟨hdom, hdvr, hirr⟩ := GlobalTheory.T.isDiscreteValuationRing_cyclotomicTowerLevel p n hn
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hb0 (by rw [← hw, map_zero])
  obtain ⟨k, ε, hε⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hw0 hirr
  refine ⟨n, k, hn, ι (ε : On p n), hmem _, ι ((ε⁻¹ : (On p n)ˣ) : On p n), hmem _, ?_, ?_⟩
  · rw [← map_mul, Units.mul_inv, map_one]
  · rw [← hw, hε, map_mul, map_pow, map_sub, map_one, hemb.1]

end GlobalTheory.K5.UnitPow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqUnitMulPowCyclotomicUniformizerStatement
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_unit_mul_pow_cyclotomic_uniformizer : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω), ∀ b ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq), b ≠ 0 → ∃ (n k : ℕ), 1 ≤ n ∧ ∃ u ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq), ∃ u' ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq), u * u' = 1 ∧ b = u * (T.ζ n - 1) ^ k := by
  first | exact @GlobalTheory.K5.UnitPow.eq_unit_mul_pow | exact GlobalTheory.K5.UnitPow.eq_unit_mul_pow | (intros; apply GlobalTheory.K5.UnitPow.eq_unit_mul_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusSurjectiveModPrimeCyclotomicKummerTower
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PAdicCompletionLaurentEqSumPthPowersModP
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PAdicCompletionLaurentEqSumPthPowersModP
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.K5

theorem qO_pow_eq (p : ℕ) [Fact p.Prime] (j : ℕ) :
    qO p ^ j = algebraMap (Lau p) (O0 p) (HahnSeries.single (j : ℤ) (1 : ℤ_[p])) := by
  rw [qO, ← map_pow, HahnSeries.single_pow]
  simp

theorem exists_lau_add_p_mul (p : ℕ) [Fact p.Prime] (x : O0 p) :
    ∃ (f : Lau p) (z : O0 p), x = algebraMap (Lau p) (O0 p) f + (p : O0 p) * z := by
  have fg : (pI p).FG := Submodule.fg_span_singleton _
  have hker := AdicCompletion.ker_evalOneₐ_eq_map (pI p) fg
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalOneₐ (pI p) x)
  have hmem : x - algebraMap (Lau p) (O0 p) a ∈
      RingHom.ker (AdicCompletion.evalOneₐ (pI p)).toRingHom := by
    rw [RingHom.mem_ker]
    show AdicCompletion.evalOneₐ (pI p) (x - algebraMap (Lau p) (O0 p) a) = 0
    rw [map_sub, (AdicCompletion.evalOneₐ (pI p)).commutes a]
    show _ - Ideal.Quotient.mk (pI p) a = 0
    rw [ha, sub_self]
  have hmap : (pI p).map (algebraMap (Lau p) (O0 p)) = Ideal.span {(p : O0 p)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  rw [hker, hmap, Ideal.mem_span_singleton] at hmem
  obtain ⟨z, hz⟩ := hmem
  exact ⟨a, z, by rw [← hz]; ring⟩

theorem exists_eq_sum_qO_pow_mul_pow_add_mul (p : ℕ) [Fact p.Prime] (x : O0 p) :
    ∃ (g : Fin p → O0 p) (h : O0 p), x = ∑ j : Fin p, qO p ^ (j : ℕ) * g j ^ p + (p : O0 p) * h := by
  obtain ⟨f, z, rfl⟩ := exists_lau_add_p_mul p x
  obtain ⟨g, h, hf⟩ := GlobalTheory.T.laurentSeriesPadic_exists_pthPower_combination p f
  refine ⟨fun j => algebraMap (Lau p) (O0 p) (g j), algebraMap (Lau p) (O0 p) h + z, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hf, map_add (f := _), map_sum, map_mul, map_natCast]
  simp only [map_mul, map_pow, qO_pow_eq]
  ring

end GlobalTheory.K5
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PAdicCompletionLaurentEqSumPthPowersModPStatement
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pAdicCompletionLaurent_eq_sum_pthPowers_mod_p : ∀ (p : ℕ) [Fact p.Prime] (x : O0 p), ∃ (g : Fin p → O0 p) (h : O0 p), x = ∑ j : Fin p, qO p ^ (j : ℕ) * g j ^ p + (p : O0 p) * h := by
  first | exact @GlobalTheory.K5.exists_eq_sum_qO_pow_mul_pow_add_mul | exact GlobalTheory.K5.exists_eq_sum_qO_pow_mul_pow_add_mul | (intros; apply GlobalTheory.K5.exists_eq_sum_qO_pow_mul_pow_add_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusSurjectiveModPrimeCyclotomicKummerTower
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.K5

def IsPowModP {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (S : Subalgebra R A) (p : ℕ)
    (x : A) : Prop :=
  ∃ y ∈ S, ∃ z ∈ S, x = y ^ p + (p : A) * z

section Closure

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (S : Subalgebra R A) {p : ℕ}

theorem isPthPowerModP_add (hp : p.Prime) {x x' : A} (hx : IsPowModP S p x) (hx' : IsPowModP S p x') :
    IsPowModP S p (x + x') := by
  obtain ⟨y, hy, z, hz, rfl⟩ := hx
  obtain ⟨y', hy', z', hz', rfl⟩ := hx'
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp (⟨y, hy⟩ : S) ⟨y', hy'⟩
  have hr' := congrArg Subtype.val hr
  push_cast at hr'
  refine ⟨y + y', S.add_mem hy hy', z + z' - y * y' * r, ?_, ?_⟩
  · exact S.sub_mem (S.add_mem hz hz') (S.mul_mem (S.mul_mem hy hy') r.2)
  · rw [hr']; ring

theorem isPthPowerModP_mul {x x' : A} (hx : IsPowModP S p x) (hx' : IsPowModP S p x') :
    IsPowModP S p (x * x') := by
  obtain ⟨y, hy, z, hz, rfl⟩ := hx
  obtain ⟨y', hy', z', hz', rfl⟩ := hx'
  refine ⟨y * y', S.mul_mem hy hy', z * y' ^ p + y ^ p * z' + (p : A) * z * z', ?_, ?_⟩
  · refine S.add_mem (S.add_mem (S.mul_mem hz (S.pow_mem hy' _))
      (S.mul_mem (S.pow_mem hy _) hz')) (S.mul_mem (S.mul_mem ?_ hz) hz')
    exact S.natCast_mem p
  · ring

theorem isPthPowerModP_pow {y : A} (hy : y ∈ S) : IsPowModP S p (y ^ p) :=
  ⟨y, hy, 0, S.zero_mem, by ring⟩

theorem isPthPowerModP_zero (hp : p.Prime) : IsPowModP S p 0 :=
  ⟨0, S.zero_mem, 0, S.zero_mem, by rw [zero_pow hp.ne_zero]; ring⟩

theorem isPthPowerModP_add_p_mul {x h : A} (hx : IsPowModP S p x) (hh : h ∈ S) :
    IsPowModP S p (x + (p : A) * h) := by
  obtain ⟨y, hy, z, hz, rfl⟩ := hx
  exact ⟨y, hy, z + h, S.add_mem hz hh, by ring⟩

end Closure

theorem frob_surj_adjoin_tower : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω]
    (T : Tower p Ω), ∀ x ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq),
      ∃ y ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq),
      ∃ z ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq), x = y ^ p + (p : Ω) * z := by
  intro p hp Ω _ _ T x hx
  set S := Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq) with hS
  have hpp : p.Prime := hp.out
  have hζ : ∀ n, T.ζ n ∈ S := fun n => Algebra.subset_adjoin (Or.inl ⟨n, rfl⟩)
  have hq : ∀ n, T.qq n ∈ S := fun n => Algebra.subset_adjoin (Or.inr ⟨n, rfl⟩)
  suffices IsPowModP S p x from this
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨n, rfl⟩ | ⟨n, rfl⟩
    · rw [← T.ζpow n]; exact isPthPowerModP_pow S (hζ _)
    · rw [← T.qpow n]; exact isPthPowerModP_pow S (hq _)
  | algebraMap r =>
    obtain ⟨g, h, rfl⟩ := GlobalTheory.T.pAdicCompletionLaurent_eq_sum_pthPowers_mod_p p r
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_add (f := _), map_sum, map_mul, map_natCast]
    refine isPthPowerModP_add_p_mul S ?_ ?_
    · refine Finset.sum_induction _ (IsPowModP S p) (fun a b ha hb => isPthPowerModP_add S hpp ha hb)
        (isPthPowerModP_zero S hpp) ?_
      intro j _
      have e : algebraMap (O0 p) Ω (qO p ^ (j : ℕ) * g j ^ p) =
          (T.qq 1 ^ (j : ℕ) * algebraMap (O0 p) Ω (g j)) ^ p := by
        rw [map_mul, map_pow, map_pow, ← T.q0, ← T.qpow 0, mul_pow, ← pow_mul, ← pow_mul, mul_comm p]
      rw [e]
      exact isPthPowerModP_pow S (S.mul_mem (S.pow_mem (hq 1) _) (S.algebraMap_mem _))
    · exact S.algebraMap_mem _
  | add x y _ _ hx hy => exact isPthPowerModP_add S hpp hx hy
  | mul x y _ _ hx hy => exact isPthPowerModP_mul S hx hy

end GlobalTheory.K5
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusSurjectiveModPrimeCyclotomicKummerTowerStatement
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_surjective_mod_prime_cyclotomicKummerTower : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω] (T : Tower p Ω), ∀ x ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq), ∃ y ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq), ∃ z ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq), x = y ^ p + (p : Ω) * z := by
  first | exact @GlobalTheory.K5.frob_surj_adjoin_tower | exact GlobalTheory.K5.frob_surj_adjoin_tower | (intros; apply GlobalTheory.K5.frob_surj_adjoin_tower <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ApproxPthRootClosedMulDivPow
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ApproxPthRootClosedMulDivPow
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

variable {L : Type} [Field L] (v : Valuation L ℝ≥0) {p : ℕ} {θ : ℝ≥0}

theorem approxRoot_pow_le (hθ : θ ≤ 1) {u w : L} (h : v (u - w ^ p) ≤ θ * v u) :
    v (w ^ p) ≤ v u := by
  have e : w ^ p = u - (u - w ^ p) := by ring
  rw [e]
  refine (Valuation.map_sub v _ _).trans (max_le le_rfl (h.trans ?_))
  simpa using mul_le_mul' hθ (le_refl (v u))

theorem approxRoot_mul (hθ : θ ≤ 1) {u u' w w' : L} (h : v (u - w ^ p) ≤ θ * v u)
    (h' : v (u' - w' ^ p) ≤ θ * v u') : v (u * u' - (w * w') ^ p) ≤ θ * v (u * u') := by
  have e : u * u' - (w * w') ^ p = u * (u' - w' ^ p) + w' ^ p * (u - w ^ p) := by ring
  rw [e, map_mul]
  refine (Valuation.map_add v _ _).trans (max_le ?_ ?_)
  · rw [map_mul]
    calc v u * v (u' - w' ^ p) ≤ v u * (θ * v u') := mul_le_mul' le_rfl h'
      _ = θ * (v u * v u') := by ring
  · rw [map_mul]
    calc v (w' ^ p) * v (u - w ^ p) ≤ v u' * (θ * v u) :=
          mul_le_mul' (approxRoot_pow_le v hθ h') h
      _ = θ * (v u * v u') := by ring

theorem approxRoot_inv (hθ : θ < 1) {u w : L} (hu : u ≠ 0) (h : v (u - w ^ p) ≤ θ * v u) :
    v (u⁻¹ - (w⁻¹) ^ p) ≤ θ * v u⁻¹ := by
  have hvu : 0 < v u := by
    rw [pos_iff_ne_zero]; exact (Valuation.ne_zero_iff v).mpr hu
  have hlt : v (w ^ p - u) < v u := by
    rw [Valuation.map_sub_swap]
    exact h.trans_lt (by simpa using mul_lt_mul_of_pos_right hθ hvu)
  have heq : v (w ^ p) = v u := Valuation.map_eq_of_sub_lt v hlt
  have hw : w ^ p ≠ 0 := by
    intro h0; rw [h0, map_zero] at heq; exact hvu.ne' heq.symm
  have e : u⁻¹ - (w⁻¹) ^ p = (w ^ p - u) * (u⁻¹ * (w ^ p)⁻¹) := by
    rw [inv_pow]; field_simp
  rw [e, map_mul, map_mul, map_inv₀, map_inv₀, heq, Valuation.map_sub_swap]
  calc v (u - w ^ p) * ((v u)⁻¹ * (v u)⁻¹) ≤ θ * v u * ((v u)⁻¹ * (v u)⁻¹) :=
        mul_le_mul' h le_rfl
    _ = θ * (v u)⁻¹ := by field_simp

theorem approxRoot_closed : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ) (F : Subfield L) (θ : ℝ≥0), θ < 1 → ∀ u u' : L, (∃ w ∈ F, v (u - w ^ p) ≤ θ * v u) → (∃ w ∈ F, v (u' - w ^ p) ≤ θ * v u') → (∃ w ∈ F, v (u * u' - w ^ p) ≤ θ * v (u * u')) ∧ (u' ≠ 0 → ∃ w ∈ F, v (u / u' - w ^ p) ≤ θ * v (u / u')) ∧ ∀ k : ℕ, ∃ w ∈ F, v (u ^ k - w ^ p) ≤ θ * v (u ^ k) := by
  intro L _ v p F θ hθ u u' ⟨w, hwF, hw⟩ ⟨w', hw'F, hw'⟩
  have hθ1 : θ ≤ 1 := hθ.le
  refine ⟨⟨w * w', F.mul_mem hwF hw'F, approxRoot_mul v hθ1 hw hw'⟩, fun hu' => ?_, fun k => ?_⟩
  · refine ⟨w * w'⁻¹, F.mul_mem hwF (F.inv_mem hw'F), ?_⟩
    rw [div_eq_mul_inv]
    exact approxRoot_mul v hθ1 hw (approxRoot_inv v hθ hu' hw')
  · induction k with
    | zero => exact ⟨1, F.one_mem, by simp⟩
    | succ k ih =>
      obtain ⟨x, hxF, hx⟩ := ih
      refine ⟨x * w, F.mul_mem hxF hwF, ?_⟩
      rw [pow_succ]
      exact approxRoot_mul v hθ1 hx hw

end GlobalTheory.AlmostEt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ApproxPthRootClosedMulDivPowStatement
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.approxPthRoot_closed_mul_div_pow : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ) (F : Subfield L) (θ : ℝ≥0), θ < 1 → ∀ u u' : L, (∃ w ∈ F, v (u - w ^ p) ≤ θ * v u) → (∃ w ∈ F, v (u' - w ^ p) ≤ θ * v u') → (∃ w ∈ F, v (u * u' - w ^ p) ≤ θ * v (u * u')) ∧ (u' ≠ 0 → ∃ w ∈ F, v (u / u' - w ^ p) ≤ θ * v (u / u')) ∧ ∀ k : ℕ, ∃ w ∈ F, v (u ^ k - w ^ p) ≤ θ * v (u ^ k) := by
  first | exact @GlobalTheory.AlmostEt.approxRoot_closed | exact GlobalTheory.AlmostEt.approxRoot_closed | (intros; apply GlobalTheory.AlmostEt.approxRoot_closed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ApproxPthRootFixedFieldCyclotomicTower
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.K5.TopRoots

theorem approxRoot_fix_tower : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
    p ≠ 2 → IsClo p Ω → ∀ (T : Tower p Ω) (v : Valuation Ω ℝ≥0),
    (∀ x : Ω, v x ≤ 1 ↔ IsInt (p := p) x) →
    0 < v (p : Ω) → v (p : Ω) < 1 → ApproxRoot p v (Fix Ω (⨅ n, Gn T n)) := by
  intro p _ Ω _ _ hp2 hclo T v hv _ hp1
  classical
  have hpp : p.Prime := Fact.out
  let S : Set Ω := Set.range T.ζ ∪ Set.range T.qq
  let B := Algebra.adjoin (O0 p) S
  let F := Fix Ω (⨅ n, Gn T n)

  have hBle : B ≤ integralClosure (O0 p) Ω := by
    rw [Algebra.adjoin_le_iff]
    rintro y (⟨n, rfl⟩ | ⟨n, rfl⟩)
    · refine IsIntegral.of_pow (pow_pos hpp.pos n) ?_
      rw [(T.prim n).pow_eq_one]; exact isIntegral_one
    · refine IsIntegral.of_pow (pow_pos hpp.pos n) ?_
      rw [Basic.qq_pow]; exact isIntegral_algebraMap
  have hBint : ∀ x ∈ B, v x ≤ 1 := fun x hx => (hv x).2 (hBle hx)

  have hBF : ∀ x ∈ B, x ∈ F := by
    intro x hx g
    have hg : (g : Gal p Ω) ∈ ⨅ n, Gn T n := g.2
    rw [Subgroup.mem_iInf] at hg
    have hle : B ≤ AlgHom.equalizer (g : Gal p Ω).toAlgHom (AlgHom.id (O0 p) Ω) := by
      rw [Algebra.adjoin_le_iff]
      rintro y (⟨n, rfl⟩ | ⟨n, rfl⟩)
      · exact ((Basic.mem_gn T n _).1 (hg n)).1
      · exact ((Basic.mem_gn T n _).1 (hg n)).2
    have := hle hx
    rw [AlgHom.mem_equalizer] at this
    exact this

  set θ := v (T.ζ 1 - 1) with hθ
  have hz1 := GlobalTheory.T.valuation_tower_zeta_sub_one p Ω hp2 T v hp1 1 le_rfl
  have hθ1 : θ < 1 := hz1.1
  let good : Ω → Prop := fun x => ∃ w ∈ F, v (x - w ^ p) ≤ θ * v x

  have hgoodB : ∀ x ∈ B, v (p : Ω) ≤ θ * v x → good x := by
    intro x hx hvx
    obtain ⟨y, hy, z, hz, e⟩ := GlobalTheory.T.frobenius_surjective_mod_prime_cyclotomicKummerTower p Ω T x hx
    refine ⟨y, hBF y hy, ?_⟩
    have : x - y ^ p = (p : Ω) * z := by rw [e]; ring
    rw [this, map_mul]
    calc v (p : Ω) * v z ≤ v (p : Ω) * 1 := mul_le_mul_of_nonneg_left (hBint z hz) zero_le
      _ = v (p : Ω) := mul_one _
      _ ≤ θ * v x := hvx

  have hunit : ∀ u ∈ B, ∀ u' ∈ B, u * u' = 1 → good u := by
    intro u hu u' hu' e
    have hvu : v u = 1 := by
      have h1 := hBint u hu
      have h2 := hBint u' hu'
      have h3 : v u * v u' = 1 := by rw [← map_mul, e, map_one]
      by_contra hne
      have hlt : v u < 1 := lt_of_le_of_ne h1 hne
      have : v u * v u' < 1 := by
        calc v u * v u' ≤ v u * 1 := mul_le_mul_of_nonneg_left h2 zero_le
          _ = v u := mul_one _
          _ < 1 := hlt
      exact absurd h3 (ne_of_lt this)
    refine hgoodB u hu ?_
    rw [hvu, mul_one]
    calc v (p : Ω) ≤ θ * v (T.ζ 1 - 1) := hz1.2
      _ ≤ θ * 1 := mul_le_mul_of_nonneg_left hθ1.le zero_le
      _ = θ := mul_one _

  have hzeta : ∀ n, 1 ≤ n → good (T.ζ n - 1) := by
    intro n hn
    have hmem : T.ζ n - 1 ∈ B :=
      Subalgebra.sub_mem _ (Algebra.subset_adjoin (Or.inl ⟨n, rfl⟩)) (Subalgebra.one_mem _)
    exact hgoodB _ hmem (GlobalTheory.T.valuation_tower_zeta_sub_one p Ω hp2 T v hp1 n hn).2

  have hB : ∀ b ∈ B, good b := by
    intro b hb
    by_cases hb0 : b = 0
    · refine ⟨0, F.zero_mem, ?_⟩
      rw [hb0, zero_pow hpp.ne_zero, sub_zero, map_zero]; exact zero_le
    obtain ⟨n, k, hn, u, hu, u', hu', e, rfl⟩ := GlobalTheory.T.eq_unit_mul_pow_cyclotomic_uniformizer p Ω hclo T b hb hb0
    have h1 := hunit u hu u' hu' e
    have h2 := (GlobalTheory.T.approxPthRoot_closed_mul_div_pow Ω v p F θ hθ1 _ _ (hzeta n hn) (hzeta n hn)).2.2 k
    exact (GlobalTheory.T.approxPthRoot_closed_mul_div_pow Ω v p F θ hθ1 _ _ h1 h2).1

  refine ⟨θ, hθ1, fun x hx => ?_⟩
  haveI : CharZero Ω := Basic.charZero_of_isClo hclo
  haveI : IsAlgClosed Ω := hclo.clo
  haveI : Algebra.IsAlgebraic (O0 p) Ω := hclo.alg
  have hfix : ∀ g : Ω ≃ₐ[O0 p] Ω, (∀ s ∈ S, g s = s) → g x = x := by
    intro g hg
    have hgm : g ∈ ⨅ n, Gn T n := by
      rw [Subgroup.mem_iInf]
      intro n
      exact (Basic.mem_gn T n g).2
        ⟨hg _ (Or.inl ⟨n, rfl⟩), hg _ (Or.inr ⟨n, rfl⟩)⟩
    exact hx ⟨g, hgm⟩
  obtain ⟨b, hb, c, hc, hc0, rfl⟩ := GlobalTheory.T.exists_div_mem_adjoin_of_fixed (O0 p) Ω hclo.inj S x hfix
  exact (GlobalTheory.T.approxPthRoot_closed_mul_div_pow Ω v p F θ hθ1 _ _ (hB b hb) (hB c hc)).2.1 hc0

end GlobalTheory.K5.TopRoots
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ApproxPthRootFixedFieldCyclotomicTowerStatement
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.approxPthRoot_fixedField_cyclotomic_tower : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], p ≠ 2 → IsClo p Ω → ∀ (T : Tower p Ω) (v : Valuation Ω ℝ≥0), (∀ x : Ω, v x ≤ 1 ↔ IsInt (p := p) x) → 0 < v (p : Ω) → v (p : Ω) < 1 → ApproxRoot p v (Fix Ω (⨅ n, Gn T n)) := by
  first | exact @GlobalTheory.K5.TopRoots.approxRoot_fix_tower | exact GlobalTheory.K5.TopRoots.approxRoot_fix_tower | (intros; apply GlobalTheory.K5.TopRoots.approxRoot_fix_tower <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsValuationAlmostEtaleTowerFixer
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.ValuationAlmostSeparation

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem orbit_finite (h : IsClo p Ω) (H : Subgroup (Gal p Ω)) (s : Ω) :
    (MulAction.orbit H s).Finite := by
  classical
  obtain ⟨P, hP0, hPs⟩ := (h.alg.isAlgebraic s)
  have hQ : P.map (algebraMap (O0 p) Ω) ≠ 0 :=
    (Polynomial.map_ne_zero_iff h.inj).2 hP0
  refine (P.map (algebraMap (O0 p) Ω)).roots.toFinset.finite_toSet.subset ?_
  rintro _ ⟨g, rfl⟩
  simp only [Finset.mem_coe, Multiset.mem_toFinset]
  rw [Polynomial.mem_roots hQ, Polynomial.IsRoot, Polynomial.eval_map_algebraMap]
  show Polynomial.aeval ((g : Gal p Ω) s) P = 0
  rw [Polynomial.aeval_algEquiv, AlgHom.comp_apply]
  simp [hPs]

theorem fix_top (H : Subgroup (Gal p Ω)) :
    Fix Ω (⊤ : Subgroup H) = Fix Ω H := by
  ext x
  constructor
  · intro hx g
    exact hx ⟨g, Subgroup.mem_top g⟩
  · intro hx g
    exact hx g.1

end GlobalTheory.ValuationAlmostSeparation

open GlobalTheory.ValuationAlmostSeparation

theorem GlobalTheory.ValuationAlmostSeparation.exists_valuation_almostSep : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], p ≠ 2 → IsClo p Ω → ∀ (T : Tower p Ω), ∃ v : Valuation Ω ℝ≥0, (∀ x : Ω, v x ≤ 1 ↔ IsInt (p := p) x) ∧ (∀ (g : Gal p Ω) (x : Ω), v (g x) = v x) ∧ 0 < v (p : Ω) ∧ v (p : Ω) < 1 ∧ ∀ S : Finset Ω, ∃ U : Subgroup ↥(⨅ n, Gn T n), U.Normal ∧ U.FiniteIndex ∧ (∀ s ∈ S, s ∈ Fix Ω U) ∧ AlmostSep v U := by
  intro p _ Ω _ _ hp2 hclo T
  obtain ⟨v, hint, hinv, hp0, hp1⟩ := GlobalTheory.T.exists_galoisInvariant_valuation_integers_eq_integral p Ω hclo
  refine ⟨v, hint, hinv, hp0, hp1, fun S => ?_⟩
  obtain ⟨U, hUn, hUf, hUS, hUsep⟩ := GlobalTheory.T.exists_normal_finiteIndex_fixing_finite_orbits Ω (↥(⨅ n, Gn T n)) S
    (fun s _ => orbit_finite hclo _ s)
  refine ⟨U, hUn, hUf, hUS, ?_⟩
  have hR := GlobalTheory.T.approxPthRoot_fixedField_cyclotomic_tower p Ω hp2 hclo T v hint hp0 hp1
  refine GlobalTheory.T.almostPurity_of_normal_finiteIndex_subgroup Ω v p (Fact.out) hp0 hp1 (↥(⨅ n, Gn T n)) (fun g x => hinv g.1 x)
    (T.ζ 1) (by simpa using T.prim 1) ?_ (by rw [fix_top]; exact hR) U hUn hUf hUsep
  intro g
  have hg : (g : Gal p Ω) ∈ Gn T 1 := (iInf_le (fun n => Gn T n) 1) g.2
  exact hg.1
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsValuationAlmostEtaleTowerFixerStatement
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_valuation_almostEtale_towerFixer : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], p ≠ 2 → IsClo p Ω → ∀ (T : Tower p Ω), ∃ v : Valuation Ω ℝ≥0, (∀ x : Ω, v x ≤ 1 ↔ GlobalTheory.K5.IsInt (p := p) x) ∧ (∀ (g : Gal p Ω) (x : Ω), v (g x) = v x) ∧ 0 < v (p : Ω) ∧ v (p : Ω) < 1 ∧ ∀ S : Finset Ω, ∃ U : Subgroup ↥(⨅ n, Gn T n), U.Normal ∧ U.FiniteIndex ∧ (∀ s ∈ S, s ∈ Fix Ω U) ∧ AlmostSep v U := by
  first | exact @GlobalTheory.ValuationAlmostSeparation.exists_valuation_almostSep | exact GlobalTheory.ValuationAlmostSeparation.exists_valuation_almostSep | (intros; apply GlobalTheory.ValuationAlmostSeparation.exists_valuation_almostSep <;> assumption)
end

module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAlmostGaloisCoordinates
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteDimensionalOfGammaLe

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerGnExponentsKummerCochains
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerGnExponentsKummerCochains
open GlobalTheory.K5 GlobalTheory.KumDlog

namespace GlobalTheory.KumExpo

theorem exponents : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], ∀ (T : Tower p Ω) (n m : ℕ), 2 * n ≤ m → ∀ lz lq : Gal p Ω → ZMod (p ^ n),
  IsKum T n (Gn T n) (T.ζ (2 * n)) lz → IsKum T n (Gn T n) (T.qq (2 * n)) lq → ∀ g ∈ Gn T n,
  ∃ (i j : ℕ) (s t : ℤ), g (T.ζ m) = T.ζ m ^ i ∧ g (T.qq m) = T.ζ m ^ j * T.qq m ∧
    (i : ℤ) = 1 + p ^ n * ((lz g).val : ℤ) + p ^ (2 * n) * s ∧ (j : ℤ) = p ^ n * ((lq g).val : ℤ) + p ^ (2 * n) * t := by
  intro p _ Ω _ _ T n m hm lz lq hz hq g hg
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm

  have h1 : (g (T.ζ (2 * n + k))) ^ (p ^ (2 * n + k)) = 1 := by
    rw [← map_pow, (T.prim _).pow_eq_one, map_one]
  obtain ⟨i, -, hi⟩ := (T.prim _).eq_pow_of_pow_eq_one h1
  have hqne := qq_ne T (2 * n + k)
  have h2 : (g (T.qq (2 * n + k)) / T.qq (2 * n + k)) ^ (p ^ (2 * n + k)) = 1 := by
    rw [div_pow, ← map_pow, kummerTower_qq_pow_level_eq_q, AlgEquiv.commutes, ← kummerTower_qq_pow_level_eq_q T (2 * n + k),
      div_self (pow_ne_zero _ hqne)]
  obtain ⟨j, -, hj⟩ := (T.prim _).eq_pow_of_pow_eq_one h2
  have hj' : g (T.qq (2 * n + k)) = T.ζ (2 * n + k) ^ j * T.qq (2 * n + k) := by
    rw [hj, div_mul_cancel₀ _ hqne]

  have ez : T.ζ (2 * n + k) ^ (p ^ k) = T.ζ (2 * n) := zeta_pow T (2 * n) k
  have eq' : T.qq (2 * n + k) ^ (p ^ k) = T.qq (2 * n) := qq_pow T (2 * n) k
  have ezn : T.ζ (2 * n) ^ (p ^ n) = T.ζ n := by
    have := zeta_pow T n n
    rwa [← two_mul] at this
  have gz : g (T.ζ (2 * n)) = T.ζ (2 * n) ^ i := by
    rw [← ez, map_pow, ← hi, ← pow_mul, ← pow_mul, Nat.mul_comm i]
  have gq : g (T.qq (2 * n)) = T.ζ (2 * n) ^ j * T.qq (2 * n) := by
    rw [← eq', map_pow, hj', mul_pow, ← pow_mul, mul_comm j, pow_mul, ez]
  have kz := hz g hg
  have kq := hq g hg
  rw [gz, ← ezn, ← pow_mul, ← pow_succ] at kz
  rw [gq, ← ezn, ← pow_mul] at kq
  have kq' := mul_right_cancel₀ (qq_ne T (2 * n)) kq
  rw [GlobalTheory.K5.Basic.zeta_pow_eq_iff] at kz kq'
  rw [Nat.modEq_iff_dvd] at kz kq'
  obtain ⟨s, hs⟩ := kz
  obtain ⟨t, ht⟩ := kq'
  refine ⟨i, j, -s, -t, hi.symm, hj', ?_, ?_⟩
  · push_cast at hs ⊢
    linear_combination -hs
  · push_cast at ht ⊢
    linear_combination -ht

end GlobalTheory.KumExpo
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerGnExponentsKummerCochainsStatement
open GlobalTheory.K5 GlobalTheory.KumDlog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.towerGn_exponents_kummer_cochains : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], ∀ (T : Tower p Ω) (n m : ℕ), 2 * n ≤ m → ∀ lz lq : Gal p Ω → ZMod (p ^ n),
  IsKum T n (Gn T n) (T.ζ (2 * n)) lz → IsKum T n (Gn T n) (T.qq (2 * n)) lq → ∀ g ∈ Gn T n,
  ∃ (i j : ℕ) (s t : ℤ), g (T.ζ m) = T.ζ m ^ i ∧ g (T.qq m) = T.ζ m ^ j * T.qq m ∧
    (i : ℤ) = 1 + p ^ n * ((lz g).val : ℤ) + p ^ (2 * n) * s ∧ (j : ℤ) = p ^ n * ((lq g).val : ℤ) + p ^ (2 * n) * t := by
  first | exact @GlobalTheory.KumExpo.exponents | exact GlobalTheory.KumExpo.exponents | (intros; apply GlobalTheory.KumExpo.exponents <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerGaloisFixedEqDivLevelElements
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerGaloisFixedEqDivLevelElements
open GlobalTheory.K5 GlobalTheory.KumDlog

noncomputable section

namespace GlobalTheory.FixFrac

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

def fracField (T : Tower p Ω) : Subfield Ω where
  carrier := {x | ∃ m : ℕ, ∃ a ∈ Lev T m, ∃ b ∈ Lev T m, b ≠ 0 ∧ x = a / b}
  zero_mem' := ⟨0, 0, zero_mem _, 1, one_mem _, one_ne_zero, by simp⟩
  one_mem' := ⟨0, 1, one_mem _, 1, one_mem _, one_ne_zero, by simp⟩
  add_mem' := by
    rintro _ _ ⟨m, a, ha, b, hb, hb0, rfl⟩ ⟨m', c, hc, d, hd, hd0, rfl⟩
    have h1 := Lev_mono T (le_max_left m m')
    have h2 := Lev_mono T (le_max_right m m')
    refine ⟨max m m', a * d + b * c, add_mem (mul_mem (h1 ha) (h2 hd)) (mul_mem (h1 hb) (h2 hc)),
      b * d, mul_mem (h1 hb) (h2 hd), mul_ne_zero hb0 hd0, ?_⟩
    rw [div_add_div _ _ hb0 hd0]
  mul_mem' := by
    rintro _ _ ⟨m, a, ha, b, hb, hb0, rfl⟩ ⟨m', c, hc, d, hd, hd0, rfl⟩
    have h1 := Lev_mono T (le_max_left m m')
    have h2 := Lev_mono T (le_max_right m m')
    exact ⟨max m m', a * c, mul_mem (h1 ha) (h2 hc), b * d, mul_mem (h1 hb) (h2 hd),
      mul_ne_zero hb0 hd0, div_mul_div_comm a b c d⟩
  neg_mem' := by
    rintro _ ⟨m, a, ha, b, hb, hb0, rfl⟩
    exact ⟨m, -a, neg_mem ha, b, hb, hb0, (neg_div b a).symm⟩
  inv_mem' := by
    rintro _ ⟨m, a, ha, b, hb, hb0, rfl⟩
    by_cases ha0 : a = 0
    · exact ⟨0, 0, zero_mem _, 1, one_mem _, one_ne_zero, by simp [ha0]⟩
    · exact ⟨m, b, hb, a, ha, ha0, inv_div a b⟩

theorem mem_fracField_of_mem (T : Tower p Ω) {m : ℕ} {a : Ω} (ha : a ∈ Lev T m) :
    a ∈ fracField T :=
  ⟨m, a, ha, 1, one_mem _, one_ne_zero, (div_one a).symm⟩

theorem fixed_eq_div : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ (T : Tower p Ω) (x : Ω), (∀ h ∈ Hinf T, h x = x) →
    ∃ m : ℕ, ∃ a ∈ Lev T m, ∃ b ∈ Lev T m, b ≠ 0 ∧ x = a / b := by
  intro p _ Ω _ _ hC T x hx
  haveI : FaithfulSMul (O0 p) Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 hC.inj
  letI : Algebra (FractionRing (O0 p)) Ω := FractionRing.liftAlgebra (O0 p) Ω
  haveI : IsScalarTower (O0 p) (FractionRing (O0 p)) Ω :=
    FractionRing.isScalarTower_liftAlgebra _ _
  haveI : Algebra.IsAlgebraic (O0 p) Ω := hC.alg
  haveI : Algebra.IsAlgebraic (FractionRing (O0 p)) Ω :=
    Algebra.IsAlgebraic.extendScalars (IsFractionRing.injective (O0 p) (FractionRing (O0 p)))
  haveI : IsAlgClosed Ω := hC.clo
  haveI : IsAlgClosure (FractionRing (O0 p)) Ω := ⟨hC.clo, inferInstance⟩
  haveI : CharZero Ω := Basic.charZero_of_isClo hC
  haveI : CharZero (FractionRing (O0 p)) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective (O0 p) (FractionRing (O0 p)))
  haveI : IsGalois (FractionRing (O0 p)) Ω := IsAlgClosure.isGalois _ _
  let E := IntermediateField.adjoin (FractionRing (O0 p)) (Set.range T.ζ ∪ Set.range T.qq)
  have hxE : x ∈ E := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup E, IntermediateField.mem_fixedField_iff]
    intro σ hσ
    have hfix : ∀ y ∈ E, σ y = y := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ
    have hmem : σ.restrictScalars (O0 p) ∈ Hinf T := by
      rw [mem_Hinf]
      intro n
      exact ⟨hfix _ (IntermediateField.subset_adjoin _ _ (Or.inl ⟨n, rfl⟩)),
        hfix _ (IntermediateField.subset_adjoin _ _ (Or.inr ⟨n, rfl⟩))⟩
    exact hx _ hmem
  have halg : ∀ c : FractionRing (O0 p), algebraMap (FractionRing (O0 p)) Ω c ∈ fracField T := by
    intro c
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (O0 p)) c
    dsimp only
    rw [IsFractionRing.mk'_eq_div, map_div₀, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
    exact ⟨0, _, Subalgebra.algebraMap_mem _ a, _, Subalgebra.algebraMap_mem _ (s : O0 p),
      (map_ne_zero_iff _ hC.inj).2 (nonZeroDivisors.ne_zero s.2), rfl⟩
  have hle : E ≤ (fracField T).toIntermediateField halg := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ (⟨n, rfl⟩ | ⟨n, rfl⟩)
    · exact mem_fracField_of_mem T (zeta_mem_Lev T n)
    · exact mem_fracField_of_mem T (qq_mem_Lev T n)
  exact hle hxE

end GlobalTheory.FixFrac
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerGaloisFixedEqDivLevelElementsStatement
open GlobalTheory.K5 GlobalTheory.KumDlog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.towerGaloisFixed_eq_div_levelElements : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (x : Ω), (∀ h ∈ Hinf T, h x = x) →
  ∃ m : ℕ, ∃ a ∈ Lev T m, ∃ b ∈ Lev T m, b ≠ 0 ∧ x = a / b := by
  first | exact @GlobalTheory.FixFrac.fixed_eq_div | exact GlobalTheory.FixFrac.fixed_eq_div | (intros; apply GlobalTheory.FixFrac.fixed_eq_div <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KaehlerRelationDerivationModIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KaehlerRelationDerivationModIntegral
noncomputable section

open GlobalTheory.K5 GlobalTheory.KumDlog

namespace GlobalTheory.KumDlog

theorem kaehler_rel_isInt (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω]
    (n : ℕ) (ι : On p n →ₐ[O0 p] Ω) (S : Subalgebra (O0 p) Ω)
    (hS : ∀ x ∈ S, IsInt (p := p) x)
    (hι : ∀ x, ι x ∈ S) (D : Ω → Ω) (hD : GlobalTheory.KumDlog.IsDer S D) (a b c x y z : On p n)
    (hrel : a • KaehlerDifferential.D (O0 p) (On p n) x =
      b • KaehlerDifferential.D (O0 p) (On p n) y + c • KaehlerDifferential.D (O0 p) (On p n) z) :
    IsInt (p := p) (ι a * D (ι x) - ι b * D (ι y) - ι c * D (ι z)) := by
  letI : Module (On p n) Ω := Module.compHom Ω ι.toRingHom
  have hsm : ∀ (r : On p n) (w : Ω), r • w = ι r * w := fun _ _ => rfl
  haveI : IsScalarTower (O0 p) (On p n) Ω := ⟨fun r s w => by
    rw [hsm, hsm, map_smul, smul_mul_assoc]⟩
  let N : Submodule (On p n) Ω :=
    { carrier := {w | IsInt (p := p) w}
      add_mem' := fun ha hb => int_add ha hb
      zero_mem' := int_zero
      smul_mem' := fun r w hw => by
        show IsInt (p := p) (r • w)
        rw [hsm]; exact int_mul (hS _ (hι r)) hw }
  have memN : ∀ w, w ∈ N ↔ IsInt (p := p) w := fun _ => Iff.rfl
  have key : ∀ w w' : Ω, IsInt (p := p) (w - w') → N.mkQ w = N.mkQ w' := fun w w' h =>
    (Submodule.Quotient.eq N).2 h
  let L : On p n →ₗ[O0 p] Ω ⧸ N :=
    { toFun := fun u => N.mkQ (D (ι u))
      map_add' := fun u v => by
        rw [← map_add (f := _)]
        refine key _ _ ?_
        rw [map_add (f := _)]
        exact int_congr (hD.1 _ (hι u) _ (hι v)) (by ring)
      map_smul' := fun r u => by
        simp only [RingHom.id_apply]
        rw [← LinearMap.map_smul_of_tower]
        refine key _ _ ?_
        rw [map_smul, Algebra.smul_def, Algebra.smul_def]
        exact hD.alg_mul hS r (hι u) }
  let d : Derivation (O0 p) (On p n) (Ω ⧸ N) := Derivation.mk' L (fun u v => by
    show N.mkQ (D (ι (u * v))) = u • N.mkQ (D (ι v)) + v • N.mkQ (D (ι u))
    rw [← LinearMap.map_smul, ← LinearMap.map_smul, ← map_add (f := _)]
    refine key _ _ ?_
    rw [hsm, hsm, map_mul]
    exact int_congr (hD.2.1 _ (hι u) _ (hι v)) (by ring))
  have hd : ∀ u, d.liftKaehlerDifferential (KaehlerDifferential.D (O0 p) (On p n) u) =
      N.mkQ (D (ι u)) := fun u => by
    rw [Derivation.liftKaehlerDifferential_comp_D]; rfl
  have h2 := congrArg d.liftKaehlerDifferential hrel
  simp only [map_add (f := _), LinearMap.map_smul, hd] at h2
  rw [← LinearMap.map_smul, ← LinearMap.map_smul, ← LinearMap.map_smul, ← map_add (f := _),
    ← sub_eq_zero, ← map_sub, ← LinearMap.mem_ker, N.ker_mkQ, memN, hsm, hsm, hsm] at h2
  exact int_congr h2 (by ring)

end GlobalTheory.KumDlog
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KaehlerRelationDerivationModIntegralStatement
open GlobalTheory.K5 GlobalTheory.KumDlog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kaehler_relation_derivationModIntegral : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], ∀ (n : ℕ) (ι : On p n →ₐ[O0 p] Ω) (S : Subalgebra (O0 p) Ω), (∀ x ∈ S, IsInt (p := p) x) → (∀ x, ι x ∈ S) →
  ∀ D : Ω → Ω, IsDer S D → ∀ a b c x y z : On p n,
  a • KaehlerDifferential.D (O0 p) (On p n) x = b • KaehlerDifferential.D (O0 p) (On p n) y + c • KaehlerDifferential.D (O0 p) (On p n) z →
  IsInt (p := p) (ι a * D (ι x) - ι b * D (ι y) - ι c * D (ι z)) := by
  first | exact @GlobalTheory.KumDlog.kaehler_rel_isInt | exact GlobalTheory.KumDlog.kaehler_rel_isInt | (intros; apply GlobalTheory.KumDlog.kaehler_rel_isInt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivationModIntegralAlmostDualPSqIsInt
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivationModIntegralAlmostDualPSqIsInt
open GlobalTheory.K5 GlobalTheory.KumDlog

namespace GlobalTheory.KumDlog

theorem der_dual_p_sq_int : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
    ∀ (B C : Subalgebra (O0 p) Ω) (ι : Type) [Fintype ι] (u v : ι → Ω) (tr : Ω → Ω),
    DualData B C u v tr →
  ∀ D : Ω → Ω, IsDer C D → ∀ x ∈ C, (∀ k l, IsInt (p := p) (D (tr (u l * (x * v k))))) →
    IsInt (p := p) ((p : Ω) ^ 2 * D x) := by
  intro p _ Ω _ _ B C ι _ u v tr hd D hD x hx hT
  obtain ⟨hBC, hCi, hu, hv, htr, -, -, hsu, hsv, huv⟩ := hd
  have s1 : ∀ k, IsInt (p := p) ((p : Ω) * D (x * v k) - ∑ l, tr (u l * (x * v k)) * D (v l)) := by
    intro k
    have hy : x * v k ∈ C := mul_mem hx (hv k)
    have a1 := hD.alg_mul hCi (p : O0 p) hy
    simp only [map_natCast] at a1
    rw [← hsv _ hy] at a1
    have a2 := hD.sum Finset.univ (fun l => v l * tr (u l * (x * v k)))
      (fun l _ => mul_mem (hv l) (hBC (htr _ (mul_mem (hu l) hy))))
    have a3 : IsInt (p := p) (∑ l, D (v l * tr (u l * (x * v k))) -
        ∑ l, tr (u l * (x * v k)) * D (v l)) := by
      rw [← Finset.sum_sub_distrib]
      refine int_sum _ _ fun l _ => ?_
      have ht : tr (u l * (x * v k)) ∈ C := hBC (htr _ (mul_mem (hu l) hy))
      exact int_congr (int_add (hD.2.1 _ (hv l) _ ht) (int_mul (hCi _ (hv l)) (hT k l))) (by ring)
    exact int_congr (int_add (int_add (int_neg a1) a2) a3) (by ring)
  have e2 : ∀ l, ∑ k, u k * (tr (u l * (x * v k)) * D (v l)) = (p : Ω) * (x * (u l * D (v l))) := by
    intro l
    have h := hsu (x * u l) (mul_mem hx (hu l))
    calc ∑ k, u k * (tr (u l * (x * v k)) * D (v l))
        = (∑ k, u k * tr (v k * (x * u l))) * D (v l) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [show u l * (x * v k) = v k * (x * u l) by ring]; ring
      _ = _ := by rw [h]; ring
  have e : ∑ k, u k * ∑ l, tr (u l * (x * v k)) * D (v l) = (p : Ω) * (x * ∑ l, u l * D (v l)) := by
    calc _ = ∑ l, ∑ k, u k * (tr (u l * (x * v k)) * D (v l)) := by
            simp_rw [Finset.mul_sum]; exact Finset.sum_comm
      _ = ∑ l, (p : Ω) * (x * (u l * D (v l))) := Finset.sum_congr rfl fun l _ => e2 l
      _ = _ := by rw [Finset.mul_sum, Finset.mul_sum]
  have s2 : IsInt (p := p) ((p : Ω) * ∑ k, u k * D (x * v k) - (p : Ω) * (x * ∑ l, u l * D (v l))) := by
    have a : IsInt (p := p) (∑ k, u k * ((p : Ω) * D (x * v k) - ∑ l, tr (u l * (x * v k)) * D (v l))) :=
      int_sum _ _ fun k _ => int_mul (hCi _ (hu k)) (s1 k)
    refine int_congr a ?_
    rw [← e, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have s3 : IsInt (p := p) (∑ k, u k * D (x * v k) - x * ∑ k, u k * D (v k) - (p : Ω) * D x) := by
    have a : IsInt (p := p) (∑ k, u k * (D (x * v k) - x * D (v k) - v k * D x)) :=
      int_sum _ _ fun k _ => int_mul (hCi _ (hu k)) (hD.2.1 x hx (v k) (hv k))
    refine int_congr a ?_
    rw [← huv, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  exact int_congr (int_sub s2 (int_mul (int_nat p) s3)) (by ring)

end GlobalTheory.KumDlog
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivationModIntegralAlmostDualPSqIsIntStatement
open GlobalTheory.K5 GlobalTheory.KumDlog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivationModIntegral_almostDual_p_sq_isInt : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], ∀ (B C : Subalgebra (O0 p) Ω) (ι : Type) [Fintype ι] (u v : ι → Ω) (tr : Ω → Ω), DualData B C u v tr →
  ∀ D : Ω → Ω, IsDer C D → ∀ x ∈ C, (∀ k l, IsInt (p := p) (D (tr (u l * (x * v k))))) → IsInt (p := p) ((p : Ω) ^ 2 * D x) := by
  first | exact @GlobalTheory.KumDlog.der_dual_p_sq_int | exact GlobalTheory.KumDlog.der_dual_p_sq_int | (intros; apply GlobalTheory.KumDlog.der_dual_p_sq_int <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceTowerAlmostDualBasesAdjoinKummerRoot
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceTowerAlmostDualBasesAdjoinKummerRoot
noncomputable section

open GlobalTheory.K5 GlobalTheory.KumDlog

namespace GlobalTheory.TraceTower

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem eq_on_fix {T : Tower p Ω} {r : Ω} {h h' : Gal p Ω} (hh : h ∈ Hinf T) (hh' : h' ∈ Hinf T)
    (e : h r = h' r) {x : Ω} (hx : x ∈ FixI (Hfix T r)) : h x = h' x := by
  have hm : h'⁻¹ * h ∈ Hfix T r := by
    refine ⟨(Hinf T).mul_mem ((Hinf T).inv_mem hh') hh, ?_⟩
    refine MulAction.mem_stabilizer_iff.2 ?_
    rw [AlgEquiv.smul_def, AlgEquiv.mul_apply, e]
    exact h'.symm_apply_apply r
  have h1 : h'.symm (h x) = x := hx.2 _ hm
  exact h'.symm_apply_eq.1 h1

end GlobalTheory.TraceTower

open GlobalTheory.TraceTower in
theorem GlobalTheory.traceTower_dualData : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], ∀ (T : Tower p Ω) (n : ℕ) (r : Ω), IsInt (p := p) r → (∀ h ∈ Hinf T, ∃ i : ℕ, h r = T.ζ n ^ i * r) →
  ∀ (ι : Type) [Fintype ι] (u v : ι → Ω), (∀ k, u k ∈ FixI (Hfix T r)) → (∀ k, v k ∈ FixI (Hfix T r)) →
  ∑ k, u k * v k = (p : Ω) → (∀ h ∈ Hinf T, h r ≠ r → ∑ k, u k * h (v k) = 0) →
  ∃ tr : Ω → Ω, DualData (FixI (Hinf T)) (FixI (Hfix T r)) u v tr := by
  intro p _ Ω _ _ T n r _ hor ι _ u v hu hv huv hz
  classical
  have hfin : {ρ : Ω | ∃ h ∈ Hinf T, h r = ρ}.Finite := by
    refine ((Finset.range (p ^ n)).image (fun i => T.ζ n ^ i * r)).finite_toSet.subset ?_
    rintro ρ ⟨h, hh, rfl⟩
    obtain ⟨i, hi⟩ := hor h hh
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
    refine ⟨i % p ^ n, Nat.mod_lt _ (ppow_pos n), ?_⟩
    rw [hi]
    congr 1
    conv_rhs => rw [← Nat.div_add_mod i (p ^ n)]
    rw [pow_add, pow_mul, (T.prim n).pow_eq_one, one_pow, one_mul]
  set O := hfin.toFinset with hOdef
  have hO : ∀ ρ, ρ ∈ O ↔ ∃ h ∈ Hinf T, h r = ρ := fun ρ => hfin.mem_toFinset
  have hg0 : ∀ ρ, ∃ f : Gal p Ω, ρ ∈ O → f ∈ Hinf T ∧ f r = ρ := by
    intro ρ
    by_cases hρ : ρ ∈ O
    · obtain ⟨h, hh, e⟩ := (hO ρ).1 hρ
      exact ⟨h, fun _ => ⟨hh, e⟩⟩
    · exact ⟨1, fun h => absurd h hρ⟩
  choose g hg using hg0
  have hrO : r ∈ O := (hO r).2 ⟨1, (Hinf T).one_mem, rfl⟩
  have fixr : ∀ x ∈ FixI (Hfix T r), g r x = x := fun x hx =>
    hx.2 _ ⟨(hg r hrO).1, MulAction.mem_stabilizer_iff.2 (by rw [AlgEquiv.smul_def]; exact (hg r hrO).2)⟩
  have kk : ∀ f ∈ Hinf T, ∀ ρ ∈ O, ∀ x ∈ FixI (Hfix T r), f (g ρ x) = g (f ρ) x ∧ f ρ ∈ O := by
    intro f hf ρ hρ x hx
    have hm : f * g ρ ∈ Hinf T := (Hinf T).mul_mem hf (hg ρ hρ).1
    have hr' : (f * g ρ) r = f ρ := by rw [AlgEquiv.mul_apply, (hg ρ hρ).2]
    have hfO : f ρ ∈ O := (hO _).2 ⟨_, hm, hr'⟩
    refine ⟨?_, hfO⟩
    have := eq_on_fix hm (hg _ hfO).1 (by rw [hr', (hg _ hfO).2]) hx
    rwa [AlgEquiv.mul_apply] at this
  have zero_inv : ∀ ρ ∈ O, ρ ≠ r → ∑ k, v k * g ρ (u k) = 0 := by
    intro ρ hρ hne
    set f := g ρ
    have hf : f ∈ Hinf T := (hg ρ hρ).1
    have hne' : f⁻¹ r ≠ r := by
      intro e
      apply hne
      rw [← (hg ρ hρ).2]
      have e' : f.symm r = r := e
      conv_lhs => rw [← e']
      exact f.apply_symm_apply r
    have h0 := hz _ ((Hinf T).inv_mem hf) hne'
    calc ∑ k, v k * f (u k) = f (∑ k, u k * f⁻¹ (v k)) := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [map_mul]
          have : f (f⁻¹ (v k)) = v k := f.apply_symm_apply (v k)
          rw [this, mul_comm]
      _ = 0 := by rw [h0, map_zero]
  refine ⟨fun x => ∑ ρ ∈ O, g ρ x, fun x hx => ⟨hx.1, fun f hf => hx.2 f hf.1⟩, fun x hx => hx.1,
    hu, hv, ?_, ?_, ?_, ?_, ?_, huv⟩
  · intro x hx
    refine ⟨int_sum _ _ fun ρ _ => int_gal _ hx.1, fun f hf => ?_⟩
    show f (∑ ρ ∈ O, g ρ x) = ∑ ρ ∈ O, g ρ x
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    calc ∑ ρ ∈ O, f (g ρ x) = ∑ ρ ∈ O, g (f ρ) x :=
          Finset.sum_congr rfl fun ρ hρ => (kk f hf ρ hρ x hx).1
      _ = ∑ ρ ∈ O, g ρ x := by
        refine Finset.sum_nbij' (fun ρ => f ρ) (fun ρ => f.symm ρ) (fun ρ hρ => (kk f hf ρ hρ x hx).2)
          (fun ρ hρ => (kk f⁻¹ ((Hinf T).inv_mem hf) ρ hρ x hx).2) (fun ρ _ => f.symm_apply_apply ρ)
          (fun ρ _ => f.apply_symm_apply ρ) (fun ρ _ => rfl)
  · intro x _ y _
    simp only [map_add (f := _), Finset.sum_add_distrib]
  · intro b hb x _
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    rw [map_mul, hb.2 _ (hg ρ hρ).1]
  · intro y hy
    calc ∑ k, u k * ∑ ρ ∈ O, g ρ (v k * y) = ∑ ρ ∈ O, g ρ y * ∑ k, u k * g ρ (v k) := by
          simp only [map_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun k _ => by ring
      _ = g r y * ∑ k, u k * g r (v k) := by
          refine Finset.sum_eq_single r (fun ρ hρ hne => ?_) (fun h => absurd hrO h)
          rw [hz _ (hg ρ hρ).1 (by rw [(hg ρ hρ).2]; exact hne), mul_zero]
      _ = p * y := by
          rw [fixr y hy, Finset.sum_congr rfl fun k _ => by rw [fixr (v k) (hv k)], huv, mul_comm]
  · intro y hy
    calc ∑ k, v k * ∑ ρ ∈ O, g ρ (u k * y) = ∑ ρ ∈ O, g ρ y * ∑ k, v k * g ρ (u k) := by
          simp only [map_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun k _ => by ring
      _ = g r y * ∑ k, v k * g r (u k) := by
          refine Finset.sum_eq_single r (fun ρ hρ hne => ?_) (fun h => absurd hrO h)
          rw [zero_inv ρ hρ hne, mul_zero]
      _ = p * y := by
          rw [fixr y hy, Finset.sum_congr rfl fun k _ => by rw [fixr (u k) (hu k)], ← huv,
            mul_comm]
          congr 1
          exact Finset.sum_congr rfl fun k _ => mul_comm _ _
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceTowerAlmostDualBasesAdjoinKummerRootStatement
open GlobalTheory.K5 GlobalTheory.KumDlog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traceTower_almostDualBases_adjoin_kummer_root : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], ∀ (T : Tower p Ω) (n : ℕ) (r : Ω), IsInt (p := p) r → (∀ h ∈ Hinf T, ∃ i : ℕ, h r = T.ζ n ^ i * r) →
  ∀ (ι : Type) [Fintype ι] (u v : ι → Ω), (∀ k, u k ∈ FixI (Hfix T r)) → (∀ k, v k ∈ FixI (Hfix T r)) →
  ∑ k, u k * v k = (p : Ω) → (∀ h ∈ Hinf T, h r ≠ r → ∑ k, u k * h (v k) = 0) →
  ∃ tr : Ω → Ω, DualData (FixI (Hinf T)) (FixI (Hfix T r)) u v tr := by
  first | exact @GlobalTheory.traceTower_dualData | exact GlobalTheory.traceTower_dualData | (intros; apply GlobalTheory.traceTower_dualData <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDlogDerivationsGluedTowerLevels
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDlogDerivationsGluedTowerLevels
noncomputable section

namespace GlobalTheory.LevGlue

open GlobalTheory.K5 GlobalTheory.KumDlog

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem der_pow_val {S : Subalgebra (O0 p) Ω} {D : Ω → Ω} (hD : GlobalTheory.KumDlog.IsDer S D)
    (hS : ∀ x ∈ S, IsInt (p := p) x) (hp : (p : Ω) ≠ 0) {x c : Ω} {m j : ℕ} (hx : x ∈ S)
    (h : IsInt (p := p) (D x - c * x / (p : Ω) ^ (m + j))) :
    IsInt (p := p) (D (x ^ (p ^ j)) - c * x ^ (p ^ j) / (p : Ω) ^ m) := by
  obtain ⟨k, hk⟩ : ∃ k, p ^ j = k + 1 := ⟨p ^ j - 1, (Nat.succ_pred_eq_of_pos (ppow_pos j)).symm⟩
  have h1 := hD.pow hS hx k
  rw [← hk] at h1
  have e : c * x ^ (p ^ j) / (p : Ω) ^ m =
      ((p ^ j : ℕ) : Ω) * x ^ k * (c * x / (p : Ω) ^ (m + j)) := by
    have e1 : x ^ (p ^ j) = x ^ k * x := by rw [hk, pow_succ]
    have e2 : ((p ^ j : ℕ) : Ω) = (p : Ω) ^ j := by push_cast; ring
    rw [e1, e2, pow_add]
    field_simp
  refine int_congr (int_add h1 (int_mul (int_mul (int_nat (p ^ j)) (int_pow (hS x hx) k)) h)) ?_
  linear_combination (-1 : Ω) * e

theorem compat_gen (T : Tower p Ω) {m n : ℕ} (hmn : m ≤ n) {D D' : Ω → Ω}
    (hD : GlobalTheory.KumDlog.IsDer (Lev T n) D) (hD' : GlobalTheory.KumDlog.IsDer (Lev T m) D')
    (hz : IsInt (p := p) (D (T.ζ m) - D' (T.ζ m))) (hq : IsInt (p := p) (D (T.qq m) - D' (T.qq m))) :
    ∀ x ∈ Lev T m, IsInt (p := p) (D x - D' x) :=
  GlobalTheory.KumDlog.IsDer.adjoin (t := {T.ζ m, T.qq m}) (GlobalTheory.KumDlog.IsDer.sub (hD.mono (Lev_mono T hmn)) hD') (Lev_int T m)
    (by rintro x (rfl | rfl); exacts [zeta_mem_Lev T m, qq_mem_Lev T m])
    (by rintro x (rfl | rfl); exacts [hz, hq])

theorem vals_down (T : Tower p Ω) (hp : (p : Ω) ≠ 0) {m n : ℕ} (hmn : m ≤ n) {dz dq : Ω → Ω}
    (hz : GlobalTheory.KumDlog.IsDer (Lev T n) dz) (hq : GlobalTheory.KumDlog.IsDer (Lev T n) dq) (hv : GlobalTheory.KumDlog.Vals T n dz dq) : GlobalTheory.KumDlog.Vals T m dz dq := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have hS := Lev_int T (m + j)
  have zm := zeta_mem_Lev T (m + j)
  have qm := qq_mem_Lev T (m + j)
  have z0 : ∀ {D : Ω → Ω} {x : Ω}, IsInt (p := p) (D x) → IsInt (p := p) (D x - 0 * x / (p : Ω) ^ (m + j)) :=
    fun h => int_congr h (by ring)
  have z1 : ∀ {D : Ω → Ω} {y : Ω}, IsInt (p := p) (D y - 0 * y / (p : Ω) ^ m) → IsInt (p := p) (D y) :=
    fun h => int_congr h (by ring)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := der_pow_val hz hS hp zm hv.1
    rwa [zeta_pow] at this
  · have := z1 (der_pow_val hz hS hp qm (z0 hv.2.1))
    rwa [qq_pow] at this
  · have := z1 (der_pow_val hq hS hp zm (z0 hv.2.2.1))
    rwa [zeta_pow] at this
  · have := der_pow_val hq hS hp qm hv.2.2.2
    rwa [qq_pow] at this

theorem glue_fam (T : Tower p Ω) (F : ℕ → Ω → Ω) (hF : ∀ m, GlobalTheory.KumDlog.IsDer (Lev T (m + 1)) (F m))
    (hc : ∀ m n, m ≤ n → ∀ x ∈ Lev T (m + 1), IsInt (p := p) (F n x - F m x)) :
    ∃ G : Ω → Ω, (∀ m, ∀ x ∈ Lev T (m + 1), IsInt (p := p) (G x - F m x)) ∧
      ∀ S : Subalgebra (O0 p) Ω, (∀ x ∈ S, ∃ m, x ∈ Lev T m) → GlobalTheory.KumDlog.IsDer S G := by
  classical
  let M : Ω → ℕ := fun x => if h : ∃ m, x ∈ Lev T (m + 1) then Classical.choose h else 0
  have hG : ∀ m, ∀ x ∈ Lev T (m + 1), IsInt (p := p) (F (M x) x - F m x) := by
    intro m x hx
    have h : ∃ m, x ∈ Lev T (m + 1) := ⟨m, hx⟩
    have hM : M x = Classical.choose h := dif_pos h
    have ha := Classical.choose_spec h
    rw [hM]
    have h1 := hc _ (max m (Classical.choose h)) (le_max_right _ _) x ha
    have h2 := hc _ (max m (Classical.choose h)) (le_max_left _ _) x hx
    exact int_congr (int_sub h2 h1) (by ring)
  refine ⟨fun x => F (M x) x, hG, fun S hS => ?_⟩
  have two : ∀ x ∈ S, ∀ y ∈ S, ∃ n, x ∈ Lev T (n + 1) ∧ y ∈ Lev T (n + 1) := by
    intro x hx y hy
    obtain ⟨a, ha⟩ := hS x hx
    obtain ⟨b, hb⟩ := hS y hy
    exact ⟨a + b, Lev_mono T (by omega) ha, Lev_mono T (by omega) hb⟩
  refine ⟨fun x hx y hy => ?_, fun x hx y hy => ?_, fun c => ?_⟩
  · obtain ⟨n, hxn, hyn⟩ := two x hx y hy
    refine int_congr (int_add (int_add (int_sub (int_sub ((hF n).1 x hxn y hyn)
      (hG n x hxn)) (hG n y hyn)) (hG n _ (add_mem hxn hyn))) int_zero) ?_
    ring
  · obtain ⟨n, hxn, hyn⟩ := two x hx y hy
    have ix := Lev_int T _ x hxn
    have iy := Lev_int T _ y hyn
    refine int_congr (int_sub (int_sub (int_add ((hF n).2.1 x hxn y hyn)
      (hG n _ (mul_mem hxn hyn))) (int_mul ix (hG n y hyn))) (int_mul iy (hG n x hxn))) ?_
    ring
  · have hm := (Lev T (0 + 1)).algebraMap_mem c
    exact int_congr (int_add (hG 0 _ hm) ((hF 0).2.2 c)) (by ring)

theorem glue : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ (T : Tower p Ω) (B : Subalgebra (O0 p) Ω), (∀ x ∈ B, ∃ m : ℕ, x ∈ Lev T m) →
    (∀ m : ℕ, 1 ≤ m → ∃ dz dq : Ω → Ω, GlobalTheory.KumDlog.IsDer (Lev T m) dz ∧ GlobalTheory.KumDlog.IsDer (Lev T m) dq ∧ GlobalTheory.KumDlog.Vals T m dz dq) →
    ∃ dz dq : Ω → Ω, GlobalTheory.KumDlog.IsDer B dz ∧ GlobalTheory.KumDlog.IsDer B dq ∧ ∀ m : ℕ, 1 ≤ m → GlobalTheory.KumDlog.Vals T m dz dq := by
  intro p _ Ω _ _ hclo T B hB hlev
  haveI : CharZero Ω := GlobalTheory.K5.Basic.charZero_of_isClo hclo
  have hp : (p : Ω) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have h' : ∀ m : ℕ, ∃ dz dq : Ω → Ω, GlobalTheory.KumDlog.IsDer (Lev T (m + 1)) dz ∧ GlobalTheory.KumDlog.IsDer (Lev T (m + 1)) dq ∧
      GlobalTheory.KumDlog.Vals T (m + 1) dz dq := fun m => hlev (m + 1) (by omega)
  choose Z Q hZ hQ hV using h'
  have cZ : ∀ m n, m ≤ n → ∀ x ∈ Lev T (m + 1), IsInt (p := p) (Z n x - Z m x) := by
    intro m n hmn
    have v := vals_down T hp (by omega : m + 1 ≤ n + 1) (hZ n) (hQ n) (hV n)
    exact compat_gen T (by omega : m + 1 ≤ n + 1) (hZ n) (hZ m)
      (int_congr (int_sub v.1 (hV m).1) (by ring)) (int_congr (int_sub v.2.1 (hV m).2.1) (by ring))
  have cQ : ∀ m n, m ≤ n → ∀ x ∈ Lev T (m + 1), IsInt (p := p) (Q n x - Q m x) := by
    intro m n hmn
    have v := vals_down T hp (by omega : m + 1 ≤ n + 1) (hZ n) (hQ n) (hV n)
    exact compat_gen T (by omega : m + 1 ≤ n + 1) (hQ n) (hQ m)
      (int_congr (int_sub v.2.2.1 (hV m).2.2.1) (by ring))
      (int_congr (int_sub v.2.2.2 (hV m).2.2.2) (by ring))
  obtain ⟨dz, hdz, hdzB⟩ := glue_fam T Z hZ cZ
  obtain ⟨dq, hdq, hdqB⟩ := glue_fam T Q hQ cQ
  refine ⟨dz, dq, hdzB B hB, hdqB B hB, fun m hm => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have v := hV k
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact int_congr (int_add (hdz k _ (zeta_mem_Lev T _)) v.1) (by ring)
  · exact int_congr (int_add (hdz k _ (qq_mem_Lev T _)) v.2.1) (by ring)
  · exact int_congr (int_add (hdq k _ (zeta_mem_Lev T _)) v.2.2.1) (by ring)
  · exact int_congr (int_add (hdq k _ (qq_mem_Lev T _)) v.2.2.2) (by ring)

end GlobalTheory.LevGlue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDlogDerivationsGluedTowerLevelsStatement
open GlobalTheory.K5 GlobalTheory.KumDlog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dlog_derivations_glued_tower_levels : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (B : Subalgebra (O0 p) Ω), (∀ x ∈ B, ∃ m : ℕ, x ∈ Lev T m) →
  (∀ m : ℕ, 1 ≤ m → ∃ dz dq : Ω → Ω, IsDer (Lev T m) dz ∧ IsDer (Lev T m) dq ∧ Vals T m dz dq) →
  ∃ dz dq : Ω → Ω, IsDer B dz ∧ IsDer B dq ∧ ∀ m : ℕ, 1 ≤ m → Vals T m dz dq := by
  first | exact @GlobalTheory.LevGlue.glue | exact GlobalTheory.LevGlue.glue | (intros; apply GlobalTheory.LevGlue.glue <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCochainEqDlogCombinationFiniteLevel
open GlobalTheory.K5

noncomputable section
namespace GlobalTheory.KumDlog
variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem emb_mem_Lev {T : Tower p Ω} {n : ℕ} {ι : On p n →ₐ[O0 p] Ω} (hΩ : IsClo p Ω) (hn : 1 ≤ n)
    (hι : IsEmb T n ι) (x : On p n) : ι x ∈ Lev T n := by
  rw [← (GlobalTheory.T.towerLevelEmbedding_injective_range_adjoinRoots p Ω hΩ T n hn ι hι).2]; exact ⟨x, rfl⟩

theorem p_ne (T : Tower p Ω) : (p : Ω) ≠ 0 := by
  have h := (T.prim 1).neZero'
  have := h.ne
  simpa using this

theorem conj_mem_Hinf {T : Tower p Ω} {n : ℕ} {lz lq : Gal p Ω → ZMod (p ^ n)}
    (hz : IsKum T n (Gn T n) (T.ζ (2 * n)) lz) (hq : IsKum T n (Gn T n) (T.qq (2 * n)) lq)
    {g h : Gal p Ω} (hg : g ∈ Gn T n) (hh : h ∈ Hinf T) : g⁻¹ * h * g ∈ Hinf T := by
  rw [mem_Hinf] at hh ⊢
  intro m
  obtain ⟨i, j, -, -, e1, e2, -⟩ := GlobalTheory.T.towerGn_exponents_kummer_cochains p Ω T n (m + 2 * n) (by omega) lz lq hz hq g hg
  have k1 : (g⁻¹ * h * g) (T.ζ (m + 2 * n)) = T.ζ (m + 2 * n) := by
    show g.symm (h (g _)) = _
    rw [AlgEquiv.symm_apply_eq, e1, map_pow, (hh _).1]
  have k2 : (g⁻¹ * h * g) (T.qq (m + 2 * n)) = T.qq (m + 2 * n) := by
    show g.symm (h (g _)) = _
    rw [AlgEquiv.symm_apply_eq, e2, map_mul, map_pow, (hh _).1, (hh _).2]
  constructor
  · rw [← zeta_pow T m (2 * n), map_pow, k1]
  · rw [← qq_pow T m (2 * n), map_pow, k2]

theorem gal_mem_fix {T : Tower p Ω} {n : ℕ} {a lz lq : Gal p Ω → ZMod (p ^ n)} {r : Ω}
    (ha : IsKum T n (Gn T n) r a)
    (hz : IsKum T n (Gn T n) (T.ζ (2 * n)) lz) (hq : IsKum T n (Gn T n) (T.qq (2 * n)) lq)
    {g : Gal p Ω} (hg : g ∈ Gn T n) : ∀ x ∈ FixI (Hfix T r), g x ∈ FixI (Hfix T r) := by
  intro x hx
  refine ⟨int_gal g hx.1, fun h hh => ?_⟩
  have h1 : g⁻¹ * h * g ∈ Hfix T r := by
    refine ⟨conj_mem_Hinf hz hq hg hh.1, ?_⟩
    show g.symm (h (g r)) = r
    have h2 : h r = r := hh.2
    rw [AlgEquiv.symm_apply_eq, ha g hg, map_mul, map_pow, h2, (mem_Hinf.1 hh.1 n).1]
  have h3 : g.symm (h (g x)) = x := hx.2 _ h1
  rwa [AlgEquiv.symm_apply_eq] at h3

theorem fix_mem_Lev (hΩ : IsClo p Ω) (T : Tower p Ω) :
    ∀ x ∈ FixI (Hinf T), ∃ m : ℕ, x ∈ Lev T m := by
  intro x hx
  obtain ⟨m, a, ha, b, hb, hb0, rfl⟩ := GlobalTheory.T.towerGaloisFixed_eq_div_levelElements p Ω hΩ T x hx.2
  exact ⟨m + 1, GlobalTheory.T.towerLevelAdjoinRoots_integrallyClosed_quotient p Ω hΩ T (m + 1) (by omega) a (Lev_mono T (by omega) ha) b
    (Lev_mono T (by omega) hb) hb0 hx.1⟩

theorem der_zeta_pow {T : Tower p Ω} {C : Subalgebra (O0 p) Ω} {D : Ω → Ω} (hD : IsDer C D)
    (hC : ∀ x ∈ C, IsInt (p := p) x) {m : ℕ} (hm : T.ζ m ∈ C) {e : Ω}
    (he : IsInt (p := p) (D (T.ζ m) - e * T.ζ m)) (i : ℕ) :
    IsInt (p := p) (D (T.ζ m ^ i) - i * e * T.ζ m ^ i) := by
  have h1 := int_mul (int_zeta_inv T m) (int_add (hD.pow' hC hm i)
    (int_mul (int_mul (int_nat i) (int_pow (int_zeta T m) i)) he))
  refine int_congr h1 ?_
  have := zeta_ne T m
  field_simp
  ring

theorem exists_ders (hp2 : p ≠ 2) (hΩ : IsClo p Ω) (T : Tower p Ω) (n : ℕ) (hn : 1 ≤ n) {r : Ω}
    (hr : IsInt (p := p) r) {a lz lq : Gal p Ω → ZMod (p ^ n)} (ha : IsKum T n (Gn T n) r a)
    (hz : IsKum T n (Gn T n) (T.ζ (2 * n)) lz) (hq : IsKum T n (Gn T n) (T.qq (2 * n)) lq) :
    ∃ Dz Dq : Ω → Ω, IsDer (FixI (Hfix T r)) Dz ∧ IsDer (FixI (Hfix T r)) Dq ∧
      IsInt (p := p) (Dz (T.ζ n) - (p : Ω) ^ 4 / p ^ n * T.ζ n) ∧ IsInt (p := p) (Dz (T.qq n)) ∧
      IsInt (p := p) (Dq (T.ζ n)) ∧ IsInt (p := p) (Dq (T.qq n) - (p : Ω) ^ 4 / p ^ n * T.qq n) ∧
      ∀ g ∈ Gn T n, ∃ s t : ℤ, IsInt (p := p) ((p : Ω) ^ 2 * (Dz (g r) -
        (1 + p ^ n * ((lz g).val : Ω) + p ^ (2 * n) * s) * g (Dz r) -
        (p ^ n * ((lq g).val : Ω) + p ^ (2 * n) * t) * g (Dq r))) := by
  have hH : ∀ h ∈ Hinf T, ∃ i : ℕ, h r = T.ζ n ^ i * r := fun h hh => ⟨_, ha h (Hinf_le T n hh)⟩
  obtain ⟨ι, _, u, v, hu, hv, huv, h0⟩ := GlobalTheory.T.exists_almostGalois_coordinates p hp2 Ω hΩ T n r hr hH
  obtain ⟨tr, hd⟩ := GlobalTheory.T.traceTower_almostDualBases_adjoin_kummer_root p Ω T n r hr hH ι u v hu hv huv h0
  obtain ⟨dz, dq, hdz, hdq, hval⟩ := GlobalTheory.T.exists_dlog_derivations_glued_tower_levels p Ω hΩ T _ (fix_mem_Lev hΩ T)
    (fun m hm => GlobalTheory.T.exists_dlog_derivations_towerLevel_mod_integral p Ω hΩ T m hm)
  obtain ⟨Dz, hDz, ez⟩ := GlobalTheory.T.exists_derivationModIntegral_extension_p_cube p Ω _ _ ι u v tr hd dz hdz
  obtain ⟨Dq, hDq, eq⟩ := GlobalTheory.T.exists_derivationModIntegral_extension_p_cube p Ω _ _ ι u v tr hd dq hdq
  have hC := hd.2.1
  have hLB : ∀ m, Lev T m ≤ FixI (Hinf T) := fun m => Lev_le_FixI T m (Hinf_le T m)
  have p3 : IsInt (p := p) ((p : Ω) ^ 3) := int_pow (int_nat p) 3
  have V : ∀ m, 1 ≤ m → IsInt (p := p) (Dz (T.ζ m) - (p : Ω) ^ 4 / p ^ m * T.ζ m) ∧ IsInt (p := p) (Dz (T.qq m)) ∧
      IsInt (p := p) (Dq (T.ζ m)) ∧ IsInt (p := p) (Dq (T.qq m) - (p : Ω) ^ 4 / p ^ m * T.qq m) := by
    intro m hm
    obtain ⟨v1, v2, v3, v4⟩ := hval m hm
    have z := hLB m (zeta_mem_Lev T m)
    have q := hLB m (qq_mem_Lev T m)
    exact ⟨int_congr (int_add (ez _ z) (int_mul p3 v1)) (by ring),
      int_congr (int_add (ez _ q) (int_mul p3 v2)) (by ring),
      int_congr (int_add (eq _ z) (int_mul p3 v3)) (by ring),
      int_congr (int_add (eq _ q) (int_mul p3 v4)) (by ring)⟩
  obtain ⟨w1, w2, w3, w4⟩ := V n hn
  refine ⟨Dz, Dq, hDz, hDq, w1, w2, w3, w4, fun g hg => ?_⟩
  have hrC : r ∈ FixI (Hfix T r) := ⟨hr, fun h hh => hh.2⟩
  have hex : ∀ kl : ι × ι, ∃ m, tr (u kl.2 * (r * v kl.1)) ∈ Lev T m := fun kl =>
    fix_mem_Lev hΩ T _ (hd.2.2.2.2.1 _ (mul_mem (hu _) (mul_mem hrC (hv _))))
  choose M hM using hex
  obtain ⟨m, hm2, hmM⟩ : ∃ m, 2 * n ≤ m ∧ ∀ kl, M kl ≤ m :=
    ⟨max (2 * n) (Finset.univ.sup M), le_max_left _ _, fun kl =>
      le_trans (Finset.le_sup (f := M) (Finset.mem_univ kl)) (le_max_right _ _)⟩
  obtain ⟨i, j, s, t, e1, e2, hi, hj⟩ := GlobalTheory.T.towerGn_exponents_kummer_cochains p Ω T n m hm2 lz lq hz hq g hg
  obtain ⟨y1, y2, y3, y4⟩ := V m (by omega)
  have zC := hd.1 (hLB m (zeta_mem_Lev T m))
  have qC := hd.1 (hLB m (qq_mem_Lev T m))
  have hD' := ((hDz.conj g (gal_mem_fix ha hz hq hg)).sub (hDz.smul (int_nat i))).sub
    (hDq.smul (int_nat j))
  have hvan := hD'.adjoin hC (t := {T.ζ m, T.qq m}) (by rintro x (rfl | rfl); exacts [zC, qC]) (by
    rintro x (rfl | rfl)
    · have a1 := int_gal g.symm (der_zeta_pow hDz hC zC y1 i)
      rw [← e1] at a1
      refine int_congr (int_sub (int_sub a1 (int_mul (int_nat i) y1)) (int_mul (int_nat j) y3)) ?_
      simp only [map_sub, map_mul, map_div₀, map_pow, map_natCast, AlgEquiv.symm_apply_apply]
      ring
    · have a1 := int_add (int_add (hDz.2.1 _ (pow_mem zC j) _ qC)
        (int_mul (int_pow (int_zeta T m) j) y2)) (int_mul (int_qq T m) (der_zeta_pow hDz hC zC y1 j))
      have a2 : IsInt (p := p) (Dz (g (T.qq m)) - j * ((p : Ω) ^ 4 / p ^ m) * g (T.qq m)) := by
        rw [e2]; exact int_congr a1 (by ring)
      have a3 := int_gal g.symm a2
      refine int_congr (int_sub (int_sub a3 (int_mul (int_nat i) y2)) (int_mul (int_nat j) y4)) ?_
      simp only [map_sub, map_mul, map_div₀, map_pow, map_natCast, AlgEquiv.symm_apply_apply]
      ring)
  have hU := GlobalTheory.T.derivationModIntegral_almostDual_p_sq_isInt p Ω _ _ ι u v tr hd _ hD' r hrC
    (fun k l => hvan _ (Lev_mono T (hmM (k, l)) (hM (k, l))))
  refine ⟨s, t, int_congr (int_gal g hU) ?_⟩
  have hi' : (i : Ω) = 1 + p ^ n * ((lz g).val : Ω) + p ^ (2 * n) * s := by
    have := congrArg (Int.cast : ℤ → Ω) hi
    push_cast at this
    simpa using this
  have hj' : (j : Ω) = p ^ n * ((lq g).val : Ω) + p ^ (2 * n) * t := by
    have := congrArg (Int.cast : ℤ → Ω) hj
    push_cast at this
    simpa using this
  rw [← hi', ← hj']
  simp only [map_sub, map_mul, map_pow, map_natCast, AlgEquiv.apply_symm_apply]

theorem core (hp2 : p ≠ 2) (hΩ : IsClo p Ω) (T : Tower p Ω) (n : ℕ) (hn : 1 ≤ n)
    (ι : On p n →ₐ[O0 p] Ω) (hι : IsEmb T n ι) (u A B : On p n)
    (hrel : (xn p n * yn p n) • KaehlerDifferential.D (O0 p) (On p n) u =
      (xn p n * A) • KaehlerDifferential.D (O0 p) (On p n) (yn p n) +
      (yn p n * B) • KaehlerDifferential.D (O0 p) (On p n) (xn p n))
    {r : Ω} (hr : r ^ (p ^ n) = ι u) {a lz lq : Gal p Ω → ZMod (p ^ n)}
    (ha : IsKum T n (Gn T n) r a)
    (hz : IsKum T n (Gn T n) (T.ζ (2 * n)) lz) (hq : IsKum T n (Gn T n) (T.qq (2 * n)) lq) :
    Cob1 n (Gn T n) (fun g => (p : Ω) ^ 6 *
      (ι u * ((a g).val : Ω) - ι A * ((lq g).val : Ω) - ι B * ((lz g).val : Ω))) := by
  have hL := emb_mem_Lev hΩ hn hι
  have hI : ∀ x, IsInt (p := p) (ι x) := fun x => Lev_int T n _ (hL x)
  have hrI : IsInt (p := p) r := int_of_pow (ppow_pos n) (hr ▸ hI u)
  obtain ⟨Dz, Dq, hDz, hDq, w1, w2, w3, w4, hE⟩ := exists_ders hp2 hΩ T n hn hrI ha hz hq
  have hC : ∀ x ∈ FixI (Hfix T r), IsInt (p := p) x := fun x hx => hx.1
  have hLC : Lev T n ≤ FixI (Hfix T r) := Lev_le_FixI T n (le_trans inf_le_left (Hinf_le T n))
  have hrC : r ∈ FixI (Hfix T r) := ⟨hrI, fun h hh => hh.2⟩
  have kz := GlobalTheory.T.kaehler_relation_derivationModIntegral p Ω n ι _ hC (fun x => hLC (hL x)) Dz hDz _ _ _ _ _ _ hrel
  have kq := GlobalTheory.T.kaehler_relation_derivationModIntegral p Ω n ι _ hC (fun x => hLC (hL x)) Dq hDq _ _ _ _ _ _ hrel
  simp only [map_mul, hι.1, hι.2] at kz kq
  have z0 := zeta_ne T n
  have q0 := qq_ne T n
  have p0 := p_ne T
  have inv := int_mul (int_zeta_inv T n) (int_qq_inv T n)
  obtain ⟨N, hN⟩ : ∃ N, p ^ n = N + 1 := ⟨p ^ n - 1, by have := ppow_pos (p := p) n; omega⟩
  have hN' : ((N + 1 : ℕ) : Ω) = (p : Ω) ^ n := by rw [← hN]; push_cast; rfl
  have pz := hDz.pow hC hrC N
  have pq := hDq.pow hC hrC N
  rw [hN', ← hN, hr] at pz pq
  have Ez : IsInt (p := p) ((p : Ω) ^ n * (r ^ N * Dz r) - ι B * (p ^ 4 / p ^ n)) := by
    refine int_congr (int_sub (int_mul inv (int_add (int_add kz
      (int_mul (int_mul (int_zeta T n) (hI A)) w2)) (int_mul (int_mul (int_qq T n) (hI B)) w1))) pz) ?_
    field_simp
    ring
  have Eq : IsInt (p := p) ((p : Ω) ^ n * (r ^ N * Dq r) - ι A * (p ^ 4 / p ^ n)) := by
    refine int_congr (int_sub (int_mul inv (int_add (int_add kq
      (int_mul (int_mul (int_zeta T n) (hI A)) w4)) (int_mul (int_mul (int_qq T n) (hI B)) w3))) pq) ?_
    field_simp
    ring
  have p2 : IsInt (p := p) ((p : Ω) ^ 2) := int_pow (int_nat p) 2
  refine ⟨_, int_mul p2 Ez, fun g hg => ?_⟩
  obtain ⟨s, t, hst⟩ := hE g hg
  have hfix : ∀ x, g (ι x) = ι x := fun x => (Lev_le_FixI T n le_rfl (hL x)).2 g hg
  have zC := hLC (zeta_mem_Lev T n)
  have b1 := int_add (hDz.2.1 _ (pow_mem zC (a g).val) _ hrC)
    (int_mul hrI (der_zeta_pow hDz hC zC w1 (a g).val))
  rw [← ha g hg] at b1
  have b2 := int_mul (int_pow (int_gal g hrI) N) (int_sub hst (int_mul p2 b1))
  have gz := int_gal g Ez
  have gq := int_gal g Eq
  have pn : IsInt (p := p) ((p : Ω) ^ n) := int_pow (int_nat p) n
  have p6 : IsInt (p := p) ((p : Ω) ^ 6) := int_pow (int_nat p) 6
  refine ⟨_, int_add (int_add (int_add (int_add b2
    (int_mul (int_mul (int_add (int_nat (lz g).val) (int_mul pn (int_int s))) p2) gz))
    (int_mul (int_mul (int_add (int_nat (lq g).val) (int_mul pn (int_int t))) p2) gq))
    (int_mul (int_mul p6 (hI B)) (int_int s))) (int_mul (int_mul p6 (hI A)) (int_int t)), ?_⟩
  simp only [map_sub, map_mul, map_div₀, map_pow, map_natCast, hfix]
  have c1 : g r ^ N * T.ζ n ^ (a g).val = r ^ N := by
    rw [ha g hg, mul_pow, mul_right_comm, ← pow_succ, ← hN, ← pow_mul, mul_comm (a g).val, pow_mul,
      (T.prim n).pow_eq_one, one_pow, one_mul]
  have c2 : r ^ N * r = ι u := by rw [← pow_succ, ← hN, hr]
  rw [two_mul, pow_add]
  have hQ : (p : Ω) ^ n * ((p : Ω) ^ 4 / (p : Ω) ^ n) = (p : Ω) ^ 4 :=
    mul_div_cancel₀ _ (pow_ne_zero _ p0)
  generalize (p : Ω) ^ 4 / (p : Ω) ^ n = Q at *
  generalize (p : Ω) ^ n = P at *
  linear_combination (-(p : Ω) ^ 2 * P * Dz r - (p : Ω) ^ 6 * r * ((a g).val : Ω)) * c1 -
    (p : Ω) ^ 6 * ((a g).val : Ω) * c2 +
    (-(p : Ω) ^ 2 * r * ((a g).val : Ω) * (g r ^ N * T.ζ n ^ (a g).val) +
      (((lz g).val : Ω) + P * s) * (p : Ω) ^ 2 * ι B + (((lq g).val : Ω) + P * t) * (p : Ω) ^ 2 * ι A) * hQ

theorem exists_kum (T : Tower p Ω) (n : ℕ) {r : Ω} (hr : r ≠ 0)
    (h : ∀ g ∈ Gn T n, g (r ^ (p ^ n)) = r ^ (p ^ n)) : ∃ a, IsKum T n (Gn T n) r a := by
  haveI : NeZero (p ^ n) := ⟨(ppow_pos n).ne'⟩
  have : ∀ g : Gal p Ω, ∃ i : ZMod (p ^ n), g ∈ Gn T n → g r = T.ζ n ^ i.val * r := by
    intro g
    by_cases hg : g ∈ Gn T n
    · obtain ⟨i, hi, e⟩ := (T.prim n).eq_pow_of_pow_eq_one (ξ := g r / r) (by
        rw [div_pow, ← map_pow, h g hg, div_self (pow_ne_zero _ hr)])
      refine ⟨i, fun _ => ?_⟩
      rw [ZMod.val_cast_of_lt hi, e, div_mul_cancel₀ _ hr]
    · exact ⟨0, fun h => absurd h hg⟩
  choose a ha using this
  exact ⟨a, fun g hg => ha g hg⟩

theorem kummer_eq_dlog : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (n : ℕ), 1 ≤ n → ∀ ι : On p n →ₐ[O0 p] Ω, IsEmb T n ι →
  ∀ (k : ℤ) (w : (On p n)ˣ) (α β : On p n), IsDlog p n (w : On p n) α β →
  ∀ r : Ω, r ^ (p ^ n) = (T.ζ n - 1) ^ k * ι w →
  ∀ a lz lq : Gal p Ω → ZMod (p ^ n), IsKum T n (Gn T n) r a →
    IsKum T n (Gn T n) (T.ζ (2 * n)) lz → IsKum T n (Gn T n) (T.qq (2 * n)) lq →
    Cob1 n (Gn T n) (fun g => (p : Ω) ^ c * ((a g).val : Ω) - (p : Ω) ^ c * ι α * ((lq g).val : Ω) -
      (p : Ω) ^ c * (ι β + (k : Ω) * T.ζ n / (T.ζ n - 1)) * ((lz g).val : Ω)) := by
  intro p _ hp2
  refine ⟨7, ?_⟩
  intro Ω _ _ hΩ T n hn ι hι k w α β hd r hr a lz lq ha hz hq
  haveI := hΩ.clo
  have hL := emb_mem_Lev hΩ hn hι
  have hI : ∀ x, IsInt (p := p) (ι x) := fun x => Lev_int T n _ (hL x)
  have hfix : ∀ g ∈ Gn T n, ∀ x, g (ι x) = ι x := fun g hg x =>
    (Lev_le_FixI T n le_rfl (hL x)).2 g hg
  have hπ : T.ζ n - 1 ≠ 0 := sub_ne_zero.2 ((T.prim n).ne_one
    (Nat.one_lt_pow (by omega) (Fact.out : p.Prime).one_lt))
  have hww : ι w * ι (↑w⁻¹ : On p n) = 1 := by rw [← map_mul]; simp
  have hw0 : ι w ≠ 0 := left_ne_zero_of_mul_eq_one hww
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (T.ζ n - 1) (ppow_pos (p := p) n)
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hπ (by rw [← hs, zero_pow (ppow_pos (p := p) n).ne'])
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [zero_pow (ppow_pos (p := p) n).ne'] at hr
    exact mul_ne_zero (zpow_ne_zero k hπ) hw0 hr.symm
  have hr' : (r / s ^ k) ^ (p ^ n) = ι w := by
    rw [div_pow, hr, ← zpow_natCast, ← zpow_mul, mul_comm k, zpow_mul, zpow_natCast, hs,
      mul_div_cancel_left₀ _ (zpow_ne_zero k hπ)]
  have hs' : s ^ (p ^ n) = ι (xn p n - 1) := by rw [hs, map_sub, hι.1, map_one]
  have hr0' : r / s ^ k ≠ 0 := div_ne_zero hr0 (zpow_ne_zero k hs0)
  obtain ⟨b, hb⟩ := exists_kum T n hs0 (fun g hg => by rw [hs', hfix g hg])
  obtain ⟨a', ha'⟩ := exists_kum T n hr0' (fun g hg => by rw [hr', hfix g hg])
  obtain ⟨x1, i1, e1⟩ := core hp2 hΩ T n hn ι hι w (w * α) (w * β) (by
    rw [hd, mul_left_comm, mul_left_comm (yn p n), mul_assoc, mul_assoc]) hr' ha' hz hq
  obtain ⟨x2, i2, e2⟩ := core hp2 hΩ T n hn ι hι (xn p n - 1) 0 (xn p n) (by
    simp [mul_comm]) hs' hb hz hq
  have hpπ : IsInt (p := p) ((p : Ω) / (T.ζ n - 1)) := by
    simpa using GlobalTheory.T.isInt_prime_div_rootOfUnity_sub_one_pow p Ω T n 1 hn (Nat.totient_pos.2 (ppow_pos n))
  have j1 := int_mul (int_nat (Ω := Ω) (p := p) p) (hI (↑w⁻¹ : On p n))
  have j2 := int_mul (int_int (Ω := Ω) (p := p) k) hpπ
  refine ⟨_, int_add (int_mul j1 i1) (int_mul j2 i2), fun g hg => ?_⟩
  obtain ⟨z1, l1, f1⟩ := e1 g hg
  obtain ⟨z2, l2, f2⟩ := e2 g hg
  have z0 := zeta_ne T n
  have hdvd : ((p ^ n : ℕ) : ℤ) ∣ ((a g).val : ℤ) - (a' g).val - k * (b g).val := by
    rw [← (T.prim n).zpow_eq_one_iff_dvd]
    have h1 := ha' g hg
    rw [map_div₀, map_zpow₀, ha g hg, hb g hg, mul_zpow, mul_div_mul_comm,
      mul_left_inj' hr0'] at h1
    rw [zpow_sub₀ z0, zpow_sub₀ z0, mul_comm k, zpow_mul]
    simp only [zpow_natCast]
    rw [div_right_comm, h1, div_self (pow_ne_zero _ z0)]
  obtain ⟨t, ht⟩ := hdvd
  have ht' : ((a g).val : Ω) - (a' g).val - k * (b g).val = (p : Ω) ^ n * t := by
    have := congrArg (Int.cast : ℤ → Ω) ht
    simpa only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Nat.cast_pow, Int.cast_pow] using this
  refine ⟨_, int_add (int_add (int_mul j1 l1) (int_mul j2 l2))
    (int_mul (int_pow (int_nat p) 7) (int_int t)), ?_⟩
  simp only [map_add (f := _), map_sub, map_mul, map_div₀, map_natCast, map_intCast, map_one, map_zero,
    hfix g hg, hι.1, (mem_Gn.1 hg).1] at f1 f2 ⊢
  have hinv : (T.ζ n - 1) * (T.ζ n - 1)⁻¹ = 1 := mul_inv_cancel₀ hπ
  simp only [div_eq_mul_inv]
  generalize (T.ζ n - 1)⁻¹ = V at *
  linear_combination ((p : Ω) * ι (↑w⁻¹ : On p n)) * f1 + ((k : Ω) * (p * V)) * f2 + (p : Ω) ^ 7 * ht' -
    (p : Ω) ^ 7 * (((a' g).val : Ω) - ι α * ((lq g).val : Ω) - ι β * ((lz g).val : Ω)) * hww -
    (p : Ω) ^ 7 * k * ((b g).val : Ω) * hinv

end GlobalTheory.KumDlog
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCochainEqDlogCombinationFiniteLevelStatement
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerCochain_eq_dlog_combination_finiteLevel : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (n : ℕ), 1 ≤ n → ∀ ι : On p n →ₐ[O0 p] Ω, IsEmb T n ι →
  ∀ (k : ℤ) (w : (On p n)ˣ) (α β : On p n), IsDlog p n (w : On p n) α β →
  ∀ r : Ω, r ^ (p ^ n) = (T.ζ n - 1) ^ k * ι w →
  ∀ a lz lq : Gal p Ω → ZMod (p ^ n), IsKum T n (Gn T n) r a →
    IsKum T n (Gn T n) (T.ζ (2 * n)) lz → IsKum T n (Gn T n) (T.qq (2 * n)) lq →
    Cob1 n (Gn T n) (fun g => (p : Ω) ^ c * ((a g).val : Ω) - (p : Ω) ^ c * ι α * ((lq g).val : Ω) -
      (p : Ω) ^ c * (ι β + (k : Ω) * T.ζ n / (T.ζ n - 1)) * ((lz g).val : Ω)) := by
  first | exact @GlobalTheory.KumDlog.kummer_eq_dlog | exact GlobalTheory.KumDlog.kummer_eq_dlog | (intros; apply GlobalTheory.KumDlog.kummer_eq_dlog <;> assumption)
end

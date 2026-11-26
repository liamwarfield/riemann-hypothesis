module

public import Lemmata.GeneralBFactLeftBis.Imports
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.IsUnitIffSub
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.ExistsConjugationFixedUniformizer
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.DetectIdeal
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BridgeFinK
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.IsMaximalComapCj
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.Imports

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.IsUnimodularOfIsSDG
noncomputable section
open NumberField Matrix

namespace PI.SqPairLocal

open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG PI.UG

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem isLattice_of_isSDG {N : ℕ} {L : Submodule (𝓞 E) (Fin N → E)} (h : IsSDG E N L) :
    Submodule.IsFullLattice E L := by
  obtain ⟨h1, h2, -⟩ := h
  exact { toIsLattice := Submodule.IsLattice.of_fg E h1, span_eq_top := h2 }

theorem isUnimodular_of_isSDG {N : ℕ} {L : Submodule (𝓞 E) (Fin N → E)} (h : IsSDG E N L) :
    IsUnimodular (hStd E N) L := by
  obtain ⟨-, -, h3⟩ := h
  unfold PI.UG.IsUnimodular PI.UG.dual
  ext y
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply, Submodule.mem_one]
  rw [h3 y]
  exact forall₂_congr fun x _ => RingHom.mem_range.symm

theorem mem_hcompl_of_inert {Q : Ideal (𝓞 E)} (hQ : Q.IsPrime) (hc : Q.comap (cj E) = Q) (s : 𝓞 E) :
    s ∈ hcompl (K := E) Q ↔ s ∉ Q := by
  haveI := hQ
  constructor
  · intro h
    have hle : hcompl (K := E) Q ≤ Q.primeCompl := Submonoid.closure_le.mpr fun s hs => hs.1
    exact hle h
  · intro hs
    apply Submonoid.subset_closure
    refine ⟨hs, fun t ht => ?_⟩
    have htc : t = cj E s := by
      apply RingOfIntegers.ext
      exact ht
    subst htc
    intro hcs
    apply hs
    have h2 : s ∈ Q.comap (cj E) := Ideal.mem_comap.mpr hcs
    rwa [hc] at h2

theorem mem_loc_inert {Q : Ideal (𝓞 E)} (hQ : Q.IsPrime) (hc : Q.comap (cj E) = Q) {N : ℕ}
    (L : Submodule (𝓞 E) (Fin N → E)) (y : Fin N → E) :
    y ∈ loc (K := E) Q L ↔ ∃ s : 𝓞 E, s ∉ Q ∧ s • y ∈ L := by
  simp [loc, locS, mem_hcompl_of_inert hQ hc]

theorem mem_loc_stdLat {Q : Ideal (𝓞 E)} (hQ : Q.IsPrime) (hc : Q.comap (cj E) = Q) {N : ℕ}
    (x : Fin N → E) : x ∈ loc (K := E) Q (stdLat E N) ↔ ∀ i, IntAt Q (x i) := by
  rw [mem_loc_inert hQ hc]
  constructor
  · rintro ⟨s, hs, hx⟩ i
    obtain ⟨w, hw⟩ := Submodule.mem_one.mp ((Submodule.mem_pi.mp hx) i (Set.mem_univ i))
    refine ⟨s, hs, w, ?_⟩
    change algebraMap (𝓞 E) E s * x i = algebraMap (𝓞 E) E w
    rw [hw, Pi.smul_apply, Algebra.smul_def]
  · intro h
    choose s hs w hw using h
    haveI := hQ
    refine ⟨∏ i, s i, ?_, ?_⟩
    · have : (∏ i, s i) ∈ Q.primeCompl := Submonoid.prod_mem _ fun i _ => hs i
      exact this
    · refine Submodule.mem_pi.mpr fun i _ => Submodule.mem_one.mpr
        ⟨(∏ j ∈ Finset.univ.erase i, s j) * w i, ?_⟩
      rw [Pi.smul_apply, Algebra.smul_def, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), map_mul,
        map_mul, mul_assoc]
      congr 1
      exact (hw i).symm

theorem unitary_of_isom {N : ℕ} {g : (Fin N → E) ≃ₗ[E] (Fin N → E)} (hg : g ∈ isom (hStd E N)) :
    (LinearMap.toMatrix' (g : (Fin N → E) →ₗ[E] (Fin N → E)))ᴴ *
      LinearMap.toMatrix' (g : (Fin N → E) →ₗ[E] (Fin N → E)) = 1 := by
  ext i j
  have h1 : hStd E N (g (PI.UG.W.eStd E N i)) (g (PI.UG.W.eStd E N j)) = if i = j then 1 else 0 :=
    (hg _ _).trans (PI.UG.W.hStd_eStd E N i j)
  rw [PI.UG.W.hStd_apply] at h1
  rw [Matrix.mul_apply, Matrix.one_apply, ← h1]
  simp only [conjTranspose_apply, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe, PI.UG.W.eStd]

end SlopeTestRemainingChoices

theorem dict : Dict := by
  intro E _ _ _ hE N L hL Q hQ hc
  obtain ⟨g, hg, hgL⟩ := unimodular_genus_unique E N hE L (isLattice_of_isSDG hL).toIsLattice
    (isUnimodular_of_isSDG hL) Q hQ
  have h1 := unitary_of_isom hg
  have h2 := mul_eq_one_comm.mp h1
  refine ⟨LinearMap.toMatrix' (g : (Fin N → E) →ₗ[E] (Fin N → E)), h1, h2, fun y => ?_⟩
  have hQp := hQ.isPrime
  rw [← mem_loc_inert hQp hc, ← mem_loc_stdLat hQp hc]
  change y ∈ loc (K := E) Q L ↔ _
  rw [← hgL]
  have hs : g.symm y = (LinearMap.toMatrix' (g : (Fin N → E) →ₗ[E] (Fin N → E)))ᴴ *ᵥ y := by
    rw [LinearEquiv.symm_apply_eq]
    rw [← LinearEquiv.coe_coe, ← LinearMap.toMatrix'_mulVec, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
  rw [← hs]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨g.symm y, h, by simp⟩

end PI.SqPairLocal
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.SplitPlaceOf
noncomputable section
open NumberField Matrix

namespace PI.SqPairLocal

open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG

variable {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}

theorem scal_sq (ε : 𝓞 E) :
    (ε : E) • (1 : Matrix (Fin N) (Fin N) E) * (ε : E) • 1 - (ε : E) • 1 =
      ((ε * (ε - 1) : 𝓞 E) : E) • (1 : Matrix (Fin N) (Fin N) E) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, ← sub_smul]
  congr 1
  push_cast
  ring

theorem scal_adj (ε : 𝓞 E) :
    (ε : E) • (1 : Matrix (Fin N) (Fin N) E) + ((ε : E) • (1 : Matrix (Fin N) (Fin N) E))ᴴ - 1 =
      ((ε + cj E ε - 1 : 𝓞 E) : E) • (1 : Matrix (Fin N) (Fin N) E) := by
  have hc0 : ((cj E ε : 𝓞 E) : E) = star (ε : E) := rfl
  have hc : ((ε + cj E ε - 1 : 𝓞 E) : E) = (ε : E) + star (ε : E) - 1 := by
    push_cast
    exact congrArg (fun z => (ε : E) + z - 1) hc0
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hc, sub_smul, add_smul, one_smul]

private lemma smallAt_smul_one_of_dv {Q : Ideal (𝓞 E)} {c a : 𝓞 E} {L : Submodule (𝓞 E) (Fin N → E)}
    (h : Dv Q c a) : SmallAt Q c L (((a : 𝓞 E) : E) • (1 : Matrix (Fin N) (Fin N) E)) := by
  unfold Dv at h
  unfold SmallAt
  intro y hy
  obtain ⟨s, hs, w, hw⟩ := h
  refine ⟨s, hs, w • y, L.smul_mem w hy, ?_⟩
  have key : ∀ (r : 𝓞 E) (z : Fin N → E), r • z = (r : E) • z := fun r z => rfl
  simp only [Matrix.smul_mulVec, Matrix.one_mulVec, key, smul_smul]
  congr 1
  exact_mod_cast hw

theorem good_scal {Q : Ideal (𝓞 E)} [Q.IsPrime] {c : 𝓞 E} {L' L'' : Submodule (𝓞 E) (Fin N → E)}
    {ε : 𝓞 E} (h1 : Dv Q c (ε * (ε - 1))) (h2 : Dv Q c (ε + cj E ε - 1)) :
    Good Q c L' L'' ((ε : E) • (1 : Matrix (Fin N) (Fin N) E)) := by
  unfold Good
  rw [scal_sq, scal_adj]
  repeat' constructor
  all_goals first | exact smallAt_smul_one_of_dv h1 | exact smallAt_smul_one_of_dv h2

private lemma pres_integer_smul_one {L : Submodule (𝓞 E) (Fin N → E)} (ε : 𝓞 E) :
    Pres L ((ε : E) • (1 : Matrix (Fin N) (Fin N) E)) := by
  unfold Pres
  intro y hy
  have key : ∀ (r : 𝓞 E) (z : Fin N → E), r • z = (r : E) • z := fun r z => rfl
  have he : ((ε : E) • (1 : Matrix (Fin N) (Fin N) E)) *ᵥ y = ε • y := by
    rw [key]
    simp only [Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [he]
  exact L.smul_mem ε hy

theorem splitPlace_of (hP : PowLoc) : SplitPlace := by
  intro E _ _ _ _ N L' L'' _ _ _ Q hQ hne c hc
  have cjcj : ∀ x : 𝓞 E, cj E (cj E x) = x := fun x => by
    apply NumberField.RingOfIntegers.ext
    show star (star (x : E)) = (x : E)
    exact star_star _
  set Q' := Ideal.comap (cj E) Q with hQ'def
  have hsurj : Function.Surjective (cj E) := fun y => ⟨cj E y, cjcj y⟩
  haveI := hQ
  have hQ' : Q'.IsMaximal := Ideal.comap_isMaximal_of_surjective (cj E) hsurj
  have hcc : Ideal.comap (cj E) Q' = Q := by
    ext x
    rw [hQ'def, Ideal.mem_comap, Ideal.mem_comap, cjcj]
  have hsup : Q ⊔ Q' = ⊤ := by
    by_contra h
    have h1 : Q = Q ⊔ Q' := hQ.eq_of_le h le_sup_left
    have h2 : Q' = Q ⊔ Q' := hQ'.eq_of_le h le_sup_right
    exact hne (h2.trans h1.symm)
  obtain ⟨K, hK⟩ := hP E Q hQ c hc
  obtain ⟨K', hK'⟩ := hP E Q' hQ' c hc
  set M := max K K'
  have h1top : (1 : 𝓞 E) ∈ Q ^ M ⊔ Q' ^ M := by
    rw [Ideal.pow_sup_pow_eq_top hsup]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h1top
  have hb1 : b - 1 ∈ Q ^ M := by
    have hba : b - 1 = -a := by
      rw [← hab]
      ring
    rw [hba]
    exact (Q ^ M).neg_mem ha
  have toQ' : ∀ x, x ∈ Q ^ M → cj E x ∈ Q' ^ M := fun x hx => by
    have hle : Q ^ M ≤ Ideal.comap (cj E) (Q' ^ M) := by
      calc Q ^ M = (Ideal.comap (cj E) Q') ^ M := by rw [hcc]
        _ ≤ Ideal.comap (cj E) (Q' ^ M) := Ideal.le_comap_pow _ M
    exact Ideal.mem_comap.mp (hle hx)
  have toQ : ∀ x, x ∈ Q' ^ M → cj E x ∈ Q ^ M := fun x hx => by
    have hle : Q' ^ M ≤ Ideal.comap (cj E) (Q ^ M) := Ideal.le_comap_pow _ M
    exact Ideal.mem_comap.mp (hle hx)
  have hcb1 : cj E b - 1 ∈ Q' ^ M := by
    have h := toQ' _ hb1
    rwa [map_sub, map_one] at h
  have hcb : cj E b ∈ Q ^ M := toQ _ hb
  have dvQ : ∀ x, x ∈ Q ^ M → Dv Q c x := fun x hx =>
    hK x (Ideal.pow_le_pow_right (le_max_left K K') hx)
  have dvQ' : ∀ x, x ∈ Q' ^ M → Dv Q' c x := fun x hx =>
    hK' x (Ideal.pow_le_pow_right (le_max_right K K') hx)
  haveI := hQ.isPrime
  haveI := hQ'.isPrime
  refine ⟨(b : E) • (1 : Matrix (Fin N) (Fin N) E), pres_integer_smul_one b, pres_integer_smul_one b, ?_, ?_⟩
  · apply good_scal
    · exact dvQ _ (Ideal.mul_mem_left _ b hb1)
    · have hr : b + cj E b - 1 = (b - 1) + cj E b := by ring
      rw [hr]
      exact dvQ _ (Ideal.add_mem _ hb1 hcb)
  · apply good_scal
    · exact dvQ' _ (Ideal.mul_mem_right _ _ hb)
    · have hr : b + cj E b - 1 = b + (cj E b - 1) := by ring
      rw [hr]
      exact dvQ' _ (Ideal.add_mem _ hb hcb1)

end PI.SqPairLocal
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.ExistsDenFg
noncomputable section
open NumberField

namespace PI.SqPairLocal

open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG

theorem powLoc : PowLoc := by
  intro E _ _ Q hQ c hc
  have := hQ.isPrime
  have hQ0 : Q ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hQ (NumberField.RingOfIntegers.not_isField E)
  have : IsDiscreteValuationRing (Localization.AtPrime Q) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 E) hQ0 _
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime Q)
  have hc' : algebraMap (𝓞 E) (Localization.AtPrime Q) c ≠ 0 := by
    intro h
    apply hc
    apply IsLocalization.injective (Localization.AtPrime Q) (Ideal.primeCompl_le_nonZeroDivisors Q)
    rw [h, map_zero]
  obtain ⟨K, hK⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (s := Ideal.span {algebraMap (𝓞 E) (Localization.AtPrime Q) c})
    (by rwa [Ne, Ideal.span_singleton_eq_bot]) hϖ
  refine ⟨K, fun x hx => ?_⟩
  have hmax : IsLocalRing.maximalIdeal (Localization.AtPrime Q) = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have hxA : algebraMap (𝓞 E) (Localization.AtPrime Q) x ∈
      Ideal.span {algebraMap (𝓞 E) (Localization.AtPrime Q) c} := by
    rw [hK, ← Ideal.span_singleton_pow, ← hmax,
      ← IsLocalization.AtPrime.map_eq_maximalIdeal (p := Q), ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hx
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hxA
  obtain ⟨⟨w, s⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl y
  have key : algebraMap (𝓞 E) (Localization.AtPrime Q) (c * w) =
      algebraMap (𝓞 E) (Localization.AtPrime Q) (s * x) := by
    rw [map_mul, map_mul, ← hy, ← IsLocalization.mk'_spec (Localization.AtPrime Q) w s]
    ring
  obtain ⟨t, ht⟩ := (IsLocalization.eq_iff_exists Q.primeCompl (Localization.AtPrime Q)).mp key
  refine ⟨(t * s : Q.primeCompl), (t * s : Q.primeCompl).2, t * w, ?_⟩
  push_cast
  linear_combination -ht

theorem locGlob : LocGlob := by
  intro E _ _ W _ _ X x p hp hloc
  let J : Ideal (𝓞 E) := X.comap (LinearMap.toSpanSingleton (𝓞 E) W x)
  have hJ : ∀ a, a ∈ J ↔ a • x ∈ X := fun a => by
    simp [J, LinearMap.toSpanSingleton_apply]
  have htop : J ⊔ Ideal.span {(p : 𝓞 E)} = ⊤ := by
    by_contra h
    obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨s, hs, hsx⟩ := hloc Q hQ (hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
    exact hs (hle (Ideal.mem_sup_left ((hJ s).mpr hsx)))
  have hpnu : Ideal.span {(p : 𝓞 E)} ≠ ⊤ := by
    intro h
    have h2 := congrArg Ideal.absNorm h
    rw [Ideal.absNorm_span_singleton, Algebra.norm_natCast, Ideal.absNorm_top, Int.natAbs_pow,
      Int.natAbs_natCast] at h2
    have hd : 0 < Module.finrank ℤ (𝓞 E) := Module.finrank_pos
    rcases Nat.pow_eq_one.mp h2 with h1 | h1
    · exact hp.one_lt.ne' h1
    · omega
  have hJ0 : J ≠ ⊥ := by
    rintro h
    rw [h, bot_sup_eq] at htop
    exact hpnu htop
  have : Finite (𝓞 E ⧸ J) :=
    (Ideal.absNorm_ne_zero_iff J).mp (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  have h1 : (1 : 𝓞 E) ∈ J ⊔ Ideal.span {(p : 𝓞 E)} := by rw [htop]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h1
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hb
  have hunit : Ideal.Quotient.mk J r * Ideal.Quotient.mk J (p : 𝓞 E) = 1 := by
    rw [← map_mul, ← map_one (Ideal.Quotient.mk J), ← hab, Ideal.Quotient.eq]
    have : r * (p : 𝓞 E) - (a + r * (p : 𝓞 E)) = -a := by ring
    rw [this]
    exact J.neg_mem ha
  have hndvd : ¬ p ∣ Ideal.absNorm J := by
    intro hdvd
    have := Fact.mk hp
    let := Fintype.ofFinite (𝓞 E ⧸ J)
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card] at hdvd
    obtain ⟨z, hz⟩ := exists_prime_addOrderOf_dvd_card p hdvd
    have hpz : Ideal.Quotient.mk J (p : 𝓞 E) * z = 0 := by
      rw [map_natCast, ← nsmul_eq_mul, ← hz, addOrderOf_nsmul_eq_zero]
    have hz0 : z = 0 := by
      calc z = (Ideal.Quotient.mk J r * Ideal.Quotient.mk J (p : 𝓞 E)) * z := by rw [hunit, one_mul]
        _ = 0 := by rw [mul_assoc, hpz, mul_zero]
    rw [hz0, addOrderOf_zero] at hz
    exact hp.one_lt.ne hz
  refine ⟨Ideal.absNorm J, ?_, ?_⟩
  · exact_mod_cast hndvd
  · rw [Int.cast_natCast, ← hJ]
    exact Ideal.absNorm_mem J

section IntMulSec

variable {E : Type} [Field E] [NumberField E] {N : ℕ}

theorem exists_den (L'' : Submodule (𝓞 E) (Fin N → E))
    (hsp : Submodule.span E (L'' : Set (Fin N → E)) = ⊤) (v : Fin N → E) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ d • v ∈ L'' := by
  first | exact Bl.general_b_fact_left_bis.goal1 .. | (apply Bl.general_b_fact_left_bis.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_left_bis.goal1 <;> assumption) | (apply @Bl.general_b_fact_left_bis.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_left_bis.goal1 <;> assumption) | (apply @Bl.general_b_fact_left_bis.goal1 <;> first | assumption | infer_instance)

theorem exists_den_fg (L' L'' : Submodule (𝓞 E) (Fin N → E)) (hfg : L'.FG)
    (hsp : Submodule.span E (L'' : Set (Fin N → E)) = ⊤) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ ∀ y ∈ L', d • y ∈ L'' := by
  classical
  obtain ⟨S, rfl⟩ := hfg
  choose f hf0 hf using fun v => exists_den L'' hsp v
  refine ⟨∏ g ∈ S, f g, Finset.prod_ne_zero_iff.mpr (fun g _ => hf0 g), fun y hy => ?_⟩
  induction hy using Submodule.span_induction with
  | mem g hg =>
    rw [← Finset.mul_prod_erase S f (Finset.mem_coe.mp hg), mul_comm, mul_smul]
    exact L''.smul_mem _ (hf g)
  | zero => rw [smul_zero]; exact L''.zero_mem
  | add y z _ _ hy hz => rw [smul_add]; exact L''.add_mem hy hz
  | smul r y _ h => rw [smul_comm]; exact L''.smul_mem r h

theorem nat_mul (d : 𝓞 E) (hd : d ≠ 0) :
    ∃ d' : 𝓞 E, ((Ideal.absNorm (Ideal.span {d}) : ℕ) : 𝓞 E) = d * d' ∧
      Ideal.absNorm (Ideal.span {d}) ≠ 0 := by
  obtain ⟨d', hd'⟩ := Ideal.mem_span_singleton.mp (Ideal.absNorm_mem (Ideal.span {d}))
  refine ⟨d', hd', ?_⟩
  rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
  exact hd

end IntMulSec

theorem intMul : IntMul := by
  intro E _ _ _ N L' L'' h' h'' n hn
  obtain ⟨d1, hd1, k1⟩ := exists_den_fg L' L'' h'.1 h''.2.1
  obtain ⟨d2, hd2, k2⟩ := exists_den_fg L'' L' h''.1 h'.2.1
  obtain ⟨D', hD', hD0⟩ := nat_mul (d1 * d2) (mul_ne_zero hd1 hd2)
  obtain ⟨n', hn', hn0⟩ := nat_mul n hn
  refine ⟨Ideal.absNorm (Ideal.span {d1 * d2}) * Ideal.absNorm (Ideal.span {n}),
    mul_ne_zero hD0 hn0, fun y hy => ?_⟩
  have hDy : (d1 * d2) • y ∈ L' ∧ (d1 * d2) • y ∈ L'' := by
    rcases hy with hy | hy
    · have e : (d1 * d2) • y = d2 • (d1 • y) := by rw [smul_smul, mul_comm]
      exact ⟨L'.smul_mem _ hy, e ▸ L''.smul_mem d2 (k1 y hy)⟩
    · have e : (d1 * d2) • y = d1 • (d2 • y) := by rw [smul_smul]
      exact ⟨e ▸ L'.smul_mem d1 (k2 y hy), L''.smul_mem _ hy⟩
  refine ⟨(D' * n') • ((d1 * d2) • y), L'.smul_mem _ hDy.1, L''.smul_mem _ hDy.2, ?_⟩
  rw [Nat.cast_mul, hD', hn', smul_smul, smul_smul]
  congr 1
  ring

end PI.SqPairLocal
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.DivAtOneOfInt
noncomputable section
open NumberField Matrix

namespace PI.SqPairLocal

open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG

variable {E : Type} [Field E] [NumberField E] [StarRing E]

section Loc

variable {Q : Ideal (𝓞 E)} [hQ : Q.IsPrime]

theorem one_nmem : (1 : 𝓞 E) ∉ Q := fun h => hQ.ne_top ((Ideal.eq_top_iff_one Q).mpr h)

theorem mul_nmem {s t : 𝓞 E} (hs : s ∉ Q) (ht : t ∉ Q) : s * t ∉ Q :=
  fun h => (hQ.mem_or_mem h).elim hs ht

theorem intAt_coe (w : 𝓞 E) : IntAt Q (w : E) := by
  unfold IntAt
  exact ⟨1, one_nmem, w, by simp⟩

theorem intAt_zero : IntAt Q (0 : E) := by
  unfold IntAt
  exact ⟨1, one_nmem, 0, by simp⟩

theorem intAt_one : IntAt Q (1 : E) := by
  unfold IntAt
  exact ⟨1, one_nmem, 1, by simp⟩

theorem intAt_mul {x y : E} (hx : IntAt Q x) (hy : IntAt Q y) : IntAt Q (x * y) := by
  unfold IntAt at *
  obtain ⟨s, hs, w, hw⟩ := hx
  obtain ⟨t, ht, v, hv⟩ := hy
  refine ⟨s * t, mul_nmem hs ht, w * v, ?_⟩
  push_cast
  linear_combination ((t : E) * y) * hw + (w : E) * hv

theorem divAt_zero {c : 𝓞 E} : DivAt Q c 0 := by
  unfold DivAt
  exact ⟨1, one_nmem, 0, by simp⟩

theorem divAt_add {c : 𝓞 E} {x y : E} (hx : DivAt Q c x) (hy : DivAt Q c y) : DivAt Q c (x + y) := by
  unfold DivAt at *
  obtain ⟨s, hs, w, hw⟩ := hx
  obtain ⟨t, ht, v, hv⟩ := hy
  refine ⟨s * t, mul_nmem hs ht, t * w + s * v, ?_⟩
  push_cast
  linear_combination (t : E) * hw + (s : E) * hv

theorem divAt_neg {c : 𝓞 E} {x : E} (hx : DivAt Q c x) : DivAt Q c (-x) := by
  unfold DivAt at *
  obtain ⟨s, hs, w, hw⟩ := hx
  refine ⟨s, hs, -w, ?_⟩
  push_cast
  linear_combination -hw

theorem divAt_sub {c : 𝓞 E} {x y : E} (hx : DivAt Q c x) (hy : DivAt Q c y) : DivAt Q c (x - y) := by
  rw [sub_eq_add_neg]
  exact divAt_add hx (divAt_neg hy)

theorem divAt_mul_left {c : 𝓞 E} {a x : E} (ha : IntAt Q a) (hx : DivAt Q c x) : DivAt Q c (a * x) := by
  unfold IntAt at ha
  unfold DivAt at *
  obtain ⟨s, hs, w, hw⟩ := ha
  obtain ⟨t, ht, v, hv⟩ := hx
  refine ⟨s * t, mul_nmem hs ht, w * v, ?_⟩
  push_cast
  linear_combination ((t : E) * x) * hw + (w : E) * hv

theorem divAt_mul_right {c : 𝓞 E} {a x : E} (hx : DivAt Q c x) (ha : IntAt Q a) : DivAt Q c (x * a) := by
  rw [mul_comm]
  exact divAt_mul_left ha hx

theorem divAt_sum {c : 𝓞 E} {ι : Type} (S : Finset ι) (f : ι → E) (h : ∀ i ∈ S, DivAt Q c (f i)) :
    DivAt Q c (∑ i ∈ S, f i) :=
  Finset.sum_induction f (DivAt Q c) (fun _ _ ha hb => divAt_add ha hb) divAt_zero h

theorem divAt_one_of_int {x : E} (hx : IntAt Q x) : DivAt Q 1 x := by
  unfold IntAt at hx
  unfold DivAt
  obtain ⟨s, hs, w, hw⟩ := hx
  exact ⟨s, hs, w, by simp [hw]⟩

theorem intAt_inv_mul {c : 𝓞 E} (hc : (c : E) ≠ 0) {x : E} (hx : DivAt Q c x) :
    IntAt Q ((c : E)⁻¹ * x) := by
  unfold DivAt at hx
  unfold IntAt
  obtain ⟨s, hs, w, hw⟩ := hx
  refine ⟨s, hs, w, ?_⟩
  calc (s : E) * ((c : E)⁻¹ * x) = (c : E)⁻¹ * ((s : E) * x) := by ring
    _ = (w : E) := by rw [hw, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

theorem divAt_of_mem {c : 𝓞 E} {K : ℕ}
    (hK : ∀ x ∈ Q ^ K, ∃ s : 𝓞 E, s ∉ Q ∧ ∃ w : 𝓞 E, s * x = c * w) {x : 𝓞 E} (hx : x ∈ Q ^ K) :
    DivAt Q c (x : E) := by
  unfold DivAt
  obtain ⟨s, hs, w, hw⟩ := hK x hx
  exact ⟨s, hs, w, by exact_mod_cast congrArg (fun z : 𝓞 E => (z : E)) hw⟩

theorem divAt_trans {c d : 𝓞 E} {K : ℕ}
    (hK : ∀ x ∈ Q ^ K, ∃ s : 𝓞 E, s ∉ Q ∧ ∃ w : 𝓞 E, s * x = c * w) (hd : d ∈ Q ^ K) {x : E}
    (hx : DivAt Q d x) : DivAt Q c x := by
  unfold DivAt at *
  obtain ⟨s, hs, w, hw⟩ := hK d hd
  have hsd : (s : E) * (d : E) = (c : E) * (w : E) := by
    exact_mod_cast congrArg (fun z : 𝓞 E => (z : E)) hw
  obtain ⟨t, ht, v, hv⟩ := hx
  refine ⟨s * t, mul_nmem hs ht, w * v, ?_⟩
  push_cast
  linear_combination (s : E) * hv + (v : E) * hsd

end Loc

section Mat

variable {Q : Ideal (𝓞 E)} [hQ : Q.IsPrime] {N : ℕ}

theorem small_of {L : Submodule (𝓞 E) (Fin N → E)} {G : Matrix (Fin N) (Fin N) E}
    (hGG : G * Gᴴ = 1)
    (hD : ∀ y : Fin N → E, (∃ s : 𝓞 E, s ∉ Q ∧ s • y ∈ L) ↔ ∀ i, IntAt Q ((Gᴴ *ᵥ y) i))
    {c : 𝓞 E} (hc : (c : E) ≠ 0) {M : Matrix (Fin N) (Fin N) E}
    (hM : ∀ i j, DivAt Q c ((Gᴴ * M * G) i j)) : SmallAt Q c L M := by
  unfold SmallAt
  intro y hy
  have hz := (hD y).mp ⟨1, one_nmem, by rw [one_smul]; exact hy⟩
  have hGM : Gᴴ *ᵥ (M *ᵥ y) = (Gᴴ * M * G) *ᵥ (Gᴴ *ᵥ y) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mul_assoc (Gᴴ * M) G Gᴴ, hGG, mul_one]
  have hdiv : ∀ i, DivAt Q c ((Gᴴ *ᵥ (M *ᵥ y)) i) := by
    intro i
    rw [hGM]
    show DivAt Q c (∑ j, (Gᴴ * M * G) i j * (Gᴴ *ᵥ y) j)
    exact divAt_sum Finset.univ _ (fun j _ => divAt_mul_right (hM i j) (hz j))
  obtain ⟨s, hs, hsv⟩ := (hD ((c : E)⁻¹ • (M *ᵥ y))).mpr (fun i => by
    rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    exact intAt_inv_mul hc (hdiv i))
  refine ⟨s, hs, s • ((c : E)⁻¹ • (M *ᵥ y)), hsv, ?_⟩
  have hcc : (c • (c : E)⁻¹ : E) = 1 := by
    rw [Algebra.smul_def]
    exact mul_inv_cancel₀ hc
  rw [smul_comm c s, ← smul_assoc c ((c : E)⁻¹) (M *ᵥ y), hcc, one_smul]

private theorem intAt_of_divAt_one {x : E} (hx : DivAt Q 1 x) : IntAt Q x := by
  unfold DivAt at hx
  unfold IntAt
  obtain ⟨s, hs, w, hw⟩ := hx
  exact ⟨s, hs, w, by simpa using hw⟩

theorem pres_of {L : Submodule (𝓞 E) (Fin N → E)} {G : Matrix (Fin N) (Fin N) E}
    (hGG : G * Gᴴ = 1)
    (hD : ∀ y : Fin N → E, (∃ s : 𝓞 E, s ∉ Q ∧ s • y ∈ L) ↔ ∀ i, IntAt Q ((Gᴴ *ᵥ y) i))
    {M : Matrix (Fin N) (Fin N) E} (hM : ∀ i j, IntAt Q ((Gᴴ * M * G) i j)) :
    ∀ y ∈ L, ∃ s : 𝓞 E, s ∉ Q ∧ s • (M *ᵥ y) ∈ L := by
  intro y hy
  have hz := (hD y).mp ⟨1, one_nmem, by rw [one_smul]; exact hy⟩
  apply (hD (M *ᵥ y)).mpr
  intro i
  have hGM : Gᴴ *ᵥ (M *ᵥ y) = (Gᴴ * M * G) *ᵥ (Gᴴ *ᵥ y) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mul_assoc (Gᴴ * M) G Gᴴ, hGG, mul_one]
  rw [hGM]
  show IntAt Q (∑ j, (Gᴴ * M * G) i j * (Gᴴ *ᵥ y) j)
  exact intAt_of_divAt_one
    (divAt_sum Finset.univ _ (fun j _ => divAt_mul_left (hM i j) (divAt_one_of_int (hz j))))

theorem clear {L : Submodule (𝓞 E) (Fin N → E)} (hL : L.FG) {M : Matrix (Fin N) (Fin N) E}
    (h : ∀ y ∈ L, ∃ s : 𝓞 E, s ∉ Q ∧ s • (M *ᵥ y) ∈ L) :
    ∃ s : 𝓞 E, s ∉ Q ∧ ∀ y ∈ L, s • (M *ᵥ y) ∈ L := by
  classical
  obtain ⟨S, hS⟩ := hL
  choose! t ht using h
  have hSL : ∀ g ∈ S, g ∈ L := fun g hg => hS ▸ Submodule.subset_span (Finset.mem_coe.mpr hg)
  refine ⟨∏ g ∈ S, t g, Finset.prod_induction t (· ∉ Q) (fun a b ha hb => mul_nmem ha hb) one_nmem
    (fun g hg => (ht g (hSL g hg)).1), ?_⟩
  let F : (Fin N → E) →ₗ[𝓞 E] (Fin N → E) :=
    (∏ g ∈ S, t g) • (Matrix.mulVecLin M).restrictScalars (𝓞 E)
  have hle : Submodule.span (𝓞 E) (S : Set (Fin N → E)) ≤ L.comap F := by
    rw [Submodule.span_le]
    intro g hg
    have hg' : g ∈ S := Finset.mem_coe.mp hg
    show (∏ g ∈ S, t g) • (M *ᵥ g) ∈ L
    rw [← Finset.mul_prod_erase S t hg', mul_comm, mul_smul]
    exact L.smul_mem _ (ht g (hSL g hg')).2
  intro y hy
  rw [← hS] at hy
  exact hle hy

theorem good_gen {L : Submodule (𝓞 E) (Fin N → E)} {G : Matrix (Fin N) (Fin N) E}
    (hG1 : Gᴴ * G = 1) (hGG : G * Gᴴ = 1)
    (hD : ∀ y : Fin N → E, (∃ s : 𝓞 E, s ∉ Q ∧ s • y ∈ L) ↔ ∀ i, IntAt Q ((Gᴴ *ᵥ y) i))
    {c : 𝓞 E} (hc : (c : E) ≠ 0) {f : Matrix (Fin N) (Fin N) E} (hf : ∀ i j, IntAt Q (f i j))
    (hf2 : ∀ i j, DivAt Q c ((f * f - f) i j)) (hf3 : ∀ i j, DivAt Q c ((f + fᴴ - 1) i j))
    {t : 𝓞 E} (ht : DivAt Q c ((t : E) - 1)) (ht' : DivAt Q c (star (t : E) - 1))
    (ht'' : IntAt Q (star (t : E)))
    {e : Matrix (Fin N) (Fin N) E} (he : Gᴴ * e * G = (t : E) • f) :
    SmallAt Q c L (e * e - e) ∧ SmallAt Q c L (e + eᴴ - 1) := by
  constructor
  · apply small_of hGG hD hc
    intro i j
    have hcs : Gᴴ * (e * e - e) * G = (Gᴴ * e * G) * (Gᴴ * e * G) - Gᴴ * e * G := by
      calc Gᴴ * (e * e - e) * G = Gᴴ * e * (G * Gᴴ) * e * G - Gᴴ * e * G := by
            rw [hGG, mul_one, mul_sub, sub_mul]
            simp only [mul_assoc]
        _ = _ := by simp only [mul_assoc]
    rw [hcs, he]
    have hm : ((t : E) • f) * ((t : E) • f) - (t : E) • f =
        ((t : E) * (t : E)) • (f * f - f) + ((t : E) * ((t : E) - 1)) • f := by
      rw [smul_mul_smul_comm, smul_sub, mul_sub, mul_one, sub_smul]
      abel
    rw [hm]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact divAt_add (divAt_mul_left (intAt_mul (intAt_coe t) (intAt_coe t)) (hf2 i j))
      (divAt_mul_right (divAt_mul_left (intAt_coe t) ht) (hf i j))
  · apply small_of hGG hD hc
    intro i j
    have hch : Gᴴ * (e + eᴴ - 1) * G = Gᴴ * e * G + (Gᴴ * e * G)ᴴ - 1 := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        mul_sub, mul_add, sub_mul, add_mul, mul_one, hG1]
      simp only [mul_assoc]
    rw [hch, he]
    have hm : (t : E) • f + ((t : E) • f)ᴴ - 1 = star (t : E) • (f + fᴴ - 1) +
        ((t : E) - star (t : E)) • f + (star (t : E) - 1) • (1 : Matrix (Fin N) (Fin N) E) := by
      rw [Matrix.conjTranspose_smul, smul_sub, smul_add, sub_smul, sub_smul, one_smul]
      abel
    rw [hm]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    have h1 : IntAt Q ((1 : Matrix (Fin N) (Fin N) E) i j) := by
      rw [Matrix.one_apply]
      split_ifs
      · exact intAt_one
      · exact intAt_zero
    have h2 : DivAt Q c ((t : E) - star (t : E)) := by
      rw [show (t : E) - star (t : E) = ((t : E) - 1) - (star (t : E) - 1) by ring]
      exact divAt_sub ht ht'
    exact divAt_add (divAt_add (divAt_mul_left ht'' (hf3 i j)) (divAt_mul_right h2 (hf i j)))
      (divAt_mul_right ht' h1)

end Mat

theorem conj_sq {N : ℕ} (u e : Matrix (Fin N) (Fin N) E) (hu : u * uᴴ = 1) :
    (uᴴ * e * u) * (uᴴ * e * u) - uᴴ * e * u = uᴴ * (e * e - e) * u := by
  calc (uᴴ * e * u) * (uᴴ * e * u) - uᴴ * e * u
      = uᴴ * e * (u * uᴴ) * e * u - uᴴ * e * u := by simp only [mul_assoc]
    _ = uᴴ * (e * e - e) * u := by
      rw [hu, mul_one, mul_sub, sub_mul]
      simp only [mul_assoc]

theorem conj_herm {N : ℕ} (u e : Matrix (Fin N) (Fin N) E) (hu : uᴴ * u = 1) :
    uᴴ * e * u + (uᴴ * e * u)ᴴ - 1 = uᴴ * (e + eᴴ - 1) * u := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    mul_sub, mul_add, sub_mul, add_mul, mul_one, hu]
  simp only [mul_assoc]

theorem star_coe (t : 𝓞 E) : star (t : E) = ((cj E t : 𝓞 E) : E) := by
  rfl

theorem inertAsm : InertAsm := by
  unfold InertAsm InertPlace
  intro hLCP hME hD hLM hPL E _ _ _ hE N L' L'' hN hL' hL'' Q hQ hcj c hc
  haveI : Q.IsPrime := hQ.isPrime
  obtain ⟨M⟩ := hME E hE Q hQ hcj
  obtain ⟨G', hG'1, hG'2, hD'⟩ := hD E hE N L' hL' Q hQ hcj
  obtain ⟨G'', hG''1, hG''2, hD''⟩ := hD E hE N L'' hL'' Q hQ hcj
  have hu1 : (G'ᴴ * G'')ᴴ * (G'ᴴ * G'') = 1 := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, mul_assoc,
      ← mul_assoc G' G'ᴴ G'', hG'2, one_mul, hG''1]
  have hu2 : (G'ᴴ * G'') * (G'ᴴ * G'')ᴴ = 1 := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, mul_assoc,
      ← mul_assoc G'' G''ᴴ G', hG''2, one_mul, hG'1]
  unfold PowLoc at hPL
  obtain ⟨K, hK⟩ := hPL E Q hQ c hc
  obtain ⟨e₁, h1, h2, h3, h4, h5, h6⟩ := hLM E Q hQ M hLCP N hN (G'ᴴ * G'') hu1 hu2 K
  have hϖ : M.ϖ ^ K ∈ Q ^ K := Ideal.pow_mem_pow M.ϖ_Q K
  have tr : ∀ x : E, DivAt Q (M.ϖ ^ K) x → DivAt Q c x := fun x hx => divAt_trans hK hϖ hx
  have hFG' : L'.FG := by
    unfold IsSDG at hL'
    exact hL'.1
  have hFG'' : L''.FG := by
    unfold IsSDG at hL''
    exact hL''.1
  have hA' : G'ᴴ * (G' * e₁ * G'ᴴ) * G' = e₁ := by
    simp only [mul_assoc, hG'1, mul_one]
    rw [← mul_assoc, hG'1, one_mul]
  have hA'' : G''ᴴ * (G' * e₁ * G'ᴴ) * G'' = (G'ᴴ * G'')ᴴ * e₁ * (G'ᴴ * G'') := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    simp only [mul_assoc]
  obtain ⟨s', hs', hs'L⟩ := clear hFG'
    (pres_of hG'2 hD' (M := G' * e₁ * G'ᴴ) (fun i j => by rw [hA']; exact h1 i j))
  obtain ⟨s'', hs'', hs''L⟩ := clear hFG''
    (pres_of hG''2 hD'' (M := G' * e₁ * G'ᴴ) (fun i j => by rw [hA'']; exact h2 i j))
  obtain ⟨y, i, hi, hyi⟩ := hQ.exists_inv (mul_nmem hs' hs'')
  obtain ⟨t, ht⟩ : ∃ t : 𝓞 E, t = s' * s'' * (y * ∑ k ∈ Finset.range K, i ^ k) := ⟨_, rfl⟩
  have ht1 : t - 1 = -(i ^ K) := by
    have hg := geom_sum_mul i K
    linear_combination ht + (∑ k ∈ Finset.range K, i ^ k) * hyi - hg
  have htQ : t - 1 ∈ Q ^ K := by
    rw [ht1]
    exact neg_mem (Ideal.pow_mem_pow hi K)
  have hci : cj E i ∈ Q := by
    have hi' : i ∈ Ideal.comap (cj E) Q := by rw [hcj]; exact hi
    exact hi'
  have hct : cj E t - 1 ∈ Q ^ K := by
    have hc1 : cj E t - 1 = -((cj E i) ^ K) := by
      rw [← map_one (cj E), ← map_sub, ht1, map_neg, map_pow]
    rw [hc1]
    exact neg_mem (Ideal.pow_mem_pow hci K)
  have htc : DivAt Q c ((t : E) - 1) := by
    have h := divAt_of_mem hK htQ
    push_cast at h
    exact h
  have htc' : DivAt Q c (star (t : E) - 1) := by
    rw [star_coe]
    have h := divAt_of_mem hK hct
    push_cast at h
    exact h
  have htc'' : IntAt Q (star (t : E)) := by
    rw [star_coe]
    exact intAt_coe _
  have hE' : G'ᴴ * ((t : E) • (G' * e₁ * G'ᴴ)) * G' = (t : E) • e₁ := by
    rw [Matrix.mul_smul, Matrix.smul_mul, hA']
  have hE'' : G''ᴴ * ((t : E) • (G' * e₁ * G'ᴴ)) * G'' =
      (t : E) • ((G'ᴴ * G'')ᴴ * e₁ * (G'ᴴ * G'')) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, hA'']
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc
  obtain ⟨a1, a2⟩ := good_gen hG'1 hG'2 hD' hcE h1 (fun i j => tr _ (h3 i j)) (fun i j => tr _ (h5 i j))
    htc htc' htc'' hE'
  obtain ⟨b1, b2⟩ := good_gen hG''1 hG''2 hD'' hcE h2
    (fun i j => by rw [conj_sq (G'ᴴ * G'') e₁ hu2]; exact tr _ (h4 i j))
    (fun i j => by rw [conj_herm (G'ᴴ * G'') e₁ hu1]; exact tr _ (h6 i j))
    htc htc' htc'' hE''
  refine ⟨(t : E) • (G' * e₁ * G'ᴴ), ?_, ?_, ?_⟩
  · unfold Pres
    intro z hz
    have hsm : ((t : E) • (G' * e₁ * G'ᴴ)) *ᵥ z = (t : E) • ((G' * e₁ * G'ᴴ) *ᵥ z) := by
      first
        | exact Matrix.smul_mulVec (t : E) (G' * e₁ * G'ᴴ) z
        | (ext k; simp [Matrix.mulVec, Finset.mul_sum, mul_assoc])
    rw [hsm,
      show (t : E) • ((G' * e₁ * G'ᴴ) *ᵥ z) = t • ((G' * e₁ * G'ᴴ) *ᵥ z) from algebraMap_smul E t _,
      ht, show s' * s'' * (y * ∑ k ∈ Finset.range K, i ^ k) =
        (s'' * (y * ∑ k ∈ Finset.range K, i ^ k)) * s' by ring, mul_smul]
    exact L'.smul_mem _ (hs'L z hz)
  · unfold Pres
    intro z hz
    have hsm : ((t : E) • (G' * e₁ * G'ᴴ)) *ᵥ z = (t : E) • ((G' * e₁ * G'ᴴ) *ᵥ z) := by
      first
        | exact Matrix.smul_mulVec (t : E) (G' * e₁ * G'ᴴ) z
        | (ext k; simp [Matrix.mulVec, Finset.mul_sum, mul_assoc])
    rw [hsm,
      show (t : E) • ((G' * e₁ * G'ᴴ) *ᵥ z) = t • ((G' * e₁ * G'ᴴ) *ᵥ z) from algebraMap_smul E t _,
      ht, show s' * s'' * (y * ∑ k ∈ Finset.range K, i ^ k) =
        (s' * (y * ∑ k ∈ Finset.range K, i ^ k)) * s'' by ring, mul_smul]
    exact L''.smul_mem _ (hs''L z hz)
  · unfold Good
    exact ⟨a1, b1, a2, b2⟩

end PI.SqPairLocal
end
end

namespace PI.SqPairLocal

theorem modelEx : ModelEx := modelEx_of fixedDVR realUnif

theorem sqPairLocal_of (h : PI.SqPair.LocCartanPair) : PI.SqPair.PLocalAll :=
  sqPairLocal_of_steps h locGlob intMul (glue_of powLoc) (splitPlace_of powLoc) inertAsm modelEx dict locMat
    powLoc

end PI.SqPairLocal

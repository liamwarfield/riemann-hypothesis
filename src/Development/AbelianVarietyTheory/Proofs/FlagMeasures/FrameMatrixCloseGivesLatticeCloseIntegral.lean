module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TupleJacobianRightMulIsometry
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesComplementUnitaryActsOnTerms

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairingConjInverseAdjointCloseToOne
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairingConjInverseAdjointCloseToOne
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.Sloc.CloseConj

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem cT_mul (L : LocE F E) {n : ℕ} (A B : Matrix (Fin n) (Fin n) E) :
    cT L (A * B) = cT L B * cT L A := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [cT, Matrix.mul_apply, map_sum, map_mul]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem cT_one (L : LocE F E) {n : ℕ} : cT L (1 : Matrix (Fin n) (Fin n) E) = 1 := by
  ext i j
  simp only [cT, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

theorem cT_sub (L : LocE F E) {n : ℕ} (A B : Matrix (Fin n) (Fin n) E) :
    cT L (A - B) = cT L A - cT L B := by
  ext i j
  simp [cT, map_sub]

theorem cj_mem (L : LocE F E) {x : E} (hx : x ∈ L.O) : L.cj x ∈ L.O := by
  rw [L.O_def] at hx ⊢
  exact hx.map (L.cj.toAlgHom.restrictScalars 𝒪[F])

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (n : ℕ) (Z Zi M Mi M' : Matrix (Fin n) (Fin n) E) (t e : E), t ∈ L.O → L.cj t = t → Zi * Z = 1 → (∀ i j, e * Z i j ∈ L.O) → (∀ i j, e * Zi i j ∈ L.O) → Mi * M = 1 → M * Mi = 1 → (∀ i j, ∃ o ∈ L.O, (Mi - 1) i j = t * o) → cT L M * Z * M' = Z → ∀ i j, ∃ o ∈ L.O, e * e * (M' - 1) i j = t * o := by
  intro F _ _ _ E _ _ _ L n Z Zi M Mi M' t e ht htc hZiZ heZ heZi hMiM hMMi hclose hM'
  have hc : cT L Mi * cT L M = 1 := by rw [← cT_mul, hMMi, cT_one]
  have hM'eq : M' = Zi * cT L Mi * Z := by
    calc M' = Zi * (cT L Mi * cT L M) * Z * M' := by rw [hc, Matrix.mul_one, hZiZ, Matrix.one_mul]
      _ = Zi * cT L Mi * (cT L M * Z * M') := by simp only [Matrix.mul_assoc]
      _ = Zi * cT L Mi * Z := by rw [hM']
  have hsub : M' - 1 = Zi * cT L (Mi - 1) * Z := by
    rw [hM'eq, cT_sub, cT_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hZiZ]
  choose o ho hoe using hclose
  intro i j
  refine ⟨∑ l, ∑ k, (e * Zi i k) * L.cj (o l k) * (e * Z l j), ?_, ?_⟩
  · refine Subring.sum_mem _ fun l _ => Subring.sum_mem _ fun k _ => ?_
    exact Subring.mul_mem _ (Subring.mul_mem _ (heZi i k) (cj_mem L (ho l k))) (heZ l j)
  · rw [hsub]
    simp only [Matrix.mul_apply, cT, hoe, map_mul, htc, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    ring

end GlobalTheory.Sloc.CloseConj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairingConjInverseAdjointCloseToOneStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairing_conj_inverseAdjoint_close_to_one : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (n : ℕ) (Z Zi M Mi M' : Matrix (Fin n) (Fin n) E) (t e : E), t ∈ L.O → L.cj t = t → Zi * Z = 1 → (∀ i j, e * Z i j ∈ L.O) → (∀ i j, e * Zi i j ∈ L.O) → Mi * M = 1 → M * Mi = 1 → (∀ i j, ∃ o ∈ L.O, (Mi - 1) i j = t * o) → cT L M * Z * M' = Z → ∀ i j, ∃ o ∈ L.O, e * e * (M' - 1) i j = t * o := by
  first | exact @GlobalTheory.Sloc.CloseConj.main | exact GlobalTheory.Sloc.CloseConj.main | (intros; apply GlobalTheory.Sloc.CloseConj.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemMaximalCompactOfIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemMaximalCompactOfIntegral
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.Frames

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem stab_span_of_integral {L : LocE F E} {r k : ℕ} (S : Frames L r k) (h : S.GLV)
    (g : Fin (r + 1) → S.V) (s si : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hs : ∀ i j, s i j ∈ L.O) (hsi : ∀ i j, si i j ∈ L.O) (hm : s * si = 1)
    (hg : ∀ j, h (g j) = ∑ i, s i j • g i) :
    h ∈ MulAction.stabilizer S.GLV (Submodule.span L.O (Set.range g)) := by
  rw [MulAction.mem_stabilizer_iff]
  set N := Submodule.span L.O (Set.range g) with hN
  have mem : ∀ (c : Matrix (Fin (r + 1)) (Fin (r + 1)) E), (∀ i j, c i j ∈ L.O) →
      ∀ j, ∑ i, c i j • g i ∈ N := by
    intro c hc j
    refine Submodule.sum_mem _ fun i _ => ?_
    have : c i j • g i = (⟨c i j, hc i j⟩ : L.O) • g i := rfl
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  apply le_antisymm
  · rw [Submodule.pointwise_smul_def, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    show h (g j) ∈ N
    rw [hg j]
    exact mem s hs j
  · rw [hN, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have key : g j = h (∑ i, si i j • g i) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp_rw [map_smul, hg, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_smul]
      have : ∀ x, ∑ i, si i j * s x i = (s * si) x j := fun x => by
        rw [Matrix.mul_apply]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
      simp_rw [this, hm, Matrix.one_apply, ite_smul, one_smul, zero_smul]
      simp
    rw [key]
    exact Submodule.smul_mem_pointwise_smul _ h _ (mem si hsi j)

theorem mem_K0_of_integral : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (r k : ℕ) (S : Frames L r k) (h : S.GLV) (s si s' si' : Matrix (Fin (r + 1)) (Fin (r + 1)) E), h ∈ S.St → (∀ i j, s i j ∈ L.O) → (∀ i j, si i j ∈ L.O) → s * si = 1 → (∀ i j, s' i j ∈ L.O) → (∀ i j, si' i j ∈ L.O) → s' * si' = 1 → (∀ j, h (S.f j) = ∑ i, s i j • S.f i) → (∀ j, h (S.f' j) = ∑ i, s' i j • S.f' i) → h ∈ S.K0 := by
  intro F _ _ _ E _ _ _ L r k S h s si s' si' hSt hs hsi hm hs' hsi' hm' hg hg'
  unfold Frames.K0
  exact ⟨⟨hSt, S.stab_span_of_integral h S.f s si hs hsi hm hg⟩,
    S.stab_span_of_integral h S.f' s' si' hs' hsi' hm' hg'⟩

end GlobalTheory.HL.Frames
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemMaximalCompactOfIntegralStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_maximal_compact_of_integral : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (r k : ℕ) (S : Frames L r k) (h : S.GLV) (s si s' si' : Matrix (Fin (r + 1)) (Fin (r + 1)) E), h ∈ S.St → (∀ i j, s i j ∈ L.O) → (∀ i j, si i j ∈ L.O) → s * si = 1 → (∀ i j, s' i j ∈ L.O) → (∀ i j, si' i j ∈ L.O) → s' * si' = 1 → (∀ j, h (S.f j) = ∑ i, s i j • S.f i) → (∀ j, h (S.f' j) = ∑ i, s' i j • S.f' i) → h ∈ S.K0 := by
  first | exact @GlobalTheory.HL.Frames.mem_K0_of_integral | exact GlobalTheory.HL.Frames.mem_K0_of_integral | (intros; apply GlobalTheory.HL.Frames.mem_K0_of_integral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsCommonDenominatorForHermitianLatticeData
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntSmulMemLattice
namespace GlobalTheory.IntMulIntegerSmulMemLattice

open NumberField

theorem exists_int_mul_eq_integer {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ d : ℤ, d ≠ 0 ∧ ∃ r : 𝓞 E, (r : E) = (d : E) * c := by
  have hQ : IsAlgebraic ℚ c := Algebra.IsAlgebraic.isAlgebraic c
  have hZ : IsAlgebraic ℤ c := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 hQ
  obtain ⟨d, hd, hint⟩ := hZ.exists_integral_multiple
  refine ⟨d, hd, ⟨d • c, hint⟩, ?_⟩
  change d • c = (d : E) * c
  rw [zsmul_eq_mul]

theorem exists_int_smul_mem_lattice {E : Type} [Field E] [NumberField E] {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) (hΛ : Submodule.IsFullLattice E Λ) (w : Fin n → E) :
    ∃ m : ℤ, m ≠ (0 : ℤ) ∧ (m : 𝓞 E) • w ∈ Λ := by
  have hw : w ∈ Submodule.span E (Λ : Set (Fin n → E)) := by
    rw [hΛ.span_eq_top]; trivial
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have h : ((a * b : ℤ) : 𝓞 E) • (x + y)
        = (b : 𝓞 E) • ((a : 𝓞 E) • x) + (a : 𝓞 E) • ((b : 𝓞 E) • y) := by
      rw [smul_add, smul_smul, smul_smul, Int.cast_mul, mul_comm (b : 𝓞 E) (a : 𝓞 E)]
    rw [h]
    exact Λ.add_mem (Λ.smul_mem _ hax) (Λ.smul_mem _ hby)
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨d, hd, r, hr⟩ := exists_int_mul_eq_integer c
    refine ⟨d * a, mul_ne_zero hd ha, ?_⟩
    have h : ((d * a : ℤ) : 𝓞 E) • (c • x) = r • ((a : 𝓞 E) • x) := by
      funext i
      simp only [Pi.smul_apply, Algebra.smul_def, map_intCast, Algebra.algebraMap_self,
        RingHom.id_apply, Int.cast_mul, map_mul]
      have hr' : algebraMap (𝓞 E) E r = (d : E) * c := hr
      rw [hr', Pi.mul_apply, Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      ring
    rw [h]
    exact Λ.smul_mem _ hax

end GlobalTheory.IntMulIntegerSmulMemLattice
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsCommonDenominatorForHermitianLatticeData
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DenClear

theorem ringOfIntegers_smul_eq {E : Type} [Field E] [NumberField E] (o : 𝓞 E) (x : E) :
    o • x = (o : E) * x := rfl

theorem coeO_mul {E : Type} [Field E] [NumberField E] (a b : 𝓞 E) :
    ((a * b : 𝓞 E) : E) = (a : E) * b := rfl

theorem coeO_add {E : Type} [Field E] [NumberField E] (a b : 𝓞 E) :
    ((a + b : 𝓞 E) : E) = (a : E) + b := rfl

theorem coeO_int {E : Type} [Field E] [NumberField E] (k : ℤ) : ((k : 𝓞 E) : E) = (k : E) := by
  rfl

theorem exists_int_mul_eq {E : Type} [Field E] [NumberField E] (e : E) :
    ∃ m : ℤ, m ≠ 0 ∧ ∃ o : 𝓞 E, (m : E) * e = o := by
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := E) {e}
  have h := hy e (Finset.mem_singleton_self e)
  rw [zsmul_eq_mul] at h
  exact ⟨y, hy0, ⟨(y : E) * e, h⟩, rfl⟩

theorem clear_of_dvd {E : Type} [Field E] [NumberField E] {m D : ℤ} (h : m ∣ D) {e : E}
    (he : ∃ o : 𝓞 E, (m : E) * e = o) : ∃ o : 𝓞 E, (D : E) * e = o := by
  obtain ⟨k, rfl⟩ := h
  obtain ⟨o, ho⟩ := he
  refine ⟨(k : 𝓞 E) * o, ?_⟩
  rw [coeO_mul, coeO_int, ← ho]
  push_cast
  ring

theorem exists_int_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) (hΛ : Submodule.IsFullLattice E Λ) (w : Fin n → E) :
    ∃ m : ℤ, m ≠ 0 ∧ (m : 𝓞 E) • w ∈ Λ := by
  exact _root_.GlobalTheory.IntMulIntegerSmulMemLattice.exists_int_smul_mem_lattice Λ hΛ w

theorem den_clear : ∀ {E : Type} [Field E] [NumberField E] {n : ℕ} {ι κ : Type} [Fintype ι] [Fintype κ] (v : ι → E) (g : κ → Fin n → E) (Hm : Matrix (Fin n) (Fin n) E) (sg : E →+* E) (Λ : Submodule (𝓞 E) (Fin n → E)), Submodule.IsFullLattice E Λ → ∃ D : ℤ, D ≠ 0 ∧ (∀ i, ∃ o : 𝓞 E, (D : E) * v i = o) ∧ (∀ x ∈ Λ, ∀ l, ∃ o : 𝓞 E, (D : E) * ∑ a, ∑ b, x a * Hm a b * sg (g l b) = o) ∧ ∀ l, (D : 𝓞 E) • g l ∈ Λ := by
  intro E _ _ n ι κ _ _ v g Hm sg Λ hΛ
  choose mv hmv0 hmv using fun i => exists_int_mul_eq (v i)
  choose mg hmg0 hmg using fun l => exists_int_smul_mem Λ hΛ (g l)
  obtain ⟨s, hs⟩ := Submodule.IsLattice.fg (A := E) (M := Λ)
  choose mp hmp0 hmp using fun (p : κ × (Fin n → E)) =>
    exists_int_mul_eq (∑ a, ∑ b, p.2 a * Hm a b * sg (g p.1 b))
  let T : Finset (κ × (Fin n → E)) := Finset.univ ×ˢ s
  let A : ℤ := ∏ i, mv i
  let B : ℤ := ∏ l, mg l
  let C : ℤ := ∏ p ∈ T, mp p
  have hA : A ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hmv0 i
  have hB : B ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hmg0 i
  have hC : C ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hmp0 i
  have dA : ∀ i, mv i ∣ A * B * C := fun i =>
    ((Finset.dvd_prod_of_mem mv (Finset.mem_univ i)).mul_right B).mul_right C
  have dB : ∀ l, mg l ∣ A * B * C := fun l =>
    ((Finset.dvd_prod_of_mem mg (Finset.mem_univ l)).mul_left A).mul_right C
  have dC : ∀ p ∈ T, mp p ∣ A * B * C := fun p hp =>
    (Finset.dvd_prod_of_mem mp hp).mul_left _
  refine ⟨A * B * C, mul_ne_zero (mul_ne_zero hA hB) hC, fun i => clear_of_dvd (dA i) (hmv i),
    ?_, ?_⟩
  · intro x hx l
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      exact clear_of_dvd (dC (l, x) (Finset.mem_product.2 ⟨Finset.mem_univ l, hx⟩)) (hmp (l, x))
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨o₁, h₁⟩ := hx
      obtain ⟨o₂, h₂⟩ := hy
      refine ⟨o₁ + o₂, ?_⟩
      rw [coeO_add, ← h₁, ← h₂, ← mul_add, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [Pi.add_apply]
      ring
    | smul c x _ hx =>
      obtain ⟨o, h⟩ := hx
      refine ⟨c * o, ?_⟩
      rw [coeO_mul, ← h]
      simp only [Pi.smul_apply, ringOfIntegers_smul_eq, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  · intro l
    obtain ⟨k, hk⟩ := dB l
    have : ((A * B * C : ℤ) : 𝓞 E) • g l = (k : 𝓞 E) • ((mg l : 𝓞 E) • g l) := by
      rw [smul_smul, hk]
      push_cast
      rw [mul_comm]
    rw [this]
    exact Λ.smul_mem _ (hmg l)

end GlobalTheory.DenClear
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsCommonDenominatorForHermitianLatticeDataStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_denominator_for_hermitian_lattice_data : ∀ {E : Type} [Field E] [NumberField E] {n : ℕ} {ι κ : Type} [Fintype ι] [Fintype κ] (v : ι → E) (g : κ → Fin n → E) (Hm : Matrix (Fin n) (Fin n) E) (sg : E →+* E) (Λ : Submodule (𝓞 E) (Fin n → E)), Submodule.IsFullLattice E Λ → ∃ D : ℤ, D ≠ 0 ∧ (∀ i, ∃ o : 𝓞 E, (D : E) * v i = o) ∧ (∀ x ∈ Λ, ∀ l, ∃ o : 𝓞 E, (D : E) * ∑ a, ∑ b, x a * Hm a b * sg (g l b) = o) ∧ ∀ l, (D : 𝓞 E) • g l ∈ Λ := by
  exact @GlobalTheory.DenClear.den_clear
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularCloseToOneInverseClose
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularCloseToOneInverseClose
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory

theorem unitriangular_inv_close {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (n : ℕ) (M : Matrix (Fin n) (Fin n) E) (t : E) (ht : t ∈ L.O) (hlow : ∀ i j, j < i → M i j = 0) (hdiag : ∀ i, M i i = 1) (hcl : ∀ i j, ∃ o ∈ L.O, (M - 1) i j = t * o) : ∃ Mi : Matrix (Fin n) (Fin n) E, Mi * M = 1 ∧ M * Mi = 1 ∧ ∀ i j, ∃ o ∈ L.O, (Mi - 1) i j = t * o := by
  have hMO : ∀ i j, M i j ∈ L.O := by
    intro i j
    obtain ⟨o, ho, he⟩ := hcl i j
    have : M i j = t * o + (1 : Matrix (Fin n) (Fin n) E) i j := by
      rw [← he]; simp
    rw [this]
    refine L.O.add_mem (L.O.mul_mem ht ho) ?_
    by_cases h : i = j
    · subst h; simp [L.O.one_mem]
    · simp [h, L.O.zero_mem]
  let f : L.O →+* E := L.O.subtype
  let M' : Matrix (Fin n) (Fin n) L.O := Matrix.of fun i j => ⟨M i j, hMO i j⟩
  have hM' : f.mapMatrix M' = M := by
    ext i j; rfl
  have hdet : M'.det = 1 := by
    apply Subtype.ext
    have h1 : f M'.det = (f.mapMatrix M').det := RingHom.map_det f M'
    have h2 : M.det = 1 := by
      rw [Matrix.det_of_upperTriangular (M := M) (fun i j hij => hlow i j hij)]
      simp [hdiag]
    change f M'.det = f 1
    rw [h1, hM', h2, map_one]
  have hu : IsUnit M'.det := by rw [hdet]; exact isUnit_one
  refine ⟨f.mapMatrix M'⁻¹, ?_, ?_, ?_⟩
  · rw [← hM', ← map_mul, Matrix.nonsing_inv_mul _ hu, map_one]
  · rw [← hM', ← map_mul, Matrix.mul_nonsing_inv _ hu, map_one]
  · intro i j
    set Mi := f.mapMatrix M'⁻¹ with hMi
    have hinv : Mi * M = 1 := by
      rw [hMi, ← hM', ← map_mul, Matrix.nonsing_inv_mul _ hu, map_one]
    have key : Mi - 1 = -(Mi * (M - 1)) := by
      rw [Matrix.mul_sub, hinv, Matrix.mul_one]; abel
    choose o ho he using hcl
    refine ⟨-(∑ k, (M'⁻¹ i k : E) * o k j), ?_, ?_⟩
    · exact L.O.neg_mem (L.O.sum_mem fun k _ => L.O.mul_mem (M'⁻¹ i k).2 (ho k j))
    · rw [key, Matrix.neg_apply, Matrix.mul_apply]
      simp only [he]
      rw [mul_neg, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [hMi, f]
      ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularCloseToOneInverseCloseStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitriangular_close_to_one_inverse_close : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (n : ℕ) (M : Matrix (Fin n) (Fin n) E) (t : E), t ∈ L.O → (∀ i j, j < i → M i j = 0) → (∀ i, M i i = 1) → (∀ i j, ∃ o ∈ L.O, (M - 1) i j = t * o) → ∃ Mi : Matrix (Fin n) (Fin n) E, Mi * M = 1 ∧ M * Mi = 1 ∧ ∀ i j, ∃ o ∈ L.O, (Mi - 1) i j = t * o := by
  first | exact @GlobalTheory.unitriangular_inv_close | exact GlobalTheory.unitriangular_inv_close | (intros; apply GlobalTheory.unitriangular_inv_close <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CloseOnCompletedLatticeOfCloseOnFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CloseOnCompletedLatticeOfCloseOnFrames
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.LatClose

section
variable {K R : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [CommRing R] [Algebra K R] [TopologicalSpace R]
  (L : LocE K R) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) R)

theorem hf_add_right (x a b : Fin n → R) : hf L Hm x (a + b) = hf L Hm x a + hf L Hm x b := by
  simp [hf, mul_add, Finset.sum_add_distrib]

theorem hf_smul_right (x : Fin n → R) (c : R) (a : Fin n → R) : hf L Hm x (c • a) = L.cj c * hf L Hm x a := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hf_zero_right (x : Fin n → R) : hf L Hm x 0 = 0 := by simp [hf]
end

theorem form_sub_sum {E : Type} [Field E] {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) {ι : Type} [Fintype ι] (x : Fin n → E) (a : ι → E)
    (v : ι → Fin n → E) (s : Fin n → E) :
    ∑ i, ∑ j, (x - ∑ k, a k • v k) i * Hm i j * s j =
      (∑ i, ∑ j, x i * Hm i j * s j) - ∑ k, a k * ∑ i, ∑ j, v k i * Hm i j * s j := by
  simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib,
    Finset.sum_mul, Finset.mul_sum]
  congr 1
  calc _ = ∑ i, ∑ k, ∑ j, a k * v k i * Hm i j * s j :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  (A : Places F E sig) (p : HeightOneSpectrum (𝓞 F)) {n : ℕ}

theorem bc_add (x y : Fin n → E) : A.bc p (x + y) = A.bc p x + A.bc p y := by
  funext i; simp [Places.bc]
theorem bc_smul (c : E) (x : Fin n → E) : A.bc p (c • x) = (A.loc p).ιE c • A.bc p x := by
  funext i; simp [Places.bc]
theorem bc_sum {ι : Type} (s : Finset ι) (x : ι → Fin n → E) :
    A.bc p (∑ i ∈ s, x i) = ∑ i ∈ s, A.bc p (x i) := by
  funext j; simp [Places.bc, Finset.sum_apply]
theorem bc_mem_lat (Λ : Submodule (𝓞 E) (Fin n → E)) {x : Fin n → E} (hx : x ∈ Λ) :
    A.bc p x ∈ A.lat p Λ :=
  Submodule.subset_span ⟨x, hx, rfl⟩

end

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}

theorem step (A : Places F E sig) (p : HeightOneSpectrum (𝓞 F)) {n m : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E))
    (D : ℤ) (h : (Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep))
    (g : Fin m → Fin n → E) (Mx : Matrix (Fin m) (Fin m) (A.loc p).Ep) (t : (A.loc p).Fp)
    (hg : ∀ j, h (A.bc p (g j)) = ∑ i, Mx i j • A.bc p (g i))
    (hMx : ∀ i j, ∃ o ∈ (A.L p).O, (Mx - 1) i j =
      algebraMap (A.loc p).Fp (A.loc p).Ep (t * (D : (A.loc p).Fp) ^ 3) * o)
    (hgΛ : ∀ i, (D : 𝓞 E) • g i ∈ Λ) (a : E) (ha : ∃ o : 𝓞 E, (D : E) ^ 2 * a = o) (j : Fin m) :
    ∃ z ∈ A.lat p Λ, (A.loc p).ιE a • (h (A.bc p (g j)) - A.bc p (g j)) =
      algebraMap (A.loc p).Fp (A.loc p).Ep t • z := by
  obtain ⟨oa, hoa⟩ := ha
  choose o ho hoeq using hMx
  have hdiff : h (A.bc p (g j)) - A.bc p (g j) = ∑ i, (Mx - 1) i j • A.bc p (g i) := by
    rw [hg]
    simp [Matrix.sub_apply, Matrix.one_apply, sub_smul, Finset.sum_sub_distrib]
  refine ⟨∑ i, (⟨o i j, ho i j⟩ : (A.L p).O) • A.bc p (oa • ((D : 𝓞 E) • g i)),
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (bc_mem_lat A p Λ (Λ.smul_mem _ (hgΛ i))), ?_⟩
  rw [hdiff, Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e1 : (oa • ((D : 𝓞 E) • g i) : Fin n → E) = ((D : E) ^ 3 * a) • g i := by
    change (oa : E) • (((D : 𝓞 E) : E) • g i) = _
    have hD : ((D : 𝓞 E) : E) = (D : E) := by simp
    rw [smul_smul, ← hoa, hD]
    congr 1
    ring
  rw [Subring.smul_def, e1, bc_smul, hoeq, smul_smul, smul_smul, smul_smul]
  congr 1
  simp only [map_mul, map_pow, map_intCast]
  ring
end

theorem close_on_lattice : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig) (r k : ℕ) (G : GFrames A r k) (Λ : G.Lt) (D : ℤ) (p : HeightOneSpectrum (𝓞 F)) (h : (G.S p).GLV) (M M' : Matrix (Fin (r + 1)) (Fin (r + 1)) (A.loc p).Ep) (t : (A.loc p).Fp), (Matrix.of fun k l : Fin (r + 1) ⊕ Fin (r + 1) => ∑ i, ∑ j, Sum.elim G.f G.f' k i * G.Hm i j * sig (Sum.elim G.f G.f' l j))⁻¹ * (Matrix.of fun k l : Fin (r + 1) ⊕ Fin (r + 1) => ∑ i, ∑ j, Sum.elim G.f G.f' k i * G.Hm i j * sig (Sum.elim G.f G.f' l j)) = 1 → (∀ k l, ∃ o : 𝓞 E, (D : E) * (Matrix.of fun k l : Fin (r + 1) ⊕ Fin (r + 1) => ∑ i, ∑ j, Sum.elim G.f G.f' k i * G.Hm i j * sig (Sum.elim G.f G.f' l j))⁻¹ k l = o) → (∀ x ∈ Λ, ∀ l, ∃ o : 𝓞 E, (D : E) * ∑ a, ∑ b, x a * G.Hm a b * sig (Sum.elim G.f G.f' l b) = o) → (∀ l, (D : 𝓞 E) • Sum.elim G.f G.f' l ∈ Λ) → h ∈ (G.S p).St → (∀ j, h (A.bc p (G.f j)) = ∑ i, M i j • A.bc p (G.f i)) → (∀ j, h (A.bc p (G.f' j)) = ∑ i, M' i j • A.bc p (G.f' i)) → (∀ i j, ∃ o ∈ (A.L p).O, (M - 1) i j = algebraMap (A.loc p).Fp (A.loc p).Ep (t * (D : (A.loc p).Fp) ^ 3) * o) → (∀ i j, ∃ o ∈ (A.L p).O, (M' - 1) i j = algebraMap (A.loc p).Fp (A.loc p).Ep (t * (D : (A.loc p).Fp) ^ 3) * o) → ∀ x ∈ A.lat p Λ, ∃ y ∈ A.lat p Λ, h x - x = algebraMap (A.loc p).Fp (A.loc p).Ep t • y := by
  intro F E _ _ _ _ _ sig A r k G Λ D p h M M' t hΓ hΓD hb hDu hh hM hM' hM1 hM1'
  haveI := (A.loc p).lf
  haveI := (A.loc p).char0
  have key : ∀ l ∈ Λ, ∃ y ∈ A.lat p Λ,
      h (A.bc p l) - A.bc p l = algebraMap (A.loc p).Fp (A.loc p).Ep t • y := by
    intro l hl
    set Γ : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) E :=
      Matrix.of fun k l => ∑ i, ∑ j, Sum.elim G.f G.f' k i * G.Hm i j * sig (Sum.elim G.f G.f' l j)
      with hΓdef
    have hbl : ∀ m, ∃ o : 𝓞 E, (D : E) * ∑ i, ∑ j, l i * G.Hm i j * sig (Sum.elim G.f G.f' m j) = o :=
      hb l hl
    choose ob hob using hbl
    choose og hog using hΓD
    let b : Fin (r + 1) ⊕ Fin (r + 1) → E := fun m => ∑ i, ∑ j, l i * G.Hm i j * sig (Sum.elim G.f G.f' m j)
    let α := Matrix.vecMul b Γ⁻¹
    let w := l - ∑ q, α q • Sum.elim G.f G.f' q
    have hw0 : ∀ m, ∑ i, ∑ j, w i * G.Hm i j * sig (Sum.elim G.f G.f' m j) = 0 := by
      intro m
      rw [form_sub_sum]
      have e : ∑ q, α q * ∑ i, ∑ j, Sum.elim G.f G.f' q i * G.Hm i j * sig (Sum.elim G.f G.f' m j) =
          Matrix.vecMul α Γ m := rfl
      rw [e, Matrix.vecMul_vecMul, hΓ, Matrix.vecMul_one, sub_self]
    have hwloc : ∀ m, hf (A.L p) (G.S p).Hm (A.bc p w) (A.bc p (Sum.elim G.f G.f' m)) = 0 := by
      intro m
      rw [G.Hm_eq p, (RatExt.rational_extend A (k + 2 * r + 1) p).2.2.2.2.1, hw0, map_zero]
    have hwW : A.bc p w ∈ (G.S p).W0 := by
      have hME : (G.S p).ME = Submodule.span _ (Set.range (Sum.elim (G.S p).f (G.S p).f')) := by
        rw [Frames.ME, FrameStab.spanTo_top, FrameStab.spanTo_top, Set.Sum.elim_range, Submodule.span_union]
      change ∀ y ∈ (G.S p).ME, hf (A.L p) (G.S p).Hm (A.bc p w) y = 0
      intro y hy
      rw [hME] at hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨q, rfl⟩ := hy
        rcases q with a | a
        · have e := G.f_eq p a
          have h0 := hwloc (Sum.inl a)
          simp only [Sum.elim_inl] at h0 ⊢
          rw [← e, hf_smul_right, AlgEquiv.commutes] at h0
          exact ((((G.c p).isUnit.pow _).map (algebraMap _ _)).mul_right_eq_zero).1 h0
        · have e := G.f'_eq p a
          have h0 := hwloc (Sum.inr a)
          simp only [Sum.elim_inr] at h0 ⊢
          rw [← e, hf_smul_right, AlgEquiv.commutes] at h0
          exact ((((G.c p).isUnit.pow _).map (algebraMap _ _)).mul_right_eq_zero).1 h0
      | zero => exact hf_zero_right _ _ _
      | add x y _ _ hx hy => rw [hf_add_right, hx, hy, add_zero]
      | smul c x _ hx => rw [hf_smul_right, hx, mul_zero]
    have hhw : h (A.bc p w) = A.bc p w := (FrameStab.stab_eq (A.L p) r k (G.S p)).1 h hh _ hwW
    have hl' : l = w + ∑ q, α q • Sum.elim G.f G.f' q := by simp only [w, sub_add_cancel]
    have hsplit : h (A.bc p l) - A.bc p l = ∑ q, (A.loc p).ιE (α q) •
        (h (A.bc p (Sum.elim G.f G.f' q)) - A.bc p (Sum.elim G.f G.f' q)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hl', bc_add, bc_sum, map_add (f := _), map_sum, hhw]
      simp only [bc_smul, map_smul, smul_sub, Finset.sum_sub_distrib]
      abel
    have hα : ∀ q, ∃ o : 𝓞 E, (D : E) ^ 2 * α q = o := by
      intro q
      refine ⟨∑ m, ob m * og m q, ?_⟩
      have e : ((∑ m, ob m * og m q : 𝓞 E) : E) = ∑ m, ((ob m : 𝓞 E) : E) * ((og m q : 𝓞 E) : E) := by
        simp
      rw [e]
      simp only [α, Matrix.vecMul, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      linear_combination ((D : E) * Γ⁻¹ m q) * hob m + ((ob m : 𝓞 E) : E) * hog m q
    have hper : ∀ q, ∃ z ∈ A.lat p Λ, (A.loc p).ιE (α q) •
        (h (A.bc p (Sum.elim G.f G.f' q)) - A.bc p (Sum.elim G.f G.f' q)) =
          algebraMap (A.loc p).Fp (A.loc p).Ep t • z := by
      rintro (j | j)
      · exact step A p Λ D h G.f M t hM hM1 (fun i => hDu (Sum.inl i)) (α (Sum.inl j)) (hα _) j
      · exact step A p Λ D h G.f' M' t hM' hM1' (fun i => hDu (Sum.inr i)) (α (Sum.inr j)) (hα _) j
    choose z hz hze using hper
    exact ⟨∑ q, z q, Submodule.sum_mem _ fun q _ => hz q, by
      rw [hsplit, Finset.smul_sum]; exact Finset.sum_congr rfl fun q _ => hze q⟩
  intro x hx
  change x ∈ Submodule.span _ _ at hx
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨l, hl, rfl⟩ := hx; exact key l hl
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add a b _ _ ha hb' =>
    obtain ⟨y1, hy1, e1⟩ := ha
    obtain ⟨y2, hy2, e2⟩ := hb'
    exact ⟨y1 + y2, add_mem hy1 hy2, by rw [map_add (f := _), smul_add, ← e1, ← e2]; abel⟩
  | smul c a _ ha =>
    obtain ⟨y, hy, e⟩ := ha
    refine ⟨c • y, Submodule.smul_mem _ c hy, ?_⟩
    rw [Subring.smul_def, Subring.smul_def, map_smul, ← smul_sub, e, smul_comm]

end GlobalTheory.HL.LatClose
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CloseOnCompletedLatticeOfCloseOnFramesStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.close_on_completed_lattice_of_close_on_frames : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig) (r k : ℕ) (G : GFrames A r k) (Λ : G.Lt) (D : ℤ) (p : HeightOneSpectrum (𝓞 F)) (h : (G.S p).GLV) (M M' : Matrix (Fin (r + 1)) (Fin (r + 1)) (A.loc p).Ep) (t : (A.loc p).Fp), (Matrix.of fun k l : Fin (r + 1) ⊕ Fin (r + 1) => ∑ i, ∑ j, Sum.elim G.f G.f' k i * G.Hm i j * sig (Sum.elim G.f G.f' l j))⁻¹ * (Matrix.of fun k l : Fin (r + 1) ⊕ Fin (r + 1) => ∑ i, ∑ j, Sum.elim G.f G.f' k i * G.Hm i j * sig (Sum.elim G.f G.f' l j)) = 1 → (∀ k l, ∃ o : 𝓞 E, (D : E) * (Matrix.of fun k l : Fin (r + 1) ⊕ Fin (r + 1) => ∑ i, ∑ j, Sum.elim G.f G.f' k i * G.Hm i j * sig (Sum.elim G.f G.f' l j))⁻¹ k l = o) → (∀ x ∈ Λ, ∀ l, ∃ o : 𝓞 E, (D : E) * ∑ a, ∑ b, x a * G.Hm a b * sig (Sum.elim G.f G.f' l b) = o) → (∀ l, (D : 𝓞 E) • Sum.elim G.f G.f' l ∈ Λ) → h ∈ (G.S p).St → (∀ j, h (A.bc p (G.f j)) = ∑ i, M i j • A.bc p (G.f i)) → (∀ j, h (A.bc p (G.f' j)) = ∑ i, M' i j • A.bc p (G.f' i)) → (∀ i j, ∃ o ∈ (A.L p).O, (M - 1) i j = algebraMap (A.loc p).Fp (A.loc p).Ep (t * (D : (A.loc p).Fp) ^ 3) * o) → (∀ i j, ∃ o ∈ (A.L p).O, (M' - 1) i j = algebraMap (A.loc p).Fp (A.loc p).Ep (t * (D : (A.loc p).Fp) ^ 3) * o) → ∀ x ∈ A.lat p Λ, ∃ y ∈ A.lat p Λ, h x - x = algebraMap (A.loc p).Fp (A.loc p).Ep t • y := by
  first | exact @GlobalTheory.HL.LatClose.close_on_lattice | exact GlobalTheory.HL.LatClose.close_on_lattice | (intros; apply GlobalTheory.HL.LatClose.close_on_lattice <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameMatrixCloseGivesLatticeCloseIntegral
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.FrameClose

section Loc
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem algebraMap_mem (L : LocE F E) {a : F} (ha : a ∈ 𝒪[F]) : algebraMap F E a ∈ L.O := by
  rw [L.O_def]
  exact isIntegral_algebraMap (R := 𝒪[F]) (x := (⟨a, ha⟩ : 𝒪[F]))

theorem inv_mem {a : F} (h : a ∉ 𝒪[F]) : a⁻¹ ∈ 𝒪[F] := by
  have h' : ¬ valuation F a ≤ 1 := h
  show valuation F a⁻¹ ≤ 1
  rw [map_inv₀]
  exact inv_le_one_of_one_le₀ (le_of_lt (not_le.1 h'))

theorem coord_scale {n r : ℕ} (g : Fin (r + 1) → Fin n → E) (hg : LinearIndependent E g)
    (h : (Fin n → E) ≃ₗ[E] (Fin n → E)) (la : Fin (r + 1) → E) (s M : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hs : ∀ j, h (g j) = ∑ i, s i j • g i) (hM : ∀ j, h (la j • g j) = ∑ i, M i j • (la i • g i)) :
    ∀ i j, M i j * la i = la j * s i j := by
  intro i j
  have h1 : ∑ i, (M i j * la i - la j * s i j) • g i = 0 := by
    have e1 : ∑ i, M i j • (la i • g i) = ∑ i, (M i j * la i) • g i :=
      Finset.sum_congr rfl fun i _ => (smul_smul _ _ _)
    have e2 : h (la j • g j) = ∑ i, (la j * s i j) • g i := by
      rw [map_smul, hs j, Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => (smul_smul _ _ _)
    have := hM j
    rw [e1, e2] at this
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [this, sub_self]
  have := Fintype.linearIndependent_iff.1 hg _ h1 i
  exact sub_eq_zero.1 this

end Loc
end GlobalTheory.HL.FrameClose

namespace GlobalTheory.HL.FrameClose
section Loc2
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem pair_fix (L : LocE F E) {r n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (u u' : Fin (r + 1) → Fin n → E)
    (h : (Fin n → E) ≃ₗ[E] (Fin n → E)) (hi : ∀ x y, hf L Hm (h x) (h y) = hf L Hm x y)
    (M M' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hM : ∀ j, h (u j) = ∑ i, M i j • u i)
    (hM' : ∀ j, h (u' j) = ∑ i, M' i j • u' i) :
    cT L M * Matrix.of (fun i j => hf L Hm (u' j) (u i)) * M' = Matrix.of (fun i j => hf L Hm (u' j) (u i)) := by
  ext a b
  rw [Matrix.of_apply, ← hi, hM', hM, GlobalTheory.HL.FrameStab.hf_sum]
  simp only [Matrix.mul_apply, Finset.sum_mul, cT, Matrix.of_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem scale_int (L : LocE F E) {r : ℕ} (c a q : F) (hc : c ≠ 0) (ha : a ∈ 𝒪[F]) (hac : a * c ∈ 𝒪[F])
    (hq : q ∈ 𝒪[F]) (i j : Fin (r + 1)) (hij : i < j) (x y : E)
    (hx : ∃ o ∈ L.O, x = algebraMap F E (q * a ^ r) * o)
    (hrel : x * algebraMap F E (c ^ (r - (i : ℕ))) = algebraMap F E (c ^ (r - (j : ℕ))) * y) : y ∈ L.O := by
  obtain ⟨o, ho, rfl⟩ := hx
  have hij' : (i : ℕ) < j := hij
  have hj : (j : ℕ) ≤ r := Nat.lt_succ_iff.1 j.2
  have hr : r - (i : ℕ) = (r - (j : ℕ)) + ((j : ℕ) - i) := by omega
  have hr2 : r = (r - ((j : ℕ) - i)) + ((j : ℕ) - i) := by omega
  have hu : IsUnit (algebraMap F E (c ^ (r - (j : ℕ)))) := (IsUnit.mk0 _ (pow_ne_zero _ hc)).map (algebraMap F E)
  have hy : y = algebraMap F E (q * (a ^ (r - ((j : ℕ) - i)) * (a * c) ^ ((j : ℕ) - i))) * o := by
    have p1 : c ^ (r - (i : ℕ)) = c ^ (r - (j : ℕ)) * c ^ ((j : ℕ) - i) := by rw [← pow_add, ← hr]
    have p2 : a ^ r = a ^ (r - ((j : ℕ) - i)) * a ^ ((j : ℕ) - i) := by rw [← pow_add, ← hr2]
    apply hu.mul_right_injective
    dsimp only
    rw [← hrel, p1, p2]
    simp only [map_mul, map_pow, mul_pow]
    ring
  rw [hy]
  exact L.O.mul_mem (algebraMap_mem L (mul_mem hq (mul_mem (pow_mem ha _) (pow_mem hac _)))) ho

theorem int_inv (L : LocE F E) {n : ℕ} (s : Matrix (Fin n) (Fin n) E) (hlow : ∀ i j, j < i → s i j = 0)
    (hdiag : ∀ i, s i i = 1) (hO : ∀ i j, s i j ∈ L.O) :
    ∃ si : Matrix (Fin n) (Fin n) E, s * si = 1 ∧ ∀ i j, si i j ∈ L.O := by
  have h1O : ∀ i j, (1 : Matrix (Fin n) (Fin n) E) i j ∈ L.O := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · exact L.O.one_mem
    · exact L.O.zero_mem
  obtain ⟨si, -, h2, h3⟩ := GlobalTheory.T.unitriangular_close_to_one_inverse_close L n s 1 L.O.one_mem hlow hdiag
    (fun i j => ⟨(s - 1) i j, L.O.sub_mem (hO i j) (h1O i j), (one_mul _).symm⟩)
  refine ⟨si, h2, fun i j => ?_⟩
  obtain ⟨o, ho, he⟩ := h3 i j
  have : si i j = o + (1 : Matrix (Fin n) (Fin n) E) i j := by
    rw [one_mul, Matrix.sub_apply] at he
    rw [← he]; ring
  rw [this]
  exact L.O.add_mem ho (h1O i j)

variable [IsNonarchimedeanLocalField F] [CharZero F]

theorem loc_close (L : LocE F E) (r k : ℕ) (S : Frames L r k) (c a t e : F)
    (Zi : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (h : S.GLV) (M : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hc : c ≠ 0) (ha : a ∈ 𝒪[F]) (hac : a * c ∈ 𝒪[F]) (ht : t ∈ 𝒪[F]) (he : e ∈ 𝒪[F]) (he0 : e ≠ 0)
    (hZi : Zi * Matrix.of (fun i j : Fin (r + 1) => hf L S.Hm (algebraMap F E (c ^ (r - (j : ℕ))) • S.f' j)
      (algebraMap F E (c ^ (r - (i : ℕ))) • S.f i)) = 1)
    (hZ : ∀ i j : Fin (r + 1), algebraMap F E e * hf L S.Hm (algebraMap F E (c ^ (r - (j : ℕ))) • S.f' j)
      (algebraMap F E (c ^ (r - (i : ℕ))) • S.f i) ∈ L.O)
    (hZi' : ∀ i j, algebraMap F E e * Zi i j ∈ L.O) (hh : h ∈ S.St)
    (hM : ∀ j : Fin (r + 1), h (algebraMap F E (c ^ (r - (j : ℕ))) • S.f j) =
      ∑ i, M i j • (algebraMap F E (c ^ (r - (i : ℕ))) • S.f i))
    (hcl : ∀ i j, ∃ o ∈ L.O, (M - 1) i j = algebraMap F E (t * e ^ 2 * a ^ r) * o) :
    h ∈ S.K0 ∧ ∃ M' : Matrix (Fin (r + 1)) (Fin (r + 1)) E,
      (∀ j : Fin (r + 1), h (algebraMap F E (c ^ (r - (j : ℕ))) • S.f' j) =
        ∑ i, M' i j • (algebraMap F E (c ^ (r - (i : ℕ))) • S.f' i)) ∧
      ∀ i j, ∃ o ∈ L.O, (M' - 1) i j = algebraMap F E (t * a ^ r) * o := by
  have := L.free
  have hnt : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; norm_num)
  have hinj : Function.Injective (algebraMap F E) := (algebraMap F E).injective
  obtain ⟨hli, -⟩ := GlobalTheory.FrameBasic.main L r k S
  have hli1 : LinearIndependent E S.f := (linearIndependent_sum.1 hli).1
  obtain ⟨hN, hN', -⟩ := GlobalTheory.HL.FrameOnto.unipotent_onto L r k S
  have hhN : h ∈ S.N := (Subgroup.mem_inf.1 hh).1
  have hhN' : h ∈ S.N' := (Subgroup.mem_inf.1 hh).2
  obtain ⟨s, hs, hsf⟩ := hN h hhN
  obtain ⟨s', hs', hsf'⟩ := hN' h hhN'
  have hiso : ∀ x y, hf L S.Hm (h x) (h y) = hf L S.Hm x y := hhN.1.1
  set cp : Fin (r + 1) → E := fun j => algebraMap F E (c ^ (r - (j : ℕ))) with hcp
  have hcpu : ∀ j, IsUnit (cp j) := fun j => (IsUnit.mk0 _ (pow_ne_zero _ hc)).map (algebraMap F E)

  have hMs := coord_scale S.f hli1 h cp s M hsf hM
  have hMlow : ∀ i j, j < i → M i j = 0 := by
    intro i j hij
    have := hMs i j
    rw [hs.1 i j hij, mul_zero] at this
    exact (hcpu i).mul_left_eq_zero.1 this
  have hMdiag : ∀ i, M i i = 1 := by
    intro i
    have := hMs i i
    rw [hs.2 i, mul_one] at this
    exact (hcpu i).mul_left_inj.1 (this.trans (one_mul _).symm)

  set M' : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
    Matrix.of fun i j => algebraMap F E (c ^ (r - (j : ℕ)) / c ^ (r - (i : ℕ))) * s' i j with hM'def
  have hM' : ∀ j, h (cp j • S.f' j) = ∑ i, M' i j • (cp i • S.f' i) := by
    intro j
    rw [map_smul, hsf' j, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, smul_smul]
    congr 1
    have e1 : algebraMap F E (c ^ (r - (j : ℕ)) / c ^ (r - (i : ℕ))) * algebraMap F E (c ^ (r - (i : ℕ))) =
        algebraMap F E (c ^ (r - (j : ℕ))) := by
      rw [← map_mul, div_mul_cancel₀ _ (pow_ne_zero _ hc)]
    simp only [hM'def, hcp, Matrix.of_apply]
    linear_combination (-(s' i j)) * e1

  have hpair := pair_fix L S.Hm (fun j => cp j • S.f j) (fun j => cp j • S.f' j) h hiso M M' hM hM'
  have htO : algebraMap F E (t * e ^ 2 * a ^ r) ∈ L.O :=
    algebraMap_mem L (mul_mem (mul_mem ht (pow_mem he _)) (pow_mem ha _))
  obtain ⟨Mi, hMi1, hMi2, hMi⟩ := GlobalTheory.T.unitriangular_close_to_one_inverse_close L (r + 1) M _ htO hMlow hMdiag hcl
  have hcl' := GlobalTheory.T.pairing_conj_inverseAdjoint_close_to_one L (r + 1) _ Zi M Mi M' _ (algebraMap F E e) htO
    (by rw [L.cj_fix]; exact ⟨_, rfl⟩) hZi hZ hZi' hMi1 hMi2 hMi hpair
  have heu : IsUnit (algebraMap F E e) := (IsUnit.mk0 _ he0).map (algebraMap F E)
  have hM'cl : ∀ i j, ∃ o ∈ L.O, (M' - 1) i j = algebraMap F E (t * a ^ r) * o := by
    intro i j
    obtain ⟨o, ho, hoe⟩ := hcl' i j
    refine ⟨o, ho, ?_⟩
    have : algebraMap F E e * algebraMap F E e * ((M' - 1) i j - algebraMap F E (t * a ^ r) * o) = 0 := by
      rw [mul_sub, hoe]
      simp only [map_mul, map_pow]
      ring
    exact sub_eq_zero.1 ((heu.mul heu).mul_right_eq_zero.1 this)
  refine ⟨?_, M', hM', hM'cl⟩
  have hsO : ∀ i j, s i j ∈ L.O := by
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hij
    · refine scale_int L c a (t * e ^ 2) hc ha hac (mul_mem ht (pow_mem he _)) i j hij (M i j) (s i j) ?_ (hMs i j)
      obtain ⟨o, ho, hoe⟩ := hcl i j
      refine ⟨o, ho, ?_⟩
      rw [Matrix.sub_apply, Matrix.one_apply_ne (ne_of_lt hij), sub_zero] at hoe
      rw [hoe]
    · rw [hs.2 i]; exact L.O.one_mem
    · rw [hs.1 i j hij]; exact L.O.zero_mem
  have hs'O : ∀ i j, s' i j ∈ L.O := by
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hij
    · refine scale_int L c a t hc ha hac ht i j hij (M' i j) (s' i j) ?_ ?_
      · obtain ⟨o, ho, hoe⟩ := hM'cl i j
        refine ⟨o, ho, ?_⟩
        rw [Matrix.sub_apply, Matrix.one_apply_ne (ne_of_lt hij), sub_zero] at hoe
        rw [hoe]
      · simp only [hM'def, Matrix.of_apply]
        rw [mul_comm _ (s' i j), mul_assoc, ← map_mul, div_mul_cancel₀ _ (pow_ne_zero _ hc), mul_comm]
    · rw [hs'.2 i]; exact L.O.one_mem
    · rw [hs'.1 i j hij]; exact L.O.zero_mem
  obtain ⟨si, hsi, hsiO⟩ := int_inv L s hs.1 hs.2 hsO
  obtain ⟨si', hsi', hsi'O⟩ := int_inv L s' hs'.1 hs'.2 hs'O
  exact GlobalTheory.T.mem_maximal_compact_of_integral L r k S h s si s' si' hh hsO hsiO hsi hs'O hsi'O hsi' hsf hsf'

end Loc2
end GlobalTheory.HL.FrameClose

namespace GlobalTheory.HL.FrameClose

theorem close_lattice : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), ∀ Λ : G.Lt, Submodule.IsFullLattice E Λ → ∃ d : ∀ p, (A.loc p).Fp, (∀ p, d p ≠ 0) ∧ {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = d p}.Finite ∧ ∀ p (c0 : (A.loc p).Fp) (h : (G.S p).GLV) (M : Matrix (Fin (r + 1)) (Fin (r + 1)) (A.loc p).Ep), c0 ≠ 0 → c0 ∈ 𝒪[(A.loc p).Fp] → h ∈ (G.S p).St → (∀ j, h (A.bc p (G.f j)) = ∑ i, M i j • A.bc p (G.f i)) → (∀ i j, ∃ o ∈ (A.L p).O, (M - 1) i j = algebraMap (A.loc p).Fp (A.loc p).Ep (c0 * d p) * o) → h ∈ (G.S p).K0 ∧ ∀ x ∈ A.lat p Λ, ∃ y ∈ A.lat p Λ, h x - x = algebraMap (A.loc p).Fp (A.loc p).Ep c0 • y := by
  intro F E _ _ _ _ _ sig A r k G Λ hΛ
  have hZinv := GlobalTheory.T.rationalPairingMatrix_inv_mul_self A r k G
  have hΓinv := GlobalTheory.T.globalFrames_joint_gram_inv_mul_self A r k G
  obtain ⟨D, hD0, hDv, hDpair, hDg⟩ := GlobalTheory.T.exists_common_denominator_for_hermitian_lattice_data
    (Sum.elim (fun ab : Fin (r + 1) × Fin (r + 1) => G.Zh ab.1 ab.2)
      (Sum.elim (fun ab : Fin (r + 1) × Fin (r + 1) => G.Zh⁻¹ ab.1 ab.2)
        (fun kl : (Fin (r + 1) ⊕ Fin (r + 1)) × (Fin (r + 1) ⊕ Fin (r + 1)) =>
          (Matrix.of fun k l : Fin (r + 1) ⊕ Fin (r + 1) => ∑ i, ∑ j, Sum.elim G.f G.f' k i * G.Hm i j *
            sig (Sum.elim G.f G.f' l j))⁻¹ kl.1 kl.2)))
    (Sum.elim G.f G.f') G.Hm (sig : E →+* E) Λ hΛ
  let a : ∀ p, (A.loc p).Fp := fun p =>
    if ((G.c p : (A.loc p).Fp) ∈ 𝒪[(A.loc p).Fp]) then 1 else (G.c p : (A.loc p).Fp)⁻¹
  have ha : ∀ p, a p ∈ 𝒪[(A.loc p).Fp] ∧ a p * G.c p ∈ 𝒪[(A.loc p).Fp] ∧ a p ≠ 0 := by
    intro p
    by_cases hc : ((G.c p : (A.loc p).Fp) ∈ 𝒪[(A.loc p).Fp])
    · simp only [a, if_pos hc, one_mul]
      exact ⟨one_mem _, hc, one_ne_zero⟩
    · simp only [a, if_neg hc]
      exact ⟨inv_mem hc, by rw [inv_mul_cancel₀ (Units.ne_zero _)]; exact one_mem _,
        inv_ne_zero (Units.ne_zero _)⟩
  refine ⟨fun p => (D : (A.loc p).Fp) ^ 5 * a p ^ r, fun p => ?_, ?_, ?_⟩
  · have : (D : (A.loc p).Fp) ≠ 0 := by
      haveI := (A.loc p).char0
      exact_mod_cast hD0
    exact mul_ne_zero (pow_ne_zero _ this) (pow_ne_zero _ (ha p).2.2)
  · refine ((GlobalTheory.T.intCast_isUnit_completion_almost_all_places A D hD0).union G.c_unit).subset fun p hp => ?_
    by_contra hq
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hq
    obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := hq
    apply hp
    have hcO : ((G.c p : (A.loc p).Fp) ∈ 𝒪[(A.loc p).Fp]) := hv ▸ (v : 𝒪[(A.loc p).Fp]).2
    refine ⟨u ^ 5, ?_⟩
    simp only [a, if_pos hcO, one_pow, mul_one]
    rw [← hu]
    push_cast
    rfl
  · intro p c0 h M hc0 hc0O hh hM hcl
    haveI := (A.loc p).lf
    haveI := (A.loc p).char0
    obtain ⟨haO, hacO, ha0⟩ := ha p
    have hform := (GlobalTheory.HL.RatExt.rational_extend A (k + 2 * r + 1) p).2.2.2.2.1
    have hZloc : ∀ i j : Fin (r + 1), hf (A.L p) (G.S p).Hm (A.bc p (G.f' j)) (A.bc p (G.f i)) =
        (A.loc p).ιE (G.Zh i j) := by
      intro i j
      rw [G.Hm_eq p, hform]
      rfl
    have hint : ∀ x : E, (∃ o : 𝓞 E, (D : E) * x = o) → (A.loc p).ιE ((D : E) * x) ∈ (A.L p).O := by
      rintro x ⟨o, ho⟩
      exact ((GlobalTheory.HL.PlacesInt.integers_local A).1 _).2 ⟨o, ho.symm⟩ p
    have hDE : algebraMap (A.loc p).Fp (A.loc p).Ep (D : (A.loc p).Fp) = (A.loc p).ιE (D : E) := by
      rw [map_intCast, map_intCast]
    have hDO : (D : (A.loc p).Fp) ∈ 𝒪[(A.loc p).Fp] := intCast_mem _ D
    have hD0' : (D : (A.loc p).Fp) ≠ 0 := by exact_mod_cast hD0
    have hZm : (Matrix.of fun i j : Fin (r + 1) => hf (A.L p) (G.S p).Hm (A.bc p (G.f' j)) (A.bc p (G.f i))) =
        G.Zh.map (A.loc p).ιE := by
      ext i j
      rw [Matrix.of_apply, hZloc]
      rfl
    obtain ⟨hK0, M', hM', hcl'⟩ := loc_close (A.L p) r k (G.S p) (G.c p) (a p)
      (c0 * (D : (A.loc p).Fp) ^ 3) (D : (A.loc p).Fp) ((G.Zh⁻¹).map (A.loc p).ιE) h M (Units.ne_zero _) haO hacO
      (mul_mem hc0O (pow_mem hDO _)) hDO hD0'
      (by
        simp only [G.f_eq p, G.f'_eq p]
        rw [hZm, ← Matrix.map_mul, hZinv, Matrix.map_one _ (map_zero _) (map_one _)])
      (by
        intro i j
        simp only [G.f_eq p, G.f'_eq p]
        rw [hZloc, hDE, ← map_mul]
        exact hint _ (hDv (Sum.inl (i, j))))
      (by
        intro i j
        rw [Matrix.map_apply, hDE, ← map_mul]
        exact hint _ (hDv (Sum.inr (Sum.inl (i, j)))))
      hh (by simpa only [G.f_eq p] using hM)
      (by
        intro i j
        obtain ⟨o, ho, hoe⟩ := hcl i j
        refine ⟨o, ho, ?_⟩
        rw [hoe]
        congr 2
        ring)
    refine ⟨hK0, ?_⟩
    refine GlobalTheory.T.close_on_completed_lattice_of_close_on_frames A r k G Λ D p h M M' c0 hΓinv (fun k l => hDv (Sum.inr (Sum.inr (k, l))))
      (fun x hx l => hDpair x hx l) hDg hh hM (by simpa only [G.f'_eq p] using hM') ?_ ?_
    · intro i j
      obtain ⟨o, ho, hoe⟩ := hcl i j
      refine ⟨algebraMap _ _ ((D : (A.loc p).Fp) ^ 2 * a p ^ r) * o,
        (A.L p).O.mul_mem (algebraMap_mem (A.L p) (mul_mem (pow_mem hDO _) (pow_mem haO _))) ho, ?_⟩
      rw [hoe]
      simp only [map_mul, map_pow]
      ring
    · intro i j
      obtain ⟨o, ho, hoe⟩ := hcl' i j
      refine ⟨algebraMap _ _ (a p ^ r) * o, (A.L p).O.mul_mem (algebraMap_mem (A.L p) (pow_mem haO _)) ho, ?_⟩
      rw [hoe]
      simp only [map_mul, map_pow]
      ring

end GlobalTheory.HL.FrameClose
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameMatrixCloseGivesLatticeCloseIntegralStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameMatrix_close_gives_lattice_close_integral : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), ∀ Λ : G.Lt, Submodule.IsFullLattice E Λ → ∃ d : ∀ p, (A.loc p).Fp, (∀ p, d p ≠ 0) ∧ {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = d p}.Finite ∧ ∀ p (c0 : (A.loc p).Fp) (h : (G.S p).GLV) (M : Matrix (Fin (r + 1)) (Fin (r + 1)) (A.loc p).Ep), c0 ≠ 0 → c0 ∈ 𝒪[(A.loc p).Fp] → h ∈ (G.S p).St → (∀ j, h (A.bc p (G.f j)) = ∑ i, M i j • A.bc p (G.f i)) → (∀ i j, ∃ o ∈ (A.L p).O, (M - 1) i j = algebraMap (A.loc p).Fp (A.loc p).Ep (c0 * d p) * o) → h ∈ (G.S p).K0 ∧ ∀ x ∈ A.lat p Λ, ∃ y ∈ A.lat p Λ, h x - x = algebraMap (A.loc p).Fp (A.loc p).Ep c0 • y := by
  first | exact @GlobalTheory.HL.FrameClose.close_lattice | exact GlobalTheory.HL.FrameClose.close_lattice | (intros; apply GlobalTheory.HL.FrameClose.close_lattice <;> first | assumption | exact (show Submodule.IsFullLattice _ _ from by assumption).toIsLattice)
end

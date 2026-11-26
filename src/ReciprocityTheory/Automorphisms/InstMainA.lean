module

public import Mathlib

@[expose] public section

section -- merged from ReciprocityTheory.Automorphisms.InstMainA
noncomputable section

namespace ReciprocityTheory.Aut

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem mem_maxIdeal_iff (x : v.adicCompletionIntegers F) :
    x ∈ maximalIdeal (v.adicCompletionIntegers F) ↔ Valued.v (x : v.adicCompletion F) < 1 := by
  have hint := Valuation.integer.integers (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hle : Valued.v (x : v.adicCompletion F) ≤ 1 := x.2
  constructor
  · intro hx
    exact lt_of_le_of_ne hle (fun h => hx ((hint.isUnit_iff_valuation_eq_one (x := x)).mpr h))
  · intro hx hu
    exact (ne_of_lt hx) ((hint.isUnit_iff_valuation_eq_one (x := x)).mp hu)

theorem val_le_exp_neg_one_of_lt_one {x : v.adicCompletion F} (h : Valued.v x < 1) :
    Valued.v x ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne (Valued.v x) 0 with h0 | h0
  · rw [h0]
    exact zero_le'
  · obtain ⟨a, ha⟩ := WithZero.ne_zero_iff_exists.mp h0
    rw [← ha] at h ⊢
    have h1 : a < 1 := by exact_mod_cast h
    have h2 : Multiplicative.toAdd a < 0 := by
      rw [← toAdd_one, Multiplicative.toAdd_lt]
      exact h1
    have h3 : a ≤ Multiplicative.ofAdd (-1 : ℤ) := by
      rw [← Multiplicative.toAdd_le, toAdd_ofAdd]
      omega
    show (a : WithZero (Multiplicative ℤ)) ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
    exact WithZero.coe_le_coe.mpr h3

theorem maxIdeal_eq_span {π : v.adicCompletionIntegers F}
    (hπ : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ)) :
    maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {π} := by
  have hπ0 : (π : v.adicCompletion F) ≠ 0 := by
    intro h
    rw [h, map_zero] at hπ
    exact WithZero.zero_ne_coe hπ
  have hexp : WithZero.exp (-1 : ℤ) < 1 := by
    rw [← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by norm_num)
  apply le_antisymm
  · intro x hx
    rw [mem_maxIdeal_iff] at hx
    have hx1 := val_le_exp_neg_one_of_lt_one v hx
    have hq : Valued.v ((x : v.adicCompletion F) / π) ≤ 1 := by
      rw [map_div₀, hπ]
      exact (div_le_one₀ (lt_of_le_of_ne zero_le' (Ne.symm (by rw [← hπ]; exact (map_ne_zero _).mpr hπ0)))).mpr hx1
    rw [Ideal.mem_span_singleton']
    refine ⟨⟨(x : v.adicCompletion F) / π, hq⟩, ?_⟩
    ext
    simp [div_mul_cancel₀ _ hπ0]
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    show π ∈ maximalIdeal _
    rw [mem_maxIdeal_iff, hπ]
    exact hexp

end ReciprocityTheory.Aut
end
end

section -- merged from ReciprocityTheory.Automorphisms.PlaceA
noncomputable section

namespace ReciprocityTheory.Aut

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

section Gen

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

theorem adic_valued_algebraMap (k : K) :
    Valued.v (algebraMap K (v.adicCompletion K) k) = v.valuation K k :=
  valuedAdicCompletion_eq_valuation' v k

theorem adic_algebraMap_R (a : R) :
    algebraMap R (v.adicCompletion K) a = algebraMap K (v.adicCompletion K) (algebraMap R K a) := rfl

theorem adic_exists_approx (y : v.adicCompletion K) (hy : Valued.v y ≤ 1) :
    ∃ a : R, Valued.v (y - algebraMap R (v.adicCompletion K) a) < 1 := by
  classical
  obtain ⟨k, hk⟩ : ∃ k : K, Valued.v (y - algebraMap K (v.adicCompletion K) k) < 1 := by
    have hn : {w : v.adicCompletion K | Valued.v (w - y) < 1} ∈ nhds y :=
      Valued.mem_nhds.mpr ⟨1, fun w hw => by simpa using hw⟩
    obtain ⟨w, hw, k, rfl⟩ := mem_closure_iff_nhds.mp (denseRange_algebraMap K v y) _ hn
    refine ⟨k, ?_⟩
    rw [← Valuation.map_neg, neg_sub]
    exact hw
  have hk1 : v.valuation K k ≤ 1 := by
    rw [← adic_valued_algebraMap]
    have e : algebraMap K (v.adicCompletion K) k = y - (y - algebraMap K _ k) := by ring
    rw [e]
    exact le_trans (Valuation.map_sub _ _ _) (max_le hy hk.le)
  obtain ⟨c, hc⟩ : ∃ c : R, v.valuation K (k - algebraMap R K c) < 1 := by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) k
    have hb0 : algebraMap R K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    haveI := v.isPrime
    have hex : ∃ N, b ∉ v.asIdeal ^ N := by
      by_contra hall
      push_neg at hall
      have hmem : b ∈ ⨅ i, v.asIdeal ^ i := Submodule.mem_iInf _ |>.mpr hall
      rw [Ideal.iInf_pow_eq_bot_of_isDomain _ v.isPrime.ne_top, Ideal.mem_bot] at hmem
      exact hb0 (by rw [hmem, map_zero])
    have hspec := Nat.find_spec hex
    have hmin : ∀ m < Nat.find hex, b ∈ v.asIdeal ^ m := fun m hm => by
      by_contra h'
      exact Nat.find_min hex hm h'
    obtain ⟨n, hn⟩ : ∃ n, Nat.find hex = n + 1 := Nat.exists_eq_succ_of_ne_zero (by
      intro h0
      rw [h0, pow_zero] at hspec
      exact hspec (by simp))
    rw [hn] at hspec
    have hbn : b ∈ v.asIdeal ^ n := hmin n (by omega)
    have hvb : 0 < v.valuation K (algebraMap R K b) := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hb0)
    have hk1' := hk1
    rw [map_div₀, div_le_one₀ hvb, valuation_of_algebraMap, valuation_of_algebraMap] at hk1'
    have ha : a ∈ v.asIdeal ^ n := by
      rw [← intValuation_le_pow_iff_mem]
      exact hk1'.trans ((intValuation_le_pow_iff_mem v b n).mpr hbn)
    have hI : Ideal.span {b} ⊔ v.asIdeal ^ (n + 1) = v.asIdeal ^ n := by
      apply Ideal.eq_prime_pow_of_succ_lt_of_le v.ne_bot
      · refine lt_of_le_of_ne le_sup_right ?_
        intro heq
        apply hspec
        rw [heq]
        exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self b)
      · exact sup_le ((Ideal.span_singleton_le_iff_mem _).mpr hbn)
          (Ideal.pow_le_pow_right (Nat.le_succ n))
    rw [← hI] at ha
    obtain ⟨y1, hy1, z, hz, hyz⟩ := Submodule.mem_sup.mp ha
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hy1
    refine ⟨r, ?_⟩
    have hkz : algebraMap R K a / algebraMap R K b - algebraMap R K r =
        algebraMap R K z / algebraMap R K b := by
      rw [← hyz, map_add (f := _), map_mul]
      field_simp
      ring
    rw [hkz, map_div₀, div_lt_one₀ hvb, valuation_of_algebraMap, valuation_of_algebraMap]
    have h1 := (intValuation_le_pow_iff_mem v z (n + 1)).mpr hz
    have h2 : ¬ v.intValuation b ≤ WithZero.exp (-((n + 1 : ℕ) : ℤ)) := fun h =>
      hspec ((intValuation_le_pow_iff_mem v b (n + 1)).mp h)
    exact lt_of_le_of_lt h1 (not_le.mp h2)
  refine ⟨c, ?_⟩
  have e : y - algebraMap R (v.adicCompletion K) c =
      (y - algebraMap K _ k) + algebraMap K _ (k - algebraMap R K c) := by
    rw [adic_algebraMap_R, map_sub]
    ring
  rw [e]
  refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hk ?_)
  rw [adic_valued_algebraMap]
  exact hc

theorem adic_le_one_of_poly {x : v.adicCompletion K} (p : Polynomial ℤ) (hm : p.Monic)
    (hp : p.eval₂ (Int.castRingHom _) x = 0) : Valued.v x ≤ 1 := by
  have hint : IsIntegral (Valued.v : Valuation (v.adicCompletion K) _).integer x := by
    refine ⟨p.map (Int.castRingHom _), hm.map _, ?_⟩
    rw [Polynomial.eval₂_map, RingHom.ext_int (RingHom.comp _ _) (Int.castRingHom _)]
    exact hp
  have hmem := (Valuation.integer.integers _).mem_of_integral hint
  exact hmem

end Gen

end ReciprocityTheory.Aut
end
end

section -- merged from ReciprocityTheory.Automorphisms.Unitary
namespace ReciprocityTheory.Aut

open NumberField IsDedekindDomain TensorProduct

section General

variable {R : Type*} [CommRing R] {n : ℕ}

def conjT (σ : R →+* R) (g : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R := (g.map σ).transpose

theorem conjT_mul (σ : R →+* R) (g h : Matrix (Fin n) (Fin n) R) :
    conjT σ (g * h) = conjT σ h * conjT σ g := by
  unfold conjT
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem conjT_one (σ : R →+* R) : conjT σ (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  unfold conjT
  simp

theorem conjT_conjT (σ : R →+* R) (hσ : ∀ x, σ (σ x) = x) (g : Matrix (Fin n) (Fin n) R) :
    conjT σ (conjT σ g) = g := by
  ext i j
  simp [conjT, hσ]

def UGroup (n : ℕ) (σ : R →+* R) (hσ : ∀ x, σ (σ x) = x) : Subgroup (GL (Fin n) R) where
  carrier := {g | (g : Matrix (Fin n) (Fin n) R) * conjT σ g = 1}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Units.val_mul] at *
    rw [conjT_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (b : Matrix (Fin n) (Fin n) R), hb,
      Matrix.one_mul, ha]
  one_mem' := by
    simp [conjT_one]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at *
    have h1 : ((a⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = conjT σ a :=
      Units.inv_eq_of_mul_eq_one_right ha
    rw [h1, conjT_conjT σ hσ]
    exact mul_eq_one_comm.mp ha

end General

variable (L : Type*) [Field L] [NumberField L] [IsCMField L]

local notation3 "L⁺" => maximalRealSubfield L

abbrev AFplus : Type _ := FiniteAdeleRing (𝓞 L⁺) L⁺

abbrev AL : Type _ := L ⊗[L⁺] AFplus L

noncomputable def conjAL : AL L →+* AL L :=
  (Algebra.TensorProduct.map (IsCMField.complexConj L).toAlgHom (AlgHom.id L⁺ (AFplus L))).toRingHom

theorem conjAL_conjAL (x : AL L) : conjAL L (conjAL L x) = x := by
  have hc : ∀ y : L, IsCMField.complexConj L (IsCMField.complexConj L y) = y := by
    intro y
    have h := pow_orderOf_eq_one (IsCMField.complexConj L)
    rw [IsCMField.orderOf_complexConj, pow_two] at h
    simpa [AlgEquiv.mul_apply] using DFunLike.congr_fun h y
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [conjAL, hc]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem complexConj_invol (x : L) :
    (IsCMField.complexConj L : L →+* L) ((IsCMField.complexConj L : L →+* L) x) = x := by
  have hc : ∀ y : L, IsCMField.complexConj L (IsCMField.complexConj L y) = y := by
    intro y
    have h := pow_orderOf_eq_one (IsCMField.complexConj L)
    rw [IsCMField.orderOf_complexConj, pow_two] at h
    simpa [AlgEquiv.mul_apply] using DFunLike.congr_fun h y
  simpa using hc x

structure SplitPlace where
  v : HeightOneSpectrum (𝓞 L⁺)
  i : L →ₐ[L⁺] v.adicCompletion L⁺

noncomputable def evalAt (v : HeightOneSpectrum (𝓞 L⁺)) : AFplus L →ₐ[L⁺] v.adicCompletion L⁺ :=
  { RestrictedProduct.evalRingHom (fun v : HeightOneSpectrum (𝓞 L⁺) => v.adicCompletion L⁺) v with
    commutes' := fun _ => rfl }

noncomputable def compAt (v : HeightOneSpectrum (𝓞 L⁺)) : AL L →+* L ⊗[L⁺] v.adicCompletion L⁺ :=
  (Algebra.TensorProduct.map (AlgHom.id L⁺ L) (evalAt L v)).toRingHom


variable {L} in
noncomputable def SplitPlace.proj (s : SplitPlace L) : AL L →+* s.v.adicCompletion L⁺ :=
  (Algebra.TensorProduct.lift s.i (evalAt L s.v) (fun _ _ => Commute.all _ _)).toRingHom

noncomputable def ALint : Subring (AL L) :=
  Subring.closure ({x | ∃ y : 𝓞 L, x = (y : L) ⊗ₜ[L⁺] (1 : AFplus L)} ∪
    {x | ∃ a : AFplus L, (∀ v, a v ∈ v.adicCompletionIntegers L⁺) ∧ x = (1 : L) ⊗ₜ[L⁺] a})

noncomputable def GA (n : ℕ) : Subgroup (GL (Fin n) (AL L)) := UGroup n (conjAL L) (conjAL_conjAL L)

noncomputable def GQ0 (n : ℕ) : Subgroup (GL (Fin n) L) :=
  UGroup n (IsCMField.complexConj L : L →+* L) (complexConj_invol L)

noncomputable def GQ (n : ℕ) : Subgroup (GA L n) :=
  ((GQ0 L n).map (Matrix.GeneralLinearGroup.map
    (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L))).subgroupOf (GA L n)

theorem conjAL_mem_ALint {x : AL L} (hx : x ∈ ALint L) : conjAL L x ∈ ALint L := by
  have key : ALint L ≤ (ALint L).comap (conjAL L) := by
    refine Subring.closure_le.mpr ?_
    rintro x (⟨y, rfl⟩ | ⟨a, ha, rfl⟩)
    · refine Subring.subset_closure (Or.inl
        ⟨RingOfIntegers.mapRingEquiv (IsCMField.complexConj L).toRingEquiv y, ?_⟩)
      simp [conjAL] <;> rfl
    · refine Subring.subset_closure (Or.inr ⟨a, ha, ?_⟩)
      simp [conjAL]
  exact key hx

noncomputable def Umax (n : ℕ) : Subgroup (GA L n) where
  carrier := {g | ∀ i j, (g.1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L}
  mul_mem' := by
    intro a b ha hb i j
    simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply]
    exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (ha i k) (hb k j)
  one_mem' := by
    intro i j
    simp only [OneMemClass.coe_one, Units.val_one, Matrix.one_apply]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  inv_mem' := by
    intro a ha i j
    have hm := a.2
    simp only [GA, UGroup, Subgroup.mem_mk] at hm
    have h1 : ((a.1⁻¹ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = conjT (conjAL L) a.1 :=
      Units.inv_eq_of_mul_eq_one_right hm
    simp only [Set.mem_ofPred_eq] at ha
    simp only [InvMemClass.coe_inv, h1, conjT, Matrix.transpose_apply, Matrix.map_apply]
    exact conjAL_mem_ALint L (ha j i)


variable {L} in
noncomputable def SplitPlace.loc (s : SplitPlace L) (n : ℕ) :
    GA L n →* GL (Fin n) (s.v.adicCompletion L⁺) :=
  (Matrix.GeneralLinearGroup.map s.proj).comp (GA L n).subtype


variable {L} in
def TrivOutside {n : ℕ} (T : Set (HeightOneSpectrum (𝓞 L⁺))) (x : GA L n) : Prop :=
  ∀ v, v ∉ T → (x.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) = 1


variable {L} in
noncomputable def Level {n : ℕ} {ι : Type*} (s : ι → SplitPlace L)
    (H : ∀ a, Subgroup (GL (Fin n) ((s a).v.adicCompletion L⁺))) : Subgroup (GA L n) :=
  Umax L n ⊓ ⨅ a, (H a).comap (SplitPlace.loc (s a) n)

end ReciprocityTheory.Aut
end

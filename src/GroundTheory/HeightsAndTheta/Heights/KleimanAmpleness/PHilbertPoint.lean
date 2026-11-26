module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SubFamilyTwistSt

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PHilbertPoint
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

namespace HilbertPoint

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}

def aff (y : Fin (N + 1) → Ω) (j : Fin (N + 1)) : Fin (N + 1) → Ω := fun l => y l / y j

theorem aff_def (y : Fin (N + 1) → Ω) (j : Fin (N + 1)) : aff y j = fun l => y l / y j := rfl

variable (k) in
def affRing (y : Fin (N + 1) → Ω) (j : Fin (N + 1)) : Subalgebra k Ω :=
  (aeval (aff y j) : Poly k N →ₐ[k] Ω).range

variable (k) in
def affPiece (y : Fin (N + 1) → Ω) (j : Fin (N + 1)) (n : ℕ) : Submodule k Ω :=
  Submodule.span k {z | ∃ f : Poly k N, f.IsHomogeneous n ∧ z = aeval (aff y j) f}

variable {y : Fin (N + 1) → Ω} {j : Fin (N + 1)}

theorem aeval_aff_of_mem_primeOf {f : Poly k N} (hf : f ∈ primeOf (S := k) y) :
    aeval (aff y j) f = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← sum_homogeneousComponent f, map_sum]
  refine Finset.sum_eq_zero fun d _ => ?_
  rw [aff_def, aeval_div_of_isHomogeneous (homogeneousComponent_isHomogeneous d f),
    (mem_primeOf_of_isHomogeneous y (homogeneousComponent_isHomogeneous d f)).mp
      (homogeneousComponent_mem_primeOf y hf d), zero_div]

theorem le_zero_of_add_one_le_one {d : WithBot ℕ∞} (h : d + 1 ≤ 1) : d ≤ 0 := by
  induction d using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe e =>
    have h' : e + 1 ≤ 1 := by exact_mod_cast h
    induction e using ENat.recTopCoe with
    | top => simp at h'
    | coe m =>
      have : m + 1 ≤ 1 := by exact_mod_cast h'
      have hm : m = 0 := by omega
      subst hm
      simp

theorem isField_affRing (hy : IsSubvar (x := y) (primeOf (S := k) y) 0) (hj : y j ≠ 0) :
    IsField (affRing k y j) := by
  let φ : Poly k N →ₐ[k] affRing k y j := (aeval (aff y j)).rangeRestrict
  have hφ : Function.Surjective φ := AlgHom.rangeRestrict_surjective _
  have hker : ∀ f ∈ primeOf (S := k) y, φ.toRingHom f = 0 := fun f hf =>
    Subtype.ext (aeval_aff_of_mem_primeOf hf)
  let ψ : Poly k N ⧸ primeOf (S := k) y →+* affRing k y j :=
    Ideal.Quotient.lift (primeOf (S := k) y) φ.toRingHom hker
  have hψ : Function.Surjective ψ := Ideal.Quotient.lift_surjective_of_surjective _ hker hφ
  let r : Poly k N ⧸ primeOf (S := k) y := Ideal.Quotient.mk _ (X j - 1)
  have hr : r ≠ 0 := by
    intro h
    have hmem : (X j - 1 : Poly k N) ∈ primeOf (S := k) y := Ideal.Quotient.eq_zero_iff_mem.mp h
    have h0 := homogeneousComponent_mem_primeOf y hmem 0
    rw [homogeneousComponent_zero] at h0
    have := (mem_primeOf_of_isHomogeneous y (isHomogeneous_C _ _)).mp h0
    simp at this
  have hr' : r ∈ nonZeroDivisors (Poly k N ⧸ primeOf (S := k) y) := mem_nonZeroDivisors_of_ne_zero hr
  have hψr : ψ r = 0 := by
    apply Subtype.ext
    change aeval (aff y j) (X j - 1 : Poly k N) = 0
    simp [aff, hj]
  have hrψ : ∀ a ∈ Ideal.span {r}, ψ a = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, hψr, mul_zero]
  have hχ : Function.Surjective (Ideal.Quotient.lift (Ideal.span {r}) ψ hrψ) :=
    Ideal.Quotient.lift_surjective_of_surjective _ hrψ hψ
  have h1 : ringKrullDim (affRing k y j) ≤
      ringKrullDim ((Poly k N ⧸ primeOf (S := k) y) ⧸ Ideal.span {r}) := by
    exact ringKrullDim_le_of_surjective _ hχ
  have h2 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr'
  rw [hy.dim] at h2
  have h3 : ringKrullDim (affRing k y j) ≤ 0 :=
    le_zero_of_add_one_le_one ((add_le_add h1 (le_refl (1 : WithBot ℕ∞))).trans (by simpa using h2))
  have : Ring.KrullDimLE 0 (affRing k y j) := Ring.krullDimLE_iff.mpr (by simpa using h3)
  exact Ring.KrullDimLE.isField_of_isDomain

theorem funField_eq (hj : y j ≠ 0) (hF : IsField (affRing k y j)) :
    funField (k := k) y = (affRing k y j).toIntermediateField' hF := by
  have haff : ∀ l, aff y j l ∈ (affRing k y j).toIntermediateField' hF := fun l =>
    show aff y j l ∈ affRing k y j from ⟨X l, by simp⟩
  apply le_antisymm
  · rw [funField, IntermediateField.adjoin_le_iff]
    rintro _ ⟨i, l, hi, rfl⟩
    have : y l / y i = aff y j l * (aff y j i)⁻¹ := by
      simp only [aff]; field_simp
    rw [this]
    exact mul_mem (haff l) (inv_mem (haff i))
  · intro z hz
    change z ∈ affRing k y j at hz
    rw [affRing, ← Algebra.adjoin_range_eq_range_aeval] at hz
    refine Algebra.adjoin_le (S := (funField (k := k) y).toSubalgebra) ?_ hz
    rintro _ ⟨l, rfl⟩
    exact IntermediateField.subset_adjoin _ _ ⟨j, l, hj, rfl⟩

theorem finiteDimensional_affField (hy : IsSubvar (x := y) (primeOf (S := k) y) 0) (hj : y j ≠ 0) :
    FiniteDimensional k ((affRing k y j).toIntermediateField' (isField_affRing hy hj)) := by
  set E := (affRing k y j).toIntermediateField' (isField_affRing hy hj)
  let g : Poly k N →ₐ[k] E :=
    AlgHom.codRestrict (aeval (aff y j) : Poly k N →ₐ[k] Ω) E.toSubalgebra
      (fun f => show _ ∈ affRing k y j from ⟨f, rfl⟩)
  have hg : Function.Surjective g := by
    rintro ⟨z, f, rfl⟩
    exact ⟨f, rfl⟩
  have : Algebra.FiniteType k E := Algebra.FiniteType.of_surjective g hg
  exact finite_of_finite_type_of_isJacobsonRing k E

theorem affPiece_le (n : ℕ) : affPiece k y j n ≤ Subalgebra.toSubmodule (affRing k y j) :=
  Submodule.span_le.mpr (by rintro _ ⟨f, _, rfl⟩; exact ⟨f, rfl⟩)

theorem affPiece_mono (hj : y j ≠ 0) {m n : ℕ} (h : m ≤ n) :
    affPiece k y j m ≤ affPiece k y j n := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨f, hf, rfl⟩
  refine Submodule.subset_span ⟨X j ^ (n - m) * f, ?_, ?_⟩
  · have := (isHomogeneous_X_pow (R := k) j (n - m)).mul hf
    rwa [Nat.sub_add_cancel h] at this
  · simp [aff, hj]

theorem aeval_mem_affPiece (hj : y j ≠ 0) (f : Poly k N) :
    aeval (aff y j) f ∈ affPiece k y j f.totalDegree := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [show aeval (aff y j) f = ∑ d ∈ Finset.range (f.totalDegree + 1),
      aeval (aff y j) (homogeneousComponent d f) by rw [← map_sum, sum_homogeneousComponent]]
  refine Submodule.sum_mem _ fun d hd => ?_
  have hd' : d ≤ f.totalDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
  exact affPiece_mono hj hd' (Submodule.subset_span ⟨_, homogeneousComponent_isHomogeneous d f, rfl⟩)

theorem eventually_affPiece_eq (hy : IsSubvar (x := y) (primeOf (S := k) y) 0) (hj : y j ≠ 0) :
    ∀ᶠ n : ℕ in atTop, affPiece k y j n = Subalgebra.toSubmodule (affRing k y j) := by
  have := finiteDimensional_affField hy hj
  have hfin : (Subalgebra.toSubmodule (affRing k y j)).FG := by
    rw [← Module.Finite.iff_fg]
    exact inferInstanceAs (Module.Finite k ((affRing k y j).toIntermediateField' (isField_affRing hy hj)))
  obtain ⟨s, hs⟩ := hfin
  have hex : ∀ z ∈ s, ∃ n, z ∈ affPiece k y j n := fun z hz => by
    have : z ∈ affRing k y j := by
      rw [← Subalgebra.mem_toSubmodule, ← hs]; exact Submodule.subset_span hz
    obtain ⟨f, rfl⟩ := this
    exact ⟨_, aeval_mem_affPiece hj f⟩
  choose! m hm using hex
  refine eventually_atTop.mpr ⟨s.sup m, fun n hn => le_antisymm (affPiece_le n) ?_⟩
  rw [← hs, Submodule.span_le]
  intro z hz
  exact affPiece_mono hj ((Finset.le_sup hz).trans hn) (hm z hz)

theorem coordGraded_piece_eq (hj : y j ≠ 0) (n : ℕ) :
    (coordGraded k y).piece (n : ℤ) = (affPiece k y j n).map (LinearMap.mulLeft k (y j ^ n)) := by
  rw [show (coordGraded k y).piece (n : ℤ) = Submodule.span k {z | ∃ (f : Poly k N) (e : ℕ),
    f.IsHomogeneous e ∧ (e : ℤ) = n ∧ z = aeval y f} from rfl, affPiece, Submodule.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨f, e, hf, he, rfl⟩
    have hen : e = n := by exact_mod_cast he
    subst hen
    refine ⟨aeval (aff y j) f, ⟨f, hf, rfl⟩, ?_⟩
    rw [LinearMap.mulLeft_apply, aff_def, aeval_div_of_isHomogeneous hf]
    field_simp
  · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    refine ⟨f, n, hf, rfl, ?_⟩
    rw [LinearMap.mulLeft_apply, aff_def, aeval_div_of_isHomogeneous hf]
    field_simp

theorem coordGraded_le_secs (n : ℕ) :
    (coordGraded k y).piece (n : ℤ) ≤ (twistSys k y (n : ℤ)).secs := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨f, e, hf, he, rfl⟩
  refine (Submodule.mem_iInf _).mpr fun I => ?_
  exact Submodule.subset_span ⟨f, 1, 0, e, one_mem _, hf, isHomogeneous_one _ _, by simp [he],
    by simp⟩

theorem affRing_eq_ampleBase : affRing k y j = ampleBase (S := k) y j := by
  rw [affRing, ampleBase, Algebra.adjoin_range_eq_range_aeval]
  rfl

theorem div_mem_affRing_of_mem_twistMod (hj : y j ≠ 0) (n : ℕ) {z : Ω}
    (hz : z ∈ twistMod k y (n : ℤ) (singleChart hj)) : z / y j ^ n ∈ affRing k y j := by
  refine Submodule.span_induction (p := fun z _ => z / y j ^ n ∈ affRing k y j) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨f, s, e, e', hs, hf, hse, hc, rfl⟩
    have hs' : s ∈ Submonoid.closure {(X j : Poly k N)} := by
      have : ((fun i => (X i : Poly k N)) '' ((({j} : Finset (Fin (N + 1))) : Set (Fin (N + 1))))) =
          {X j} := by simp
      rw [← this]; exact hs
    obtain ⟨m, rfl⟩ := Submonoid.mem_closure_singleton.mp hs'
    have hme : e = m := hse.inj_right (isHomogeneous_X_pow j m) (by
      rw [X_pow_eq_monomial, Ne, monomial_eq_zero]; exact one_ne_zero)
    subst hme
    have he' : e' = e + n := by omega
    subst he'
    refine ⟨f, ?_⟩
    change aeval (aff y j) f = _
    rw [aff_def, aeval_div_of_isHomogeneous hf, map_pow, aeval_X, pow_add, div_div]
  · simp
  · intro a b _ _ ha hb
    rw [add_div]; exact add_mem ha hb
  · intro c z _ hz
    rw [chartRing_smul_def, mul_div_assoc]
    refine mul_mem ?_ hz
    rw [affRing_eq_ampleBase]
    exact mem_ampleBase_of_mem_chartRing (S := k) hj c.2

theorem proof : HilbertPoint.Statement.{u, w} := by
  intro k _ Ω _ _ N y hy
  obtain ⟨j, hjX⟩ := hy.relevant
  have hj : y j ≠ 0 := fun h =>
    hjX ((mem_primeOf_of_isHomogeneous y (isHomogeneous_X k j)).mpr (by simp [h]))
  have hF := isField_affRing hy hj
  have hfun := funField_eq hj hF
  have hfd := finiteDimensional_affField hy hj
  have hev := eventually_affPiece_eq hy hj
  refine ⟨hfun ▸ hfd, hev.mono fun n hn => ?_, hev.mono fun n hn => ?_⟩
  · have hinj : Function.Injective (LinearMap.mulLeft k (y j ^ n)) :=
      mul_right_injective₀ (pow_ne_zero n hj)
    rw [coordGraded_piece_eq hj n,
      ← LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj _), hn,
      Subalgebra.finrank_toSubmodule, hfun, ← IntermediateField.finrank_eq_finrank_subalgebra]
    rfl
  · refine le_antisymm ?_ (coordGraded_le_secs n)
    intro z hz
    have hz1 : z ∈ twistMod k y (n : ℤ) (singleChart hj) :=
      (Submodule.mem_iInf _).mp hz (singleChart hj)
    have hd := div_mem_affRing_of_mem_twistMod hj n hz1
    rw [coordGraded_piece_eq hj n, hn]
    refine ⟨z / y j ^ n, hd, ?_⟩
    rw [LinearMap.mulLeft_apply]
    field_simp

end HilbertPoint

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PNefPlusAmple
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section Lemmas

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem SubSystem.twist_sub_eq_mul (F Q : SubSystem k x Ω) (I : Chart x) :
    (F.twist Q).sub I = F.sub I * Q.sub I := by
  rw [Submodule.mul_eq_span_mul_set]
  change Submodule.span _ _ = _
  congr 1
  ext z
  constructor
  · rintro ⟨q, hq, y, hy, rfl⟩
    exact ⟨y, hy, q, hq, by rw [smul_eq_mul, mul_comm]⟩
  · rintro ⟨y, hy, q, hq, rfl⟩
    exact ⟨q, hq, y, hy, by rw [smul_eq_mul, mul_comm]⟩

theorem twistMod_zero_eq_one (I : Chart x) : twistMod k x 0 I = 1 := by
  obtain ⟨i, hi⟩ := I.2.1
  rw [twistMod_eq_span 0 I hi, zpow_zero, Submodule.one_eq_span]

theorem SubSystem.pow_sub_eq_pow (Q : SubSystem k x Ω) (n : ℕ) (I : Chart x) :
    (Q.pow n).sub I = Q.sub I ^ n := by
  induction n with
  | zero => rw [pow_zero]; exact twistMod_zero_eq_one I
  | succ n ih => rw [pow_succ, ← ih]; exact SubSystem.twist_sub_eq_mul _ _ I

end Lemmas

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GeneratedTwistSysZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def GraphClosed.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (G H : LineBundle k x), G.toSubSystem.Generated → IsVeryAmple H.toSubSystem →
    IsVeryAmple (G.toSubSystem.twist H.toSubSystem)

def PointGenerated.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (Q : LineBundle k x), IsSubvar x (primeOf (S := k) x) 0 → Q.toSubSystem.Generated

section Hypotheses

variable (k : Type u) [Field k]

theorem generated_twistSys_zero' {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
    {x : Fin (N + 1) → Ω} : (twistSys S x 0).Generated := by
  have h1 : (1 : Ω) ∈ (twistSys S x 0).secs := by
    rw [SubSystem.secs, Submodule.mem_iInf]
    intro I
    exact one_mem_twistMod_zero I
  intro I
  obtain ⟨i, hi⟩ := I.2.1
  apply le_antisymm
  · refine Submodule.span_le.mpr fun z hz => ?_
    rw [SubSystem.secs, SetLike.mem_coe, Submodule.mem_iInf] at hz
    exact hz I
  · change twistMod S x 0 I ≤ _
    rw [twistMod_eq_span 0 I hi, zpow_zero]
    exact Submodule.span_mono (Set.singleton_subset_iff.mpr h1)

end Hypotheses

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTildeShift
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

section Tilde

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]


omit [IsScalarTower S Ω E] in
theorem FinGradedSub.zpow_smul_mem_tilde (M : FinGradedSub (S := S) (x := x) E) {I : Chart x}
    {i : Fin (N + 1)} (hi : i ∈ I.1) (c d : ℤ) {y : E} (hy : y ∈ M.tilde d I) :
    x i ^ c • y ∈ M.tilde (d + c) I := by
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  refine Submodule.span_induction (p := fun y _ => x i ^ c • y ∈ M.tilde (d + c) I) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩
    have hs0 := eval_ne_zero_of_mem_monos I hs
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg c
    · refine Submodule.subset_span ⟨aeval x (X i ^ n : Poly S N) • m, s, a + n, e, hs, hse,
        M.smul_mem n a _ m (isHomogeneous_X_pow i n) hm, by omega, ?_⟩
      rw [smul_smul, smul_smul]
      congr 1
      simp only [map_pow, aeval_X, zpow_natCast]
      ring
    · refine Submodule.subset_span ⟨m, s * X i ^ n, a, e + n, mul_mem hs (pow_mem (X_mem_monos hi) n),
        hse.mul (isHomogeneous_X_pow i n), hm, by push_cast; omega, ?_⟩
      rw [smul_smul]
      congr 1
      simp only [map_mul, map_pow, aeval_X, zpow_neg, zpow_natCast, mul_inv]
      ring
  · rw [smul_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
  · intro a y _ hy
    have : x i ^ c • (a • y) = a • (x i ^ c • y) := by
      rw [Subalgebra.smul_def, Subalgebra.smul_def, smul_smul, smul_smul, mul_comm]
    rw [this]
    exact Submodule.smul_mem _ a hy

theorem TildeShift.proof : TildeShift.Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ M c
  refine SubSystem.ext_sub fun I => ?_
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  apply le_antisymm
  · intro y hy
    have h0 : x i ^ (-c) • y ∈ M.tilde 0 I := by
      simpa using M.zpow_smul_mem_tilde hi (-c) c hy
    refine Submodule.subset_span ⟨x i ^ c, ?_, x i ^ (-c) • y, h0, ?_⟩
    · change x i ^ c ∈ twistMod S x c I
      rw [twistMod_eq_span c I hi]
      exact Submodule.mem_span_singleton_self _
    · rw [smul_smul, ← zpow_add₀ hxi, add_neg_cancel, zpow_zero, one_smul]
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, y, hy, rfl⟩
    change q ∈ twistMod S x c I at hq
    rw [twistMod_eq_span c I hi, Submodule.mem_span_singleton] at hq
    obtain ⟨a, rfl⟩ := hq
    have hy' : x i ^ c • y ∈ M.tilde c I := by
      simpa using M.zpow_smul_mem_tilde hi c 0 hy
    have : (a • x i ^ c) • y = a • (x i ^ c • y) := by
      rw [chartRing_smul_def, Subalgebra.smul_def, smul_smul]
    rw [SetLike.mem_coe, this]
    exact Submodule.smul_mem _ a hy'

end Tilde

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwistTilde
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

namespace TwistTildeProof

theorem smul_mem_of_mem_span {R A M : Type*} [CommRing R] [Ring A] [AddCommGroup M] [Module R A]
    [Module A M] [Module R M] [IsScalarTower R A M] [SMulCommClass A R M] {s : Set A} {t : Set M}
    {T : Submodule R M} (h : ∀ a ∈ s, ∀ b ∈ t, a • b ∈ T) {q : A} (hq : q ∈ Submodule.span R s)
    {m : M} (hm : m ∈ Submodule.span R t) : q • m ∈ T := by
  refine Submodule.span_induction (p := fun q _ => q • m ∈ T) ?_ ?_ ?_ ?_ hq
  · intro a ha
    refine Submodule.span_induction (p := fun m _ => a • m ∈ T) ?_ ?_ ?_ ?_ hm
    · exact fun b hb => h a ha b hb
    · rw [smul_zero]; exact T.zero_mem
    · intro b c _ _ hb hc; rw [smul_add]; exact T.add_mem hb hc
    · intro r b _ hb; rw [smul_comm]; exact T.smul_mem r hb
  · rw [zero_smul]; exact T.zero_mem
  · intro a b _ _ ha hb; rw [add_smul]; exact T.add_mem ha hb
  · intro r a _ ha; rw [smul_assoc]; exact T.smul_mem r ha

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E]
  [IsScalarTower S Ω E]

def prodSet (M : FinGradedSub (S := S) (x := x) E) (Q : FinGradedSub (S := S) (x := x) Ω) (c : ℤ) :
    Set E :=
  {z | ∃ (a b : ℤ) (q : Ω) (m : E), q ∈ Q.piece a ∧ m ∈ M.piece b ∧ a + b = c ∧ z = q • m}

def prod (M : FinGradedSub (S := S) (x := x) E) (Q : FinGradedSub (S := S) (x := x) Ω) :
    FinGradedSub (S := S) (x := x) E where
  piece c := Submodule.span S (prodSet M Q c)
  smul_mem d c f m hf hm := by
    refine Submodule.span_induction (p := fun m _ => aeval x f • m ∈ Submodule.span S
      (prodSet M Q (c + d))) ?_ ?_ ?_ ?_ hm
    · rintro _ ⟨a, b, q, m, hq, hm, hab, rfl⟩
      refine Submodule.subset_span ⟨a, b + d, q, aeval x f • m, hq, M.smul_mem d b f m hf hm,
        by omega, ?_⟩
      rw [smul_smul, smul_smul, mul_comm]
    · rw [smul_zero]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
    · intro r a _ ha; rw [smul_comm]; exact Submodule.smul_mem _ r ha
  fg := by
    obtain ⟨n, deg, gen, hgen, hspan⟩ := M.fg
    obtain ⟨n', deg', gen', hgen', hspan'⟩ := Q.fg
    let e := (finProdFinEquiv : Fin n' × Fin n ≃ Fin (n' * n))
    refine ⟨n' * n, fun k => deg' (e.symm k).1 + deg (e.symm k).2,
      fun k => gen' (e.symm k).1 • gen (e.symm k).2, fun k => Submodule.subset_span
        ⟨_, _, _, _, hgen' _, hgen _, rfl, rfl⟩, fun c => Submodule.span_le.mpr ?_⟩
    rintro _ ⟨a, b, q, m, hq, hm, hab, rfl⟩
    refine smul_mem_of_mem_span ?_ (hspan' a hq) (hspan b hm)
    rintro _ ⟨l, f', e', hf', he', rfl⟩ _ ⟨j, f, e'', hf, he'', rfl⟩
    refine Submodule.subset_span ⟨e (l, j), f' * f, e' + e'', hf'.mul hf, ?_, ?_⟩
    · simp only [Equiv.symm_apply_apply]; push_cast; omega
    · simp only [Equiv.symm_apply_apply, smul_eq_mul, map_mul, smul_smul]
      congr 1; ring

theorem twist_eq (M : FinGradedSub (S := S) (x := x) E) (Q : FinGradedSub (S := S) (x := x) Ω)
    (I : Chart x) : ((M.tildeSys 0).twist (Q.tildeSys 0)).sub I = (prod M Q).tilde 0 I := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, y, hy, rfl⟩
    change q ∈ Q.tilde 0 I at hq
    change y ∈ M.tilde 0 I at hy
    refine smul_mem_of_mem_span ?_ hq hy
    rintro _ ⟨q, s₁, a₁, e₁, hs₁, hse₁, hq, ha₁, rfl⟩ _ ⟨m, s₂, a₂, e₂, hs₂, hse₂, hm, ha₂, rfl⟩
    refine Submodule.subset_span ⟨q • m, s₁ * s₂, a₁ + a₂, e₁ + e₂, mul_mem hs₁ hs₂, hse₁.mul hse₂,
      Submodule.subset_span ⟨a₁, a₂, q, m, hq, hm, rfl, rfl⟩, by push_cast; omega, ?_⟩
    simp only [smul_eq_mul, smul_smul, map_mul, mul_inv]
    congr 1; ring
  · obtain ⟨i, hi⟩ := I.2.1
    have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨p, s, a, e, hs, hse, hp, hae, rfl⟩
    have hs0 := eval_ne_zero_of_mem_monos I hs
    refine Submodule.span_induction (p := fun p _ => (aeval x s)⁻¹ • p ∈
      ((M.tildeSys 0).twist (Q.tildeSys 0)).sub I) ?_ ?_ ?_ ?_ hp
    · rintro _ ⟨a', b', q, m, hq, hm, hab, rfl⟩
      set k := a'.toNat
      set j := (-a').toNat
      have hkj : (k : ℤ) - j = a' := Int.toNat_sub_toNat_neg a'
      have hq' : (aeval x (X i ^ k : Poly S N))⁻¹ • (aeval x (X i ^ j : Poly S N) • q) ∈
          Q.tilde 0 I := by
        have h := Q.smul_mem j a' _ q (isHomogeneous_X_pow i j) hq
        rw [show a' + (j : ℤ) = k by omega] at h
        exact Submodule.subset_span ⟨_, X i ^ k, k, k, pow_mem (X_mem_monos hi) k,
          isHomogeneous_X_pow i k, h, by simp, rfl⟩
      have hm' : (aeval x (s * X i ^ j))⁻¹ • (aeval x (X i ^ k : Poly S N) • m) ∈ M.tilde 0 I := by
        have h := M.smul_mem k b' _ m (isHomogeneous_X_pow i k) hm
        exact Submodule.subset_span ⟨_, s * X i ^ j, b' + k, e + j,
          mul_mem hs (pow_mem (X_mem_monos hi) j), hse.mul (isHomogeneous_X_pow i j), h,
          by push_cast; omega, rfl⟩
      have heq : (aeval x s)⁻¹ • (q • m) = ((aeval x (X i ^ k : Poly S N))⁻¹ •
          (aeval x (X i ^ j : Poly S N) • q)) • ((aeval x (s * X i ^ j))⁻¹ •
          (aeval x (X i ^ k : Poly S N) • m)) := by
        simp only [smul_eq_mul, smul_smul, map_mul, map_pow, aeval_X]
        congr 1
        field_simp
      rw [heq]
      exact Submodule.subset_span ⟨_, hq', _, hm', rfl⟩
    · rw [smul_zero]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
    · intro r a _ ha; rw [smul_comm]; exact Submodule.smul_of_tower_mem _ r ha

end TwistTildeProof


open TwistTildeProof in
theorem TwistTilde.proof : TwistTilde.Statement := by
  intro S _ Ω _ _ N x E _ _ _ _ M Q
  exact ⟨prod M Q, fun c => rfl, twist_eq M Q⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.InterNumPointSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u v w

def InterNumPoint.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (y : Fin (N + 1) → Ω),
    IsSubvar y (primeOf (S := k) y) 0 → ∀ L : Fin 0 → SubSystem k y Ω,
      interNum (primeOf (S := k) y) L = (Module.finrank k (funField (k := k) y) : ℤ)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsZeroIdealChart
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def ZeroIdealChart.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (T : StepData k x) (I : Chart x) (y : Ω),
    (∀ δ ∈ T.D.sub I, y * δ ∈ chartRing k x I) → T.si * y ∈ idealMod (x := x) T.J I

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleEmbedSectionsSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u v w

def VeryAmpleEmbed.Sections.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (y : Fin (N + 1) → Ω)
    (Q : LineBundle k y) (r : ℕ) (h : Fin (r + 1) → Ω), y ≠ 0 → IsVeryAmpleBy Q.toSubSystem h →
    ∀ m : ℕ, (Q.toSubSystem.pow m).secs = (twistSys k h (m : ℤ)).secs

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.QuotientH0FiniteHypothesesLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def QuotientH0Finite.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (F G : SubSystem S x E), (∀ I, G.sub I ≤ F.sub I) →
    Module.Finite S (F.H 0) → Module.Finite S (G.H 1) → Module.Finite S (SubSystem.quotH F G 0)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleCechSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

def VeryAmpleCech.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (F : SubFamily S x E), (∀ I, (F.sub I).FG) → ∀ (H : LineBundle S x) (r : ℕ) (h : Fin (r + 1) → Ω),
    IsVeryAmpleBy H.toSubSystem h →
    ∃ F' : SubFamily S h E, (∀ J, (F'.sub J).FG) ∧ ∀ a i : ℕ,
      Nonempty ((F.twist (H.pow a)).H i ≃ₗ[S] (F'.twist (twistSys S h (a : ℤ))).H i)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.QuotTransSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def QuotTrans.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (F₁ F₂ F₃ : SubSystem S x E), (∀ I, F₃.sub I ≤ F₂.sub I) → (∀ I, F₂.sub I ≤ F₁.sub I) →
    Subsingleton (SubSystem.quotH F₂ F₃ 1) → Subsingleton (SubSystem.quotH F₁ F₂ 1) →
    Subsingleton (SubSystem.quotH F₁ F₃ 1)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsStepThreeAway
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def StepThree.Away.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (T : StepData k x) (b : ℕ) (c : ℤ), 0 ≤ c → ∀ I : Chart x,
      ((idealMod (x := x) T.J I).comap (Algebra.linearMap (chartRing k x I) Ω)) ^ b •
          ((T.L.pow b).twist (twistSys k x c)).sub I ≤
        Submodule.span (chartRing k x I) (((T.L.pow b).twist (twistSys k x c)).secs : Set Ω)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SectionCountDropFiltFiniteSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def SectionCount.Drop.Filt.Finite.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (Q : LineBundle S x) (pp : Ideal (Poly S N)) (c : ℤ), pp.IsPrime →
    (∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp) → primeOf (S := S) x ≤ pp →
    Module.Finite S (SubSystem.quotH (Q.twist (twistSys S x c))
      ((Q.twist (twistSys S x c)).twist (idealSys x pp)) 0)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleEmbedNumbersSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u v w

def VeryAmpleEmbed.Numbers.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (y : Fin (N + 1) → Ω)
    (Q : LineBundle k y) (r : ℕ) (h : Fin (r + 1) → Ω), IsVeryAmpleBy Q.toSubSystem h →
    ∀ n : ℕ, IsSubvar y (primeOf (S := k) y) n →
      IsSubvar h (primeOf (S := k) h) n ∧
        interNum (primeOf (S := k) y) (fun _ : Fin n => Q.toSubSystem) =
          interNum (primeOf (S := k) h) (fun _ : Fin n => twistSys k h 1)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SectionCountDropFiltKernelSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def SectionCount.Drop.Filt.Kernel.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (j : Fin (N + 1)) (b : ℕ) (F : SubSystem S x Ω), x j ≠ 0 →
    (∀ t ∈ (F.twist (twistSys S x (-(b : ℤ)))).secs, x j ^ b * t ∈ F.secs) ∧
    ∀ s ∈ (F.twist (idealSys x (primeOf (S := S) x ⊔
        zeroIdeal (twistSys S x (b : ℤ)) (x j ^ b)))).secs,
      ∃ t ∈ (F.twist (twistSys S x (-(b : ℤ)))).secs, s = x j ^ b * t

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SectionCountTopSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open Filter

noncomputable section

universe u w

def SectionCount.Top.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω) (d : ℕ)
    (Nb : LineBundle k x), IsSubvar x (primeOf (S := k) x) (d + 1) → IsVeryAmple Nb.toSubSystem →
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      (interNum (primeOf (S := k) x) (fun _ : Fin (d + 1) => Nb.toSubSystem) : ℝ) *
          (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) - C * (n : ℝ) ^ d ≤
        (Module.finrank k (twistMul Nb.toSubSystem n 0).secs : ℝ)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SectionCountDropHilbWSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open Filter

noncomputable section

universe u w

def SectionCount.Drop.HilbW.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (Nb : LineBundle k x) (pp : Ideal (Poly k N)) (e : ℕ),
    IsVeryAmple Nb.toSubSystem → IsSubvar x pp e →
    ∃ C : ℝ, ∀ᶠ m : ℕ in atTop,
      |(Module.finrank k (SubSystem.quotH (twistMul Nb.toSubSystem m 0)
          ((twistMul Nb.toSubSystem m 0).twist (idealSys x pp)) 0) : ℝ) -
        (interNum pp (fun _ : Fin e => Nb.toSubSystem) : ℝ) * (m : ℝ) ^ e / (e.factorial : ℝ)| ≤
        C * (m : ℝ) ^ e / m

end

end GroundTheory.Heights₂.Heights.Kleiman
end

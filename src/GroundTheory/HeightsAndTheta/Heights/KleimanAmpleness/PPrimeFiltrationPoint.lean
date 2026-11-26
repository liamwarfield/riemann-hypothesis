module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Statements
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CoordIdealIsMultiProjPrime
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgDefs
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.GenericComplexPoint

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationPoint
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

section PointLemmas

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {j : Fin (N + 1)}

theorem ideal_eq_of_isHomogeneous {I J : Ideal (Poly S N)}
    (hI : ∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I)
    (hJ : ∀ p ∈ J, ∀ d : ℕ, homogeneousComponent d p ∈ J)
    (h : ∀ (f : Poly S N) (e : ℕ), f.IsHomogeneous e → (f ∈ I ↔ f ∈ J)) : I = J := by
  ext f
  constructor
  · intro hf
    rw [← sum_homogeneousComponent f]
    exact J.sum_mem fun d _ => (h _ d (homogeneousComponent_isHomogeneous d f)).mp (hI f hf d)
  · intro hf
    rw [← sum_homogeneousComponent f]
    exact I.sum_mem fun d _ => (h _ d (homogeneousComponent_isHomogeneous d f)).mpr (hJ f hf d)

theorem exists_eq_X_pow_of_mem_monos_single {s : Poly S N} (hs : s ∈ monos {j}) :
    ∃ n : ℕ, s = X j ^ n := by
  have hs' : s ∈ Submonoid.closure {(X j : Poly S N)} := by
    have : ((fun i => (X i : Poly S N)) '' ((({j} : Finset (Fin (N + 1))) : Set (Fin (N + 1))))) =
        {X j} := by simp
    rw [← this]
    exact hs
  obtain ⟨n, rfl⟩ := Submonoid.mem_closure_singleton.mp hs'
  exact ⟨n, rfl⟩

theorem notMem_of_mem_monos_single {pp : Ideal (Poly S N)} [hpp : pp.IsPrime]
    (hX : (X j : Poly S N) ∉ pp) {s : Poly S N} (hs : s ∈ monos {j}) : s ∉ pp := by
  obtain ⟨n, rfl⟩ := exists_eq_X_pow_of_mem_monos_single hs
  exact fun h => hX (hpp.mem_of_pow_mem n h)

theorem mem_of_div_eq (hj : x j ≠ 0) {pp : Ideal (Poly S N)} [hpp : pp.IsPrime]
    (hle : primeOf (S := S) x ≤ pp) (hX : (X j : Poly S N) ∉ pp) {f s' G s : Poly S N} {e D : ℕ}
    (hf : f.IsHomogeneous e) (hs' : s' ∈ monos {j}) (hs'e : s'.IsHomogeneous e) (hG : G ∈ pp)
    (hGD : G.IsHomogeneous D) (hs : s ∈ monos {j}) (hsD : s.IsHomogeneous D)
    (h : aeval x f / aeval x s' = aeval x G / aeval x s) : f ∈ pp := by
  have h0 : aeval x s ≠ 0 := eval_ne_zero_of_mem_monos (singleChart hj) hs
  have h0' : aeval x s' ≠ 0 := eval_ne_zero_of_mem_monos (singleChart hj) hs'
  rw [div_eq_div_iff h0' h0] at h
  have h2 : (s' * G).IsHomogeneous (D + e) := by
    rw [add_comm D e]
    exact hs'e.mul hGD
  have hF : s * f - s' * G ∈ primeOf (S := S) x := by
    rw [mem_primeOf_of_isHomogeneous x ((hsD.mul hf).sub h2)]
    simp only [map_sub, map_mul]
    linear_combination h
  have h3 : s * f ∈ pp := by
    have := pp.add_mem (hle hF) (pp.mul_mem_left s' hG)
    rwa [sub_add_cancel] at this
  exact (hpp.mem_or_mem h3).resolve_left (notMem_of_mem_monos_single hX hs)


variable (x) in
def chartPrimeIdeal (hj : x j ≠ 0) (pp : Ideal (Poly S N)) :
    Ideal (chartRing S x (singleChart hj)) where
  carrier := {a | ∃ (f s : Poly S N) (e : ℕ), f ∈ pp ∧ s ∈ monos {j} ∧ f.IsHomogeneous e ∧
    s.IsHomogeneous e ∧ (a : Ω) = aeval x f / aeval x s}
  zero_mem' := ⟨0, 1, 0, pp.zero_mem, one_mem _, isHomogeneous_zero _ _ _, isHomogeneous_one _ _,
    by simp⟩
  add_mem' := by
    rintro a b ⟨f, s, e, hf, hs, hfe, hse, ha⟩ ⟨g, t, d, hg, ht, hgd, htd, hb⟩
    refine ⟨f * t + s * g, s * t, e + d, pp.add_mem (pp.mul_mem_right t hf) (pp.mul_mem_left s hg),
      mul_mem hs ht, (hfe.mul htd).add (hse.mul hgd), hse.mul htd, ?_⟩
    rw [Subalgebra.coe_add, ha, hb, div_add_div _ _ (eval_ne_zero_of_mem_monos (singleChart hj) hs)
      (eval_ne_zero_of_mem_monos (singleChart hj) ht)]
    simp only [map_add (f := _), map_mul]
  smul_mem' := by
    rintro c a ⟨g, t, d, hg, ht, hgd, htd, ha⟩
    obtain ⟨f, s, e, hs, hfe, hse, hc⟩ := c.2
    refine ⟨f * g, s * t, e + d, pp.mul_mem_left f hg, mul_mem hs ht, hfe.mul hgd, hse.mul htd, ?_⟩
    change (c : Ω) * (a : Ω) = _
    rw [hc, ha, map_mul, map_mul, div_mul_div_comm]

theorem chartPrime_le_chartPrimeIdeal (hj : x j ≠ 0) (pp : Ideal (Poly S N)) :
    chartPrime pp hj ≤ chartPrimeIdeal x hj pp := by
  rw [chartPrime, Ideal.span_le]
  intro a ha
  exact ha

theorem mem_chartPrime_iff (hj : x j ≠ 0) {pp : Ideal (Poly S N)} [pp.IsPrime]
    (hle : primeOf (S := S) x ≤ pp) (hX : (X j : Poly S N) ∉ pp) {a : chartRing S x (singleChart hj)}
    {f s : Poly S N} {e : ℕ} (hf : f.IsHomogeneous e) (hs : s ∈ monos {j}) (hse : s.IsHomogeneous e)
    (ha : (a : Ω) = aeval x f / aeval x s) : a ∈ chartPrime pp hj ↔ f ∈ pp := by
  constructor
  · intro h
    obtain ⟨G, t, D, hG, ht, hGD, htD, hat⟩ := chartPrime_le_chartPrimeIdeal hj pp h
    exact mem_of_div_eq hj hle hX hf hs hse hG hGD ht htD (ha.symm.trans hat)
  · intro h
    exact Ideal.subset_span ⟨f, s, e, h, hs, hf, hse, ha⟩

theorem coe_aeval_ratio (hj : x j ≠ 0) {f : Poly S N} {e : ℕ} (hf : f.IsHomogeneous e) :
    ((aeval (ratio (S := S) hj) f : chartRing S x (singleChart hj)) : Ω) = aeval x f / x j ^ e := by
  rw [← aeval_div_of_isHomogeneous hf j]
  change (chartRing S x (singleChart hj)).val _ = _
  rw [comp_aeval_apply]
  rfl

theorem coe_aeval_ratio' (hj : x j ≠ 0) {f : Poly S N} {e : ℕ} (hf : f.IsHomogeneous e) :
    ((aeval (ratio (S := S) hj) f : chartRing S x (singleChart hj)) : Ω) =
      aeval x f / aeval x (X j ^ e : Poly S N) := by
  rw [coe_aeval_ratio hj hf, map_pow, aeval_X]

end PointLemmas

theorem PrimeFiltration.Point.proof : PrimeFiltration.Point.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x pp hpp hhom hle j hj hX
  refine ⟨?_, ?_⟩
  · rw [Ideal.isPrime_iff]
    refine ⟨?_, ?_⟩
    · rw [Ideal.ne_top_iff_one]
      rw [mem_chartPrime_iff (f := 1) (s := 1) hj hle hX (isHomogeneous_one _ _) (one_mem _)
        (isHomogeneous_one _ _) (by simp)]
      exact (Ideal.ne_top_iff_one pp).mp hpp.ne_top
    · intro a b hab
      obtain ⟨f, s, e, hs, hf, hse, ha⟩ := a.2
      obtain ⟨g, t, d, ht, hg, htd, hb⟩ := b.2
      have hab' : ((a * b : chartRing S x (singleChart hj)) : Ω) = aeval x (f * g) / aeval x (s * t) := by
        rw [Subalgebra.coe_mul, ha, hb, map_mul, map_mul, div_mul_div_comm]
      rw [mem_chartPrime_iff hj hle hX (hf.mul hg) (mul_mem hs ht) (hse.mul htd) hab'] at hab
      rw [mem_chartPrime_iff hj hle hX hf hs hse ha, mem_chartPrime_iff hj hle hX hg ht htd hb]
      exact hpp.mem_or_mem hab
  · intro K' _ _ ψ hker
    apply ideal_eq_of_isHomogeneous (fun p hp d => homogeneousComponent_mem_primeOf _ hp d) hhom
    intro f e hf
    rw [mem_primeOf_of_isHomogeneous _ hf, ← comp_aeval_apply, ← RingHom.mem_ker, hker]
    exact mem_chartPrime_iff hj hle hX hf (pow_mem (X_mem_monos (Finset.mem_singleton_self j)) e)
      (isHomogeneous_X_pow j e) (coe_aeval_ratio' hj hf)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsSerrePoly
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def Cech.idRes (R : Type u) [CommRing R] (V : Type v) [AddCommGroup V] [Module R V] {n : ℕ}
    (U : Finset (Fin n)) : ∀ I J : Cell U, I.1 ⊆ J.1 → V →ₗ[R] V :=
  fun _ _ _ => LinearMap.id

section Laurent

variable (S : Type u) [CommRing S] (N : ℕ)

abbrev Laurent : Type u := (Fin (N + 1) → ℤ) →₀ S

def laurentExps (c : ℤ) (I : Finset (Fin (N + 1))) : Set (Fin (N + 1) → ℤ) :=
  {a | ∑ j, a j = c ∧ ∀ j ∉ I, 0 ≤ a j}

def laurentDeg (c : ℤ) (I : StdCell N) : Submodule S (Laurent S N) :=
  Finsupp.supported S S (laurentExps N c I.1)

def laurentCohom (i : ℕ) (c : ℤ) : Type u :=
  Cech.Hdeg (fun _ : StdCell N => Laurent S N) (laurentDeg S N c)
    (Cech.idRes S (Laurent S N) Finset.univ) i

instance (i : ℕ) (c : ℤ) : AddCommGroup (laurentCohom S N i c) :=
  inferInstanceAs (AddCommGroup (Cech.Hdeg _ _ _ _))
instance (i : ℕ) (c : ℤ) : Module S (laurentCohom S N i c) :=
  inferInstanceAs (Module S (Cech.Hdeg _ _ _ _))

def expToInt (e : Fin (N + 1) →₀ ℕ) : Fin (N + 1) → ℤ := fun j => (e j : ℤ)

def polyToLaurent : Poly S N →ₗ[S] Laurent S N where
  toFun p := Finsupp.mapDomain (expToInt N) (AddMonoidAlgebra.coeff p)
  map_add' p q := by
    change Finsupp.mapDomain _ (AddMonoidAlgebra.coeff p + AddMonoidAlgebra.coeff q) = _
    exact Finsupp.mapDomain_add
  map_smul' r p := by
    change Finsupp.mapDomain _ (r • AddMonoidAlgebra.coeff p) = _
    exact Finsupp.mapDomain_smul r _

end Laurent

def SerrePoly.Laurent.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (N : ℕ),
    Function.Injective (polyToLaurent S N) ∧
    (∀ c : ℤ, ((polyGraded (S := S) (N := N)).piece c).map (polyToLaurent S N) =
      Finsupp.supported S S (laurentExps N c ∅)) ∧
    ∃ ι : ∀ I : StdCell N, LocMod S N (Poly S N) I.1 →ₗ[S] Laurent S N,
      (∀ I, Function.Injective (ι I)) ∧
      (∀ (I J : StdCell N) (h : I.1 ⊆ J.1) (z : LocMod S N (Poly S N) I.1),
        ι J (locResS I J h z) = ι I z) ∧
      (∀ (I : StdCell N) (p : Poly S N), ι I (locMk (M := Poly S N) I.1 p) = polyToLaurent S N p) ∧
      ∀ (c : ℤ) (I : StdCell N),
        (degLoc (polyGraded (S := S) (N := N)) c I).map (ι I) = laurentDeg S N c I

def Cech.Transport.Statement : Prop :=
  ∀ (n : ℕ) (U : Finset (Fin n)) (R : Type u) [CommRing R]
    (G : Cell U → Type v) [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)]
    (G' : Cell U → Type w) [∀ I, AddCommGroup (G' I)] [∀ I, Module R (G' I)]
    (ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J) (ρ' : ∀ I J : Cell U, I.1 ⊆ J.1 → G' I →ₗ[R] G' J)
    (deg : ∀ I, Submodule R (G I)) (deg' : ∀ I, Submodule R (G' I)) (φ : ∀ I, G I →ₗ[R] G' I)
    (hφ : ∀ I J h m, φ J (ρ I J h m) = ρ' I J h (φ I m)) (hdeg : ∀ I m, m ∈ deg I → φ I m ∈ deg' I),
    (∀ I, Function.Injective (φ I)) → (∀ I, (deg I).map (φ I) = deg' I) →
    ∀ i, Function.Bijective (Cech.mapHdeg deg deg' φ hφ hdeg i)

def Cech.Cone.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (V : Type v) [AddCommGroup V] [Module R V] (N : ℕ)
    (J : Finset (Fin (N + 1))),
    (∀ (W : Submodule R V) (i₀ : Fin (N + 1)), i₀ ∉ J → ∀ (i : ℕ)
      (z : Cech.Cochain (fun _ : StdCell N => V) (i + 1)),
      Cech.d (fun _ : StdCell N => V) (Cech.idRes R V Finset.univ) (i + 1) z = 0 →
      (∀ I, z I ∈ W) → (∀ I, ¬ J ⊆ I.1.1 → z I = 0) →
      ∃ y : Cech.Cochain (fun _ : StdCell N => V) i, (∀ I, y I ∈ W) ∧ (∀ I, ¬ J ⊆ I.1.1 → y I = 0) ∧
        Cech.d (fun _ : StdCell N => V) (Cech.idRes R V Finset.univ) i y = z) ∧
    (J.Nonempty → ∀ i₀ : Fin (N + 1), i₀ ∉ J → ∀ z : Cech.Cochain (fun _ : StdCell N => V) 0,
      Cech.d (fun _ : StdCell N => V) (Cech.idRes R V Finset.univ) 0 z = 0 →
      (∀ I, ¬ J ⊆ I.1.1 → z I = 0) → z = 0) ∧
    ∀ z : Cech.Cochain (fun _ : StdCell N => V) 0,
      Cech.d (fun _ : StdCell N => V) (Cech.idRes R V Finset.univ) 0 z = 0 → ∀ I K, z I = z K

def SerrePoly.LaurentCohom.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (N : ℕ),
    (∀ (i : ℕ) (c : ℤ), Module.Finite S (laurentCohom S N i c)) ∧
    (∀ c : ℤ, 0 ≤ c → ∀ i, 1 ≤ i → Subsingleton (laurentCohom S N i c)) ∧
    ∀ c : ℤ, 0 ≤ c → ∀ z : Cech.Cochain (fun _ : StdCell N => Laurent S N) 0,
      z ∈ Cech.cocyDeg (fun _ : StdCell N => Laurent S N) (laurentDeg S N c)
        (Cech.idRes S (Laurent S N) Finset.univ) 0 →
      ∃ f ∈ Finsupp.supported S S (laurentExps N c ∅), ∀ I, z I = f

section Hypotheses

end Hypotheses

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PAmpleTwistLocal
section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsAmpleAffine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def AmpleAffineGen.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (H : LineBundle S x) (A : AmpleData S x H) (Q : LineBundle S x) (b : ℕ)
    (j : Fin (A.r + 1)), A.h j ≠ 0 →
    ∃ (p : ℕ) (s : Fin p → Ω),
      (∀ (t : Fin p) (I : Chart x), ∃ k : ℕ,
        s t * A.h j ^ k ∈ (Q.twist (H.pow (b + A.m * k))).sub I) ∧
      ∀ (I : Chart x) (z : Ω) (k : ℕ), z * A.h j ^ k ∈ (Q.twist (H.pow (b + A.m * k))).sub I →
        ∃ (e : ℕ) (g : Fin p → Ω), (∀ t, g t * A.h j ^ e ∈ (H.pow (A.m * e)).sub I) ∧
          z = ∑ t, g t * s t

section Hypotheses

variable (k : Type u) [Field k]

end Hypotheses

end

end GroundTheory.Heights₂.Heights.Kleiman
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace AmpleTwistLocal

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem mem_chartRing_of_mem_zero {I : Chart x} {q : Ω} (hq : q ∈ twistMod S x 0 I) :
    q ∈ chartRing S x I := by
  refine Submodule.span_induction (p := fun q _ => q ∈ chartRing S x I) ?_ ?_ ?_ ?_ hq
  · rintro _ ⟨f, s, e, e', hs, hf, hse, he, rfl⟩
    have hee : e' = e := by omega
    subst hee
    exact ⟨f, s, e', hs, hf, hse, rfl⟩
  · exact Subalgebra.zero_mem _
  · intro a b _ _ ha hb; exact Subalgebra.add_mem _ ha hb
  · intro a q _ hq
    rw [chartRing_smul_def]
    exact Subalgebra.mul_mem _ a.2 hq

theorem mul_mem_pow (H : SubSystem S x Ω) (I : Chart x) {c : ℕ} {z : Ω}
    (hz : z ∈ (H.pow c).sub I) (d : ℕ) {w : Ω} (hw : w ∈ (H.pow d).sub I) :
    z * w ∈ (H.pow (c + d)).sub I := by
  induction d generalizing w with
  | zero =>
    change w ∈ twistMod S x 0 I at hw
    have h := Submodule.smul_mem ((H.pow c).sub I)
      (⟨w, mem_chartRing_of_mem_zero hw⟩ : chartRing S x I) hz
    rw [chartRing_smul_def] at h
    rwa [Nat.add_zero, mul_comm]
  | succ d ih =>
    change w ∈ Submodule.span _ _ at hw
    refine Submodule.span_induction
      (p := fun w _ => z * w ∈ ((H.pow (c + d)).twist H).sub I) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨q, hq, y, hy, rfl⟩
      refine Submodule.subset_span ⟨q, hq, z * y, ih hy, ?_⟩
      simp only [smul_eq_mul]; ring
    · rw [mul_zero]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [mul_add]; exact Submodule.add_mem _ ha hb
    · intro a w _ hw
      rw [chartRing_smul_def, mul_left_comm, ← chartRing_smul_def]
      exact Submodule.smul_mem _ a hw

theorem pow_mem_pow (H : SubSystem S x Ω) (I : Chart x) {m : ℕ} {h : Ω}
    (hh : h ∈ (H.pow m).sub I) (n : ℕ) : h ^ n ∈ (H.pow (m * n)).sub I := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact one_mem_twistMod_zero I
  | succ n ih =>
    rw [pow_succ, Nat.mul_succ]
    exact mul_mem_pow H I ih m hh

theorem mul_mem_twist_pow (Q H : SubSystem S x Ω) (I : Chart x) {c d : ℕ} {z w : Ω}
    (hz : z ∈ (Q.twist (H.pow c)).sub I) (hw : w ∈ (H.pow d).sub I) :
    z * w ∈ (Q.twist (H.pow (c + d))).sub I := by
  change z ∈ Submodule.span _ _ at hz
  refine Submodule.span_induction
    (p := fun z _ => z * w ∈ (Q.twist (H.pow (c + d))).sub I) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨q, hq, y, hy, rfl⟩
    refine Submodule.subset_span ⟨q * w, mul_mem_pow H I hq d hw, y, hy, ?_⟩
    simp only [smul_eq_mul]; ring
  · rw [zero_mul]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [add_mul]; exact Submodule.add_mem _ ha hb
  · intro a z _ hz
    rw [chartRing_smul_def, mul_assoc, ← chartRing_smul_def]
    exact Submodule.smul_mem _ a hz

theorem proof (hA : AmpleAffineGen.Statement.{u, w}) : AmpleTwistLocal.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x H A Q b j
  classical
  by_cases h0 : A.h j = 0
  · refine ⟨0, fun n _ I y _ => ⟨1, ?_⟩⟩
    rw [h0, pow_one, mul_zero]
    exact Submodule.zero_mem _
  obtain ⟨p, s, hs, hgen⟩ := hA S Ω N x H A Q b j h0
  have hhI : ∀ I : Chart x, A.h j ∈ (H.pow A.m).sub I := fun I =>
    (Submodule.mem_iInf _).mp (A.mem_secs j) I
  choose k hk using hs
  refine ⟨Finset.univ.sup fun q : Fin p × Chart x => k q.1 q.2, fun n hn I y hy => ?_⟩
  have hglob : ∀ t, s t * A.h j ^ n ∈ (Q.twist (H.pow (b + A.m * n))).secs := by
    intro t
    refine (Submodule.mem_iInf _).mpr fun I' => ?_
    have hle : k t I' ≤ n := le_trans
      (Finset.le_sup (f := fun q : Fin p × Chart x => k q.1 q.2) (Finset.mem_univ (t, I'))) hn
    have h1 := mul_mem_twist_pow Q.toSubSystem H.toSubSystem I' (hk t I')
      (pow_mem_pow H.toSubSystem I' (hhI I') (n - k t I'))
    have e1 : s t * A.h j ^ k t I' * A.h j ^ (n - k t I') = s t * A.h j ^ n := by
      rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hle]
    have e2 : b + A.m * k t I' + A.m * (n - k t I') = b + A.m * n := by
      rw [add_assoc, ← mul_add, Nat.add_sub_cancel' hle]
    rw [e1, e2] at h1
    exact h1
  have hpn : A.h j ^ n ≠ 0 := pow_ne_zero n h0
  obtain ⟨e, g, hg, hz⟩ := hgen I (y / A.h j ^ n) n (by rwa [div_mul_cancel₀ y hpn])
  refine ⟨e, ?_⟩
  have hy' : y = A.h j ^ n * ∑ t, g t * s t := by
    rw [← hz]; field_simp
  rw [hy', Finset.mul_sum, Finset.sum_mul]
  refine Submodule.sum_mem _ fun t _ => ?_
  have e3 : A.h j ^ n * (g t * s t) * A.h j ^ e = (s t * A.h j ^ n) * (g t * A.h j ^ e) := by ring
  rw [e3]
  exact Submodule.mul_mem_mul (Submodule.subset_span (hglob t)) (hg t)

end AmpleTwistLocal

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.EqZeroOrIsHomogeneousOfMemPolyPiece
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq

open MvPolynomial

noncomputable section

section Graded

variable (S : Type) [CommRing S] (N : ℕ)

theorem mem_polyPiece_of_isHomogeneous {f : Poly S N} {e : ℕ} (hf : f.IsHomogeneous e) :
    f ∈ IndefiniteRowSideFullHecke.Kleiman.polyPiece S N e := by
  rw [IndefiniteRowSideFullHecke.Kleiman.polyPiece, mem_weightedHomogeneousSubmodule]
  exact isWeightedHomogeneous_int_of_isHomogeneous hf

theorem eq_zero_or_isHomogeneous_of_mem_polyPiece {f : Poly S N} {d : ℤ}
    (hf : f ∈ IndefiniteRowSideFullHecke.Kleiman.polyPiece S N d) :
    f = 0 ∨ ∃ e : ℕ, (e : ℤ) = d ∧ f.IsHomogeneous e := by
  classical
  rw [IndefiniteRowSideFullHecke.Kleiman.polyPiece, mem_weightedHomogeneousSubmodule] at hf
  have hw : ∀ s : Fin (N + 1) →₀ ℕ,
      Finsupp.weight (fun _ : Fin (N + 1) => (1 : ℤ)) s = ((Finsupp.weight (1 : Fin (N + 1) → ℕ) s : ℕ) : ℤ) := by
    intro s
    simp [Finsupp.weight_apply, Finsupp.sum]
  by_cases h0 : f = 0
  · exact Or.inl h0
  · right
    obtain ⟨s, hs⟩ := MvPolynomial.ne_zero_iff.mp h0
    refine ⟨Finsupp.weight (1 : Fin (N + 1) → ℕ) s, ?_, ?_⟩
    · rw [← hw]; exact hf hs
    · intro t ht
      have h1 := hf ht
      have h2 := hf hs
      rw [hw] at h1 h2
      exact_mod_cast h1.trans h2.symm

variable (M : Type) [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]

def gradedEquiv : IndefiniteRowSideFullHecke.Kleiman.GradedMod S N M ≃ Kleiman.GradedPMod S N M where
  toFun G :=
    { piece := G.piece
      isInternal := G.internal
      smul_mem := fun d c p m hp hm => by
        rw [add_comm]
        exact G.smul_mem d c p (mem_polyPiece_of_isHomogeneous S N hp) m hm }
  invFun G :=
    { piece := G.piece
      internal := G.isInternal
      smul_mem := fun d c f hf m hm => by
        rcases eq_zero_or_isHomogeneous_of_mem_polyPiece S N hf with rfl | ⟨e, rfl, he⟩
        · rw [zero_smul]; exact zero_mem _
        · rw [add_comm]; exact G.smul_mem e c f m he hm }
  left_inv _ := rfl
  right_inv _ := rfl

end Graded

section Charts

variable (S : Type) [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω]

theorem pow_div_mem_chartRingI (x : Fin (N + 1) → Ω) (I : Kleiman.Chart x) (i₀ : Fin (N + 1))
    {s : Poly S N} (hs : s ∈ Kleiman.monos I.1) :
    ∃ e : ℕ, s.IsHomogeneous e ∧ x i₀ ^ e / aeval x s ∈ IndefiniteRowSideFullHecke.Kleiman.chartRingI S x I.1 := by
  induction hs using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨i, hi, rfl⟩ := ha
    refine ⟨1, isHomogeneous_X S i, ?_⟩
    rw [pow_one, aeval_X]
    exact Algebra.subset_adjoin ⟨i, hi, i₀, rfl⟩
  | one => exact ⟨0, isHomogeneous_one _ _, by simp⟩
  | mul a b _ _ ha hb =>
    obtain ⟨e, hae, hea⟩ := ha
    obtain ⟨e', hbe, heb⟩ := hb
    refine ⟨e + e', hae.mul hbe, ?_⟩
    have : x i₀ ^ (e + e') / aeval x (a * b) = (x i₀ ^ e / aeval x a) * (x i₀ ^ e' / aeval x b) := by
      rw [map_mul, pow_add, mul_div_mul_comm]
    rw [this]
    exact mul_mem hea heb

theorem chartRingI.equiv (x : Fin (N + 1) → Ω) (I : Kleiman.Chart x) :
    IndefiniteRowSideFullHecke.Kleiman.chartRingI S x I.1 = Kleiman.chartRing S x I := by
  apply le_antisymm
  · rw [IndefiniteRowSideFullHecke.Kleiman.chartRingI, Algebra.adjoin_le_iff]
    rintro _ ⟨i, hi, j, rfl⟩
    exact ⟨X j, X i, 1, Kleiman.X_mem_monos hi, isHomogeneous_X S j, isHomogeneous_X S i, by simp⟩
  · rintro _ ⟨f, s, e, hs, hf, hse, rfl⟩
    obtain ⟨i₀, hi₀⟩ := I.2.1
    have hx₀ : x i₀ ≠ 0 := (Kleiman.mem_support x).mp (I.2.2 hi₀)
    have hs0 : aeval x s ≠ 0 := Kleiman.eval_ne_zero_of_mem_monos I hs
    have hsne : s ≠ 0 := fun h => hs0 (by rw [h, map_zero])
    obtain ⟨e', hse', hmem⟩ := pow_div_mem_chartRingI S x I i₀ hs
    have hee : e = e' := hse.inj_right hse' hsne
    subst hee
    have hall : ∀ g : Poly S N, aeval (fun l => x l / x i₀) g ∈ IndefiniteRowSideFullHecke.Kleiman.chartRingI S x I.1 := by
      intro g
      induction g using MvPolynomial.induction_on with
      | C a => rw [aeval_C]; exact Subalgebra.algebraMap_mem _ a
      | add p q hp hq => rw [map_add]; exact add_mem hp hq
      | mul_X p i hp =>
        rw [map_mul, aeval_X]
        exact mul_mem hp (Algebra.subset_adjoin ⟨i₀, hi₀, i, rfl⟩)
    have hf' : aeval x f / x i₀ ^ e ∈ IndefiniteRowSideFullHecke.Kleiman.chartRingI S x I.1 := by
      rw [← Kleiman.aeval_div_of_isHomogeneous hf i₀]
      exact hall f
    have heq : aeval x f / aeval x s = (aeval x f / x i₀ ^ e) * (x i₀ ^ e / aeval x s) := by
      field_simp
    rw [heq]
    exact mul_mem hf' hmem

theorem chartRing.equiv (x : Fin (N + 1) → Ω) {i : Fin (N + 1)} (hi : x i ≠ 0) :
    ReciprocityTheory.ChartRestriction.G.Geo.chartRing S x i = Kleiman.chartRing S x (Kleiman.singleChart hi) := by
  rw [← IndefiniteRowSideFullHecke.Kleiman.chartRingI_singleton, ← chartRingI.equiv]
  rfl

end Charts

section Families

variable {S : Type} [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω] {x : Fin (N + 1) → Ω}
variable {E : Type} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]



omit [Module S E] [IsScalarTower S Ω E] in
theorem mem_twist_twistSys_iff (F : Kleiman.SubSystem S x E) (c : ℤ) (I : Kleiman.Chart x)
    {i : Fin (N + 1)} (hi : i ∈ I.1) (z : E) :
    z ∈ (F.twist (Kleiman.twistSys S x c)).sub I ↔ ∃ y ∈ F.sub I, z = x i ^ c • y := by
  constructor
  · intro hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨q, hq, y, hy, rfl⟩ := hz
      change q ∈ Kleiman.twistMod S x c I at hq
      rw [Kleiman.twistMod_eq_span c I hi, Submodule.mem_span_singleton] at hq
      obtain ⟨a, rfl⟩ := hq
      refine ⟨a • y, Submodule.smul_mem _ a hy, ?_⟩
      rw [Kleiman.chartRing_smul_def, mul_smul]
      exact smul_comm _ _ _
    | zero => exact ⟨0, zero_mem _, (smul_zero _).symm⟩
    | add a b _ _ ha hb =>
      obtain ⟨y, hy, rfl⟩ := ha
      obtain ⟨y', hy', rfl⟩ := hb
      exact ⟨y + y', add_mem hy hy', (smul_add _ _ _).symm⟩
    | smul a w _ hw =>
      obtain ⟨y, hy, rfl⟩ := hw
      refine ⟨a • y, Submodule.smul_mem _ a hy, ?_⟩
      rw [Subalgebra.smul_def, Subalgebra.smul_def, smul_comm]
  · rintro ⟨y, hy, rfl⟩
    refine Submodule.subset_span ⟨x i ^ c, ?_, y, hy, rfl⟩
    change x i ^ c ∈ Kleiman.twistMod S x c I
    rw [Kleiman.twistMod_eq_span c I hi]
    exact Submodule.mem_span_singleton_self _

end Families

section Filtration

variable (S : Type) [CommRing S] (N : ℕ)
variable {M : Type} [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]

end Filtration

end

end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsPres
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def GradedPres.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (N : ℕ) (M : Type (max u v))
    [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    (𝓜 : GradedPMod S N M), Module.Finite (Poly S N) M →
    ∃ (F : Type (max u v)) (_ : AddCommGroup F) (_ : Module (Poly S N) F) (_ : Module S F)
      (_ : IsScalarTower S (Poly S N) F) (K : Type (max u v)) (_ : AddCommGroup K)
      (_ : Module (Poly S N) K) (_ : Module S K) (_ : IsScalarTower S (Poly S N) K)
      (𝓕 : GradedPMod S N F) (𝓚 : GradedPMod S N K) (r : ℕ) (b : Module.Basis (Fin r) (Poly S N) F)
      (d : Fin r → ℤ) (f : GradedHom 𝓚 𝓕) (g : GradedHom 𝓕 𝓜),
      (∀ j, b j ∈ 𝓕.piece (d j)) ∧ Module.Finite (Poly S N) K ∧ Function.Injective f.toLin ∧
        Function.Surjective g.toLin ∧ Function.Exact f.toLin g.toLin

def GradedULift.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (N : ℕ) (M : Type v)
    [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    (𝓜 : GradedPMod S N M),
    ∃ (M' : Type (max u v)) (_ : AddCommGroup M') (_ : Module (Poly S N) M') (_ : Module S M')
      (_ : IsScalarTower S (Poly S N) M') (𝓜' : GradedPMod S N M') (f : GradedHom 𝓜 𝓜')
      (g : GradedHom 𝓜' 𝓜), Function.LeftInverse g.toLin f.toLin ∧ Function.RightInverse g.toLin f.toLin

def CohomRetract.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (N : ℕ) (M : Type v) (M' : Type w)
    [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    [AddCommGroup M'] [Module (Poly S N) M'] [Module S M'] [IsScalarTower S (Poly S N) M']
    (𝓜 : GradedPMod S N M) (𝓜' : GradedPMod S N M') (f : GradedHom 𝓜 𝓜') (g : GradedHom 𝓜' 𝓜),
    Function.LeftInverse g.toLin f.toLin → ∀ (i : ℕ) (c : ℤ), Function.Injective (cohomMap f i c)

section Hypotheses

variable (k : Type u) [Field k] (N : ℕ)

end Hypotheses

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CellMeets
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

variable (S : Type) [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type}
  [Field Ω] [Algebra S Ω]

def CellMeets (y : (Σ k, ι k) → Ω) (I : ∀ k, Finset (ι k)) : Prop :=
  ∀ k, ∀ i ∈ I k, y ⟨k, i⟩ ≠ 0

open scoped Classical

open Classical in
def cellSec (y : (Σ k, ι k) → Ω) (γ : K → ℤ) (I : ∀ k, Finset (ι k)) : Submodule S Ω :=
  if CellMeets y I then
    Submodule.span S {z | ∃ (g t : MRingOver S ι) (a : K → ℕ),
      t ∈ ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.cellMon S I ∧ IsMultiHomog t a ∧ (∀ k, 0 ≤ γ k + a k) ∧
        IsMultiHomog g (fun k => (γ k + a k).toNat) ∧ z = aeval y g / aeval y t}
  else ⊥

variable [LinearOrder K] [∀ k, LinearOrder (ι k)]


open Classical in
def cellD (y : (Σ k, ι k) → Ω) (n : ℕ) :
    (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω) →ₗ[S] (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι (n + 1) → Ω) :=
  LinearMap.pi fun I => if CellMeets y I.1 then ∑ k, ∑ i ∈ I.1 k,
    if h : (∀ l, (Function.update I.1 k ((I.1 k).erase i) l).Nonempty) ∧
        ∑ l, ((Function.update I.1 k ((I.1 k).erase i) l).card - 1) = n then
      ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.faceSign I.1 k i •
        LinearMap.proj (R := S) (φ := fun _ : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n => Ω)
          ⟨Function.update I.1 k ((I.1 k).erase i), h⟩
    else 0
  else 0

def cellC (y : (Σ k, ι k) → Ω) (γ : K → ℤ) (n : ℕ) :
    Submodule S (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω) :=
  Submodule.pi Set.univ fun I => cellSec S y γ I.1

def cellZ (y : (Σ k, ι k) → Ω) (γ : K → ℤ) (n : ℕ) :
    Submodule S (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω) :=
  cellC S y γ n ⊓ LinearMap.ker (cellD S y n)

def cellB (y : (Σ k, ι k) → Ω) (γ : K → ℤ) :
    (n : ℕ) → Submodule S (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω)
  | 0 => ⊥
  | n + 1 => (cellC S y γ n).map (cellD S y n)

abbrev cellH (y : (Σ k, ι k) → Ω) (γ : K → ℤ) (n : ℕ) : Type :=
  ↥(cellZ S y γ n) ⧸ (cellB S y γ n).comap (cellZ S y γ n).subtype

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechDSq
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v

namespace CechDSq

variable {n : ℕ}

theorem sgn_mul_sgn_of_lt {K : Finset (Fin n)} {j k : Fin n} (hj : j ∈ K) (hjk : j < k) :
    Cech.sgn K k * Cech.sgn (K.erase k) j = -(Cech.sgn K j * Cech.sgn (K.erase j) k) := by
  have h1 : (K.erase k).filter (· < j) = K.filter (· < j) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨-, hz⟩, hzj⟩; exact ⟨hz, hzj⟩
    · rintro ⟨hz, hzj⟩; exact ⟨⟨(hzj.trans hjk).ne, hz⟩, hzj⟩
  have h3 : j ∈ K.filter (· < k) := Finset.mem_filter.2 ⟨hj, hjk⟩
  have h2 : ((K.erase j).filter (· < k)).card + 1 = (K.filter (· < k)).card := by
    rw [Finset.filter_erase, Finset.card_erase_add_one h3]
  unfold Cech.sgn
  rw [h1, ← h2, pow_succ]
  ring

theorem sgn_mul_sgn_swap {K : Finset (Fin n)} {j k : Fin n} (hk : k ∈ K) (hj : j ∈ K) (hne : j ≠ k) :
    Cech.sgn K k * Cech.sgn (K.erase k) j = -(Cech.sgn K j * Cech.sgn (K.erase j) k) := by
  rcases lt_or_gt_of_ne hne with h | h
  · exact sgn_mul_sgn_of_lt hj h
  · rw [sgn_mul_sgn_of_lt hk h, neg_neg]

variable {U : Finset (Fin n)} {R : Type u} [CommRing R] {G : Cell U → Type v}
  [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J}


open Classical in
def restrictTo {i : ℕ} (s : Cech.Cochain G i) (K : Cell U) (A : Finset (Fin n)) : G K :=
  if h : ∃ L : Cech.Idx U i, L.1.1 = A ∧ A ⊆ K.1 then
    ρ h.choose.1 K (by rw [h.choose_spec.1]; exact h.choose_spec.2) (s h.choose)
  else 0

theorem restrictTo_eq {i : ℕ} (s : Cech.Cochain G i) (K : Cell U) (L : Cech.Idx U i)
    (h : L.1.1 ⊆ K.1) : restrictTo (ρ := ρ) s K L.1.1 = ρ L.1 K h (s L) := by
  have hex : ∃ L' : Cech.Idx U i, L'.1.1 = L.1.1 ∧ L.1.1 ⊆ K.1 := ⟨L, rfl, h⟩
  have key : ∀ (L₁ L₂ : Cech.Idx U i) (_ : L₁ = L₂) (h₁ : L₁.1.1 ⊆ K.1) (h₂ : L₂.1.1 ⊆ K.1),
      ρ L₁.1 K h₁ (s L₁) = ρ L₂.1 K h₂ (s L₂) := by
    rintro _ _ rfl _ _; rfl
  rw [restrictTo, dite_eq_left hex]
  exact key _ _ (Subtype.ext (Subtype.ext hex.choose_spec.1)) _ _

end CechDSq


open CechDSq in
theorem CechDSq.proof : CechDSq.Statement := by
  intro n U R _ G _ _ ρ hρ i s
  classical
  funext K
  have hcomp : ∀ (I J L : Cell U) (h₁ : I.1 ⊆ J.1) (h₂ : J.1 ⊆ L.1) (x : G I),
      ρ J L h₂ (ρ I J h₁ x) = ρ I L (h₁.trans h₂) x := fun I J L h₁ h₂ x =>
    LinearMap.congr_fun (hρ I J L h₁ h₂) x

  let f : (Σ _ : Fin n, Fin n) → G K.1 := fun p =>
    (Cech.sgn K.1.1 p.1 * Cech.sgn (K.1.1.erase p.1) p.2) •
      restrictTo (ρ := ρ) s K.1 ((K.1.1.erase p.1).erase p.2)
  have step : ∀ k : K.1.1, Cech.sgn K.1.1 k • ρ (Cech.face K k).1 K.1 (Cech.face_subset K k)
      (Cech.d G ρ i s (Cech.face K k)) = ∑ j ∈ K.1.1.erase k, f ⟨k, j⟩ := by
    intro k
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Cech.d_apply, map_sum, Finset.smul_sum]
    refine Eq.trans ?_ (Finset.sum_coe_sort (K.1.1.erase k) (fun j => f ⟨k, j⟩))
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, smul_smul, hcomp, ← restrictTo_eq]
    rfl
  show Cech.d G ρ (i + 1) (Cech.d G ρ i s) K = 0
  rw [Cech.d_apply, Finset.sum_congr rfl fun k _ => step k,
    Finset.sum_coe_sort K.1.1 (fun k => ∑ j ∈ K.1.1.erase k, f ⟨k, j⟩),
    Finset.sum_sigma' K.1.1 (fun k => K.1.1.erase k) (fun k j => f ⟨k, j⟩)]
  refine Finset.sum_involution (fun p _ => ⟨p.2, p.1⟩) ?_ ?_ ?_ ?_
  · rintro ⟨k, j⟩ hp
    obtain ⟨hk, hj⟩ := Finset.mem_sigma.1 hp
    obtain ⟨hne, hj⟩ := Finset.mem_erase.1 hj
    simp only [f]
    rw [Finset.erase_right_comm, sgn_mul_sgn_swap hk hj hne, neg_smul, neg_add_cancel]
  · rintro ⟨k, j⟩ hp - h
    obtain ⟨hne, -⟩ := Finset.mem_erase.1 (Finset.mem_sigma.1 hp).2
    exact hne (congrArg Sigma.fst h)
  · rintro ⟨k, j⟩ hp
    obtain ⟨hk, hj⟩ := Finset.mem_sigma.1 hp
    obtain ⟨hne, hj⟩ := Finset.mem_erase.1 hj
    exact Finset.mem_sigma.2 ⟨hj, Finset.mem_erase.2 ⟨hne.symm, hk⟩⟩
  · rintro ⟨k, j⟩ -
    rfl

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CoordIdealXgen
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def SerreVanish.Statement : Prop :=
  ∀ (S : Type) [CommRing S] [IsNoetherianRing S] (N : ℕ)
    (M : Type) [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    (G : GradedMod S N M), Module.Finite (Poly S N) M →
    ∃ c₀ : ℤ, ∀ (i : ℕ), 1 ≤ i → ∀ c : ℤ, c₀ ≤ c → Subsingleton (gradedH S N M G i c)

section Inhabitants

variable (k : Type) [Field k]

end Inhabitants

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsDegreePos
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def ProjDegreePositive.Statement : Prop :=
  ∀ (F : Type u) [Field F] (ι₀ : Type) [Fintype ι₀] (q : Ideal (MRing (fun _ : Unit => ι₀) F))
    (D : ℕ), IsMultiProjPrime q →
    ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ q) = ((D + 1 : ℕ) : WithBot ℕ∞) →
    0 < intNum F q (fun _ : Fin D => fun _ => (1 : ℤ))

end

end GroundTheory.Heights₂.Heights.Kleiman
end

module

public import Formalism.SharpRestriction.GrowthBounds.RootWeights.ContravariantIsotypicOrthogonal
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.InvariantProjectionExtremalFormula
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CayleyForm

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.DegreeZeroWeightsBounded
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def casimirConjugation (E : GLOps n K V) (c : Fin n) (s : Finset (Fin n)) : Module.End K (Module.End K V) :=
  ∑ i ∈ s, (LinearMap.mulLeft K (E c i)).comp (LinearMap.mulRight K (E i c))

def casimirPower (E : GLOps n K V) (c : Fin n) (s : Finset (Fin n)) (q : ℕ) : Module.End K V :=
  ((casimirConjugation E c s) ^ q) 1

def casimirPowerScaled (E : GLOps n K V) (c : Fin n) (s : Finset (Fin n)) (b q : ℕ) : Module.End K V :=
  ((b.factorial : K) / (((q + b).factorial : K) * (q.factorial : K))) • casimirPower E c s q

def extremalProjector (E : GLOps n K V) (c : Fin n) (L : ℕ) : Module.End K V :=
  ∑ q ∈ range (L + 1), ((-1 : K) ^ q) • casimirPowerScaled E c (Finset.Iio c) c.val q

def DegreeZeroWeightsBounded (E : GLOps n K V) (L : ℕ) : Prop :=
  ∀ ν : Fin n → ℤ, (∑ a, ν a = 0) → weightSp E ν ≠ ⊥ → ∀ a, |ν a| ≤ (L : ℤ)

end Formalism.MainNotions.G.GLWeightTheory
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.MemWeightSpaceIffDiagonalRep
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem mem_weightSpace_iff_diagonal_rep (E : GLOps n K V) (mu : Fin n → ℤ) (x : V) :
    x ∈ weightSp E mu ↔ ∀ a, E a a x = (mu a : K) • x := by
  simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, sub_eq_zero]

theorem gl_commutation_apply {E : GLOps n K V} (hE : IsGLRep E) (a b c d : Fin n) (x : V) :
    E a b (E c d x) = E c d (E a b x) + (if b = c then E a d x else 0) - (if d = a then E c b x else 0) := by
  have h := LinearMap.congr_fun (hE.1 a b c d) x
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  have e1 : (if b = c then E a d else 0) x = (if b = c then E a d x else 0) := by split_ifs <;> rfl
  have e2 : (if d = a then E c b else 0) x = (if d = a then E c b x else 0) := by split_ifs <;> rfl
  rw [e1, e2] at h
  rw [add_sub_assoc, ← h]
  abel

theorem gl_rep_weight_shift {E : GLOps n K V} (hE : IsGLRep E) {mu : Fin n → ℤ} {x : V}
    (hx : x ∈ weightSp E mu) (a b : Fin n) : E a b x ∈ weightSp E (mu + rootW a b) := by
  rw [mem_weightSpace_iff_diagonal_rep] at hx ⊢
  intro c
  rw [gl_commutation_apply hE c c a b x, hx c, map_smul]
  simp only [rootW, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
  push_cast
  split_ifs <;> subst_vars <;> first | module | (exfalso; simp_all; done)

end Formalism.MainNotions.G.GLWeightTheory
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.FockLatticeFiniteSpanning
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def ValuationProperties (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] : Prop :=
  vK p (0 : KK O) = ⊤ ∧
  (∀ x y : KK O, vK p (x * y) = vK p x + vK p y) ∧
  (∀ x y : KK O, min (vK p x) (vK p y) ≤ vK p (x + y)) ∧
  (∀ m : ℕ, m ≠ 0 → vK p (m : KK O) = ((padicValNat p m : ℚ) : WithTop ℚ)) ∧
  (∀ x : KK O, vK p (-x) = vK p x) ∧
  (∀ x : KK O, 0 ≤ vK p x ↔ ∃ o : O, x = algebraMap O (KK O) o)

def FockLatticeClosure (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] : Prop :=
  ∀ σ : Type,
    InBB (O := O) p (0 : MvPolynomial σ (KK O)) ∧
    (∀ F G : MvPolynomial σ (KK O), InBB (O := O) p F → InBB (O := O) p G → InBB (O := O) p (F + G)) ∧
    (∀ (o : O) (F : MvPolynomial σ (KK O)), InBB (O := O) p F → InBB (O := O) p (o • F)) ∧
    (∀ (m : σ →₀ ℕ) (c : KK O), InBB (O := O) p (monomial m c) ↔
      0 ≤ vK p c + (((padicValNat p (expFact m) : ℚ) / 2 : ℚ) : WithTop ℚ)) ∧
    (∀ F : MvPolynomial σ (KK O), InBB (O := O) p F ↔ ∀ m, InBB (O := O) p (monomial m (F.coeff m))) ∧
    (∀ u : MvPolynomial σ (KK O) →ₗ[KK O] MvPolynomial σ (KK O),
      (∀ m c, InBB (O := O) p (monomial m c) → InBB (O := O) p (u (monomial m c))) →
      ∀ F, InBB (O := O) p F → InBB (O := O) p (u F)) ∧
    (∀ (m m' : σ →₀ ℕ) (c : KK O) (z : ℤ), InBB (O := O) p (monomial m c) →
      (z = 0 ∨ padicValNat p (expFact m) ≤ 2 * padicValInt p z + padicValNat p (expFact m')) →
      InBB (O := O) p (monomial m' (c * (z : KK O)))) ∧
    (∀ u : MvPolynomial σ (KK O) →ₗ[KK O] MvPolynomial σ (KK O),
      (∀ m, u (monomial m 1) ∈ IntPol O σ) → ∀ F ∈ IntPol O σ, u F ∈ IntPol O σ) ∧
    (∀ (m : σ →₀ ℕ) (z : ℤ), monomial m (z : KK O) ∈ IntPol O σ) ∧
    (∀ F : MvPolynomial σ (KK O), F ∈ IntPol O σ ↔ ∀ m, ∃ o : O, F.coeff m = algebraMap O (KK O) o)

def PolynomialIntegralFormPreservesLattices (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] : Prop :=
  ∀ (n : ℕ) (ι : Type) [Fintype ι] (LL : Letters ι) (S : Set ι),
    PolUZStable LL S (IntPol O (ι × Fin n)) ∧
        ∀ u ∈ polUZgens (KK O) LL S, ∀ F : MvPolynomial (ι × Fin n) (KK O),
          InBB (O := O) p F → InBB (O := O) p (u F)

def IntegralFormGeneratorsPreserveLattices (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] : Prop :=
  ∀ (n : ℕ) (ι : Type) [Fintype ι] (LL : Letters ι) (S : Set ι), ∀ u ∈ UZgens (glOps (KK O) n LL S),
        (∀ F ∈ IntPol O (ι × Fin n), u F ∈ IntPol O (ι × Fin n)) ∧
        ∀ F : MvPolynomial (ι × Fin n) (KK O), InBB (O := O) p F → InBB (O := O) p (u F)

def FockLatticeFiniteSpanning (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] : Prop :=
  ∀ (n : ℕ) (ι : Type) [Fintype ι],
      ∃ BBs : Submodule O (MvPolynomial (ι × Fin n) (KK O)), (∀ F, F ∈ BBs ↔ InBB (O := O) p F) ∧
        ∀ d : ι → ℕ, (latticeMultidegreePart (IntPol O (ι × Fin n)) d).FG ∧ MQ (K := KK O) (latticeMultidegreePart (IntPol O (ι × Fin n)) d) = ⊤ ∧
          (latticeMultidegreePart BBs d).FG ∧ MQ (K := KK O) (latticeMultidegreePart BBs d) = ⊤

end Formalism.MainNotions.G.GLWeightTheory
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.IsotypicProjectorSelfAdjoint
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section abs

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem mem_weightSpace_iff_diag (E : GLOps n K V) (mu : Fin n → ℤ) (x : V) :
    x ∈ weightSp E mu ↔ ∀ a, E a a x = (mu a : K) • x := by
  simp [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

theorem isotypic_stable_gl_operator (E : GLOps n K V) (mu : Fin n → ℤ) (a b : Fin n) (x : V) (hx : x ∈ isoSub E mu) :
    E a b x ∈ isoSub E mu := by
  first | exact UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator .. | (apply UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator <;> assumption) | (apply @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator <;> assumption) | (apply @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator n K V ‹_› ‹_› ‹_› E mu a b x hx | exact @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator n K V ‹_› ‹_› ‹_› E mu a b x | exact @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator n K V ‹_› ‹_› ‹_› E mu a b | exact @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator n K V ‹_› ‹_› ‹_› E mu a | exact @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator n K V ‹_› ‹_› ‹_› E mu | exact @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator n K V ‹_› ‹_› ‹_› E | exact @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator n K V ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator n K V ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator n K V ‹_› | exact @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator n K V | exact @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator n K | exact @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator n

theorem commuting_enveloping_monoid (E : GLOps n K V) (X : Module.End K V) (hX : ∀ c d, X * E c d = E c d * X)
    (u : Module.End K V) (hu : u ∈ Umon E) : X * u = u * X := by
  unfold Umon at hu
  induction hu using Submonoid.closure_induction with
  | mem u hu => obtain ⟨ab, rfl⟩ := hu; exact hX _ _
  | one => simp
  | mul u v _ _ hu hv => rw [← mul_assoc, hu, mul_assoc, hv, mul_assoc]

theorem isotypic_stable_commuting (E : GLOps n K V) (X : Module.End K V) (hX : ∀ c d, X * E c d = E c d * X)
    (mu : Fin n → ℤ) (x : V) (hx : x ∈ isoSub E mu) : X x ∈ isoSub E mu := by
  unfold isoSub at hx ⊢
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, hu, v, hv, rfl⟩ := hx
    have h1 : X (u v) = u (X v) := by
      have := congrArg (fun f : Module.End K V => f v) (commuting_enveloping_monoid E X hX u hu)
      simpa using this
    rw [h1]
    by_cases h0 : X v = 0
    · rw [h0, map_zero]; exact Submodule.zero_mem _
    · refine Submodule.subset_span ⟨u, hu, X v, ⟨h0, ?_, ?_⟩, rfl⟩
      · rw [mem_weightSpace_iff_diag]
        intro a
        have h2 := congrArg (fun f : Module.End K V => f v) (hX a a)
        have h3 := (mem_weightSpace_iff_diag E mu v).1 hv.2.1 a
        simp only [Module.End.mul_apply] at h2
        rw [← h2, h3, map_smul]
      · intro a b hab
        have h2 := congrArg (fun f : Module.End K V => f v) (hX a b)
        simp only [Module.End.mul_apply] at h2
        rw [← h2, hv.2.2 a b hab, map_zero]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem isotypic_projector_commutes (E : GLOps n K V) (hT : (⨆ mu : Fin n → ℤ, isoSub E mu) = ⊤) (lam : Fin n → ℤ)
    (e : Module.End K V) (he : IsIsoProj E lam e) (X : Module.End K V)
    (hX : ∀ mu, ∀ x ∈ isoSub E mu, X x ∈ isoSub E mu) : e * X = X * e := by
  ext x
  have hx : x ∈ (⨆ mu : Fin n → ℤ, isoSub E mu) := by rw [hT]; trivial
  simp only [Module.End.mul_apply]
  induction hx using Submodule.iSup_induction' with
  | mem mu x hx =>
    by_cases h : mu = lam
    · subst h
      rw [he.1 x hx, he.1 _ (hX _ x hx)]
    · rw [he.2 mu h x hx, he.2 mu h _ (hX _ x hx), map_zero]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add (f := _), hx, hy]

theorem isotypic_projector_selfAdjoint (E : GLOps n K V) (hT : (⨆ mu : Fin n → ℤ, isoSub E mu) = ⊤) (lam : Fin n → ℤ)
    (e : Module.End K V) (he : IsIsoProj E lam e) (B : V →ₗ[K] V →ₗ[K] K)
    (hB : ∀ lam mu : Fin n → ℤ, lam ≠ mu → ∀ x ∈ isoSub E lam, ∀ y ∈ isoSub E mu, B x y = 0) (x y : V) :
    B (e x) y = B x (e y) := by
  have hx : x ∈ (⨆ mu : Fin n → ℤ, isoSub E mu) := by rw [hT]; trivial
  have hy : y ∈ (⨆ mu : Fin n → ℤ, isoSub E mu) := by rw [hT]; trivial
  induction hx using Submodule.iSup_induction' with
  | mem mu x hx =>
    induction hy using Submodule.iSup_induction' with
    | mem nu y hy =>
      by_cases h : mu = lam
      · subst h
        rw [he.1 x hx]
        by_cases h' : nu = mu
        · subst h'; rw [he.1 y hy]
        · rw [he.2 nu h' y hy, map_zero, hB mu nu (Ne.symm h') x hx y hy]
      · rw [he.2 mu h x hx, map_zero, LinearMap.zero_apply]
        by_cases h' : nu = lam
        · subst h'; rw [he.1 y hy, hB mu nu h x hx y hy]
        · rw [he.2 nu h' y hy, map_zero]
    | zero => simp
    | add y z _ _ hy hz => simp only [map_add (f := _), hy, hz]
  | zero => simp
  | add x z _ _ hx hz => simp only [map_add (f := _), LinearMap.add_apply, hx, hz]

end abs

end Formalism.MainNotions.G.GLWeightTheory
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.BinomialExpansionCoeffZeroOfDeg
noncomputable section

open Finset Polynomial

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem coeff_binomial_power_divisibility (p P : ℕ) (hP : 0 < P) (h : ℤ[X]) (l : ℕ) : ∀ (f : ℤ[X]) (j : ℕ),
    (p : ℤ) ^ (l - j / P) ∣ (f * (X ^ P + C (p : ℤ) * h) ^ l).coeff j := by
  induction l with
  | zero => intro f j; simp
  | succ l ih =>
    intro f j
    have e : f * (X ^ P + C (p : ℤ) * h) ^ (l + 1) =
        X ^ P * (f * (X ^ P + C (p : ℤ) * h) ^ l) + C (p : ℤ) * ((f * h) * (X ^ P + C (p : ℤ) * h) ^ l) := by
      ring
    rw [e, coeff_add, coeff_X_pow_mul', coeff_C_mul]
    refine dvd_add ?_ ?_
    · split_ifs with hj
      · obtain ⟨q, rfl⟩ : ∃ q, j = q + P := ⟨j - P, by omega⟩
        rw [Nat.add_sub_cancel, Nat.add_div_right _ hP]
        exact dvd_trans (pow_dvd_pow _ (by omega)) (ih f q)
      · exact dvd_zero _
    · refine dvd_trans (pow_dvd_pow _ (show l + 1 - j / P ≤ l - j / P + 1 by omega)) ?_
      rw [pow_succ']
      exact mul_dvd_mul_left _ (ih (f * h) j)

def binomialExpansionCoeff (P rho M l : ℕ) : ℤ := (((1 + X) ^ rho * ((1 + X) ^ P - 1) ^ l : ℤ[X])).coeff M

theorem binomial_expansion_coeff_padic_dvd (p t : ℕ) (hp : p.Prime) (rho M l : ℕ) :
    (p : ℤ) ^ (l - M / p ^ t) ∣ binomialExpansionCoeff (p ^ t) rho M l := by
  have hP : 0 < p ^ t := pow_pos hp.pos t

  obtain ⟨h, hh⟩ : ∃ h : ℤ[X], (1 + X) ^ (p ^ t) - 1 = X ^ (p ^ t) + C (p : ℤ) * h := by
    have hd : C (p : ℤ) ∣ ((1 + X) ^ (p ^ t) - 1 - X ^ (p ^ t) : ℤ[X]) := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro i
      simp only [coeff_sub, coeff_one_add_X_pow, coeff_one, coeff_X_pow]
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · simp [hP.ne']
        rw [if_neg (ne_of_lt hP)]
        exact dvd_zero _
      · by_cases hiP : i = p ^ t
        · subst hiP
          simp [hP.ne']
          rw [if_neg (by simp [hp.ne_zero])]
          exact dvd_zero _
        · by_cases hlt : i < p ^ t
          · have hdv := hp.dvd_choose_pow hi.ne' hiP
            simp only [if_neg hi.ne', if_neg hiP, sub_zero]
            exact_mod_cast hdv
          · rw [Nat.choose_eq_zero_of_lt (by omega)]
            simp [hi.ne', hiP]
    obtain ⟨h, hh⟩ := hd
    exact ⟨h, by rw [← hh]; ring⟩
  unfold binomialExpansionCoeff
  rw [hh]
  exact coeff_binomial_power_divisibility p (p ^ t) hP h l _ M

theorem binomial_expansion_coeff_zero_of_gt (P rho M l : ℕ) (h : M < l) : binomialExpansionCoeff P rho M l = 0 := by
  unfold binomialExpansionCoeff
  obtain ⟨q, hq⟩ : X ∣ ((1 + X) ^ P - 1 : ℤ[X]) := by
    rw [X_dvd_iff]
    simp [coeff_one_add_X_pow]
  rw [hq, mul_pow, show (1 + X : ℤ[X]) ^ rho * (X ^ l * q ^ l) = X ^ l * ((1 + X) ^ rho * q ^ l) by ring,
    coeff_X_pow_mul', if_neg (by omega)]

theorem binomial_expansion_coeff_zero_of_deg (P rho M l : ℕ) (h : rho + P * l < M) : binomialExpansionCoeff P rho M l = 0 := by
  unfold binomialExpansionCoeff
  apply coeff_eq_zero_of_natDegree_lt
  refine lt_of_le_of_lt ?_ h
  have h1 : ((1 + X : ℤ[X])).natDegree ≤ 1 := (natDegree_add_le _ _).trans (max_le (by simp) natDegree_X_le)
  have h2 : ((1 + X : ℤ[X]) ^ P - 1).natDegree ≤ P := by
    refine (natDegree_sub_le _ _).trans (max_le ?_ (by simp))
    exact natDegree_pow_le.trans ((Nat.mul_le_mul_left P h1).trans (by simp))
  refine natDegree_mul_le.trans (add_le_add ?_ ?_)
  · exact natDegree_pow_le.trans ((Nat.mul_le_mul_left rho h1).trans (by simp))
  · exact natDegree_pow_le.trans ((Nat.mul_le_mul_left l h2).trans (le_of_eq (mul_comm _ _)))

theorem choose_shift_binomial_expansion (P rho M e : ℕ) :
    (((rho + P * e).choose M : ℕ) : ℤ) = ∑ l ∈ range (M + 1), binomialExpansionCoeff P rho M l * ((e.choose l : ℕ) : ℤ) := by

  have hpoly : ((1 + X : ℤ[X])) ^ (rho + P * e) =
      ∑ l ∈ range (e + 1), C ((e.choose l : ℕ) : ℤ) * ((1 + X) ^ rho * ((1 + X) ^ P - 1) ^ l) := by
    rw [pow_add, pow_mul, show ((1 + X : ℤ[X]) ^ P) = ((1 + X) ^ P - 1) + 1 by ring,
      add_pow ((1 + X : ℤ[X]) ^ P - 1) 1 e, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [one_pow, mul_one, C_eq_natCast, add_sub_cancel_right]
    ring
  have hc := congrArg (fun q : ℤ[X] => q.coeff M) hpoly
  simp only [coeff_one_add_X_pow, finsetSum_coeff, coeff_C_mul] at hc
  rw [hc]
  calc ∑ l ∈ range (e + 1), ((e.choose l : ℕ) : ℤ) * ((1 + X : ℤ[X]) ^ rho * ((1 + X) ^ P - 1) ^ l).coeff M
      = ∑ l ∈ range (e + 1), binomialExpansionCoeff P rho M l * ((e.choose l : ℕ) : ℤ) :=
        Finset.sum_congr rfl (fun l _ => by rw [mul_comm]; rfl)
    _ = ∑ l ∈ range (e + M + 1), binomialExpansionCoeff P rho M l * ((e.choose l : ℕ) : ℤ) := by
        refine Finset.sum_subset (Finset.range_mono (by omega)) (fun l hl hn => ?_)
        simp only [Finset.mem_range] at hl hn
        rw [Nat.choose_eq_zero_of_lt (by omega)]
        simp
    _ = ∑ l ∈ range (M + 1), binomialExpansionCoeff P rho M l * ((e.choose l : ℕ) : ℤ) := by
        refine (Finset.sum_subset (Finset.range_mono (by omega)) (fun l hl hn => ?_)).symm
        simp only [Finset.mem_range] at hl hn
        rw [binomial_expansion_coeff_zero_of_gt P rho M l (by omega)]
        simp

theorem derivative_digit_expansion (D : Formalism.BasicNotions.D7) : DerivativeDigitExpansion D := by
  intro p hp _ t σ _ rho M _ c
  classical
  have hP : 0 < p ^ t := pow_pos hp.pos t
  let a : σ → ℕ → ℤ := fun k l => binomialExpansionCoeff (p ^ t) (rho k) (M k) l

  let good : (σ → ℕ) → Prop := fun l => (∀ k, M k ≤ rho k + p ^ t * l k) ∧ ∑ k, (l k - M k / p ^ t) < c
  let B : Finset (σ → ℕ) := Fintype.piFinset (fun k => range (M k + 1))
  refine ⟨B.filter good, fun l => ∏ k, a k (l k), ?_, ?_, ?_⟩
  · intro l hl
    have hl' := (Finset.mem_filter.1 hl).2.2
    have h1 : ∑ k, l k ≤ ∑ k, (l k - M k / p ^ t) + ∑ k, M k / p ^ t := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum (fun k _ => le_tsub_add)
    have h2 : (∑ k, M k / p ^ t) ≤ (∑ k, M k) / p ^ t := by
      rw [Nat.le_div_iff_mul_le hP, Finset.sum_mul]
      exact Finset.sum_le_sum (fun k _ => Nat.div_mul_le_self _ _)
    have h3 : ((((∑ k, M k) / p ^ t : ℕ)) : ℝ) ≤ ((∑ k, M k : ℕ) : ℝ) / ((p ^ t : ℕ) : ℝ) := Nat.cast_div_le
    have h4 : ∑ k, l k ≤ c + (∑ k, M k) / p ^ t := by omega
    have h5 : ((∑ k, l k : ℕ) : ℝ) ≤ (c : ℝ) + ((((∑ k, M k) / p ^ t : ℕ)) : ℝ) := by exact_mod_cast h4
    linarith
  · intro l hl k
    exact (Finset.mem_filter.1 hl).2.1 k
  · intro e'
    have hexp : ∏ k, (((rho k + p ^ t * e' k).choose (M k) : ℕ) : ℤ) =
        ∑ l ∈ B, ∏ k, (a k (l k) * (((e' k).choose (l k) : ℕ) : ℤ)) := by
      calc ∏ k, (((rho k + p ^ t * e' k).choose (M k) : ℕ) : ℤ)
          = ∏ k, ∑ j ∈ range (M k + 1), a k j * (((e' k).choose j : ℕ) : ℤ) :=
            Finset.prod_congr rfl (fun k _ => choose_shift_binomial_expansion (p ^ t) (rho k) (M k) (e' k))
        _ = _ := Finset.prod_univ_sum _ _
    have hT : ∑ l ∈ B.filter good, (∏ k, a k (l k)) * ∏ k, (((e' k).choose (l k) : ℕ) : ℤ) =
        ∑ l ∈ B.filter good, ∏ k, (a k (l k) * (((e' k).choose (l k) : ℕ) : ℤ)) :=
      Finset.sum_congr rfl (fun l _ => Finset.prod_mul_distrib.symm)
    have hsplit := Finset.sum_filter_add_sum_filter_not B good
      (fun l => ∏ k, (a k (l k) * (((e' k).choose (l k) : ℕ) : ℤ)))
    show (p : ℤ) ^ c ∣ ∏ k, (((rho k + p ^ t * e' k).choose (M k) : ℕ) : ℤ) -
      ∑ l ∈ B.filter good, (∏ k, a k (l k)) * ∏ k, (((e' k).choose (l k) : ℕ) : ℤ)
    rw [hexp, hT, ← hsplit, add_sub_cancel_left]
    apply Finset.dvd_sum
    intro l hl
    have hng := (Finset.mem_filter.1 hl).2
    rw [Finset.prod_mul_distrib]
    apply Dvd.dvd.mul_right
    by_cases hdeg : ∀ k, M k ≤ rho k + p ^ t * l k
    · have hc : c ≤ ∑ k, (l k - M k / p ^ t) := by
        by_contra hh
        exact hng ⟨hdeg, by omega⟩
      refine dvd_trans (pow_dvd_pow _ hc) ?_
      rw [← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_dvd_prod_of_dvd _ _ (fun k _ => binomial_expansion_coeff_padic_dvd p t hp (rho k) (M k) (l k))
    · push_neg at hdeg
      obtain ⟨k, hk⟩ := hdeg
      rw [Finset.prod_eq_zero (Finset.mem_univ k) (binomial_expansion_coeff_zero_of_deg (p ^ t) (rho k) (M k) (l k) hk)]
      exact dvd_zero _

theorem unit_product_eq_choose (P n rho : ℕ) : dUnit P n rho = (((rho + P * n).choose rho : ℕ) : ℚ) := by
  induction rho with
  | zero => simp [dUnit]
  | succ r ih =>
    show (∏ y ∈ Finset.Icc 1 (r + 1), (1 + (P : ℚ) * n / y)) = _
    rw [Finset.prod_Icc_succ_top (by omega)]
    have ih' : (∏ y ∈ Finset.Icc 1 r, (1 + (P : ℚ) * n / y)) = (((r + P * n).choose r : ℕ) : ℚ) := ih
    rw [ih', show r + 1 + P * n = r + P * n + 1 by ring]

    have hc : (((r + P * n + 1 : ℕ) : ℚ)) * (((r + P * n).choose r : ℕ) : ℚ) =
        (((r + P * n + 1).choose (r + 1) : ℕ) : ℚ) * ((r : ℚ) + 1) := by
      exact_mod_cast Nat.add_one_mul_choose_eq (r + P * n) r
    have hr : ((r : ℚ) + 1) ≠ 0 := by positivity
    push_cast at hc ⊢
    field_simp
    linear_combination hc

theorem hdU_proved {p : ℕ} (hp : p.Prime) : HdU p := by
  intro t rho hrho
  refine ⟨fun l => binomialExpansionCoeff (p ^ (t + 1)) rho rho l, fun n => ?_, fun l => ?_⟩
  · rw [unit_product_eq_choose]
    exact_mod_cast choose_shift_binomial_expansion (p ^ (t + 1)) rho rho n
  · have h := binomial_expansion_coeff_padic_dvd p (t + 1) hp rho rho l
    rw [Nat.div_eq_of_lt hrho, Nat.sub_zero] at h
    exact h

end Formalism.MainNotions.G.GLWeightTheory
end
end

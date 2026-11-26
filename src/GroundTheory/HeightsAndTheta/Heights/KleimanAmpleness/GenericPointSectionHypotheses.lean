module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AlgebraMapMemChartRingLine
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationPoint

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u v w

def FiniteSections.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (Q : LineBundle S x), x ≠ 0 →
    Module.Finite S Q.secs ∧
    (∀ c₁ : ℤ, ∃ (n : ℕ) (deg : Fin n → ℤ) (gen : Fin n → Ω),
      (∀ j, c₁ ≤ deg j ∧ gen j ∈ (Q.twist (twistSys S x (deg j))).secs) ∧
      ∀ c : ℤ, c₁ ≤ c → (Q.twist (twistSys S x c)).secs ≤ Submodule.span S {z | ∃ (j : Fin n)
        (f : Poly S N) (e : ℕ), f.IsHomogeneous e ∧ (e : ℤ) + deg j = c ∧ z = aeval x f * gen j}) ∧
    ∀ (F : Type u) [Field F] [Algebra S F] [Algebra F Ω] [IsScalarTower S F Ω] [IsFractionRing S F],
      Submodule.span F (Q.secs : Set Ω) = (Q.toSubSystem.extend F).secs

def SurjectiveClosed.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (Q : LineBundle S x) (J' : Ideal (Poly S N)),
    (∀ p ∈ J', ∀ d : ℕ, homogeneousComponent d p ∈ J') →
    ∃ c₀ : ℤ, ∀ c : ℤ, c₀ ≤ c → ∀ s : Chart x → Ω,
      (∀ I, s I ∈ (Q.twist (twistSys S x c)).sub I) →
      (∀ (I₁ I₂ : Chart x), I₁.1 ⊆ I₂.1 →
        s I₁ - s I₂ ∈ ((Q.twist (twistSys S x c)).twist (idealSys x J')).sub I₂) →
      ∃ t ∈ (Q.twist (twistSys S x c)).secs,
        ∀ I, t - s I ∈ ((Q.twist (twistSys S x c)).twist (idealSys x J')).sub I

namespace SubSystem

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

instance quotH.instAddCommGroup (F₁ F₂ : SubSystem S x E) (i : ℕ) : AddCommGroup (quotH F₁ F₂ i) := by
  unfold quotH; infer_instance

instance quotH.instModule (F₁ F₂ : SubSystem S x E) (i : ℕ) : Module S (quotH F₁ F₂ i) := by
  unfold quotH; infer_instance

end SubSystem

def PrimeFiltration.RestrictQuot.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (pp : Ideal (Poly S N)), pp.IsPrime →
    (∀ p ∈ pp, ∀ d : ℕ, homogeneousComponent d p ∈ pp) → primeOf (S := S) x ≤ pp →
    ∀ (j : Fin (N + 1)) (hj : x j ≠ 0), (X j : Poly S N) ∉ pp →
    ∀ (K' : Type w) [Field K'] [Algebra S K'] (ψ : chartRing S x (singleChart hj) →ₐ[S] K'),
      RingHom.ker ψ = chartPrime pp hj →
      ∀ (hxy : ∀ i, ψ (ratio hj i) ≠ 0 → x i ≠ 0) (Q : LineBundle S x)
        (Q' : LineBundle S (fun i => ψ (ratio hj i))) (r : Ω → K'),
        RestrictData Q.toSubSystem hxy Q'.toSubSystem r →
        ∀ (c : ℤ) (i : ℕ), Nonempty (SubSystem.quotH (Q.twist (twistSys S x c))
          ((Q.twist (twistSys S x c)).twist (idealSys x pp)) i ≃ₗ[S]
            (Q'.twist (twistSys S (fun l => ψ (ratio hj l)) c)).H i)

def DimTie.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (y : Fin (N + 1) → Ω),
    y ≠ 0 → ∀ e : ℕ, IsSubvar y (primeOf (S := k) y) e ↔ dimCl k y = e

def Restriction.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (Nb : LineBundle k x) (r : ℕ) (h : Fin (r + 1) → Ω), IsVeryAmpleBy Nb.toSubSystem h →
    ∀ (pp : Ideal (Poly k N)), pp.IsPrime → (∀ p ∈ pp, ∀ d : ℕ, homogeneousComponent d p ∈ pp) →
    primeOf (S := k) x ≤ pp → ∀ (j : Fin (N + 1)) (hj : x j ≠ 0), (X j : Poly k N) ∉ pp →
    ∀ (K' : Type w) [Field K'] [Algebra k K'] (ψ : chartRing k x (singleChart hj) →ₐ[k] K'),
      RingHom.ker ψ = chartPrime pp hj → ∀ hxy : ∀ i, ψ (ratio hj i) ≠ 0 → x i ≠ 0,
      ∃ (Q' : LineBundle k (fun i => ψ (ratio hj i))) (ρ : Ω → K'),
        RestrictData Nb.toSubSystem hxy Q'.toSubSystem ρ ∧ IsVeryAmpleBy Q'.toSubSystem (ρ ∘ h) ∧
        dimCl k (fun i => ψ (ratio hj i)) = dimCl k (ρ ∘ h)

def HilbertPoint.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (y : Fin (N + 1) → Ω),
    IsSubvar y (primeOf (S := k) y) 0 →
    FiniteDimensional k (funField (k := k) y) ∧
    (∀ᶠ n : ℕ in atTop,
      Module.finrank k ((coordGraded k y).piece (n : ℤ)) = Module.finrank k (funField (k := k) y)) ∧
    ∀ᶠ n : ℕ in atTop, (twistSys k y (n : ℤ)).secs = (coordGraded k y).piece (n : ℤ)

def HilbertPositive.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (y : Fin (N + 1) → Ω) (e : ℕ),
    1 ≤ e → IsSubvar y (primeOf (S := k) y) e →
    (∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      |(Module.finrank k ((coordGraded k y).piece (n : ℤ)) : ℝ) -
        (NumbersDVR.intNum k (primeOfOne (S := k) y) (fun _ : Fin e => fun _ : Unit => (1 : ℤ)) : ℝ) *
          (n : ℝ) ^ e / (e.factorial : ℝ)| ≤ C * (n : ℝ) ^ (e - 1)) ∧
    0 < NumbersDVR.intNum k (primeOfOne (S := k) y) (fun _ : Fin e => fun _ : Unit => (1 : ℤ)) ∧
    ∀ᶠ n : ℕ in atTop, (twistSys k y (n : ℤ)).secs = (coordGraded k y).piece (n : ℤ)

def SectionCount.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω) (d : ℕ)
    (Nb : LineBundle k x) (b : ℕ), IsSubvar x (primeOf (S := k) x) (d + 1) →
    IsVeryAmple Nb.toSubSystem → 1 ≤ b →
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      ((interNum (primeOf (S := k) x) (fun _ : Fin (d + 1) => Nb.toSubSystem) -
          ((d + 1 : ℕ) : ℤ) * interNum (primeOf (S := k) x)
            (Fin.cons (α := fun _ => SubSystem k x Ω) (twistSys k x (b : ℤ))
              (fun _ : Fin d => Nb.toSubSystem)) : ℤ) : ℝ) *
          (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) - C * (n : ℝ) ^ d ≤
        (Module.finrank k (twistMul Nb.toSubSystem n (-((n : ℤ) * b))).secs : ℝ)

def SectionExists.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω) (d : ℕ)
    (M : LineBundle k x) (t s' : ℚ), IsSubvar x (primeOf (S := k) x) (d + 1) → Nef M.toSubSystem →
    0 < s' → s' < t / (d + 1) →
    (∃ (q : ℕ) (m : ℤ), 1 ≤ q ∧ (m : ℚ) = q * t ∧ IsVeryAmple (twistMul M.toSubSystem q m)) →
    ∃ (p : ℕ) (m c₁ : ℤ), 1 ≤ p ∧ (m : ℚ) = p * (t - s') ∧ 1 ≤ c₁ ∧
      ∃ σ ∈ (twistMul M.toSubSystem p (m - c₁)).secs, σ ≠ 0

def VeryAmpleNefPlusAmple.InDim (k : Type u) [Field k] (d : ℕ) : Prop :=
  ∀ (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω) (M : LineBundle k x),
    IsSubvar x (primeOf (S := k) x) d → Nef M.toSubSystem → ∀ t : ℚ, 0 < t →
    ∃ (p : ℕ) (m : ℤ), 1 ≤ p ∧ (m : ℚ) = p * t ∧ IsVeryAmple (twistMul M.toSubSystem p m)

def VeryAmpleNefPlusAmple.Statement : Prop :=
  ∀ (k : Type u) [Field k] (d : ℕ), VeryAmpleNefPlusAmple.InDim.{u, w} k d

def StepTwo.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (T : StepData k x), (∀ e ≤ T.d, VeryAmpleNefPlusAmple.InDim.{u, w} k e) →
    ∀ (E : Type v) [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
      (M₁ M₂ : FinGradedSub (S := k) (x := x) E), (∀ c, M₂.piece c ≤ M₁.piece c) →
      (∀ (f : Poly k N) (e : ℕ), f ∈ T.J → f.IsHomogeneous e → ∀ (a : ℤ), ∀ z ∈ M₁.piece a,
        aeval x f • z ∈ M₂.piece (a + e)) →
      ∃ c₀ : ℤ, ∀ (b : ℕ) (c : ℤ), c₀ ≤ c →
        Subsingleton (SubSystem.quotH ((M₁.tildeSys 0).twist ((T.L.pow b).twist (twistSys k x c)))
          ((M₂.tildeSys 0).twist ((T.L.pow b).twist (twistSys k x c))) 1)

def ClaimVanish.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (T : StepData k x), (∀ e ≤ T.d, VeryAmpleNefPlusAmple.InDim.{u, w} k e) →
    ∃ c₀ : ℤ, ∀ (b : ℕ) (c : ℤ), c₀ ≤ c → Subsingleton (((T.L.pow b).twist (twistSys k x c)).H 1)

def StepThree.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (T : StepData k x), (∀ e ≤ T.d, VeryAmpleNefPlusAmple.InDim.{u, w} k e) →
    ∃ c₂ : ℤ, ∀ b : ℕ, 1 ≤ b → ((T.L.pow b).twist (twistSys k x c₂)).Generated

def NefProductNonneg.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (e : ℕ) (pp : Ideal (Poly k N)) (Ms : Fin e → LineBundle k x), IsSubvar x pp e →
    (∀ i, Nef (Ms i).toSubSystem) → 0 ≤ interNum pp (fun i => (Ms i).toSubSystem)


open Classical in
def GenericPointSectionInput.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω),
    (∀ (n : ℕ) (pp : Ideal (Poly k N)) (L : Fin n → LineBundle k x), IsSubvar x pp n →
      ∀ᶠ c : ℕ in atTop, interSum pp (fun i => (L i).toSubSystem) c =
        interNum pp (fun i => (L i).toSubSystem)) ∧
    (∀ (n : ℕ) (pp : Ideal (Poly k N)) (L : Fin n → LineBundle k x) (σ : Equiv.Perm (Fin n)),
      IsSubvar x pp n →
      interNum pp (fun i => (L (σ i)).toSubSystem) = interNum pp (fun i => (L i).toSubSystem)) ∧
    (∀ (n : ℕ) (pp : Ideal (Poly k N)) (L : Fin n → LineBundle k x) (i : Fin n)
      (L' L'' : LineBundle k x), IsSubvar x pp n →
      interNum pp (Function.update (fun j => (L j).toSubSystem) i (L'.twist L''.toSubSystem)) =
        interNum pp (Function.update (fun j => (L j).toSubSystem) i L'.toSubSystem) +
          interNum pp (Function.update (fun j => (L j).toSubSystem) i L''.toSubSystem)) ∧
    (∀ (n : ℕ) (pp : Ideal (Poly k N)) (L : Fin n → LineBundle k x) (Lc : LineBundle k x) (s : Ω),
      IsSubvar x pp (n + 1) → s ∈ Lc.secs → (∃ I, s ∉ (Lc.twist (idealSys x pp)).sub I) →
      interNum pp (Fin.snoc (α := fun _ => SubSystem k x Ω) (fun i => (L i).toSubSystem)
          Lc.toSubSystem) =
        ∑ᶠ qq : Ideal (Poly k N),
          if h : qq ∈ (pp ⊔ zeroIdeal Lc.toSubSystem s).minimalPrimes ∧ IsSubvar x qq n then
            haveI : qq.IsPrime := h.1.1.1
            ((cutMult (pp ⊔ zeroIdeal Lc.toSubSystem s) qq).toNat : ℤ) *
              interNum qq (fun i => (L i).toSubSystem)
          else 0) ∧
    (∀ pp : Ideal (Poly k N), IsSubvar x pp 0 →
      interNum pp (![] : Fin 0 → SubSystem k x Ω) =
        (FieldNumbers.resDeg (pp.comap (oneBlock (S := k) (N := N)).toRingHom) : ℤ))

def InterNumTie.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (n : ℕ) (pp : Ideal (Poly k N)) (b : Fin n → ℤ), IsSubvar x pp n →
    interNum pp (fun i => twistSys k x (b i)) =
      NumbersDVR.intNum k (pp.comap (oneBlock (S := k) (N := N)).toRingHom) (fun i _ => b i)

section Hypotheses

variable (k : Type u) [Field k]

end Hypotheses

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistAlg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

namespace SubSystem

theorem twist_sub_eq_mul_of_line (F Q : SubSystem S x Ω) (I : Chart x) :
    (F.twist Q).sub I = Q.sub I * F.sub I := by
  rw [Submodule.mul_eq_span_mul_set]
  change Submodule.span _ _ = _
  congr 1
  ext z
  constructor
  · rintro ⟨q, hq, y, hy, rfl⟩
    exact Set.mul_mem_mul hq hy
  · rintro ⟨q, hq, y, hy, rfl⟩
    exact ⟨q, hq, y, hy, rfl⟩

theorem twist_comm (F Q : SubSystem S x Ω) : F.twist Q = Q.twist F :=
  ext_sub fun I => by rw [twist_sub_eq_mul_of_line, twist_sub_eq_mul_of_line, mul_comm]

theorem twist_assoc (F P Q : SubSystem S x Ω) : (F.twist P).twist Q = F.twist (P.twist Q) :=
  ext_sub fun I => by simp only [twist_sub_eq_mul_of_line, mul_assoc]

theorem pow_sub (Q : SubSystem S x Ω) (n : ℕ) (I : Chart x) : (Q.pow n).sub I = Q.sub I ^ n := by
  induction n with
  | zero =>
    obtain ⟨i, hi⟩ := I.2.1
    change twistMod S x 0 I = _
    rw [twistMod_eq_span 0 I hi, zpow_zero, pow_zero, Submodule.one_eq_span]
  | succ n ih =>
    change ((Q.pow n).twist Q).sub I = _
    rw [twist_sub_eq_mul_of_line, ih, pow_succ']

end SubSystem

theorem twistSys_twist_eq_add (a b : ℤ) :
    (twistSys S x a).twist (twistSys S x b) = twistSys S x (a + b) := by
  refine SubSystem.ext_sub fun I => ?_
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  rw [SubSystem.twist_sub_eq_mul_of_line]
  change twistMod S x b I * twistMod S x a I = twistMod S x (a + b) I
  rw [twistMod_eq_span b I hi, twistMod_eq_span a I hi, twistMod_eq_span (a + b) I hi,
    Submodule.span_mul_span, Set.singleton_mul_singleton, ← zpow_add₀ hxi, add_comm b a]

theorem pow_twistSys (c : ℤ) (n : ℕ) : (twistSys S x c).pow n = twistSys S x (n * c) := by
  induction n with
  | zero =>
    show twistSys S x 0 = twistSys S x (((0 : ℕ) : ℤ) * c)
    rw [Nat.cast_zero, zero_mul]
  | succ n ih =>
    change ((twistSys S x c).pow n).twist (twistSys S x c) = _
    rw [ih, twistSys_twist_eq_add]
    congr 1
    push_cast
    ring

theorem twistMul_sub (M : SubSystem S x Ω) (p : ℕ) (m : ℤ) (I : Chart x) :
    (twistMul M p m).sub I = (twistSys S x m).sub I * M.sub I ^ p := by
  rw [twistMul, SubSystem.twist_sub_eq_mul_of_line, SubSystem.pow_sub]

theorem twistSys_sub_mul (a b : ℤ) (I : Chart x) :
    (twistSys S x a).sub I * (twistSys S x b).sub I = (twistSys S x (a + b)).sub I := by
  rw [← twistSys_twist_eq_add, SubSystem.twist_sub_eq_mul_of_line, mul_comm]

theorem twistSys_sub_pow (c : ℤ) (n : ℕ) (I : Chart x) :
    (twistSys S x c).sub I ^ n = (twistSys S x (n * c)).sub I := by
  rw [← SubSystem.pow_sub, pow_twistSys]

theorem twistMul_twistMul (M : SubSystem S x Ω) (q n : ℕ) (m a : ℤ) :
    twistMul (twistMul M q m) n a = twistMul M (n * q) (n * m + a) := by
  refine SubSystem.ext_sub fun I => ?_
  rw [twistMul_sub, twistMul_sub, twistMul_sub, mul_pow, twistSys_sub_pow, ← pow_mul,
    ← mul_assoc, twistSys_sub_mul, mul_comm q n, add_comm a]

theorem pow_twistMul (M : SubSystem S x Ω) (q j : ℕ) (m : ℤ) :
    (twistMul M q m).pow j = twistMul M (j * q) (j * m) := by
  have h := twistMul_twistMul M q j m 0
  rw [add_zero] at h
  rw [← h]
  exact (SubSystem.twist_twistSys_zero _).symm

namespace LineBundle

def tensorProd (P Q : LineBundle S x) : LineBundle S x where
  toSubSystem := P.toSubSystem.twist Q.toSubSystem
  mem_iff I J h y := by
    constructor
    · intro hy
      have hy' : y ∈ Submodule.span (chartRing S x J)
          {z | ∃ q ∈ Q.sub J, ∃ p ∈ P.sub J, z = q • p} := hy
      refine Submodule.span_induction (p := fun z _ => ∃ a : chartRing S x I,
        IsUnit (chartIncl h a) ∧ (a : Ω) • z ∈ (P.toSubSystem.twist Q.toSubSystem).sub I)
        ?_ ?_ ?_ ?_ hy'
      · rintro _ ⟨q, hq, p, hp, rfl⟩
        obtain ⟨a, ha, haq⟩ := (Q.mem_iff I J h q).mp hq
        obtain ⟨b, hb, hbp⟩ := (P.mem_iff I J h p).mp hp
        refine ⟨a * b, by rw [map_mul]; exact ha.mul hb, ?_⟩
        have : ((a * b : chartRing S x I) : Ω) • (q • p) = ((a : Ω) • q) • ((b : Ω) • p) := by
          simp only [smul_eq_mul, MulMemClass.coe_mul]; ring
        rw [this]
        exact Submodule.subset_span ⟨_, haq, _, hbp, rfl⟩
      · exact ⟨1, by simp, by simp⟩
      · rintro y₁ y₂ - - ⟨a₁, ha₁, h₁⟩ ⟨a₂, ha₂, h₂⟩
        refine ⟨a₁ * a₂, by rw [map_mul]; exact ha₁.mul ha₂, ?_⟩
        have : ((a₁ * a₂ : chartRing S x I) : Ω) • (y₁ + y₂) =
            a₂ • ((a₁ : Ω) • y₁) + a₁ • ((a₂ : Ω) • y₂) := by
          simp only [smul_eq_mul, chartRing_smul_def, MulMemClass.coe_mul]; ring
        rw [this]
        exact Submodule.add_mem _ (Submodule.smul_mem _ _ h₁) (Submodule.smul_mem _ _ h₂)
      · rintro c z - ⟨a, ha, hz⟩
        obtain ⟨a', ha', hc⟩ := exists_isUnit_mul_mem h c
        refine ⟨a' * a, by rw [map_mul]; exact ha'.mul ha, ?_⟩
        have : ((a' * a : chartRing S x I) : Ω) • (c • z) =
            (⟨_, hc⟩ : chartRing S x I) • ((a : Ω) • z) := by
          simp only [smul_eq_mul, chartRing_smul_def, MulMemClass.coe_mul]; ring
        rw [this]
        exact Submodule.smul_mem _ _ hz
    · rintro ⟨a, ⟨u, hu⟩, hay⟩
      have hJ := (P.toSubSystem.twist Q.toSubSystem).mono I J h _ hay
      have hinv : ((↑u⁻¹ : chartRing S x J) : Ω) * (a : Ω) = 1 := by
        have := congrArg Subtype.val (Units.inv_mul u)
        rw [hu] at this
        exact this
      have hy : y = (↑u⁻¹ : chartRing S x J) • ((a : Ω) • y) := by
        rw [chartRing_smul_def, smul_eq_mul, ← mul_assoc, hinv, one_mul]
      rw [hy]
      exact Submodule.smul_mem _ _ hJ
  fg I := by
    rw [SubSystem.twist_sub_eq_mul_of_line]
    exact (Q.fg I).mul (P.fg I)
  invertible I := by
    obtain ⟨P', hP⟩ := P.invertible I
    obtain ⟨Q', hQ⟩ := Q.invertible I
    refine ⟨P' * Q', ?_⟩
    rw [SubSystem.twist_sub_eq_mul_of_line,
      show Q.sub I * P.sub I * (P' * Q') = (P.sub I * P') * (Q.sub I * Q') by ring, hP, hQ, one_mul]

def powBundle (Q : LineBundle S x) : ℕ → LineBundle S x
  | 0 => twistBundle S x 0
  | n + 1 => (Q.powBundle n).tensorProd Q

theorem powBundle_toSubSystem (Q : LineBundle S x) (n : ℕ) :
    (Q.powBundle n).toSubSystem = Q.toSubSystem.pow n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (Q.powBundle n).toSubSystem.twist Q.toSubSystem = (Q.toSubSystem.pow n).twist Q.toSubSystem
    rw [ih]

end LineBundle

theorem exists_lineBundle_twistMul (M : LineBundle S x) (p : ℕ) (m : ℤ) :
    ∃ L : LineBundle S x, L.toSubSystem = twistMul M.toSubSystem p m :=
  ⟨(M.powBundle p).tensorProd (twistBundle S x m), by
    change (M.powBundle p).toSubSystem.twist (twistSys S x m) = _
    rw [LineBundle.powBundle_toSubSystem]
    rfl⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsSnapper
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

section Defs

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

def SubSystem.twistPows (F : SubSystem S x E) : (t : ℕ) → (Fin t → SubSystem S x Ω) → (Fin t → ℕ) → SubSystem S x E
  | 0, _, _ => F
  | t + 1, L, n => (F.twistPows t (fun j => L j.castSucc) (fun j => n j.castSucc)).twist ((L (Fin.last t)).pow (n (Fin.last t)))

variable (k : Type u) [Field k] [Algebra k Ω] [Module k E] [IsScalarTower k Ω E]

def eulerChar (F : SubSystem k x E) : ℤ :=
  ∑ i ∈ Finset.range (N + 1), (-1 : ℤ) ^ i * (Module.finrank k (F.H i) : ℤ)

end Defs

def SnapperFinite.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
    (F : SubFamily k x E), (∀ I, (F.sub I).FG) → ∀ (t : ℕ) (L : Fin t → LineBundle k x)
    (n : Fin t → ℕ) (c : ℤ) (i : ℕ),
    FiniteDimensional k (((F.toSubSystem.twistPows t (fun j => (L j).toSubSystem) n).twist
      (twistSys k x c)).H i)

def Snapper.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω) (e : ℕ),
    IsSubvar x (primeOf (S := k) x) e →
    ∀ (E : Type v) [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
      (F : SubFamily k x E), (∀ I, (F.sub I).FG) → ∀ (t : ℕ) (L : Fin t → LineBundle k x),
    ∃ Q : MvPolynomial (Fin (t + 1)) ℚ, Q.totalDegree ≤ e ∧
      ∀ (n : Fin t → ℕ) (c : ℤ),
        ((eulerChar k ((F.toSubSystem.twistPows t (fun j => (L j).toSubSystem) n).twist
          (twistSys k x c)) : ℤ) : ℚ) =
          MvPolynomial.eval (Fin.snoc (α := fun _ => ℚ) (fun j => (n j : ℚ)) (c : ℚ)) Q

def TwistVanishAll.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (G B : LineBundle S x) (r : ℕ) (η : Fin (r + 1) → Ω),
    (∀ j, η j ∈ B.secs) → (∀ I, Submodule.span (chartRing S x I) (Set.range η) = B.sub I) →
    ∃ c₀ : ℤ, ∀ (i b : ℕ) (c : ℤ), 1 ≤ i → c₀ ≤ c →
      Subsingleton (((G.twist (B.pow b)).twist (twistSys S x c)).H i)

def AmpleVanish.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (F : SubFamily S x E), (∀ I, (F.sub I).FG) → ∀ H : LineBundle S x, IsVeryAmple H.toSubSystem →
    ∃ a₀ : ℕ, ∀ (i a : ℕ), 1 ≤ i → a₀ ≤ a → Subsingleton ((F.twist (H.pow a)).H i)

section Hypotheses

variable (k : Type u) [Field k]

end Hypotheses

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsCycleSplitFilt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w


open Classical in
def CycleSplit.Filt.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (𝔪 : Ideal S), 𝔪.IsMaximal →
    ∀ J : Ideal (Poly S N), (∀ p ∈ J, ∀ d : ℕ, homogeneousComponent d p ∈ J) →
    primeOf (S := S) x ≤ J → 𝔪.map (C : S →+* Poly S N) ≤ J →
    ∃ (n : ℕ) (pp : Fin n → Ideal (Poly S N)) (d : Fin n → ℤ),
      (∀ j, (pp j).IsPrime ∧ (∀ p ∈ pp j, ∀ e : ℕ, homogeneousComponent e p ∈ pp j) ∧ J ≤ pp j) ∧
      (∀ (G : Ideal (Poly S N)) [G.IsPrime], G ∈ J.minimalPrimes →
        (((Finset.univ.filter fun j => pp j = G).card : ℕ) : ℕ∞) = cutMult J G) ∧
      ∀ Q : LineBundle S x, ∀ᶠ c : ℕ in atTop,
        restrLen J (Q.twist (twistSys S x (c : ℤ))) =
          ∑ j, restrLen (pp j) (Q.twist (twistSys S x ((c : ℤ) + d j)))

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleDimSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u w

def VeryAmpleDim.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω) (e : ℕ)
    (Nb : LineBundle k x) (r : ℕ) (h : Fin (r + 1) → Ω), IsSubvar x (primeOf (S := k) x) e →
    IsVeryAmpleBy Nb.toSubSystem h → IsSubvar h (primeOf (S := k) h) e

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsIdealTwist
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def IdealTwistFamily.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (Q : LineBundle S x) (J' : Ideal (Poly S N)),
    (∀ p ∈ J', ∀ d : ℕ, homogeneousComponent d p ∈ J') →
    ∃ F : SubFamily S x Ω, F.toSubSystem = Q.twist (idealSys (x := x) J') ∧ ∀ I, (F.sub I).FG

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsTildeVanish
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def TildeVanish.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E]
    [IsScalarTower S Ω E] (M : FinGradedSub (S := S) (x := x) E),
    ∃ c₀ : ℤ, ∀ i : ℕ, 1 ≤ i → ∀ c : ℤ, c₀ ≤ c → Subsingleton ((M.tildeSys c).H i)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsTwistSplit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def TwistSplit.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (M₀ : FinGradedSub (S := S) (x := x) Ω) (G B : SubSystem S x Ω) (r : ℕ)
    (η : Fin (r + 1) → Ω), (∀ I, M₀.tilde 0 I = G.sub I) →
    (∀ j, η j ∈ B.secs) → (∀ I, Submodule.span (chartRing S x I) (Set.range η) = B.sub I) →
    ∃ (M : Type w) (_ : AddCommGroup M) (_ : Module (Poly (MvPolynomial (Fin (r + 1)) S) N) M)
      (_ : Module (MvPolynomial (Fin (r + 1)) S) M)
      (_ : IsScalarTower (MvPolynomial (Fin (r + 1)) S) (Poly (MvPolynomial (Fin (r + 1)) S) N) M)
      (𝓜 : GradedPMod (MvPolynomial (Fin (r + 1)) S) N M),
      Module.Finite (Poly (MvPolynomial (Fin (r + 1)) S) N) M ∧
      ∀ (b : ℕ) (c : ℤ) (i : ℕ),
        ∃ (ι : ((G.twist (B.pow b)).twist (twistSys S x c)).H i →+ cohom 𝓜 i c)
          (π : cohom 𝓜 i c →+ ((G.twist (B.pow b)).twist (twistSys S x c)).H i), ∀ z, π (ι z) = z

section Hypotheses

variable (k : Type u) [Field k] (N : ℕ)

end Hypotheses

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechTransport
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

namespace Cech

theorem Transport.proof : Transport.Statement.{u, v, w} := by
  intro n U R _ G _ _ G' _ _ ρ ρ' deg deg' φ hφ hdeg hinj hmap i

  have minj : ∀ i, Function.Injective (mapC (G := G) (G' := G') φ i) :=
    fun i s t h => funext fun I => hinj I.1 (congrFun h I)

  have lift : ∀ (i : ℕ) (w' : Cochain G' i), w' ∈ Cdeg G' deg' i →
      ∃ w ∈ Cdeg G deg i, mapC φ i w = w' := by
    intro i w' hw'
    have h : ∀ I : Idx U i, ∃ x ∈ deg I.1, φ I.1 x = w' I := fun I => by
      have hI : w' I ∈ deg' I.1 := hw' I (Set.mem_univ _)
      rw [← hmap I.1] at hI
      exact Submodule.mem_map.mp hI
    choose w hw hφw using h
    exact ⟨w, fun I _ => hw I, funext fun I => hφw I⟩

  have bdry : ∀ (i : ℕ) (z : Cochain G i), mapC φ i z ∈ bdryDeg G' deg' ρ' i → z ∈ bdryDeg G deg ρ i := by
    intro i z h
    cases i with
    | zero =>
      change mapC φ 0 z ∈ (⊥ : Submodule R _) at h
      change z ∈ (⊥ : Submodule R _)
      rw [Submodule.mem_bot] at h ⊢
      exact minj 0 (h.trans (map_zero _).symm)
    | succ i =>
      change mapC φ (i + 1) z ∈ (Cdeg G' deg' i).map (d G' ρ' i) at h
      change z ∈ (Cdeg G deg i).map (d G ρ i)
      obtain ⟨w', hw', hd⟩ := Submodule.mem_map.mp h
      obtain ⟨w, hw, rfl⟩ := lift i w' hw'
      refine Submodule.mem_map.mpr ⟨w, hw, minj (i + 1) ?_⟩
      rw [mapC_d φ hφ]
      exact hd
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    change Submodule.Quotient.mk _ = 0 at hx
    have hx' := (Submodule.Quotient.mk_eq_zero _).mp hx
    exact (Submodule.Quotient.mk_eq_zero _).mpr (bdry i z hx')
  · intro y
    obtain ⟨z', rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨w, hw, hwz⟩ := lift i z' z'.2.2
    have hdw : d G ρ i w = 0 := by
      apply minj (i + 1)
      rw [mapC_d φ hφ, hwz, map_zero]
      exact z'.2.1
    refine ⟨Submodule.Quotient.mk ⟨w, hdw, hw⟩, ?_⟩
    change Submodule.Quotient.mk _ = _
    congr 1
    exact Subtype.ext hwz

end Cech

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisFurther
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def CellDSq.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (n : ℕ)
    (s : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω), cellD S y (n + 1) (cellD S y n s) = 0

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleSecsSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u w

def VeryAmpleSecs.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (Nb : LineBundle k x) (r : ℕ) (h : Fin (r + 1) → Ω), IsVeryAmpleBy Nb.toSubSystem h →
    ∀ n : ℕ, (Nb.toSubSystem.pow n).secs = ((twistSys k h 1).pow n).secs

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmplePowSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u w

def VeryAmplePow.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (H : LineBundle S x) (j : ℕ), IsVeryAmple H.toSubSystem → 1 ≤ j →
    IsVeryAmple (H.toSubSystem.pow j)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleProductPosSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u w

def VeryAmpleProductPos.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (e : ℕ) (pp : Ideal (Poly k N)) (Ls : Fin e → LineBundle k x), IsSubvar x pp e →
    (∀ i, IsVeryAmple (Ls i).toSubSystem) → 0 < interNum pp (fun i => (Ls i).toSubSystem)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PointDegreePosSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u w

def PointDegreePos.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (pp : Ideal (Poly k N)), IsSubvar (x := x) pp 0 →
    0 < FieldNumbers.resDeg (pp.comap (oneBlock (S := k) (N := N)).toRingHom)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CutMultPosSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u

def CutMultPos.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (N : ℕ) (J qq : Ideal (Poly S N))
    (h : qq ∈ J.minimalPrimes),
    haveI : qq.IsPrime := h.1.1
    0 < cutMult J qq ∧ cutMult J qq < ⊤

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GlobalFunctionsIntegralSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def GlobalFunctionsIntegral.Statement : Prop :=
  ∀ (k : Type u) [Field k] (K : Type w) [Field K] [Algebra k K] (N : ℕ) (y : Fin (N + 1) → K) (a : K),
    y ≠ 0 → (∀ (i : Fin (N + 1)) (hi : y i ≠ 0), a ∈ chartRing k y (singleChart hi)) → IsIntegral k a

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleDegreeSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u w

def VeryAmpleDegree.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω) (e : ℕ)
    (Nb : LineBundle k x) (r : ℕ) (h : Fin (r + 1) → Ω), IsSubvar x (primeOf (S := k) x) e →
    IsVeryAmpleBy Nb.toSubSystem h →
    interNum (primeOf (S := k) x) (fun _ : Fin e => Nb.toSubSystem) =
      interNum (primeOf (S := k) h) (fun _ : Fin e => twistSys k h 1)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TildeShiftSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def TildeShift.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (M : FinGradedSub (S := S) (x := x) E) (c : ℤ),
    M.tildeSys c = (M.tildeSys 0).twist (twistSys S x c)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TildeFiniteESt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def TildeFiniteE.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (M : FinGradedSub (S := S) (x := x) E) (i : ℕ) (c : ℤ),
    Module.Finite S ((M.tildeSys c).H i)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

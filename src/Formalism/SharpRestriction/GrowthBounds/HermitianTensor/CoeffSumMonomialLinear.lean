module

public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CloudIsoDef
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.TieDefs
public import Lemmata.DualWeylPullback.DualWeylPull

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CoeffSumMonomialLinear
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

def midI (r : ℕ) (j : Fin r) : Fin (r + 1 + 1) := j.castSucc.succ

def midOf {r : ℕ} (t : Fin (r + 1 + 1)) : Option (Fin r) :=
  if h : 0 < t.val ∧ t.val < r + 1 then some ⟨t.val - 1, by omega⟩ else none

def subY (A : Type) [CommRing A] (r : ℕ) :
    MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) A →ₐ[A]
      MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Fin r × Fin r) A) :=
  aeval fun v => match midOf v.2 with
    | some j => ∑ i : Fin r, C (X (i, j)) * X (v.1, midI r i)
    | none => X v

def sub2 (K : Type) [Field K] (r : ℕ) :
    MvPolynomial (Bool × (Fin (r + 1 + 1) × Fin (r + 1 + 1))) K →ₐ[K]
      MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Bool × (Fin r × Fin r)) K) :=
  aeval fun w => map (blockEmb K (k := r) (n := r) w.1).toRingHom (subY K r (X w.2))

theorem coeff_sum_monomial_linear {K B σ : Type} [Field K] [CommRing B] [Algebra K B] (L : B →ₗ[K] K) (f : MvPolynomial σ B)
    (u : σ →₀ ℕ) : AddMonoidAlgebra.coeff (∑ u' ∈ f.support, monomial u' (L (AddMonoidAlgebra.coeff f u'))) u = L (AddMonoidAlgebra.coeff f u) := by
  classical
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with hu
  · rfl
  · have h0 : AddMonoidAlgebra.coeff f u = 0 := by simpa [mem_support_iff] using hu
    rw [h0, map_zero]

def lcoef {K B σ : Type} [Field K] [CommRing B] [Algebra K B] (L : B →ₗ[K] K) :
    MvPolynomial σ B →ₗ[K] MvPolynomial σ K where
  toFun f := ∑ u ∈ f.support, monomial u (L (AddMonoidAlgebra.coeff f u))
  map_add' f g := by
    ext u
    simp only [AddMonoidAlgebra.coeff_add (R := K), Finsupp.add_apply, coeff_sum_monomial_linear]
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, map_add]
  map_smul' c f := by
    ext u
    rw [RingHom.id_apply, coeff_smul, coeff_sum_monomial_linear, coeff_sum_monomial_linear, coeff_smul, map_smul]

theorem coeff_lcoef {K B σ : Type} [Field K] [CommRing B] [Algebra K B] (L : B →ₗ[K] K) (f : MvPolynomial σ B)
    (u : σ →₀ ℕ) : AddMonoidAlgebra.coeff (lcoef L f) u = L (AddMonoidAlgebra.coeff f u) :=
  coeff_sum_monomial_linear L f u

def lamOf (K : Type) [Field K] (r : ℕ) (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K) :
    MvPolynomial (Bool × (Fin (r + 1 + 1) × Fin (r + 1 + 1))) K →ₗ[K] MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K :=
  lcoef L ∘ₗ (sub2 K r).toLinearMap

def detY (A : Type) [CommRing A] (r : ℕ) : MvPolynomial (Fin r × Fin r) A :=
  Matrix.det (fun i j : Fin r => (X (i, j) : MvPolynomial (Fin r × Fin r) A))

def resY (A : Type) [CommRing A] (r : ℕ) (s : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) A) :
    MvPolynomial (Fin r × Fin r) A :=
  eval (idPoint (MvPolynomial (Fin r × Fin r) A) (r + 1 + 1) (r + 1 + 1)) (subY A r s)

def RowA {K : Type} [CommRing K] {k n : ℕ} (a : Fin k) (f : MvPolynomial (Fin k × Fin n) K) (d : ℕ) : Prop :=
  ∀ u, AddMonoidAlgebra.coeff f u ≠ 0 → rowDeg u a = d

def shapeC {r : ℕ} (c : ℕ) (β : Fin r → ℕ) : Fin (r + 1 + 1) → ℕ :=
  fun t => if t = 0 then c else match midOf t with
    | some j => β j
    | none => 0

def PhInv (K : Type) [Field K] (r N : ℕ) (α α' : Fin r → ℕ) (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K) : Prop :=
  ∀ l : Matrix (Fin r) (Fin r) K, IsUnit l.det → ∀ f ∈ dualWeyl K r r α, ∀ f' ∈ dualWeyl K r r α',
    L (blockEmb K true (rowAct K l f) * blockEmb K false (rowAct K l f')) =
      l.det ^ N * L (blockEmb K true f * blockEmb K false f')

def QPh : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (r : ℕ), 1 ≤ r → ∀ (a c N : ℕ) (α : Fin r → ℕ), Antitone α → (∀ i, α i ≤ N) →
    (∀ i j, α i ≤ α j + c) → c ≤ 8 * a →
    ∃ L : MvPolynomial (Bool × (Fin r × Fin r)) R.Kf →ₗ[R.Kf] R.Kf,
      PhInv R.Kf r N α (fun i => N - α i.rev) L ∧
      (∀ f ∈ intO R.O r α, ∀ f' ∈ intO R.O r (fun i => N - α i.rev),
        L (blockEmb R.Kf true f * blockEmb R.Kf false f') ∈ Set.range (algebraMap R.O R.Kf)) ∧
      ∃ (nb : ℕ) (u u' : Fin nb → MvPolynomial (Fin r × Fin r) R.Kf) (ka : Fin nb → ℕ),
        (nb : ℚ) = weylDim r (fun j => (α j : ℤ)) ∧ (∀ b, ka b ≤ ⌈kappaOneExponent p a (r + 1)⌉₊) ∧
        (∀ b, u b ∈ intO R.O r α) ∧ (∀ a', u' a' ∈ intO R.O r (fun i => N - α i.rev)) ∧
        ∀ a' b, L (blockEmb R.Kf true (u b) * blockEmb R.Kf false (u' a')) = if a' = b then (p : R.Kf) ^ ka b else 0

def SubCoeffP : Prop :=
  ∀ (A : Type) [CommRing A] (r : ℕ) (ν : Fin (r + 1 + 1) → ℕ) (v : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) A),
    v ∈ dualWeyl A (r + 1 + 1) (r + 1 + 1) ν → ∀ u, AddMonoidAlgebra.coeff (subY A r v) u ∈ dualWeyl A r r (fun j => ν (midI r j))

def SubMapP : Prop :=
  ∀ (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B) (r : ℕ) (v : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) A),
    subY B r (map φ v) = map (map φ) (subY A r v)

def SubRowP : Prop :=
  ∀ (A : Type) [CommRing A] (r : ℕ) (a : Fin (r + 1 + 1)) (d : ℕ) (v : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) A),
    RowA a v d → RowA a (subY A r v) d

def LamCoeffP : Prop :=
  ∀ (K : Type) [Field K] (r : ℕ) (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K)
    (v t : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K) (u : Fin (r + 1 + 1) × Fin (r + 1 + 1) →₀ ℕ),
    AddMonoidAlgebra.coeff (lamOf K r L (blockEmb K true v * blockEmb K false t)) u =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal u,
        L (blockEmb K true (AddMonoidAlgebra.coeff (subY K r v) x.1) * blockEmb K false (AddMonoidAlgebra.coeff (subY K r t) x.2))

def LamEquivP : Prop :=
  ∀ (K : Type) [Field K] (r : ℕ) (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K)
    (g : Matrix (Fin (r + 1 + 1)) (Fin (r + 1 + 1)) K) (v t : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K),
    lamOf K r L (blockEmb K true (rowAct K g v) * blockEmb K false (rowAct K g t)) =
      rowAct K g (lamOf K r L (blockEmb K true v * blockEmb K false t))

def LamMulP : Prop :=
  ∀ (K : Type) [Field K] (r Q : ℕ) (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K)
    (F s t : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K), subY K r F = C (detY K r ^ Q) * map C F →
    lamOf K r L (blockEmb K true (F * s) * blockEmb K false t) =
      F * lcoef L (C (blockEmb K true (detY K r ^ Q)) * map (blockEmb K (k := r) (n := r) true).toRingHom (subY K r s) *
        map (blockEmb K (k := r) (n := r) false).toRingHom (subY K r t))

def LamEvalP : Prop :=
  ∀ (K : Type) [Field K] (r : ℕ) (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K)
    (v t : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K),
    eval (idPoint K (r + 1 + 1) (r + 1 + 1)) (lamOf K r L (blockEmb K true v * blockEmb K false t)) =
      L (blockEmb K true (resY K r v) * blockEmb K false (resY K r t))

def LamMemP : Prop :=
  ∀ (K : Type) [Field K] [Infinite K] (r N : ℕ) (ν ν' νp : Fin (r + 1 + 1) → ℕ)
    (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K),
    ν (Fin.last (r + 1)) = 0 → ν' (Fin.last (r + 1)) = 0 → νp (Fin.last (r + 1)) = 0 → νp 0 = ν 0 + ν' 0 →
    (∀ j, νp (midI r j) = N) → PhInv K r N (fun j => ν (midI r j)) (fun j => ν' (midI r j)) L →
    ∀ v ∈ dualWeyl K (r + 1 + 1) (r + 1 + 1) ν, ∀ t ∈ dualWeyl K (r + 1 + 1) (r + 1 + 1) ν',
      lamOf K r L (blockEmb K true v * blockEmb K false t) ∈ dualWeyl K (r + 1 + 1) (r + 1 + 1) νp

def SubMuP : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (r : ℕ), 1 ≤ r → ∀ (P Q : ℕ),
    ∀ F ∈ dualWeyl R.Kf (r + 1 + 1) (r + 1 + 1) (nuOf (wtPQ (r + 1) P Q)), subY R.Kf r F = C (detY R.Kf r ^ Q) * map C F

def TopLineP : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (r : ℕ), 1 ≤ r → ∀ (a b : ℕ),
    ∀ Ψ ∈ dualWeyl R.Kf (r + 1 + 1) (r + 1 + 1) (nuOf (wtPQ (r + 1) a b)), RowA 0 Ψ (a + b) → RowA (Fin.last (r + 1)) Ψ 0 →
      Ψ = C (eval (idPoint R.Kf (r + 1 + 1) (r + 1 + 1)) Ψ) * hw R.Kf (le_refl (r + 1 + 1)) (nuOf (wtPQ (r + 1) a b))

def LiftP : Prop :=
  ∀ (A : Type) [CommRing A] [IsDomain A] (r c : ℕ) (β : Fin r → ℕ), Antitone β → (∀ j, β j ≤ c) →
    ∀ u ∈ dualWeyl A r r β, ∃ s ∈ dualWeyl A (r + 1 + 1) (r + 1 + 1) (shapeC c β),
      RowA 0 s c ∧ RowA (Fin.last (r + 1)) s 0 ∧ resY A r s = u

def DetDivP : Prop :=
  ∀ (A : Type) [CommRing A] [IsDomain A] (r Q : ℕ) (β : Fin r → ℕ), 1 ≤ r → Antitone β →
    ∀ u ∈ dualWeyl A r r (fun j => β j + Q), ∃ u₀ ∈ dualWeyl A r r β, u = detY A r ^ Q * u₀

def IntCapP : Prop :=
  ∀ (O K : Type) [CommRing O] [Field K] [Algebra O K], Function.Injective (algebraMap O K) →
    ∀ (k : ℕ) (ν : Fin k → ℕ) (F : MvPolynomial (Fin k × Fin k) K), F ∈ dualWeyl K k k ν →
      (∀ u, AddMonoidAlgebra.coeff F u ∈ Set.range (algebraMap O K)) → F ∈ intO O k ν

def HwMulP : Prop :=
  ∀ (A : Type) [CommRing A] (k : ℕ) (ν ν' : Fin k → ℕ), Antitone ν → Antitone ν' →
    hw A (le_refl k) (ν + ν') = hw A (le_refl k) ν * hw A (le_refl k) ν' ∧
    eval (idPoint A k k) (hw A (le_refl k) ν) = 1

end Formalism.MainNotions.flipOneThree.Pf

end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.HermitianTensor.MemInvariantSectionsTwoWeightIff
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

theorem wtPQ_eq (m a b : ℕ) (hm : 1 ≤ m) : wtPQ m a b = letterWt m a true + letterWt m b false := by
  funext i
  have hi := i.isLt
  simp only [wtPQ, letterWt, Pi.add_apply, Fin.ext_iff, Fin.val_zero, Fin.val_last, if_true, Bool.false_eq_true, if_false]
  split_ifs <;> omega

theorem wtPQ_anti (m a b : ℕ) (hm : 1 ≤ m) : Antitone (wtPQ m a b) := by
  intro i j hij
  have hij' : i.val ≤ j.val := hij
  have hi := i.isLt
  have hj := j.isLt
  simp only [wtPQ, Fin.ext_iff, Fin.val_zero, Fin.val_last]
  split_ifs <;> omega

theorem nuOf_wtPQ (m a b : ℕ) (hm : 1 ≤ m) :
    nuOf (wtPQ m a b) = nuOf (letterWt m a true) + nuOf (letterWt m b false) := by
  funext t
  have ht := t.isLt
  simp only [nuOf, wtPQ_eq m a b hm, Pi.add_apply, letterWt, Fin.ext_iff, Fin.val_zero, Fin.val_last, if_true, Bool.false_eq_true, if_false]
  split_ifs <;> omega

theorem delta_block (K : Type) [Field K] (m : ℕ) (b : Bool) (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) :
    deltaB K m (blockEmb K b F) = F := by
  simp [deltaB, blockEmb, rename_rename, Function.comp_def]
  exact rename_id_apply F

theorem delta_prod (K : Type) [Field K] (m : ℕ) (F : Bool → MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) :
    deltaB K m (∏ b, blockEmb K b (F b)) = F true * F false := by
  rw [map_prod, Fintype.prod_bool, delta_block, delta_block]

theorem mem_invariant_sections_two_weight_iff (hCO : CartanOnto) {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf]
    [Algebra O Kf] [IsFractionRing O Kf] (m a b : ℕ) (hm : 1 ≤ m) (Λ : Submodule O (Fin (m + 1) → Kf))
    (hΛ : IsLattice O Λ) (y : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) :
    y ∈ H0 O m (wtPQ m a b) Λ ↔ ∃ x ∈ twoLat O m a b Λ, deltaB Kf m x = y := by
  have hA : Antitone (letterWt m a true) := by
    intro i j hij
    have hij' : i.val ≤ j.val := hij
    simp only [letterWt, if_true, Fin.ext_iff, Fin.val_zero]
    split_ifs <;> omega
  have hB : Antitone (letterWt m b false) := by
    intro i j hij
    have hij' : i.val ≤ j.val := hij
    have hi := i.isLt
    have hj := j.isLt
    simp only [letterWt, Bool.false_eq_true, if_false, Fin.ext_iff, Fin.val_last]
    split_ifs <;> omega
  have key : H0 O m (wtPQ m a b) Λ =
      Submodule.map ((deltaB Kf m).toLinearMap.restrictScalars O) (twoLat O m a b Λ) := by
    rw [wtPQ_eq m a b hm, hCO O Kf m _ _ Λ hΛ hA hB, twoLat, tensorLat, Submodule.map_span]
    congr 1
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨F, hF, G, hG, rfl⟩
      refine ⟨∏ s, blockEmb Kf s (if s = true then F else G), ⟨fun s => if s = true then F else G, ?_, rfl⟩, ?_⟩
      · intro s
        cases s <;> simpa using ‹_›
      · simp [delta_block]
    · rintro ⟨x, ⟨F, hF, rfl⟩, rfl⟩
      refine ⟨F true, by simpa using hF true, F false, by simpa using hF false, ?_⟩
      simp [delta_block]
  rw [key, Submodule.mem_map]
  exact Iff.rfl

theorem delta_twoSp (K : Type) [Field K] (m a b : ℕ) (hm : 1 ≤ m) :
    ∀ x ∈ twoSp K m a b, deltaB K m x ∈ dualWeyl K (m + 1) (m + 1) (nuOf (wtPQ m a b)) := by
  intro x hx
  rw [nuOf_wtPQ m a b hm]
  unfold twoSp tensorLat at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨F, hF, rfl⟩ := hy
    rw [delta_prod]
    have h1 := hF true
    have h2 := hF false
    simp only [eq_self_iff_true, if_true, Bool.false_eq_true, if_false] at h1 h2
    exact Formalism.GradedWeylDivisibility.dualWeyl_mul h1 h2
  | zero => simp
  | add y z _ _ hy hz =>
    rw [map_add (f := _)]
    exact add_mem hy hz
  | smul c y _ hy =>
    rw [map_smul]
    exact Submodule.smul_mem _ c hy

theorem hXY_ne_zero (K : Type) [Field K] (k : ℕ) : hXY K (k + 1) ≠ 0 := by
  intro h
  have := congrArg (MvPolynomial.eval (Sum.elim (fun i : Fin (k + 1) => if i = 0 then (1 : K) else 0)
    (fun i : Fin (k + 1) => if i = 0 then (1 : K) else 0))) h
  simp [hXY] at this

end Formalism.MainNotions.flipOneThree.Pf

end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CloudIso
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

theorem nuOf_add {m : ℕ} (lam mu : Fin (m + 1) → ℤ) (h1 : Antitone lam) (h2 : Antitone mu) :
    nuOf (lam + mu) = nuOf lam + nuOf mu := by
  funext t
  have a1 : lam (Fin.last m) ≤ lam t := h1 (Fin.le_last t)
  have a2 : mu (Fin.last m) ≤ mu t := h2 (Fin.le_last t)
  simp only [nuOf, Pi.add_apply]
  omega

section One

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K]

theorem smulO_eq {σ : Type} (a : O) (F : MvPolynomial σ K) : a • F = algebraMap O K a • F :=
  (algebraMap_smul K a F).symm

theorem exists_pow_mem (w : O) (hw : Irreducible w) (m : ℕ) (mu : Fin (m + 1) → ℤ) (hmu : Antitone mu)
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (hg : IsUnit g.det) (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K)
    (hF : F ∈ dualWeyl K (m + 1) (m + 1) (nuOf mu)) : ∃ n : ℕ, w ^ n • F ∈ H0 O m mu (colSpan O g) := by
  first | exact Bl.DualWeylPullback.goal1 .. | (apply Bl.DualWeylPullback.goal1 <;> assumption) | (intros; apply Bl.DualWeylPullback.goal1 <;> assumption) | (apply @Bl.DualWeylPullback.goal1 <;> assumption) | (intros; apply @Bl.DualWeylPullback.goal1 <;> assumption) | (apply @Bl.DualWeylPullback.goal1 <;> first | assumption | infer_instance) | exact @Bl.DualWeylPullback.goal1 O K ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› w hw m mu hmu g hg F hF | exact @Bl.DualWeylPullback.goal1 O K ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› w hw m mu hmu g hg F | exact @Bl.DualWeylPullback.goal1 O K ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› w hw m mu hmu g hg | exact @Bl.DualWeylPullback.goal1 O K ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› w hw m mu hmu g | exact @Bl.DualWeylPullback.goal1 O K ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› w hw m mu hmu | exact @Bl.DualWeylPullback.goal1 O K ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› w hw m mu | exact @Bl.DualWeylPullback.goal1 O K ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› w hw m | exact @Bl.DualWeylPullback.goal1 O K ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› w hw | exact @Bl.DualWeylPullback.goal1 O K ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› w | exact @Bl.DualWeylPullback.goal1 O K ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.DualWeylPullback.goal1 O K ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.DualWeylPullback.goal1 O K ‹_› ‹_› ‹_› ‹_› | exact @Bl.DualWeylPullback.goal1 O K ‹_› ‹_› ‹_› | exact @Bl.DualWeylPullback.goal1 O K ‹_› ‹_› | exact @Bl.DualWeylPullback.goal1 O K ‹_› | exact @Bl.DualWeylPullback.goal1 O K | exact @Bl.DualWeylPullback.goal1 O

theorem iso_one (hCD : CartanDomain) (w : O) (hw : Irreducible w) (m : ℕ) (mu ze : Fin (m + 1) → ℤ) (hmu : Antitone mu)
    (hze : Antitone ze) (Λ : Submodule O (Fin (m + 1) → K)) (hΛ : IsLattice O Λ)
    (z : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) (hz : z ∈ H0 O m ze Λ)
    (hprim : ¬ ∃ z' ∈ H0 O m ze Λ, z = w • z') (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K)
    (hF : F ∈ dualWeyl K (m + 1) (m + 1) (nuOf mu)) (hzF : z * F ∈ H0 O m (mu + ze) Λ) : F ∈ H0 O m mu Λ := by
  have hwK : algebraMap O K w ≠ 0 := by
    intro h
    exact hw.ne_zero ((IsFractionRing.injective O K) (by rw [h, map_zero]))
  have key : ∀ n : ℕ, ∀ F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K, w ^ n • F ∈ H0 O m mu Λ →
      z * F ∈ H0 O m (mu + ze) Λ → F ∈ H0 O m mu Λ := by
    intro n
    induction n with
    | zero => intro F h _; simpa using h
    | succ n ih =>
      intro F h1 h2
      apply ih F _ h2
      have hX : (w ^ (n + 1) • F) * z = w • (w ^ n • (z * F)) := by
        rw [smul_mul_assoc, pow_succ', mul_smul, mul_comm F z]
      rcases hCD O K w hw m mu ze Λ hΛ hmu hze _ h1 z hz ⟨_, Submodule.smul_mem _ _ h2, hX⟩ with ⟨F', hF', he⟩ | h
      · have : w ^ n • F = F' := by
          rw [pow_succ', mul_smul, smulO_eq w, smulO_eq w F'] at he
          exact smul_right_injective _ hwK he
        rw [this]; exact hF'
      · exact absurd h hprim
  obtain ⟨g, hg, rfl⟩ := hΛ
  obtain ⟨n, hn⟩ := exists_pow_mem w hw m mu hmu g hg F hF
  exact key n F hn hzF

theorem retract_one (hCD : CartanDomain) (hCO : CartanOnto) (w : O) (hw : Irreducible w) (m : ℕ)
    (mu ze : Fin (m + 1) → ℤ) (hmu : Antitone mu)
    (hze : Antitone ze) (Λ : Submodule O (Fin (m + 1) → K)) (hΛ : IsLattice O Λ)
    (z : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) (hz : z ∈ H0 O m ze Λ)
    (hprim : ¬ ∃ z' ∈ H0 O m ze Λ, z = w • z') :
    ∃ ρ : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K →ₗ[K] MvPolynomial (Fin (m + 1) × Fin (m + 1)) K,
      (∀ G ∈ H0 O m (mu + ze) Λ, ρ G ∈ H0 O m mu Λ) ∧
      ∀ F ∈ dualWeyl K (m + 1) (m + 1) (nuOf mu), ρ (z * F) = F := by
  classical
  have hinj : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  have hΛ' := hΛ
  obtain ⟨g, hg, rfl⟩ := hΛ
  have hsum : Antitone (mu + ze) := hmu.add hze
  obtain ⟨B, -, hB1, hB3, hB2⟩ := la_basis hinj m mu g hg
  obtain ⟨B', -, hB1', hB3', hB2'⟩ := la_basis hinj m (mu + ze) g hg
  rw [← H0_eq_twisted_nabla (la_indep hinj) m mu hmu g hg] at hB1
  rw [← H0_eq_twisted_nabla (la_indep hinj) m (mu + ze) hsum g hg] at hB1'
  have : Fintype ↥(ssIdx (m + 1) (m + 1) (nuOf mu)) := (sSIdxFinite _ _ _).fintype
  have : Fintype ↥(ssIdx (m + 1) (m + 1) (nuOf (mu + ze))) := (sSIdxFinite _ _ _).fintype
  let b : Module.Basis _ K (dualWeyl K (m + 1) (m + 1) (nuOf mu)) :=
    (Module.Basis.span hB3).map (LinearEquiv.ofEq _ _ hB2)
  let b' : Module.Basis _ K (dualWeyl K (m + 1) (m + 1) (nuOf (mu + ze))) :=
    (Module.Basis.span hB3').map (LinearEquiv.ofEq _ _ hB2')
  have hb : ∀ i, (b i : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) = B i := by
    intro i
    simp [b, Module.Basis.span_apply]
  have hb' : ∀ i, (b' i : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) = B' i := by
    intro i
    simp [b', Module.Basis.span_apply]
  have hmem : ∀ F : dualWeyl K (m + 1) (m + 1) (nuOf mu),
      F ∈ Submodule.span O (Set.range b) ↔ (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) ∈ H0 O m mu (colSpan O g) := by
    intro F
    have e : (Submodule.span O (Set.range b)).map ((dualWeyl K (m + 1) (m + 1) (nuOf mu)).subtype.restrictScalars O) =
        H0 O m mu (colSpan O g) := by
      rw [Submodule.map_span, ← Set.range_comp, ← hB1]
      congr 2
      funext i
      exact hb i
    rw [← e]
    constructor
    · intro h; exact ⟨F, h, rfl⟩
    · rintro ⟨F', h, he⟩
      have : F' = F := Subtype.ext he
      rwa [← this]
  have hmem' : ∀ F : dualWeyl K (m + 1) (m + 1) (nuOf (mu + ze)),
      F ∈ Submodule.span O (Set.range b') ↔
        (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) ∈ H0 O m (mu + ze) (colSpan O g) := by
    intro F
    have e : (Submodule.span O (Set.range b')).map
        ((dualWeyl K (m + 1) (m + 1) (nuOf (mu + ze))).subtype.restrictScalars O) = H0 O m (mu + ze) (colSpan O g) := by
      rw [Submodule.map_span, ← Set.range_comp, ← hB1']
      congr 2
      funext i
      exact hb' i
    rw [← e]
    constructor
    · intro h; exact ⟨F, h, rfl⟩
    · rintro ⟨F', h, he⟩
      have : F' = F := Subtype.ext he
      rwa [← this]
  have hzK : z ∈ dualWeyl K (m + 1) (m + 1) (nuOf ze) := la_nablaLTw_le m ze g hg z (H0_le_twisted_nabla m ze hze g hg hz)
  let io : dualWeyl K (m + 1) (m + 1) (nuOf mu) →ₗ[K] dualWeyl K (m + 1) (m + 1) (nuOf (mu + ze)) :=
    LinearMap.codRestrict _ ((LinearMap.mulLeft K z) ∘ₗ (dualWeyl K (m + 1) (m + 1) (nuOf mu)).subtype) (by
      intro F
      rw [nuOf_add mu ze hmu hze, add_comm (nuOf mu) (nuOf ze)]
      exact dualWeyl_mul K _ _ _ _ hzK F.2)
  have hio : ∀ F, (io F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) = z * F := fun F => rfl
  obtain ⟨ret, hr1, hr2⟩ := KP.latRetract b b' io (by
    intro F
    rw [hmem, hmem', hio]
    constructor
    · intro h
      exact iso_one hCD w hw m mu ze hmu hze _ hΛ' z hz hprim F F.2 h
    · intro h
      rw [hCO O K m mu ze _ hΛ' hmu hze]
      exact Submodule.subset_span ⟨F, h, z, hz, mul_comm _ _⟩)
  obtain ⟨ρ, hρ⟩ := LinearMap.exists_extend ((dualWeyl K (m + 1) (m + 1) (nuOf mu)).subtype ∘ₗ ret)
  have hρ' : ∀ G : dualWeyl K (m + 1) (m + 1) (nuOf (mu + ze)),
      ρ (G : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) = (ret G : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) :=
    fun G => LinearMap.congr_fun hρ G
  refine ⟨ρ, ?_, ?_⟩
  · intro G hG
    have hGK : G ∈ dualWeyl K (m + 1) (m + 1) (nuOf (mu + ze)) :=
      la_nablaLTw_le m _ g hg G (H0_le_twisted_nabla m _ hsum g hg hG)
    rw [hρ' ⟨G, hGK⟩, ← hmem]
    exact hr2 _ ((hmem' ⟨G, hGK⟩).2 hG)
  · intro F hF
    have := hρ' (io ⟨F, hF⟩)
    rw [hio] at this
    rw [this, hr1]

end One

theorem iso_ten {O K : Type} [CommRing O] [Field K] [Algebra O K] {S : Type} [Fintype S] [DecidableEq S] {k n : ℕ}
    (V : S → Submodule K (MvPolynomial (Fin k × Fin n) K)) (N Np : S → Submodule O (MvPolynomial (Fin k × Fin n) K))
    (z : S → MvPolynomial (Fin k × Fin n) K)
    (ρ : S → MvPolynomial (Fin k × Fin n) K →ₗ[K] MvPolynomial (Fin k × Fin n) K)
    (h1 : ∀ s, ∀ G ∈ Np s, ρ s G ∈ N s) (h2 : ∀ s, ∀ F ∈ V s, ρ s (z s * F) = F)
    (F : MvPolynomial (S × (Fin k × Fin n)) K) (hF : F ∈ tensorLat K K V)
    (hzF : (∏ s, blockEmb K s (z s)) * F ∈ tensorLat O K Np) : F ∈ tensorLat O K N := by
  obtain ⟨T, hT⟩ := KP.tensorMap (K := K) (S := S) (α := Fin k × Fin n)
    (fun s => (blockEmb K (k := k) (n := n) s).toLinearMap ∘ₗ ρ s)
  have hT' : ∀ P : S → MvPolynomial (Fin k × Fin n) K,
      T (∏ s, blockEmb K s (P s)) = ∏ s, blockEmb K s (ρ s (P s)) := fun P => hT P
  have hA : ∀ G ∈ tensorLat O K Np, T G ∈ tensorLat O K N := by
    intro G hG
    unfold tensorLat at hG
    refine Submodule.span_induction (p := fun G _ => T G ∈ tensorLat O K N) ?_ ?_ ?_ ?_ hG
    · rintro _ ⟨P, hP, rfl⟩
      rw [hT']
      exact Submodule.subset_span ⟨fun s => ρ s (P s), fun s => h1 s _ (hP s), rfl⟩
    · rw [map_zero]; exact Submodule.zero_mem _
    · intro x y _ _ hx hy
      rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    · intro c x _ hx
      rw [← algebraMap_smul K c x, map_smul, algebraMap_smul]
      exact Submodule.smul_mem _ _ hx
  have hB : ∀ F ∈ tensorLat K K V, T ((∏ s, blockEmb K s (z s)) * F) = F := by
    intro F hF
    unfold tensorLat at hF
    refine Submodule.span_induction (p := fun F _ => T ((∏ s, blockEmb K s (z s)) * F) = F) ?_ ?_ ?_ ?_ hF
    · rintro _ ⟨P, hP, rfl⟩
      rw [← Finset.prod_mul_distrib]
      have : (∏ s, blockEmb K s (z s) * blockEmb K s (P s)) = ∏ s, blockEmb K s (z s * P s) :=
        Finset.prod_congr rfl fun s _ => (map_mul _ _ _).symm
      rw [this, hT']
      exact Finset.prod_congr rfl fun s _ => by rw [h2 s _ (hP s)]
    · rw [mul_zero, map_zero]
    · intro x y _ _ hx hy
      rw [mul_add, map_add (f := _), hx, hy]
    · intro c x _ hx
      rw [mul_smul_comm, map_smul, hx]
  rw [← hB F hF]
  exact hA _ hzF

theorem cloudIso (hCD : CartanDomain) (hCO : CartanOnto) : CloudIsoP := by
  classical
  intro O K _ _ _ _ _ _ w hw n' m mu ze hmu hze M hM z hz hprim F hF hzF
  choose ρ hρ1 hρ2 using fun s =>
    retract_one hCD hCO w hw m (mu s) (ze s) (hmu s) (hze s) (M s) (hM s) (z s) (hz s) (hprim s)
  exact iso_ten (fun s => dualWeyl K (m + 1) (m + 1) (nuOf (mu s))) (fun s => H0 O m (mu s) (M s))
    (fun s => H0 O m (mu s + ze s) (M s)) z ρ hρ1 hρ2 F hF hzF

end Formalism.MainNotions.flipOneThree.Pf

end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.HermitianTensor.LamPolySmulRight
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

def PosOK {p n' : ℕ} (R : RS p n') (m : ℕ) (lam mu mup ze lo lo' : Fin (m + 1) → ℤ) (d : ℚ) (κ : ℕ) : Prop :=
  ∃ abelian₂ : MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) R.Kf →ₗ[R.Kf] MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf,
    (∀ v ∈ dualWeyl R.Kf (m + 1) (m + 1) (nuOf lam), ∀ t ∈ dualWeyl R.Kf (m + 1) (m + 1) (nuOf lo'),
      abelian₂ (blockEmb R.Kf true v * blockEmb R.Kf false t) ∈ dualWeyl R.Kf (m + 1) (m + 1) (nuOf mup)) ∧
    (∀ Λ : Submodule R.O (Fin (m + 1) → R.Kf), IsLattice R.O Λ → ∀ v ∈ H0 R.O m lam Λ, ∀ t ∈ H0 R.O m lo' Λ,
      abelian₂ (blockEmb R.Kf true v * blockEmb R.Kf false t) ∈ H0 R.O m mup Λ) ∧
    ∀ g : Matrix (Fin (m + 1)) (Fin (m + 1)) R.Kf, IsUnit g.det →
      ∃ (nb : ℕ) (z0 : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf)
        (s s' : Fin nb → MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf) (ka : Fin nb → ℕ),
        (nb : ℚ) = d ∧ (∀ b, ka b ≤ κ) ∧
        (∀ a' b, ∀ F ∈ dualWeyl R.Kf (m + 1) (m + 1) (nuOf mu),
          abelian₂ (blockEmb R.Kf true (F * s b) * blockEmb R.Kf false (s' a')) =
            if a' = b then ((p : R.Kf) ^ ka b) • (z0 * F) else 0) ∧
        ∀ c : R.Kf, c ≠ 0 →
          (c ^ (ze 0)) • z0 ∈ H0 R.O m ze (colSpan R.O (g * lb_D _ 1 c)) ∧
          (¬ ∃ z' ∈ H0 R.O m ze (colSpan R.O (g * lb_D _ 1 c)), (c ^ (ze 0)) • z0 = R.w • z') ∧
          (∀ b, (c ^ (lo 0)) • s b ∈ H0 R.O m lo (colSpan R.O (g * lb_D _ 1 c))) ∧
          (∀ a', (c ^ (lo' 0)) • s' a' ∈ H0 R.O m lo' (colSpan R.O (g * lb_D _ 1 c)))

section Gen

variable {K : Type} [Field K] {S α : Type} [Fintype S]

theorem prod_bE_smul {k n : ℕ} (a : S → K) (f : S → MvPolynomial (Fin k × Fin n) K) :
    ∏ s, blockEmb K s (a s • f s) = (∏ s, a s) • ∏ s, blockEmb K s (f s) := by
  simp only [Algebra.smul_def, map_mul, AlgHom.commutes, Finset.prod_mul_distrib, map_prod]

def renB (K : Type) [Field K] (S α : Type) (b : Bool) : MvPolynomial (S × α) K →ₐ[K] MvPolynomial (S × (Bool × α)) K :=
  rename fun x => (x.1, (b, x.2))

theorem renB_prod {k n : ℕ} (v t : S → MvPolynomial (Fin k × Fin n) K) :
    renB K S (Fin k × Fin n) true (∏ s, blockEmb K s (v s)) * renB K S (Fin k × Fin n) false (∏ s, blockEmb K s (t s)) =
      ∏ s, rename (fun x : Bool × (Fin k × Fin n) => (s, x)) (blockEmb K true (v s) * blockEmb K false (t s)) := by
  simp only [map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  simp only [renB, blockEmb, map_mul, rename_rename]
  try rfl

end Gen

section LamPoly

variable {K : Type} [Field K] {S : Type} [Fintype S] {k n : ℕ}

def lamPoly (T : MvPolynomial (S × (Bool × (Fin k × Fin n))) K →ₗ[K] MvPolynomial (S × (Fin k × Fin n)) K)
    (V W : MvPolynomial (S × (Fin k × Fin n)) K) : MvPolynomial (S × (Fin k × Fin n)) K :=
  T (renB K S (Fin k × Fin n) true V * renB K S (Fin k × Fin n) false W)

variable (T : MvPolynomial (S × (Bool × (Fin k × Fin n))) K →ₗ[K] MvPolynomial (S × (Fin k × Fin n)) K)

theorem lamPoly_add_left (V V' W) : lamPoly T (V + V') W = lamPoly T V W + lamPoly T V' W := by
  unfold lamPoly
  rw [map_add (f := _), add_mul, map_add (f := _)]

theorem lamPoly_add_right (V W W') : lamPoly T V (W + W') = lamPoly T V W + lamPoly T V W' := by
  unfold lamPoly
  rw [map_add (f := _), mul_add, map_add (f := _)]

theorem lamPoly_smul_left (c : K) (V W) : lamPoly T (c • V) W = c • lamPoly T V W := by
  unfold lamPoly
  rw [map_smul, smul_mul_assoc, map_smul]

theorem lamPoly_smul_right (c : K) (V W) : lamPoly T V (c • W) = c • lamPoly T V W := by
  unfold lamPoly
  rw [map_smul, mul_smul_comm, map_smul]

theorem lamPoly_zero_left (W) : lamPoly T 0 W = 0 := by
  simp [lamPoly]

theorem lamPoly_zero_right (V) : lamPoly T V 0 = 0 := by
  simp [lamPoly]

variable (L : S → MvPolynomial (Bool × (Fin k × Fin n)) K →ₗ[K] MvPolynomial (Fin k × Fin n) K)
  (hT : ∀ Q : S → MvPolynomial (Bool × (Fin k × Fin n)) K,
    T (∏ s, rename (fun x => (s, x)) (Q s)) = ∏ s, blockEmb K s (L s (Q s)))

include hT in
theorem lamPoly_prod (v t : S → MvPolynomial (Fin k × Fin n) K) :
    lamPoly T (∏ s, blockEmb K s (v s)) (∏ s, blockEmb K s (t s)) =
      ∏ s, blockEmb K s (L s (blockEmb K true (v s) * blockEmb K false (t s))) := by
  unfold lamPoly
  rw [renB_prod, hT]


include hT in
theorem lamPoly_mem {A : Type} [CommRing A] [Algebra A K] (Mv Mt Mr : S → Submodule A (MvPolynomial (Fin k × Fin n) K))
    (h : ∀ s, ∀ v ∈ Mv s, ∀ t ∈ Mt s, L s (blockEmb K true v * blockEmb K false t) ∈ Mr s) :
    ∀ V ∈ tensorLat A K Mv, ∀ W ∈ tensorLat A K Mt, lamPoly T V W ∈ tensorLat A K Mr := by
  intro V hV W hW
  induction hV using Submodule.span_induction with
  | mem V hV0 =>
    induction hW using Submodule.span_induction with
    | mem W hW0 =>
      obtain ⟨F, hF, rfl⟩ := hV0
      obtain ⟨G, hG, rfl⟩ := hW0
      rw [lamPoly_prod T L hT]
      exact Submodule.subset_span ⟨fun s => L s (blockEmb K true (F s) * blockEmb K false (G s)),
        fun s => h s _ (hF s) _ (hG s), rfl⟩
    | zero => rw [lamPoly_zero_right]; exact Submodule.zero_mem _
    | add W W' _ _ h1 h2 => rw [lamPoly_add_right]; exact Submodule.add_mem _ h1 h2
    | smul a W _ h1 =>
      rw [← algebraMap_smul K a W, lamPoly_smul_right, algebraMap_smul]
      exact Submodule.smul_mem _ a h1
  | zero => rw [lamPoly_zero_left]; exact Submodule.zero_mem _
  | add V V' _ _ h1 h2 => rw [lamPoly_add_left]; exact Submodule.add_mem _ h1 h2
  | smul a V _ h1 =>
    rw [← algebraMap_smul K a V, lamPoly_smul_left, algebraMap_smul]
    exact Submodule.smul_mem _ a h1

end LamPoly

theorem cbNuOf_add {m : ℕ} (a b : Fin (m + 1) → ℤ) (ha : Antitone a) (hb : Antitone b) :
    nuOf (a + b) = nuOf a + nuOf b := by
  funext t
  simp only [nuOf, Pi.add_apply]
  have h1 : a (Fin.last m) ≤ a t := ha (Fin.le_last t)
  have h2 : b (Fin.last m) ≤ b t := hb (Fin.le_last t)
  omega

theorem Ar_one {n' m : ℕ} (X : Fin n' → Fin (m + 1) → ℤ) : Ar 1 X = ∑ s, lamAt X s 0 := by
  unfold Ar
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_eq_single_of_mem (0 : Fin (m + 1)) (by simp)]
  intro b hb hb0
  exfalso
  apply hb0
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
  exact Fin.ext (by rw [Fin.val_zero]; omega)

theorem famD_lat (O : Type) {Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] {n' k : ℕ}
    (gs : Fin n' → Matrix (Fin k) (Fin k) Kf) (hgs : ∀ s, IsUnit (gs s).det) (c : Kf) (hc : c ≠ 0) (s : Fin n') :
    IsLattice O (famD O gs c s) :=
  ⟨gs s * lb_D k 1 c, by rw [Matrix.det_mul]; exact (hgs s).mul (lb_D_det k 1 c hc), rfl⟩

end Formalism.MainNotions.flipOneThree.Pf

end
end

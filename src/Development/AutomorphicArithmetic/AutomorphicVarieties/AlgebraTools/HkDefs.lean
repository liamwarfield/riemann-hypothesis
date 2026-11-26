module

public import Mathlib

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDefs
noncomputable section

open MvPolynomial Equiv

namespace UpperTheory.V.AlgebraTools.Hk

variable (R : Type) [CommRing R] (n : ℕ)

def pairs : Finset (Fin n × Fin n) := Finset.univ.filter fun p => p.1 < p.2

def De : MvPolynomial (Fin n) R := ∏ p ∈ pairs n, (X p.2 - X p.1)


variable {R} in
def NN (q : R) : MvPolynomial (Fin n) R := ∏ p ∈ pairs n, (X p.2 - C q * X p.1)

variable {R n}

def alt (x : MvPolynomial (Fin n) R) : MvPolynomial (Fin n) R := ∑ w : Perm (Fin n), Perm.sign w • rename w x


open scoped Classical in
open Classical in
def dd (x : MvPolynomial (Fin n) R) : MvPolynomial (Fin n) R :=
  if h : ∃ y, De R n * y = alt x then h.choose else 0

def invSet (w : Perm (Fin n)) : Finset (Fin n × Fin n) := (pairs n).filter fun p => w⁻¹ p.2 < w⁻¹ p.1

def invN (w : Perm (Fin n)) : ℕ := (invSet w).card


variable (n) in
def poin (q : R) : R := ∑ w : Perm (Fin n), q ^ invN w

def IsDual {ι : Type} [Fintype ι] (a b : ι → MvPolynomial (Fin n) R) : Prop :=
  ∀ w : Perm (Fin n), ∑ i, a i * rename w (b i) = if w = 1 then De R n else 0

structure Bern (n : ℕ) (q : R) (H : Type) [Ring H] [Algebra R H] where
  th : MvPolynomial (Fin n) R →ₐ[R] H
  T : Perm (Fin n) → H
  T_one : T 1 = 1
  T_mul : ∀ a b : Fin n, a.val + 1 = b.val → ∀ w : Perm (Fin n), w⁻¹ a < w⁻¹ b → T (swap a b * w) = T (swap a b) * T w
  T_sq : ∀ a b : Fin n, a.val + 1 = b.val → T (swap a b) * T (swap a b) = (q - 1) • T (swap a b) + q • (1 : H)
  comm : ∀ a b : Fin n, a.val + 1 = b.val → ∀ j, j ≠ a → j ≠ b → T (swap a b) * th (X j) = th (X j) * T (swap a b)
  relA : ∀ a b : Fin n, a.val + 1 = b.val →
    T (swap a b) * th (X a) = th (X b) * T (swap a b) + (q - 1) • th (X a)
  relB : ∀ a b : Fin n, a.val + 1 = b.val →
    T (swap a b) * th (X b) = th (X a) * T (swap a b) - (q - 1) • th (X a)

namespace Bern

variable {q : R} {H : Type} [Ring H] [Algebra R H] (b : Bern n q H)

def one : H := ∑ w, b.T w

def Faithful : Prop := ∀ x, b.th x * b.one = 0 → x = 0

theorem rel_of_quad {H : Type} [Ring H] [Algebra R H] {q : R} (hq : IsUnit q) (T x y : H)
    (hT : T * T = (q - 1) • T + q • (1 : H)) (h : T * y * T = q • x) :
    T * x = y * T + (q - 1) • x ∧ T * y = x * T - (q - 1) • x := by
  have cancel : ∀ a c : H, q • a = q • c → a = c := by
    intro a c hac
    obtain ⟨u, rfl⟩ := hq
    have := congrArg (fun z => ((u⁻¹ : Rˣ) : R) • z) hac
    simpa [smul_smul] using this
  constructor
  · apply cancel
    rw [← mul_smul_comm, ← h, ← mul_assoc, ← mul_assoc, hT]
    rw [add_mul, add_mul, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc, one_mul, h]
    rw [smul_add, smul_comm q (q - 1) x]
    abel
  · apply cancel
    symm
    rw [smul_sub, ← smul_mul_assoc, ← h, mul_assoc (T * y), hT, mul_add, mul_smul_comm,
      mul_smul_comm, mul_one, h, smul_comm q (q - 1) x]
    abel

end Bern

end UpperTheory.V.AlgebraTools.Hk

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ProfDefs
noncomputable section

open Filter

namespace UpperTheory.V.AlgebraTools

variable (l : ℕ) (G : Type) [Group G] [TopologicalSpace G]

def IsProL : Prop := ∀ N : OpenNormalSubgroup G, IsPGroup l (G ⧸ N.toSubgroup)

theorem isProL_iff : IsProL l G ↔ ∀ (N : OpenNormalSubgroup G) (g : G), ∃ k : ℕ, g ^ l ^ k ∈ N.toSubgroup := by
  unfold IsProL
  refine forall_congr' fun N => ?_
  constructor
  · intro h g
    obtain ⟨k, hk⟩ := h (g : G ⧸ N.toSubgroup)
    exact ⟨k, by rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk⟩
  · intro h x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨k, hk⟩ := h g
    exact ⟨k, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hk⟩

def proLRes : Subgroup G :=
  ⨅ N : {N : OpenNormalSubgroup G // IsPGroup l (G ⧸ N.toSubgroup)}, N.1.toSubgroup

variable {l G} in
theorem mem_proLRes {g : G} :
    g ∈ proLRes l G ↔ ∀ N : OpenNormalSubgroup G, IsPGroup l (G ⧸ N.toSubgroup) → g ∈ N.toSubgroup := by
  simp only [proLRes, Subgroup.mem_iInf, Subtype.forall]

theorem isClosed_proLRes [ContinuousMul G] : IsClosed (proLRes l G : Set G) := by
  rw [proLRes, Subgroup.coe_iInf]
  exact isClosed_iInter fun N => N.1.toOpenSubgroup.isClosed


variable {G} in
def proLResOf (H : Subgroup G) : Subgroup G := (proLRes l H).map H.subtype


variable {G} in
def TopGen (s : Set G) : Prop := Dense (Subgroup.closure s : Set G)

def TopFG : Prop := ∃ s : Set G, s.Finite ∧ TopGen s

variable {G} in
theorem topGen_iff [IsTopologicalGroup G] (s : Set G) :
    TopGen s ↔ (Subgroup.closure s).topologicalClosure = ⊤ := by
  rw [TopGen, dense_iff_closure_eq, ← Subgroup.topologicalClosure_coe, ← Subgroup.coe_top,
    SetLike.coe_set_eq]


variable {G} in
def limKer {ι : Type} (F : Filter ι) (K : ι → Subgroup G) : Subgroup G where
  carrier := {g | ∀ O : OpenNormalSubgroup G, ∀ᶠ i in F, g ∈ K i ⊔ O.toSubgroup}
  mul_mem' ha hb O := ((ha O).and (hb O)).mono fun _ h => mul_mem h.1 h.2
  one_mem' _ := Eventually.of_forall fun _ => one_mem _
  inv_mem' h O := (h O).mono fun _ h => inv_mem h

variable {G} in
theorem mem_limKer {ι : Type} {F : Filter ι} {K : ι → Subgroup G} {g : G} :
    g ∈ limKer F K ↔ ∀ O : OpenNormalSubgroup G, ∀ᶠ i in F, g ∈ K i ⊔ O.toSubgroup := Iff.rfl

variable {G} in
instance limKer_normal {ι : Type} (F : Filter ι) (K : ι → Subgroup G) [∀ i, (K i).Normal] :
    (limKer F K).Normal :=
  ⟨fun _ h g O => (h O).mono fun i hi => by
    haveI := O.isNormal'
    exact (Subgroup.sup_normal (K i) O.toSubgroup).conj_mem _ hi g⟩

end UpperTheory.V.AlgebraTools
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IsCplAtSelf
open IsLocalRing

namespace UpperTheory.V.AlgebraTools

structure IsCplAt (R : Type) [CommRing R] (p : Ideal R) (B : Type) [CommRing B] [IsLocalRing B]
    [Algebra R B] : Prop where
  noeth : IsNoetherianRing B
  complete : IsAdicComplete (maximalIdeal B) B
  comap_eq : (maximalIdeal B).comap (algebraMap R B) = p
  dense : ∀ (n : ℕ) (b : B), ∃ a s : R, s ∉ p ∧
    algebraMap R B s * b - algebraMap R B a ∈ maximalIdeal B ^ n
  strict : ∀ (n : ℕ) (a : R), algebraMap R B a ∈ maximalIdeal B ^ n → ∃ s : R, s ∉ p ∧ s * a ∈ p ^ n

theorem IsCplAt.isPrime {R : Type} [CommRing R] {p : Ideal R} {B : Type} [CommRing B]
    [IsLocalRing B] [Algebra R B] (h : IsCplAt R p B) : p.IsPrime := by
  rw [← h.comap_eq]
  exact Ideal.comap_isPrime _ _

abbrev CplAt (R : Type) [CommRing R] (p : Ideal R) [p.IsPrime] : Type :=
  AdicCompletion (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p)

end UpperTheory.V.AlgebraTools
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.EqLagIff
noncomputable section

open Polynomial

namespace UpperTheory.V.AlgebraTools

def lag {R E ι : Type*} [CommRing R] [Ring E] [Algebra R E] [Fintype ι] [DecidableEq ι]
    (a : ι → R) (P : E) (i : ι) : E :=
  Ring.inverse (∏ j ∈ Finset.univ.erase i, (a i - a j)) •
    aeval P (∏ j ∈ Finset.univ.erase i, (X - C (a j)))

theorem eq_lag_iff {R E ι : Type*} [CommRing R] [Ring E] [Algebra R E] [Fintype ι] [DecidableEq ι]
    (a : ι → R) (P : E) (i : ι) (h : ∀ j, j ≠ i → IsUnit (a i - a j)) (f : E) :
    f = lag a P i ↔ (∏ j ∈ Finset.univ.erase i, (a i - a j)) • f =
      aeval P (∏ j ∈ Finset.univ.erase i, (X - C (a j))) := by
  have hu : IsUnit (∏ j ∈ Finset.univ.erase i, (a i - a j)) := by
    refine Finset.prod_induction _ IsUnit (fun x y hx hy => hx.mul hy) isUnit_one ?_
    intro j hj
    exact h j (Finset.ne_of_mem_erase hj)
  obtain ⟨v, hv⟩ := hu
  unfold lag
  rw [← hv, Ring.inverse_unit, ← Units.smul_def, ← Units.smul_def]
  exact eq_inv_smul_iff

def pat {ι : Type*} (R : Type*) [CommRing R] (p : ι → ι → Prop) : Submodule R (Matrix ι ι R) where
  carrier := {X | ∀ i j, ¬ p i j → X i j = 0}
  add_mem' := fun hX hY i j h => by simp [hX i j h, hY i j h]
  zero_mem' := fun _ _ _ => rfl
  smul_mem' := fun c X hX i j h => by simp [hX i j h]

theorem mem_pat {ι R : Type*} [CommRing R] {p : ι → ι → Prop} {X : Matrix ι ι R} :
    X ∈ pat R p ↔ ∀ i j, ¬ p i j → X i j = 0 := Iff.rfl

end UpperTheory.V.AlgebraTools
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CotInd
open IsLocalRing

namespace UpperTheory.V.AlgebraTools

structure CotInd (R : Type) [CommRing R] [IsLocalRing R] {κ : Type} [Fintype κ] (x : κ → R) : Prop where
  mem : ∀ k, x k ∈ maximalIdeal R
  indep : ∀ a : κ → R, ∑ k, a k * x k ∈ maximalIdeal R ^ 2 → ∀ k, a k ∈ maximalIdeal R

theorem cotInd_iff (R : Type) [CommRing R] [IsLocalRing R] {κ : Type} [Fintype κ] (x : κ → R) :
    CotInd R x ↔ ∃ h : ∀ k, x k ∈ maximalIdeal R,
      LinearIndependent (ResidueField R)
        (fun k => ((maximalIdeal R).toCotangent ⟨x k, h k⟩ : CotangentSpace R)) := by
  have key : ∀ (h : ∀ k, x k ∈ maximalIdeal R) (a : κ → R),
      (∑ k, residue R (a k) • ((maximalIdeal R).toCotangent ⟨x k, h k⟩ : CotangentSpace R) = 0) ↔
        ∑ k, a k * x k ∈ maximalIdeal R ^ 2 := by
    intro h a
    have h1 : ∑ k, residue R (a k) • ((maximalIdeal R).toCotangent ⟨x k, h k⟩ : CotangentSpace R)
        = (maximalIdeal R).toCotangent (∑ k, a k • (⟨x k, h k⟩ : maximalIdeal R)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul]
      exact algebraMap_smul (ResidueField R) (a k) _
    rw [h1, Ideal.toCotangent_eq_zero]
    simp
  constructor
  · rintro ⟨h, hi⟩
    refine ⟨h, Fintype.linearIndependent_iff.2 fun g hg k => ?_⟩
    choose a ha using fun k => residue_surjective (g k)
    rw [← ha k, residue_eq_zero_iff]
    refine hi a ((key h a).1 ?_) k
    simpa [ha] using hg
  · rintro ⟨h, hi⟩
    refine ⟨h, fun a ha k => ?_⟩
    have := Fintype.linearIndependent_iff.1 hi (fun k => residue R (a k)) ((key h a).2 ha) k
    exact (residue_eq_zero_iff _).1 this

theorem CotInd.comp {R : Type} [CommRing R] [IsLocalRing R] {κ ι : Type} [Fintype κ] [Fintype ι]
    {x : κ → R} (h : CotInd R x) (e : ι → κ) (he : Function.Injective e) : CotInd R (x ∘ e) := by
  obtain ⟨h1, h2⟩ := (cotInd_iff R x).1 h
  exact (cotInd_iff R _).2 ⟨fun i => h1 (e i), h2.comp e he⟩

end UpperTheory.V.AlgebraTools
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.TopNilDefs
noncomputable section

open Filter

namespace UpperTheory.V.AlgebraTools

section TopNil

variable {R M κ : Type} [CommRing R] [AddCommGroup M] [Module R M]

def topNil (I : Ideal R) (T : κ → Module.End R M) : Submodule R M where
  carrier := {m | ∀ i (j : ℕ), ∀ᶠ r : ℕ in atTop, (T i ^ r) m ∈ (I ^ j • ⊤ : Submodule R M)}
  add_mem' ha hb i j := ((ha i j).and (hb i j)).mono fun _ h => by
    rw [map_add]; exact add_mem h.1 h.2
  zero_mem' _ _ := Eventually.of_forall fun _ => by rw [map_zero]; exact zero_mem _
  smul_mem' c _ h i j := (h i j).mono fun _ h => by
    rw [map_smul]; exact Submodule.smul_mem _ c h

theorem mem_topNil {I : Ideal R} {T : κ → Module.End R M} {m : M} :
    m ∈ topNil I T ↔ ∀ i (j : ℕ), ∀ᶠ r : ℕ in atTop, (T i ^ r) m ∈ (I ^ j • ⊤ : Submodule R M) := Iff.rfl

theorem mem_topNil_iff_exists {I : Ideal R} {T : κ → Module.End R M} {m : M} :
    m ∈ topNil I T ↔ ∀ i (j : ℕ), ∃ r : ℕ, (T i ^ r) m ∈ (I ^ j • ⊤ : Submodule R M) := by
  rw [mem_topNil]
  refine forall₂_congr fun i j => ⟨fun h => h.exists, fun ⟨r, hr⟩ => ?_⟩
  filter_upwards [eventually_ge_atTop r] with s hs
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hs
  rw [add_comm r t, pow_add, Module.End.mul_apply]
  have hle : (I ^ j • ⊤ : Submodule R M).map (T i ^ t) ≤ I ^ j • ⊤ := by
    rw [Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  exact hle ⟨_, hr, rfl⟩

end TopNil

section Split

open Polynomial

variable {R : Type} [CommRing R] (P : R[X]) (n : ℕ)

def splitIdeal : Ideal (MvPolynomial (Fin n) R) :=
  Ideal.span (Set.range fun k : ℕ =>
    (∏ i : Fin n, (X - C (MvPolynomial.X i : MvPolynomial (Fin n) R)) - P.map MvPolynomial.C).coeff k)

abbrev SplitAlg : Type := MvPolynomial (Fin n) R ⧸ splitIdeal P n

def SplitAlg.root (i : Fin n) : SplitAlg P n := Ideal.Quotient.mk _ (MvPolynomial.X i)

theorem SplitAlg.prod_root :
    ∏ i : Fin n, (X - C (SplitAlg.root P n i)) = P.map (algebraMap R (SplitAlg P n)) := by
  have h2 : (∏ i : Fin n, (X - C (MvPolynomial.X i : MvPolynomial (Fin n) R)) -
      P.map MvPolynomial.C).map (Ideal.Quotient.mk (splitIdeal P n)) = 0 := by
    ext k
    rw [coeff_map, coeff_zero, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span ⟨k, rfl⟩
  rw [Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_map, sub_eq_zero] at h2
  simp only [Polynomial.map_sub, map_X, map_C] at h2
  exact h2

def SplitAlg.lift {A : Type} [CommRing A] [Algebra R A] (a : Fin n → A)
    (h : ∏ i : Fin n, (X - C (a i)) = P.map (algebraMap R A)) : SplitAlg P n →ₐ[R] A :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval a) fun x hx => by
    refine (Ideal.span_le (I := RingHom.ker (MvPolynomial.aeval a : MvPolynomial (Fin n) R →ₐ[R] A))).2 ?_ hx
    rintro _ ⟨k, rfl⟩
    have h2 : (∏ i : Fin n, (X - C (MvPolynomial.X i : MvPolynomial (Fin n) R)) - P.map MvPolynomial.C).map
        (MvPolynomial.aeval a : MvPolynomial (Fin n) R →ₐ[R] A).toRingHom = 0 := by
      rw [Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_map, sub_eq_zero]
      have h3 : (MvPolynomial.aeval a : MvPolynomial (Fin n) R →ₐ[R] A).toRingHom.comp MvPolynomial.C =
          algebraMap R A := RingHom.ext fun r => by simp
      rw [h3, ← h]
      simp
    have h4 := congrArg (fun q => q.coeff k) h2
    simp only [coeff_map, coeff_zero] at h4
    exact h4

theorem SplitAlg.lift_root {A : Type} [CommRing A] [Algebra R A] (a : Fin n → A)
    (h : ∏ i : Fin n, (X - C (a i)) = P.map (algebraMap R A)) (i : Fin n) :
    SplitAlg.lift P n a h (SplitAlg.root P n i) = a i := by
  show MvPolynomial.aeval a (MvPolynomial.X i) = a i
  exact MvPolynomial.aeval_X a i

theorem SplitAlg.hom_ext {A : Type} [CommRing A] [Algebra R A] {f g : SplitAlg P n →ₐ[R] A}
    (h : ∀ i, f (SplitAlg.root P n i) = g (SplitAlg.root P n i)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  exact h i

end Split

end UpperTheory.V.AlgebraTools
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.InvAlg
noncomputable section

namespace UpperTheory.V.AlgebraTools

structure TrInv (B E : Type*) [CommRing B] [Ring E] [Algebra B E] where
  st : E →ₗ[B] E
  st_mul : ∀ x y, st (x * y) = st y * st x
  st_st : ∀ x, st (st x) = x
  tr : E →ₗ[B] B
  tr_comm : ∀ x y, tr (x * y) = tr (y * x)
  tr_st : ∀ x, tr (st x) = tr x

structure OddForm (B N : Type*) [CommRing B] [AddCommGroup N] [Module B N] where
  be : N →ₗ[B] N →ₗ[B] B
  symm : ∀ b b', be b b' = be b' b
  assoc : ∀ b b' b'', be b b' • b'' = be b' b'' • b

namespace OddForm

variable {B N : Type*} [CommRing B] [AddCommGroup N] [Module B N]

instance : Inhabited (OddForm B N) := ⟨⟨0, fun _ _ => rfl, fun _ _ _ => by simp⟩⟩

@[nolint unusedArguments]
def Ext (_ : OddForm B N) : Type _ := B × N

variable (Φ : OddForm B N)

instance : AddCommGroup Φ.Ext := inferInstanceAs (AddCommGroup (B × N))
instance : Module B Φ.Ext := inferInstanceAs (Module B (B × N))

def el (a : B) (b : N) : Φ.Ext := (a, b)

variable {Φ}

def Ext.ev (z : Φ.Ext) : B := Prod.fst z

def Ext.od (z : Φ.Ext) : N := Prod.snd z

@[ext] theorem ext {z w : Φ.Ext} (hev : z.ev = w.ev) (hod : z.od = w.od) : z = w :=
  Prod.ext hev hod

instance : One Φ.Ext := ⟨Φ.el 1 0⟩
instance : Mul Φ.Ext := ⟨fun z w => Φ.el (z.ev * w.ev + Φ.be z.od w.od) (z.ev • w.od + w.ev • z.od)⟩

@[simp] theorem ev_one : (1 : Φ.Ext).ev = 1 := rfl
@[simp] theorem od_one : (1 : Φ.Ext).od = 0 := rfl
@[simp] theorem ev_zero : (0 : Φ.Ext).ev = 0 := rfl
@[simp] theorem od_zero : (0 : Φ.Ext).od = 0 := rfl
@[simp] theorem ev_add (z w : Φ.Ext) : (z + w).ev = z.ev + w.ev := rfl
@[simp] theorem od_add (z w : Φ.Ext) : (z + w).od = z.od + w.od := rfl
@[simp] theorem ev_smul (c : B) (z : Φ.Ext) : (c • z).ev = c * z.ev := rfl
@[simp] theorem od_smul (c : B) (z : Φ.Ext) : (c • z).od = c • z.od := rfl
@[simp] theorem ev_mul (z w : Φ.Ext) : (z * w).ev = z.ev * w.ev + Φ.be z.od w.od := rfl
@[simp] theorem od_mul (z w : Φ.Ext) : (z * w).od = z.ev • w.od + w.ev • z.od := rfl

instance : CommRing Φ.Ext :=
  { (inferInstance : AddCommGroup Φ.Ext), (inferInstance : One Φ.Ext), (inferInstance : Mul Φ.Ext) with
    mul_assoc := fun x y z => by
      ext
      · simp; ring
      · simp only [od_mul, ev_mul, add_smul, smul_add, smul_smul]
        rw [Φ.assoc x.od y.od z.od, mul_comm z.ev x.ev, mul_comm z.ev y.ev]; abel
    one_mul := fun x => by ext <;> simp
    mul_one := fun x => by ext <;> simp
    zero_mul := fun x => by ext <;> simp
    mul_zero := fun x => by ext <;> simp
    left_distrib := fun x y z => by
      ext
      · simp; ring
      · simp [add_smul]; abel
    right_distrib := fun x y z => by
      ext
      · simp; ring
      · simp [add_smul]; abel
    mul_comm := fun x y => by
      ext
      · simp [mul_comm, Φ.symm x.od]
      · simp [add_comm] }

instance : Algebra B Φ.Ext :=
  Algebra.ofModule
    (fun c x y => by
      ext
      · simp; ring
      · simp [smul_smul, mul_comm, add_comm])
    (fun c x y => by
      ext
      · simp; ring
      · simp [smul_smul, mul_comm, add_comm])

instance [Module.Finite B N] : Module.Finite B Φ.Ext := inferInstanceAs (Module.Finite B (B × N))

def red (Φ : OddForm B N) : Ideal B := Ideal.span {c | ∃ b b', c = Φ.be b b'}

end OddForm

variable {B E : Type*} [CommRing B] [Ring E] [Algebra B E]

def corner (B : Type*) [CommRing B] [Algebra B E] (e e' : E) : Submodule B E :=
  LinearMap.range ((LinearMap.mulLeft B e).comp (LinearMap.mulRight B e'))

def cornerProj (B : Type*) [CommRing B] [Algebra B E] (e e' : E) : E →ₗ[B] corner B e e' :=
  ((LinearMap.mulLeft B e).comp (LinearMap.mulRight B e')).rangeRestrict

structure TrInv.Units (T : TrInv B E) (ι : Type*) [Fintype ι] (o : ι → ι) where
  ep : ι → E
  x : ι → E
  o_o : ∀ i, o (o i) = o i
  coi : CompleteOrthogonalIdempotents ep
  st_ep : ∀ i, T.st (ep i) = ep i
  tr_ep : ∀ i, T.tr (ep i) = 1
  rank_one : ∀ i y, ∃ b : B, ep i * y * ep i = b • ep i
  x_mem : ∀ i, ep (o i) * x i * ep i = x i
  x_base : ∀ i, x (o i) = ep (o i)
  x_st : ∀ i, x i * T.st (x i) = ep (o i)
  st_mul_x_eq : ∀ i, T.st (x i) * x i = ep i

namespace TrInv.Units

variable {T : TrInv B E} {ι : Type*} [Fintype ι] {o : ι → ι} (U : T.Units ι o)

theorem corner_eq (i : ι) (y : E) : U.ep i * y * U.ep i = T.tr (U.ep i * y * U.ep i) • U.ep i := by
  obtain ⟨b, hb⟩ := U.rank_one i y
  rw [hb, map_smul, U.tr_ep, smul_eq_mul, mul_one]

def oddForm (p q : ι) : OddForm B (corner B (U.ep p) (U.ep q)) where
  be := LinearMap.mk₂ B (fun b b' => T.tr (b.1 * T.st b'.1))
    (fun _ _ _ => by simp [add_mul]) (fun _ _ _ => by simp) (fun _ _ _ => by simp [mul_add]) (fun _ _ _ => by simp)
  symm b b' := by
    simp only [LinearMap.mk₂_apply]
    rw [← T.tr_st, T.st_mul, T.st_st]
  assoc := by
    rintro ⟨_, y, rfl⟩ ⟨_, y', rfl⟩ ⟨_, y'', rfl⟩
    apply Subtype.ext
    have hp := (U.coi.idem p).eq
    have hq := (U.coi.idem q).eq
    have hp' : ∀ z, U.ep p * (U.ep p * z) = U.ep p * z := fun z => by rw [← mul_assoc, hp]
    have hq' : ∀ z, U.ep q * (U.ep q * z) = U.ep q * z := fun z => by rw [← mul_assoc, hq]
    have h1 := U.corner_eq p (y * U.ep q * T.st y')
    have h2 := U.corner_eq q (T.st y' * U.ep p * y'')
    have h3 : T.tr (U.ep p * (y' * U.ep q) * T.st (U.ep p * (y'' * U.ep q))) =
        T.tr (U.ep q * (T.st y' * U.ep p * y'') * U.ep q) := by
      rw [← T.tr_st, T.st_mul, T.st_st, T.tr_comm]
      simp only [T.st_mul, U.st_ep, mul_assoc, hp']
    have h4 : T.tr (U.ep p * (y * U.ep q) * T.st (U.ep p * (y' * U.ep q))) =
        T.tr (U.ep p * (y * U.ep q * T.st y') * U.ep p) := by
      simp only [T.st_mul, U.st_ep, mul_assoc, hq']
    simp only [LinearMap.mk₂_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
      SetLike.val_smul]
    rw [h3, h4]
    calc _ = (T.tr (U.ep p * (y * U.ep q * T.st y') * U.ep p) • U.ep p) * (y'' * U.ep q) := by
          rw [smul_mul_assoc]
      _ = U.ep p * y * (U.ep q * (T.st y' * U.ep p * y'') * U.ep q) := by
          rw [← h1]; simp only [mul_assoc]
      _ = _ := by rw [h2, mul_smul_comm, ← h2, mul_assoc (U.ep p)]

def vr (p q : ι) (y : E) : Matrix ι ι (U.oddForm p q).Ext := Matrix.of fun i j =>
  (U.oddForm p q).el (T.tr (U.x i * y * T.st (U.x j)))
    (cornerProj B (U.ep p) (U.ep q) (U.x i * y * T.st (U.x j)) +
      cornerProj B (U.ep p) (U.ep q) (T.st (U.x i * y * T.st (U.x j))))

end TrInv.Units

end UpperTheory.V.AlgebraTools
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaSuppBc
open IsLocalRing

theorem UpperTheory.V.AlgebraTools.mem_support_baseChange :
    ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M]
      (Q : PrimeSpectrum B), Q ∈ Module.support B (TensorProduct R B M) ↔
        PrimeSpectrum.comap (algebraMap R B) Q ∈ Module.support R M := by
  intro R B _ _ _ M _ _ _ Q
  let p := PrimeSpectrum.comap (algebraMap R B) Q
  let φ := Ideal.ResidueField.mapₐ p.asIdeal Q.asIdeal (Algebra.ofId R B) rfl
  letI : Algebra p.asIdeal.ResidueField Q.asIdeal.ResidueField := φ.toRingHom.toAlgebra
  haveI : IsScalarTower R p.asIdeal.ResidueField Q.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct,
    Module.mem_support_iff_nontrivial_residueField_tensorProduct,
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R B Q.asIdeal.ResidueField
      Q.asIdeal.ResidueField M).nontrivial_congr,
    ← (TensorProduct.AlgebraTensorModule.cancelBaseChange R p.asIdeal.ResidueField
      Q.asIdeal.ResidueField Q.asIdeal.ResidueField M).nontrivial_congr]
  exact Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right _ _
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.OrdExt
open Polynomial Matrix IsLocalRing TensorProduct

theorem UpperTheory.V.AlgebraTools.ord_ext :
    ∀ {R Γ E : Type} [CommRing R] [Monoid Γ] [Ring E] [Algebra R E] {n : ℕ} (r : Γ →* E) (ψ : Fin n → Γ →* R), (∀ g : Fin n → Γ, (List.ofFn fun i => r (g i) - algebraMap R E (ψ i (g i))).prod = 0) → ∀ z : Fin n → MonoidAlgebra R Γ, (List.ofFn fun i => MonoidAlgebra.lift R E Γ r (z i) - algebraMap R E (MonoidAlgebra.lift R R Γ (ψ i) (z i))).prod = 0 := by
  intro R Γ E _ _ _ _ n r ψ h z
  let φ : Fin n → (MonoidAlgebra R Γ →ₗ[R] E) := fun i =>
    (MonoidAlgebra.lift R E Γ r).toLinearMap -
      (Algebra.linearMap R E).comp (MonoidAlgebra.lift R R Γ (ψ i)).toLinearMap
  let F : (∀ _ : Fin n, MonoidAlgebra R Γ) →ₘₗ[R] E :=
    (MultilinearMap.mkPiAlgebraFin R n E).compLinearMap φ
  have hF : F = 0 := by
    refine Module.Basis.ext_multilinear (f := F) (g := 0)
      (fun _ => MonoidAlgebra.basis Γ R) ?_
    intro v
    simp only [F, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebraFin_apply,
      MultilinearMap.zero_apply, MonoidAlgebra.basis_apply]
    convert h v using 3
    funext i
    simp [φ, MonoidAlgebra.lift_single]
  have := congrArg (fun G => G z) hF
  simpa [F, φ] using this
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.TriProdZero
open Polynomial Matrix IsLocalRing TensorProduct

theorem UpperTheory.V.AlgebraTools.tri_prod_zero :
    ∀ {R : Type} [CommRing R] {n : ℕ} (u : Fin n → Matrix (Fin n) (Fin n) R), (∀ k i j, j < i → u k i j = 0) → (∀ k, u k k k = 0) → (List.ofFn u).prod = 0 := by
  intro R _ n u h1 h2
  have key : ∀ m, m ≤ n → ∀ i j : Fin n, j.val < m →
      ((List.ofFn u).take m).prod i j = 0 := by
    intro m
    induction m with
    | zero => intro _ i j hj; exact absurd hj (Nat.not_lt_zero _)
    | succ m ih =>
      intro hm i j hj
      have hlen : m < (List.ofFn u).length := by
        rw [List.length_ofFn]; omega
      rw [List.prod_take_succ _ _ hlen, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun l _ => ?_
      by_cases hl : l.val < m
      · rw [ih (by omega) i l hl, zero_mul]
      · have hu : (List.ofFn u)[m] = u ⟨m, by omega⟩ := by
          simp
        rw [hu]
        by_cases hjl : j < l
        · rw [h1 _ _ _ hjl, mul_zero]
        · have hjl' : l.val ≤ j.val := Fin.le_def.mp (not_lt.mp hjl)
          have e1 : l = ⟨m, by omega⟩ := Fin.ext (by simp; omega)
          have e2 : j = ⟨m, by omega⟩ := Fin.ext (by simp; omega)
          rw [e1, e2, h2, mul_zero]
  ext i j
  have := key n le_rfl i j j.isLt
  rw [List.take_of_length_le (by simp)] at this
  simpa using this
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CoiConjSingle
open Polynomial Matrix IsLocalRing TensorProduct

private theorem UpperTheory.V.AlgebraTools.exists_unit_entry {R : Type} [CommRing R] [IsLocalRing R] {ι : Type}
    [Fintype ι] [DecidableEq ι] (e : Matrix ι ι R) (he : IsIdempotentElem e) (h0 : e ≠ 0) :
    ∃ a b, IsUnit (e a b) := by
  classical
  by_contra h
  push_neg at h
  have hm : ∀ a b, e a b ∈ maximalIdeal R := fun a b => (mem_maximalIdeal _).2 (h a b)
  have hmap : (1 - e).map (residue R) = 1 := by
    ext a b
    by_cases hab : a = b
    · subst hab
      simp [(residue_eq_zero_iff _).2 (hm a a)]
    · simp [Matrix.one_apply_ne hab, (residue_eq_zero_iff _).2 (hm a b)]
  have hdet : IsUnit (1 - e).det := by
    have h1 : residue R (1 - e).det = 1 := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap, det_one]
    exact (isUnit_map_iff (residue R) _).1 (h1 ▸ isUnit_one)
  have hu : IsUnit (1 - e) := (Matrix.isUnit_iff_isUnit_det _).2 hdet
  apply h0
  have h2 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he.eq, sub_self]
  exact hu.mul_right_eq_zero.1 h2

theorem UpperTheory.V.AlgebraTools.coi_conj_single :
    ∀ {R : Type} [CommRing R] [IsLocalRing R] {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → Matrix ι ι R), CompleteOrthogonalIdempotents f → (∀ i, f i ≠ 0) → ∃ g : GL ι R, ∀ i, (g : Matrix ι ι R) * f i * ((g⁻¹ : GL ι R) : Matrix ι ι R) = single i i 1 := by
  intro R _ _ ι _ _ f hf h0
  classical
  have hc : ∀ i, ∃ a b, IsUnit (f i a b) := fun i =>
    UpperTheory.V.AlgebraTools.exists_unit_entry (f i) (hf.idem i) (h0 i)
  choose a b hu using hc
  set P : Matrix ι ι R := Matrix.of fun k j => f j k (b j) with hP
  set Q : Matrix ι ι R := Matrix.of fun i k => ((hu i).unit⁻¹ : Rˣ) * f i (a i) k with hQ
  have hent : ∀ (M : Matrix ι ι R) (j k : ι),
      (Q * M * P) j k = ((hu j).unit⁻¹ : Rˣ) * (f j * M * f k) (a j) (b k) := by
    intro M j k
    simp only [hP, hQ, Matrix.mul_apply, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  have hidem : ∀ i, f i * f i = f i := fun i => (hf.idem i).eq
  have hort : ∀ i j, i ≠ j → f i * f j = 0 := fun i j hij => hf.ortho hij
  have hQP : Q * P = 1 := by
    ext j k
    have h1 := hent 1 j k
    simp only [Matrix.mul_one] at h1
    rw [h1]
    by_cases hjk : j = k
    · subst hjk
      rw [hidem, Matrix.one_apply_eq, IsUnit.val_inv_mul]
    · rw [hort j k hjk, Matrix.one_apply_ne hjk, Matrix.zero_apply, mul_zero]
  have hPQ : P * Q = 1 := mul_eq_one_comm.1 hQP
  refine ⟨⟨Q, P, hQP, hPQ⟩, fun i => ?_⟩
  change Q * f i * P = single i i 1
  ext j k
  rw [hent, Matrix.single_apply]
  by_cases hji : i = j
  · subst hji
    by_cases hik : i = k
    · subst hik
      rw [hidem, hidem, IsUnit.val_inv_mul, if_pos ⟨rfl, rfl⟩]
    · rw [hidem, hort i k hik, Matrix.zero_apply, mul_zero, if_neg (fun h => hik h.2)]
  · rw [hort j i (Ne.symm hji), zero_mul, Matrix.zero_apply, mul_zero, if_neg (fun h => hji h.1)]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ComapPowLe
open Polynomial Matrix IsLocalRing TensorProduct

theorem UpperTheory.V.AlgebraTools.comap_pow_le :
    ∀ {A M M' : Type} [CommRing A] [IsNoetherianRing A] [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M'] [Module.Finite A M'] (I : Ideal A) (f : M →ₗ[A] M'), ∃ c : ℕ, ∀ m : ℕ, (I ^ (m + c) • (⊤ : Submodule A M')).comap f ≤ LinearMap.ker f ⊔ I ^ m • (⊤ : Submodule A M) := by
  intro A M M' _ _ _ _ _ _ _ I f
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I (LinearMap.range f)
  refine ⟨k, fun m x hx => ?_⟩
  have h1 : f x ∈ I ^ (m + k) • (⊤ : Submodule A M') ⊓ LinearMap.range f :=
    ⟨hx, LinearMap.mem_range_self f x⟩
  rw [hk (m + k) (Nat.le_add_left k m), Nat.add_sub_cancel] at h1
  have h2 : f x ∈ I ^ m • LinearMap.range f :=
    Submodule.smul_mono le_rfl inf_le_right h1
  rw [LinearMap.range_eq_map, ← Submodule.map_smul''] at h2
  have h3 : x ∈ ((I ^ m • (⊤ : Submodule A M)).map f).comap f := h2
  rw [Submodule.comap_map_eq, sup_comm] at h3
  exact h3
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.SqrtOneAdd
open Polynomial Matrix IsLocalRing TensorProduct

theorem UpperTheory.V.AlgebraTools.sqrt_one_add :
    ∀ {B : Type} [CommRing B] (I : Ideal B) [HenselianRing B I] (a : B), IsUnit (2 : B) → a - 1 ∈ I → ∃ α : Bˣ, (α : B) ^ 2 = a ∧ (α : B) - 1 ∈ I := by
  intro B _ I _ a h2 ha
  have hmon : (X ^ 2 - C a : B[X]).Monic := by
    apply Polynomial.monic_X_pow_sub_C
    norm_num
  obtain ⟨α, hroot, hα⟩ := HenselianRing.is_henselian (X ^ 2 - C a) hmon 1
    (by
      have : (X ^ 2 - C a : B[X]).eval 1 = -(a - 1) := by simp <;> ring
      rw [this]
      exact I.neg_mem ha)
    (by
      have : (derivative (X ^ 2 - C a : B[X])).eval 1 = 2 := by
        simp only [derivative_sub, derivative_X_pow, derivative_C, eval_sub, eval_mul, eval_C,
          eval_pow, eval_one, eval_zero]
        norm_num
      rw [this]
      exact h2.map _)
  have hu : IsUnit α :=
    Ideal.isUnit_of_sub_one_mem_jacobson α (HenselianRing.jac (I := I) hα)
  refine ⟨hu.unit, ?_, ?_⟩
  · simp only [IsUnit.unit_spec]
    have := hroot
    simp [Polynomial.IsRoot] at this
    exact sub_eq_zero.mp this
  · simpa using hα
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CardEqPowLength
open Polynomial Matrix IsLocalRing TensorProduct

private theorem UpperTheory.V.AlgebraTools.simple_module_equiv_residue_field {A X : Type} [CommRing A] [IsLocalRing A] [AddCommGroup X] [Module A X] [IsSimpleModule A X] : Nonempty (X ≃ ResidueField A) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp (inferInstance : IsSimpleModule A X)
  have : I = maximalIdeal A := IsLocalRing.eq_maximalIdeal hI
  subst this
  exact ⟨e.toEquiv⟩

private theorem UpperTheory.V.AlgebraTools.card_finite_length_module {A : Type} [CommRing A] [IsLocalRing A] [Finite (ResidueField A)] {X : Type} [AddCommGroup X] [Module A X] (h : IsFiniteLength A X) :
    Finite X ∧ Nat.card X = Nat.card (ResidueField A) ^ (Module.length A X).toNat := by
  induction h with
  | @of_subsingleton M _ _ _ =>
    refine ⟨Finite.of_subsingleton, ?_⟩
    rw [Module.length_eq_zero]
    simp [Nat.card_eq_one_iff_unique]
  | @of_simple_quotient M _ _ N _ hN ih =>
    obtain ⟨hfin, hcard⟩ := ih
    obtain ⟨e⟩ := UpperTheory.V.AlgebraTools.simple_module_equiv_residue_field (A := A) (X := M ⧸ N)
    have hq : Nat.card (M ⧸ N) = Nat.card (ResidueField A) := Nat.card_congr e
    have hNt : Module.length A N ≠ ⊤ := Module.length_ne_top_iff.mpr hN
    have hlen : Module.length A M = Module.length A N + 1 := by
      rw [Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
        (LinearMap.exact_subtype_mkQ N), Module.length_eq_one A (M ⧸ N)]
    have hc : Nat.card M = Nat.card (M ⧸ N) * Nat.card N :=
      AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup N.toAddSubgroup
    have hq0 : Nat.card (ResidueField A) ≠ 0 := Nat.card_pos.ne'
    have hM : Nat.card M = Nat.card (ResidueField A) ^ ((Module.length A N).toNat + 1) := by
      rw [hc, hq, hcard, pow_succ, mul_comm]
    refine ⟨Nat.finite_of_card_ne_zero (by rw [hM]; exact pow_ne_zero _ hq0), ?_⟩
    rw [hM, hlen, ENat.toNat_add hNt ENat.one_ne_top]
    simp

theorem UpperTheory.V.AlgebraTools.card_eq_pow_length :
    ∀ {A X : Type} [CommRing A] [IsLocalRing A] [Finite (ResidueField A)] [AddCommGroup X] [Module A X], (Finite X ↔ Module.length A X ≠ ⊤) ∧ (Finite X → Nat.card X = Nat.card (ResidueField A) ^ (Module.length A X).toNat) := by
  intro A X _ _ _ _ _
  have key : Finite X → Module.length A X ≠ ⊤ := fun h => by
    haveI := h
    exact Module.length_ne_top_iff.mpr
      (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, isArtinian_of_finite⟩)
  refine ⟨⟨key, fun h => (UpperTheory.V.AlgebraTools.card_finite_length_module (Module.length_ne_top_iff.mp h)).1⟩, fun h => ?_⟩
  exact (UpperTheory.V.AlgebraTools.card_finite_length_module (Module.length_ne_top_iff.mp (key h))).2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.SepChars
open Polynomial Matrix IsLocalRing TensorProduct

theorem UpperTheory.V.AlgebraTools.sep_chars :
    ∀ {R Γ : Type} [CommRing R] [IsLocalRing R] [Monoid Γ] {n : ℕ} (ψ : Fin n → Γ →* R), (n : Cardinal) ≤ Cardinal.mk (ResidueField R) → Function.Injective (fun i => (residue R : R →* ResidueField R).comp (ψ i)) → ∃ z : MonoidAlgebra R Γ, ∀ i j, i ≠ j → IsUnit (MonoidAlgebra.lift R R Γ (ψ i) z - MonoidAlgebra.lift R R Γ (ψ j) z) := by
  intro R Γ _ _ _ n ψ hcard hinj
  let χ : Fin n → Γ →* ResidueField R := fun i => (residue R : R →* ResidueField R).comp (ψ i)
  have hχ : ∀ i g, χ i g = residue R (ψ i g) := fun i g => rfl
  obtain ⟨a⟩ := (Cardinal.le_def (Fin n) (ResidueField R)).mp (by rwa [Cardinal.mk_fin])
  let L : (Γ →₀ ResidueField R) →ₗ[ResidueField R] (Fin n → ResidueField R) :=
    Finsupp.linearCombination (ResidueField R) (fun g i => χ i g)
  have hsurj : Function.Surjective L := by
    rw [← LinearMap.range_eq_top]
    by_contra hne
    obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
    have hli := (linearIndependent_monoidHom Γ (ResidueField R)).comp χ hinj
    rw [Fintype.linearIndependent_iff] at hli
    let c : Fin n → ResidueField R := fun i => f (fun j => if i = j then 1 else 0)
    have hf : ∀ v, f v = ∑ i, v i * c i := by
      intro v
      conv_lhs => rw [pi_eq_sum_univ v]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [c, map_sum, map_smul]
    have hc : ∀ i, c i = 0 := by
      apply hli c
      funext g
      have hg : (fun i => χ i g) ∈ LinearMap.range L :=
        ⟨Finsupp.single g 1, by simp [L]⟩
      have h0 := hle hg
      rw [LinearMap.mem_ker, hf] at h0
      simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, Pi.zero_apply]
      rw [← h0]
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    apply hf0
    ext v
    simp [hf, hc]
  obtain ⟨w, hw⟩ := hsurj (fun i => a i)
  let s := Function.surjInv (IsLocalRing.residue_surjective (R := R))
  let z : MonoidAlgebra R Γ := ∑ g ∈ w.support, MonoidAlgebra.single g (s (w g))
  have hz : ∀ i, residue R (MonoidAlgebra.lift R R Γ (ψ i) z) = a i := by
    intro i
    have hwi := congrFun hw i
    rw [← hwi]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [z, L, map_sum, MonoidAlgebra.lift_single, Finsupp.linearCombination_apply,
      Finsupp.sum, Finset.sum_apply, smul_eq_mul, map_mul, hχ]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    rw [Function.surjInv_eq (IsLocalRing.residue_surjective (R := R))]
    rfl
  refine ⟨z, fun i j hij => ?_⟩
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_sub, hz, hz, sub_ne_zero]
  exact fun h => hij (a.injective h)
end

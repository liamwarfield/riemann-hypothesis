module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorPowCompAdicCompletionMapToQuotientPow
noncomputable section

namespace GlobalTheory.InvAlg

theorem factorPow_evalₐ {A : Type} [CommRing A] (I : Ideal A) {k n : ℕ} (hle : k ≤ n) (x : AdicCompletion I A) :
    Ideal.Quotient.factorPow I hle (AdicCompletion.evalₐ I n x) = AdicCompletion.evalₐ I k x := by
  obtain ⟨x, rfl⟩ := AdicCompletion.mk_surjective I A x
  simp only [AdicCompletion.evalₐ_mk, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
  rw [Ideal.Quotient.eq]
  have h := x.2 hle
  rw [SModEq.sub_mem] at h
  have hI : (I ^ k • ⊤ : Submodule A A) = I ^ k := by ext; simp
  rw [← neg_sub]
  exact neg_mem (hI ▸ h)

theorem pow_le_comap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {I : Ideal A} {J : Ideal B}
    (h : I.map f ≤ J) (n : ℕ) : I ^ n ≤ (J ^ n).comap f :=
  Ideal.map_le_iff_le_comap.mp (by rw [Ideal.map_pow]; exact Ideal.pow_right_mono h n)

def adicCompletionMapToQuotientPow {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (I : Ideal A) (J : Ideal B)
    (h : I.map f ≤ J) (n : ℕ) : AdicCompletion I A →+* B ⧸ J ^ n :=
  (Ideal.quotientMap (J ^ n) f (pow_le_comap f h n)).comp (AdicCompletion.evalₐ I n : AdicCompletion I A →+* A ⧸ I ^ n)

theorem factorPow_comp_adicCompletionMapToQuotientPow {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (I : Ideal A) (J : Ideal B)
    (h : I.map f ≤ J) {k n : ℕ} (hle : k ≤ n) :
    (Ideal.Quotient.factorPow J hle).comp (adicCompletionMapToQuotientPow f I J h n) = adicCompletionMapToQuotientPow f I J h k := by
  ext x
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  have hk : AdicCompletion.evalₐ I k x = Ideal.Quotient.mk (I ^ k) r := by
    rw [← factorPow_evalₐ I hle, ← hr]
    rfl
  simp only [adicCompletionMapToQuotientPow, RingHom.comp_apply, RingHom.coe_coe]
  rw [← hr, hk, Ideal.quotientMap_mk, Ideal.quotientMap_mk]
  rfl

def cmap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (I : Ideal A) (J : Ideal B)
    (h : I.map f ≤ J) : AdicCompletion I A →+* AdicCompletion J B :=
  AdicCompletion.liftRingHom J (adicCompletionMapToQuotientPow f I J h) (factorPow_comp_adicCompletionMapToQuotientPow f I J h)

theorem evalₐ_cmap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (I : Ideal A) (J : Ideal B)
    (h : I.map f ≤ J) (n : ℕ) (x : AdicCompletion I A) :
    AdicCompletion.evalₐ J n (cmap f I J h x) =
      Ideal.quotientMap (J ^ n) f (pow_le_comap f h n) (AdicCompletion.evalₐ I n x) :=
  AdicCompletion.evalₐ_liftRingHom J _ (factorPow_comp_adicCompletionMapToQuotientPow f I J h) n x

theorem cmap_of {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (I : Ideal A) (J : Ideal B)
    (h : I.map f ≤ J) (a : A) : cmap f I J h (AdicCompletion.of I A a) = AdicCompletion.of J B (f a) := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [evalₐ_cmap, AdicCompletion.evalₐ_of, AdicCompletion.evalₐ_of, Ideal.quotientMap_mk]

theorem map_algebraMap_le {A B B' : Type} [CommRing A] [CommRing B] [CommRing B'] [Algebra A B] [Algebra A B']
    (g : B →ₐ[A] B') (J : Ideal A) : (J.map (algebraMap A B)).map (g : B →+* B') ≤ J.map (algebraMap A B') := by
  rw [Ideal.map_map, g.comp_algebraMap]

def galAlg {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (σ : GlobalTheory.Mum.Gal (algebraMap R R')) :
    R' →ₐ[R] R' :=
  { σ.1.toRingHom with commutes' := σ.2 }

def galTensor {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (O : Type) [CommRing O] [Algebra R O]
    (σ : GlobalTheory.Mum.Gal (algebraMap R R')) : TensorProduct R O R' →ₐ[O] TensorProduct R O R' :=
  Algebra.TensorProduct.map (AlgHom.id O O) (galAlg σ)

@[simp] theorem galTensor_tmul {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (O : Type) [CommRing O]
    [Algebra R O] (σ : GlobalTheory.Mum.Gal (algebraMap R R')) (x : O) (y : R') :
    galTensor O σ (x ⊗ₜ[R] y) = x ⊗ₜ[R] σ.1 y := rfl

end GlobalTheory.InvAlg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicCompletionEquivariantEquivOfLevelIsos
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicCompletionEquivariantEquivOfLevelIsos
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.InvAlg.Levels

abbrev red {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (I : Ideal A) {k n : ℕ} (h : k ≤ n) :
    A ⧸ I ^ n →ₐ[R] A ⧸ I ^ k :=
  Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right h)

theorem red_red {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (I : Ideal A) {k l n : ℕ} (h₁ : k ≤ l)
    (h₂ : l ≤ n) (z : A ⧸ I ^ n) : red (R := R) I h₁ (red (R := R) I h₂ z) = red (R := R) I (h₁.trans h₂) z := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  rfl

theorem red_refl {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (I : Ideal A) {n : ℕ}
    (z : A ⧸ I ^ n) : red (R := R) I (le_refl n) z = z := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  rfl

theorem red_evalₐ {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (I : Ideal A) {k n : ℕ} (h : k ≤ n)
    (x : AdicCompletion I A) :
    red (R := R) I h (AdicCompletion.evalₐ I n x) = AdicCompletion.evalₐ I k x :=
  GlobalTheory.InvAlg.factorPow_evalₐ I h x

theorem compat_le {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (I : Ideal A) (J : Ideal B) (β : ∀ n : ℕ, A ⧸ I ^ (n + 1) →ₐ[R] B ⧸ J ^ (n + 1))
    (hβ : ∀ n z, red (R := R) J (Nat.le_succ (n + 1)) (β (n + 1) z) = β n (red (R := R) I (Nat.le_succ (n + 1)) z))
    {k n : ℕ} (h : k ≤ n) (z : A ⧸ I ^ (n + 1)) :
    red (R := R) J (Nat.succ_le_succ h) (β n z) = β k (red (R := R) I (Nat.succ_le_succ h) z) := by
  induction n, h using Nat.le_induction with
  | base => rw [red_refl, red_refl]
  | succ n hkn ih =>
    rw [← red_red (R := R) J (Nat.succ_le_succ hkn) (Nat.le_succ (n + 1)), hβ, ih, red_red]

theorem exists_equiv {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (I : Ideal A) (J : Ideal B) (β : ∀ n : ℕ, (A ⧸ I ^ (n + 1)) ≃ₐ[R] (B ⧸ J ^ (n + 1)))
    (hβ : ∀ n z, red (R := R) J (Nat.le_succ (n + 1)) (β (n + 1) z) = β n (red (R := R) I (Nat.le_succ (n + 1)) z)) :
    ∃ Ψ : AdicCompletion I A ≃ₐ[R] AdicCompletion J B,
      ∀ n y, AdicCompletion.evalₐ J (n + 1) (Ψ y) = β n (AdicCompletion.evalₐ I (n + 1) y) := by
  have hβ' : ∀ n z, red (R := R) I (Nat.le_succ (n + 1)) ((β (n + 1)).symm z) =
      (β n).symm (red (R := R) J (Nat.le_succ (n + 1)) z) := by
    intro n z
    apply (β n).injective
    rw [AlgEquiv.apply_symm_apply, ← hβ, AlgEquiv.apply_symm_apply]
  have key : ∀ {A B : Type} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (I : Ideal A) (J : Ideal B)
      (β : ∀ n : ℕ, A ⧸ I ^ (n + 1) →ₐ[R] B ⧸ J ^ (n + 1))
      (hβ : ∀ n z, red (R := R) J (Nat.le_succ (n + 1)) (β (n + 1) z) = β n (red (R := R) I (Nat.le_succ (n + 1)) z)),
      ∃ Φ : AdicCompletion I A →ₐ[R] AdicCompletion J B,
        ∀ n y, AdicCompletion.evalₐ J (n + 1) (Φ y) = β n (AdicCompletion.evalₐ I (n + 1) y) := by
    intro A B _ _ _ _ I J β hβ
    let f : ∀ n, AdicCompletion I A →ₐ[R] B ⧸ J ^ n := fun n =>
      (red (R := R) J (Nat.le_succ n)).comp ((β n).comp ((AdicCompletion.evalₐ I (n + 1)).restrictScalars R))
    have hf : ∀ {k n : ℕ} (hle : k ≤ n), (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hle)).comp (f n) = f k := by
      intro k n hle
      refine AlgHom.ext fun y => ?_
      change red (R := R) J hle (red (R := R) J (Nat.le_succ n) (β n (AdicCompletion.evalₐ I (n + 1) y))) =
        red (R := R) J (Nat.le_succ k) (β k (AdicCompletion.evalₐ I (k + 1) y))
      rw [red_red, ← red_red (R := R) J (Nat.le_succ k) (Nat.succ_le_succ hle), compat_le I J β hβ hle, red_evalₐ]
    refine ⟨AdicCompletion.liftAlgHom J f hf, fun n y => ?_⟩
    rw [AdicCompletion.evalₐ_liftAlgHom]
    change red (R := R) J (Nat.le_succ (n + 1)) (β (n + 1) (AdicCompletion.evalₐ I (n + 1 + 1) y)) = _
    rw [hβ, red_evalₐ]
  obtain ⟨Φ, hΦ⟩ := key I J (fun n => (β n).toAlgHom) hβ
  obtain ⟨Φ', hΦ'⟩ := key J I (fun n => (β n).symm.toAlgHom) hβ'
  have ev : ∀ {A : Type} [CommRing A] [Algebra R A] (I : Ideal A) (x y : AdicCompletion I A),
      (∀ n, AdicCompletion.evalₐ I (n + 1) x = AdicCompletion.evalₐ I (n + 1) y) → x = y := by
    intro A _ _ I x y h
    refine AdicCompletion.ext_evalₐ fun n => ?_
    rw [← red_evalₐ (R := R) I (Nat.le_succ n) x, ← red_evalₐ (R := R) I (Nat.le_succ n) y, h]
  refine ⟨AlgEquiv.ofAlgHom Φ Φ' ?_ ?_, hΦ⟩
  · refine AlgHom.ext fun y => ?_
    refine ev J _ _ fun n => ?_
    simp only [AlgHom.comp_apply, AlgHom.id_apply]
    rw [hΦ, hΦ']
    exact AlgEquiv.apply_symm_apply _ _
  · refine AlgHom.ext fun y => ?_
    refine ev I _ _ fun n => ?_
    simp only [AlgHom.comp_apply, AlgHom.id_apply]
    rw [hΦ', hΦ]
    exact AlgEquiv.symm_apply_apply _ _

end GlobalTheory.InvAlg.Levels

namespace GlobalTheory.InvAlg.Levels

theorem levels_equiv : ∀ (R : Type) [CommRing R] (m : Ideal R) (R' : Type) [CommRing R'] [Algebra R R'] (C' : Type) [CommRing C']
    [Algebra R C'] [Algebra R' C'] [IsScalarTower R R' C'] (act : GlobalTheory.Mum.Gal (algebraMap R R') →* (C' ≃ₐ[R] C')),
    (∀ σ r, act σ (algebraMap R' C' r) = algebraMap R' C' (σ.1 r)) →
    ∀ (O : Type) [CommRing O] [Algebra R O] (i : ∀ e : ℕ, O →ₐ[R] C' ⧸ (m ^ (e + 1)).map (algebraMap R C')),
    (∀ e x y, Ideal.Quotient.mk _ y = i (e + 1) x → Ideal.Quotient.mk _ y = i e x) →
    (∀ e σ x y, Ideal.Quotient.mk _ y = i e x → Ideal.Quotient.mk _ (act σ y) = i e x) →
    (∀ e, Function.Surjective (Algebra.TensorProduct.lift (i e)
        ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) ∧
      RingHom.ker (Algebra.TensorProduct.lift (i e)
        ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) =
        (m ^ (e + 1)).map (algebraMap R (TensorProduct R O R'))) →
    ∀ (IT : Ideal (TensorProduct R O R')) (IC : Ideal C'), IT = m.map (algebraMap R (TensorProduct R O R')) →
      IC = m.map (algebraMap R C') →
    ∀ (hT : ∀ σ, IT.map (GlobalTheory.InvAlg.galTensor O σ).toRingHom ≤ IT)
      (hC : ∀ σ, IC.map (act σ).toRingEquiv.toRingHom ≤ IC),
    ∃ Ψ : AdicCompletion IT (TensorProduct R O R') ≃ₐ[R] AdicCompletion IC C',
      (∀ σ y, Ψ (GlobalTheory.InvAlg.cmap (GlobalTheory.InvAlg.galTensor O σ).toRingHom
          IT IT (hT σ) y) = GlobalTheory.InvAlg.cmap (act σ).toRingEquiv.toRingHom IC IC (hC σ) (Ψ y)) ∧
      ∀ e (x : O) (y : C'), Ideal.Quotient.mk ((m ^ (e + 1)).map (algebraMap R C')) y = i e x →
        AdicCompletion.evalₐ IC (e + 1) (Ψ (AdicCompletion.of IT _ (x ⊗ₜ[R] (1 : R')))) =
          Ideal.Quotient.mk (IC ^ (e + 1)) y := by
  intro R _ m R' _ _ C' _ _ _ _ act hact O _ _ i hi1 hi2 hi3 IT IC hIT hIC hT hC
  subst hIT hIC
  let L : ∀ e, TensorProduct R O R' →ₐ[R] C' ⧸ (m ^ (e + 1)).map (algebraMap R C') := fun e =>
    Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C'))
      fun _ _ => Commute.all _ _
  have hCpow : ∀ e, (m ^ (e + 1)).map (algebraMap R C') = (m.map (algebraMap R C')) ^ (e + 1) :=
    fun e => Ideal.map_pow _ _ _
  have hTpow : ∀ e, (m ^ (e + 1)).map (algebraMap R (TensorProduct R O R')) =
      (m.map (algebraMap R (TensorProduct R O R'))) ^ (e + 1) :=
    fun e => Ideal.map_pow _ _ _
  let E : ∀ e, (C' ⧸ (m ^ (e + 1)).map (algebraMap R C')) ≃ₐ[R] (C' ⧸ (m.map (algebraMap R C')) ^ (e + 1)) :=
    fun e => Ideal.quotientEquivAlgOfEq R (hCpow e)
  let L' : ∀ e, TensorProduct R O R' →ₐ[R] C' ⧸ (m.map (algebraMap R C')) ^ (e + 1) := fun e =>
    (E e).toAlgHom.comp (L e)
  have hsurj : ∀ e, Function.Surjective (L' e) := fun e => (E e).surjective.comp (hi3 e).1
  have hker : ∀ e, RingHom.ker (L' e) = (m.map (algebraMap R (TensorProduct R O R'))) ^ (e + 1) := by
    intro e
    ext t
    rw [RingHom.mem_ker, ← hTpow, ← (hi3 e).2, RingHom.mem_ker]
    exact map_eq_zero_iff (E e) (E e).injective
  let β : ∀ e, (TensorProduct R O R' ⧸ (m.map (algebraMap R (TensorProduct R O R'))) ^ (e + 1)) ≃ₐ[R]
      (C' ⧸ (m.map (algebraMap R C')) ^ (e + 1)) := fun e =>
    (Ideal.quotientEquivAlgOfEq R (hker e).symm).trans (Ideal.quotientKerAlgEquivOfSurjective (hsurj e))
  have hβmk : ∀ e t, β e (Ideal.Quotient.mk _ t) = L' e t := fun e t => rfl
  have hL : ∀ e x r y, Ideal.Quotient.mk _ y = i e x →
      L' e (x ⊗ₜ[R] r) = Ideal.Quotient.mk _ (y * algebraMap R' C' r) := by
    intro e x r y hy
    change E e (L e (x ⊗ₜ[R] r)) = _
    rw [Algebra.TensorProduct.lift_tmul, ← hy]
    change E e (Ideal.Quotient.mk _ y * Ideal.Quotient.mk _ (algebraMap R' C' r)) = _
    rw [← map_mul]
    exact Ideal.quotientEquivAlgOfEq_mk _ _ _
  have hred : ∀ n z, red (R := R) (m.map (algebraMap R C')) (Nat.le_succ (n + 1)) (β (n + 1) z) =
      β n (red (R := R) (m.map (algebraMap R (TensorProduct R O R'))) (Nat.le_succ (n + 1)) z) := by
    intro n z
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective z
    change red (R := R) (m.map (algebraMap R C')) (Nat.le_succ (n + 1)) (L' (n + 1) t) = L' n t
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x r =>
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (i (n + 1) x)
      rw [hL (n + 1) x r y hy, hL n x r y (hi1 n x y hy)]
      rfl
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  obtain ⟨Ψ, hΨ⟩ := exists_equiv _ _ β hred
  have ev : ∀ {A : Type} [CommRing A] (I : Ideal A) (x y : AdicCompletion I A),
      (∀ n, AdicCompletion.evalₐ I (n + 1) x = AdicCompletion.evalₐ I (n + 1) y) → x = y := by
    intro A _ I x y h
    refine AdicCompletion.ext_evalₐ fun n => ?_
    rw [← GlobalTheory.InvAlg.factorPow_evalₐ I (Nat.le_succ n) x, ← GlobalTheory.InvAlg.factorPow_evalₐ I (Nat.le_succ n) y, h]
  refine ⟨Ψ, fun σ y => ev _ _ _ fun n => ?_, fun e x y hy => ?_⟩
  · rw [hΨ, GlobalTheory.InvAlg.evalₐ_cmap, GlobalTheory.InvAlg.evalₐ_cmap, hΨ]
    obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ _ (n + 1) y)
    rw [← ht, Ideal.quotientMap_mk, hβmk, hβmk]
    clear ht
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x r =>
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (i n x)
      have h1 : (GlobalTheory.InvAlg.galTensor O σ).toRingHom (x ⊗ₜ[R] r) = x ⊗ₜ[R] σ.1 r := rfl
      rw [h1, hL n x _ y hy, hL n x r y hy, Ideal.quotientMap_mk]
      change _ = Ideal.Quotient.mk _ (act σ (y * algebraMap R' C' r))
      rw [map_mul (act σ), hact, map_mul (Ideal.Quotient.mk _), map_mul (Ideal.Quotient.mk _)]
      congr 1
      have h2 := hi2 n σ x y hy
      rw [← hy, Ideal.Quotient.eq, hCpow] at h2
      rw [Ideal.Quotient.eq, ← neg_sub]
      exact neg_mem h2
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  · rw [hΨ, AdicCompletion.evalₐ_of, hβmk, hL e x 1 y hy, map_one, _root_.mul_one]

end GlobalTheory.InvAlg.Levels
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicCompletionEquivariantEquivOfLevelIsosStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adicCompletion_equivariant_equiv_of_level_isos : ∀ (R : Type) [CommRing R] (m : Ideal R) (R' : Type) [CommRing R'] [Algebra R R'] (C' : Type) [CommRing C']
    [Algebra R C'] [Algebra R' C'] [IsScalarTower R R' C'] (act : GlobalTheory.Mum.Gal (algebraMap R R') →* (C' ≃ₐ[R] C')),
    (∀ σ r, act σ (algebraMap R' C' r) = algebraMap R' C' (σ.1 r)) →
    ∀ (O : Type) [CommRing O] [Algebra R O] (i : ∀ e : ℕ, O →ₐ[R] C' ⧸ (m ^ (e + 1)).map (algebraMap R C')),
    (∀ e x y, Ideal.Quotient.mk _ y = i (e + 1) x → Ideal.Quotient.mk _ y = i e x) →
    (∀ e σ x y, Ideal.Quotient.mk _ y = i e x → Ideal.Quotient.mk _ (act σ y) = i e x) →
    (∀ e, Function.Surjective (Algebra.TensorProduct.lift (i e)
        ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) ∧
      RingHom.ker (Algebra.TensorProduct.lift (i e)
        ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) =
        (m ^ (e + 1)).map (algebraMap R (TensorProduct R O R'))) →
    ∀ (IT : Ideal (TensorProduct R O R')) (IC : Ideal C'), IT = m.map (algebraMap R (TensorProduct R O R')) →
      IC = m.map (algebraMap R C') →
    ∀ (hT : ∀ σ, IT.map (GlobalTheory.InvAlg.galTensor O σ).toRingHom ≤ IT)
      (hC : ∀ σ, IC.map (act σ).toRingEquiv.toRingHom ≤ IC),
    ∃ Ψ : AdicCompletion IT (TensorProduct R O R') ≃ₐ[R] AdicCompletion IC C',
      (∀ σ y, Ψ (GlobalTheory.InvAlg.cmap (GlobalTheory.InvAlg.galTensor O σ).toRingHom
          IT IT (hT σ) y) = GlobalTheory.InvAlg.cmap (act σ).toRingEquiv.toRingHom IC IC (hC σ) (Ψ y)) ∧
      ∀ e (x : O) (y : C'), Ideal.Quotient.mk ((m ^ (e + 1)).map (algebraMap R C')) y = i e x →
        AdicCompletion.evalₐ IC (e + 1) (Ψ (AdicCompletion.of IT _ (x ⊗ₜ[R] (1 : R')))) =
          Ideal.Quotient.mk (IC ^ (e + 1)) y := by
  first | exact @GlobalTheory.InvAlg.Levels.levels_equiv | exact GlobalTheory.InvAlg.Levels.levels_equiv | (intros; apply GlobalTheory.InvAlg.Levels.levels_equiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicCompletionRingInjectiveInvariantsOfModule
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicCompletionRingInjectiveInvariantsOfModule
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.InvAlg

section CompletionTransfer

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (J : Ideal A)

theorem pow_smul_top_eq_restrictScalars (n : ℕ) :
    (J ^ n • ⊤ : Submodule A B) =
      ((J.map (algebraMap A B)) ^ n • ⊤ : Submodule B B).restrictScalars A := by
  rw [Ideal.smul_top_eq_map, Ideal.map_pow]
  ext x
  simp [smul_eq_mul, Ideal.mul_top]

def levelEquiv (n : ℕ) :
    (B ⧸ (J ^ n • ⊤ : Submodule A B)) ≃ₗ[A] (B ⧸ ((J.map (algebraMap A B)) ^ n • ⊤ : Submodule B B)) :=
  (Submodule.quotEquivOfEq _ _ (pow_smul_top_eq_restrictScalars J n)).trans
    (Submodule.Quotient.restrictScalarsEquiv A _)

theorem levelEquiv_transitionMap {m n : ℕ} (hmn : m ≤ n) (q : B ⧸ (J ^ n • ⊤ : Submodule A B)) :
    levelEquiv J m (AdicCompletion.transitionMap J B hmn q) =
      AdicCompletion.transitionMap (J.map (algebraMap A B)) B hmn (levelEquiv J n q) := by
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rfl

def complEquivFun (x : AdicCompletion J B) : AdicCompletion (J.map (algebraMap A B)) B :=
  ⟨fun n => levelEquiv J n (x.val n), fun {m n} hmn => by
    rw [← levelEquiv_transitionMap, x.property hmn]⟩

theorem complEquivFun_val (x : AdicCompletion J B) (n : ℕ) :
    (complEquivFun J x).val n = levelEquiv J n (x.val n) := rfl

theorem complEquivFun_injective : Function.Injective (complEquivFun (B := B) J) := by
  intro x y h
  refine AdicCompletion.ext fun n => (levelEquiv J n).injective ?_
  have := congrArg (fun z : AdicCompletion (J.map (algebraMap A B)) B => z.val n) h
  simpa only [complEquivFun_val] using this

theorem complEquivFun_surjective : Function.Surjective (complEquivFun (B := B) J) := by
  intro z
  refine ⟨⟨fun n => (levelEquiv J n).symm (z.val n), fun {m n} hmn => ?_⟩, ?_⟩
  · apply (levelEquiv J m).injective
    rw [levelEquiv_transitionMap, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    exact z.property hmn
  · refine AdicCompletion.ext fun n => ?_
    exact LinearEquiv.apply_symm_apply (levelEquiv J n) (z.val n)

end CompletionTransfer

theorem val_eq_mk_of_evalₐ {R : Type} [CommRing R] (I : Ideal R) (y : AdicCompletion I R) (n : ℕ) (b : R)
    (h : AdicCompletion.evalₐ I n y = Ideal.Quotient.mk _ b) :
    y.val n = Submodule.Quotient.mk b := by
  have hle : I ^ n ≤ (I ^ n • ⊤ : Ideal R) := by rw [smul_eq_mul, Ideal.mul_top]
  rw [← AdicCompletion.eval_apply, ← AdicCompletion.factor_evalₐ_eq_eval I y hle, h]
  rfl

theorem evalₐ_eq_mk_of_val {R : Type} [CommRing R] (I : Ideal R) (y : AdicCompletion I R) (n : ℕ) (b : R)
    (h : y.val n = Submodule.Quotient.mk b) :
    AdicCompletion.evalₐ I n y = Ideal.Quotient.mk _ b := by
  have hle : (I ^ n • ⊤ : Ideal R) ≤ I ^ n := by rw [smul_eq_mul, Ideal.mul_top]
  rw [← AdicCompletion.factor_eval_eq_evalₐ I y hle, AdicCompletion.eval_apply, h]
  rfl

theorem cmap_transfer : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (J : Ideal A) (Γ : Type) (g : Γ → (B →ₐ[A] B)),
    Function.Injective (AdicCompletion.map J (Algebra.linearMap A B)) →
    (∀ y, y ∈ LinearMap.range (AdicCompletion.map J (Algebra.linearMap A B)) ↔
      ∀ σ, AdicCompletion.map J (g σ).toLinearMap y = y) →
    Function.Injective (GlobalTheory.InvAlg.cmap (algebraMap A B) J (J.map (algebraMap A B)) le_rfl) ∧
    ∀ y, y ∈ Set.range (GlobalTheory.InvAlg.cmap (algebraMap A B) J (J.map (algebraMap A B)) le_rfl) ↔
      ∀ σ, GlobalTheory.InvAlg.cmap (g σ).toRingHom (J.map (algebraMap A B)) (J.map (algebraMap A B))
        (GlobalTheory.InvAlg.map_algebraMap_le (g σ) J) y = y := by
  intro A B _ _ _ J Γ g hinj hrange
  have h1 : ∀ x, complEquivFun J (AdicCompletion.map J (Algebra.linearMap A B) x) =
      cmap (algebraMap A B) J (J.map (algebraMap A B)) le_rfl x := by
    intro x
    refine AdicCompletion.ext fun n => ?_
    obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (x.val n)
    rw [complEquivFun_val, AdicCompletion.map_val_apply, ← ha]
    symm
    apply val_eq_mk_of_evalₐ
    rw [evalₐ_cmap, evalₐ_eq_mk_of_val J x n a ha.symm, Ideal.quotientMap_mk]
    rfl
  have h2 : ∀ σ z, complEquivFun J (AdicCompletion.map J (g σ).toLinearMap z) =
      cmap (g σ).toRingHom (J.map (algebraMap A B)) (J.map (algebraMap A B))
        (map_algebraMap_le (g σ) J) (complEquivFun J z) := by
    intro σ z
    refine AdicCompletion.ext fun n => ?_
    obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (z.val n)
    rw [complEquivFun_val, AdicCompletion.map_val_apply, ← hb]
    symm
    apply val_eq_mk_of_evalₐ
    refine (evalₐ_cmap _ _ _ _ n _).trans ?_
    rw [evalₐ_eq_mk_of_val _ (complEquivFun J z) n b
      (by rw [complEquivFun_val, ← hb]; rfl), Ideal.quotientMap_mk]
    rfl
  refine ⟨fun x y hxy => hinj (complEquivFun_injective J (by rw [h1, h1, hxy])), fun y => ?_⟩
  obtain ⟨z, rfl⟩ := complEquivFun_surjective J y
  constructor
  · rintro ⟨x, hx⟩ σ
    have hz : z ∈ LinearMap.range (AdicCompletion.map J (Algebra.linearMap A B)) :=
      ⟨x, complEquivFun_injective J (by rw [h1, hx])⟩
    rw [← h2, (hrange z).1 hz σ]
  · intro h
    obtain ⟨x, hx⟩ := (hrange z).2 fun σ => complEquivFun_injective J (by rw [h2, h σ])
    exact ⟨x, by rw [← h1, hx]⟩

end GlobalTheory.InvAlg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicCompletionRingInjectiveInvariantsOfModuleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adicCompletion_ring_injective_invariants_of_module : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (J : Ideal A) (Γ : Type) (g : Γ → (B →ₐ[A] B)),
    Function.Injective (AdicCompletion.map J (Algebra.linearMap A B)) →
    (∀ y, y ∈ LinearMap.range (AdicCompletion.map J (Algebra.linearMap A B)) ↔
      ∀ σ, AdicCompletion.map J (g σ).toLinearMap y = y) →
    Function.Injective (GlobalTheory.InvAlg.cmap (algebraMap A B) J (J.map (algebraMap A B)) le_rfl) ∧
    ∀ y, y ∈ Set.range (GlobalTheory.InvAlg.cmap (algebraMap A B) J (J.map (algebraMap A B)) le_rfl) ↔
      ∀ σ, GlobalTheory.InvAlg.cmap (g σ).toRingHom (J.map (algebraMap A B)) (J.map (algebraMap A B))
        (GlobalTheory.InvAlg.map_algebraMap_le (g σ) J) y = y := by
  first | exact @GlobalTheory.InvAlg.cmap_transfer | exact GlobalTheory.InvAlg.cmap_transfer | (intros; apply GlobalTheory.InvAlg.cmap_transfer <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTensorGaloisInjectiveInvariants
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTensorGaloisInjectiveInvariants
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.InvAlg

open TensorProduct

def galDiff (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] :
    R' →ₗ[R] (GlobalTheory.Mum.Gal (algebraMap R R') → R') :=
  LinearMap.pi fun σ => (galAlg σ).toLinearMap - LinearMap.id

theorem galDiff_apply {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (x : R')
    (σ : GlobalTheory.Mum.Gal (algebraMap R R')) : galDiff R R' x σ = σ.1 x - x := rfl

theorem flat_tensor_invariants (R R' O : Type) [CommRing R] [CommRing R'] [Algebra R R'] [CommRing O] [Algebra R O]
    [Module.Flat R O] :
    Function.Injective (algebraMap R R') → GlobalTheory.Mum.IsGal (algebraMap R R') →
    Function.Injective (algebraMap O (TensorProduct R O R')) ∧
    ∀ t : TensorProduct R O R', (∀ σ, GlobalTheory.InvAlg.galTensor O σ t = t) →
      t ∈ Set.range (algebraMap O (TensorProduct R O R')) := by
  intro hinj hgal
  classical
  haveI : Finite (GlobalTheory.Mum.Gal (algebraMap R R')) := hgal.1
  haveI : Fintype (GlobalTheory.Mum.Gal (algebraMap R R')) := Fintype.ofFinite _
  let incl : R →ₗ[R] R' := Algebra.linearMap R R'
  have hex : Function.Exact incl (galDiff R R') := by
    intro y
    constructor
    · intro hy
      obtain ⟨r, hr⟩ := hgal.2 y (fun σ hσ => by
        have := congrFun hy ⟨σ, hσ⟩
        rw [galDiff_apply] at this
        simpa [sub_eq_zero] using this)
      exact ⟨r, hr⟩
    · rintro ⟨r, rfl⟩
      funext σ
      simp [incl, galDiff_apply, σ.2 r]
  have hmap : ∀ x : O, LinearMap.lTensor O incl ((TensorProduct.rid R O).symm x) =
      algebraMap O (TensorProduct R O R') x := by
    intro x
    simp [incl, Algebra.TensorProduct.algebraMap_apply]
  refine ⟨?_, ?_⟩
  · intro a b hab
    rw [← hmap, ← hmap] at hab
    exact (TensorProduct.rid R O).symm.injective
      (Module.Flat.lTensor_preserves_injective_linearMap incl hinj hab)
  · intro t ht
    have hcomp : ∀ u : TensorProduct R O R', ∀ σ,
        TensorProduct.piRight R R O (fun _ : GlobalTheory.Mum.Gal (algebraMap R R') => R')
          (LinearMap.lTensor O (galDiff R R') u) σ = galTensor O σ u - u := by
      intro u σ
      induction u using TensorProduct.induction_on with
      | zero => simp
      | tmul x y =>
        rw [LinearMap.lTensor_tmul, TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]
        show x ⊗ₜ[R] galDiff R R' y σ = _
        rw [galDiff_apply, galTensor_tmul, TensorProduct.tmul_sub]
      | add u v hu hv =>
        rw [map_add (f := _), map_add (f := _), Pi.add_apply, hu, hv, map_add (f := _)]
        abel
    have h0 : LinearMap.lTensor O (galDiff R R') t = 0 := by
      apply (TensorProduct.piRight R R O (fun _ : GlobalTheory.Mum.Gal (algebraMap R R') => R')).injective
      funext σ
      rw [hcomp, ht σ, sub_self, map_zero, Pi.zero_apply]
    obtain ⟨y, hy⟩ := (Module.Flat.lTensor_exact O hex t).1 h0
    refine ⟨TensorProduct.rid R O y, ?_⟩
    rw [← hmap, LinearEquiv.symm_apply_apply, hy]

end GlobalTheory.InvAlg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTensorGaloisInjectiveInvariantsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_tensor_galois_injective_invariants : ∀ (R R' O : Type) [CommRing R] [CommRing R'] [Algebra R R'] [CommRing O] [Algebra R O] [Module.Flat R O],
    Function.Injective (algebraMap R R') → GlobalTheory.Mum.IsGal (algebraMap R R') →
    Function.Injective (algebraMap O (TensorProduct R O R')) ∧
    ∀ t : TensorProduct R O R', (∀ σ, GlobalTheory.InvAlg.galTensor O σ t = t) →
      t ∈ Set.range (algebraMap O (TensorProduct R O R')) := by
  first | exact @GlobalTheory.InvAlg.flat_tensor_invariants | exact GlobalTheory.InvAlg.flat_tensor_invariants | (intros; apply GlobalTheory.InvAlg.flat_tensor_invariants <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicCompletionMapInvariants
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapSubApply
namespace GlobalTheory.LinearMapDifferenceFormula

open AdicCompletion

theorem map_sub_apply {A : Type} [CommRing A] (J : Ideal A) {M P : Type} [AddCommGroup M] [Module A M]
    [AddCommGroup P] [Module A P] (h k : M →ₗ[A] P) (y : AdicCompletion J M) :
    AdicCompletion.map J (h - k) y = AdicCompletion.map J h y - AdicCompletion.map J k y := by
  induction y using AdicCompletion.induction_on with
  | h a =>
    ext n
    simp

theorem main : ∀ (A : Type) [inst : CommRing A] [IsNoetherianRing A] (J : Ideal A) (N M : Type) [inst_2 : AddCommGroup N] [inst_3 : Module A N] [inst_4 : AddCommGroup M] [inst_5 : Module A M] [Module.Finite A M] (f : N →ₗ[A] M) (Γ : Type) [Finite Γ] (g : Γ → M →ₗ[A] M), Function.Injective (⇑f : N → M) → (∀ (x : M), x ∈ LinearMap.range f ↔ ∀ (σ : Γ), (g σ : M → M) x = x) → Function.Injective (⇑(AdicCompletion.map J f) : AdicCompletion J N → AdicCompletion J M) ∧ ∀ (y : AdicCompletion J M), y ∈ LinearMap.range (AdicCompletion.map J f) ↔ ∀ (σ : Γ), (AdicCompletion.map J (g σ) : AdicCompletion J M → AdicCompletion J M) y = y := by
  intro A _ _ J N M _ _ _ _ _ f Γ _ g hf hfix
  classical
  haveI : Fintype Γ := Fintype.ofFinite Γ
  refine ⟨AdicCompletion.map_injective J hf, ?_⟩

  let φ : M →ₗ[A] (Γ → M) := LinearMap.pi (fun σ => g σ - LinearMap.id)
  let ψ : M →ₗ[A] LinearMap.range φ := φ.rangeRestrict
  have hψs : Function.Surjective ψ := LinearMap.surjective_rangeRestrict φ
  have hφ0 : ∀ x, φ x = 0 ↔ ∀ σ, g σ x = x := by
    intro x
    simp only [φ, funext_iff, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply,
      Pi.zero_apply, sub_eq_zero]
  have hex : Function.Exact f ψ := by
    intro x
    have : ψ x = 0 ↔ φ x = 0 := by
      simp [ψ, Subtype.ext_iff]
    rw [this, hφ0, ← hfix]
    rfl
  have hE := AdicCompletion.map_exact (I := J) hf hex hψs
  have hinj : Function.Injective (AdicCompletion.map J (LinearMap.range φ).subtype) :=
    AdicCompletion.map_injective J (Submodule.injective_subtype _)
  have hcomp : (LinearMap.range φ).subtype ∘ₗ ψ = φ := by
    ext x; simp [ψ]
  intro y
  rw [LinearMap.mem_range, ← Set.mem_range, ← hE y]
  have h1 : AdicCompletion.map J ψ y = 0 ↔ AdicCompletion.map J φ y = 0 := by
    have e : AdicCompletion.map J φ y = AdicCompletion.map J (LinearMap.range φ).subtype (AdicCompletion.map J ψ y) := by
      rw [AdicCompletion.map_comp_apply, hcomp]
    rw [e]
    constructor
    · intro h; rw [h, _root_.map_zero]
    · intro h; exact hinj (by rw [h, _root_.map_zero])
  rw [h1]
  have hpi : AdicCompletion.map J φ y = 0 ↔ ∀ σ, AdicCompletion.map J (LinearMap.proj σ) (AdicCompletion.map J φ y) = 0 := by
    constructor
    · intro h σ; rw [h, _root_.map_zero]
    · intro h
      apply (AdicCompletion.piEquivOfFintype J (fun _ : Γ => M)).injective
      rw [_root_.map_zero, AdicCompletion.piEquivOfFintype_apply]
      funext σ
      exact h σ
  rw [hpi]
  refine forall_congr' fun σ => ?_
  rw [AdicCompletion.map_comp_apply]
  have : (LinearMap.proj σ : (Γ → M) →ₗ[A] M) ∘ₗ φ = g σ - LinearMap.id := by
    ext x; simp [φ]
  rw [this, map_sub_apply, AdicCompletion.map_id, LinearMap.id_apply, sub_eq_zero]

end GlobalTheory.LinearMapDifferenceFormula
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicCompletionMapInvariants
namespace GlobalTheory


open AdicCompletion in
theorem adicCompletion_map_invariants : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (J : Ideal A) (N M : Type) [AddCommGroup N] [Module A N]
    [AddCommGroup M] [Module A M] [Module.Finite A M] (f : N →ₗ[A] M) (Γ : Type) [Finite Γ] (g : Γ → (M →ₗ[A] M)),
    Function.Injective f → (∀ x, x ∈ LinearMap.range f ↔ ∀ σ, g σ x = x) →
    Function.Injective (AdicCompletion.map J f) ∧
      ∀ y, y ∈ LinearMap.range (AdicCompletion.map J f) ↔ ∀ σ, AdicCompletion.map J (g σ) y = y := by
  first
  | exact @_root_.GlobalTheory.LinearMapDifferenceFormula.main
  | exact _root_.GlobalTheory.LinearMapDifferenceFormula.main
  | (apply _root_.GlobalTheory.LinearMapDifferenceFormula.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.LinearMapDifferenceFormula.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LinearMapDifferenceFormula.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LinearMapDifferenceFormula.main ..)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicCompletionMapInvariantsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adicCompletion_map_injective_and_invariants : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (J : Ideal A) (N M : Type) [AddCommGroup N] [Module A N]
    [AddCommGroup M] [Module A M] [Module.Finite A M] (f : N →ₗ[A] M) (Γ : Type) [Finite Γ] (g : Γ → (M →ₗ[A] M)),
    Function.Injective f → (∀ x, x ∈ LinearMap.range f ↔ ∀ σ, g σ x = x) →
    Function.Injective (AdicCompletion.map J f) ∧
      ∀ y, y ∈ LinearMap.range (AdicCompletion.map J f) ↔ ∀ σ, AdicCompletion.map J (g σ) y = y := by
  first | exact @GlobalTheory.adicCompletion_map_invariants | exact GlobalTheory.adicCompletion_map_invariants | (intros; apply GlobalTheory.adicCompletion_map_invariants <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletionGaloisInvariantsAgreeModMaxIdealPow
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.InvAlg

theorem ker_evalₐ {A : Type} [CommRing A] [IsNoetherianRing A] (J : Ideal A) (n : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ J n) = (J ^ n).map (algebraMap A (AdicCompletion J A)) := by
  ext a
  rw [RingHom.mem_ker, ← Submodule.restrictScalars_mem A, ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval J.fg_of_isNoetherianRing, LinearMap.mem_ker]
  have hle : (J ^ n • ⊤ : Ideal A) ≤ J ^ n := by intro x hx; simpa using hx
  rw [← AdicCompletion.factor_eval_eq_evalₐ J a hle]
  constructor
  · intro h
    obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval J A n a)
    rw [← hb] at h ⊢
    have : b ∈ J ^ n := Ideal.Quotient.eq_zero_iff_mem.mp h
    exact (Submodule.Quotient.mk_eq_zero _).mpr (by simpa using this)
  · intro h; rw [h, map_zero]

theorem completion_invariants_agree : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] [Module.Finite R R'], Function.Injective (algebraMap R R') → IsGal (algebraMap R R') → ∀ (C' : Type) [CommRing C'] [Algebra R C'] [Algebra R' C'] [IsScalarTower R R' C'] [Algebra.FiniteType R' C'] (act : Gal (algebraMap R R') →* (C' ≃ₐ[R] C')), (∀ σ r, act σ (algebraMap R' C' r) = algebraMap R' C' (σ.1 r)) → ∀ (O : Type) [CommRing O] [Algebra R O] [Module.Flat R O] [Algebra.FiniteType R O] (i : ∀ e : ℕ, O →ₐ[R] C' ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R C')), (∀ e x y, Ideal.Quotient.mk _ y = i (e + 1) x → Ideal.Quotient.mk _ y = i e x) → (∀ e σ x y, Ideal.Quotient.mk _ y = i e x → Ideal.Quotient.mk _ (act σ y) = i e x) → (∀ e, Function.Surjective (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) ∧ RingHom.ker (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) = (maximalIdeal R ^ (e + 1)).map (algebraMap R (TensorProduct R O R'))) → ∀ C : Subalgebra R C', (∀ x, x ∈ C ↔ ∀ σ, act σ x = x) → Algebra.FiniteType R C → Module.Finite C C' → ∀ e : ℕ, ∃ gm : (O ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R O)) ≃ₐ[R] (C ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R C)), ∀ (x : O) (c : C), gm (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ c → Ideal.Quotient.mk ((maximalIdeal R ^ (e + 1)).map (algebraMap R C')) (c : C') = i e x := by
  intro R _ _ _ hR R' _ _ _ _ hinj hgal C' _ _ _ _ _ act hact O _ _ _ _ i h1 h2 h3 C hC hCft hCfin e
  classical
  haveI : IsNoetherianRing R := hR.1
  haveI := hCft
  haveI := hCfin
  haveI : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing R C
  haveI : IsNoetherianRing O := Algebra.FiniteType.isNoetherianRing R O
  haveI : Finite (Gal (algebraMap R R')) := hgal.1
  let T := TensorProduct R O R'
  let JC : Ideal C := (maximalIdeal R).map (algebraMap R C)
  let JO : Ideal O := (maximalIdeal R).map (algebraMap R O)
  let IC : Ideal C' := JC.map (algebraMap C C')
  let IT : Ideal T := JO.map (algebraMap O T)
  let gC : Gal (algebraMap R R') → (C' →ₐ[C] C') := fun σ =>
    { (act σ).toRingEquiv.toRingHom with commutes' := fun c => (hC _).1 c.2 σ }

  have hfixC : ∀ x : C', x ∈ LinearMap.range (Algebra.linearMap C C') ↔ ∀ σ, (gC σ).toLinearMap x = x := by
    intro x; constructor
    · rintro ⟨c, rfl⟩ σ; exact (gC σ).commutes c
    · intro hx; exact ⟨⟨x, (hC x).2 hx⟩, rfl⟩
  have hmC := GlobalTheory.T.adicCompletion_map_injective_and_invariants C JC C C' (Algebra.linearMap C C') _ (fun σ => (gC σ).toLinearMap) Subtype.val_injective hfixC
  obtain ⟨injC, rangeC⟩ := GlobalTheory.T.adicCompletion_ring_injective_invariants_of_module C C' JC _ gC hmC.1 hmC.2

  obtain ⟨injOT, fixOT⟩ := GlobalTheory.T.flat_tensor_galois_injective_invariants R R' O hinj hgal
  have hfixO : ∀ t : T, t ∈ LinearMap.range (Algebra.linearMap O T) ↔
      ∀ σ, (galTensor O σ).toLinearMap t = t := by
    intro t; constructor
    · rintro ⟨x, rfl⟩ σ; exact (galTensor O σ).commutes x
    · intro ht; obtain ⟨x, hx⟩ := fixOT t ht; exact ⟨x, hx⟩
  have hmO := GlobalTheory.T.adicCompletion_map_injective_and_invariants O JO O T (Algebra.linearMap O T) _ (fun σ => (galTensor O σ).toLinearMap) injOT hfixO
  obtain ⟨injO, rangeO⟩ := GlobalTheory.T.adicCompletion_ring_injective_invariants_of_module O T JO _ (galTensor O) hmO.1 hmO.2

  have hIT : IT = (maximalIdeal R).map (algebraMap R T) := by
    simp only [IT, JO, Ideal.map_map]; rw [← IsScalarTower.algebraMap_eq]
  have hIC : IC = (maximalIdeal R).map (algebraMap R C') := by
    simp only [IC, JC, Ideal.map_map]; rw [← IsScalarTower.algebraMap_eq]
  have hCσ : ∀ σ, IC.map (act σ).toRingEquiv.toRingHom ≤ IC := fun σ => map_algebraMap_le (gC σ) JC
  obtain ⟨Ψ, hΨσ, hΨi⟩ := GlobalTheory.T.adicCompletion_equivariant_equiv_of_level_isos R (maximalIdeal R) R' C' act hact O i h1 h2 h3 IT IC hIT hIC
    (fun σ => map_algebraMap_le (galTensor O σ) JO) hCσ
  let κC := cmap (algebraMap C C') JC IC le_rfl
  let κO1 := cmap (algebraMap O T) JO IT le_rfl
  let κO : AdicCompletion JO O →+* AdicCompletion IC C' := (Ψ : _ →+* _).comp κO1
  have hr : ∀ y, y ∈ Set.range κO ↔ y ∈ Set.range κC := by
    intro y
    rw [rangeC y]
    have : y ∈ Set.range κO ↔ Ψ.symm y ∈ Set.range κO1 := by
      constructor
      · rintro ⟨a, rfl⟩; exact ⟨a, by simp [κO]⟩
      · rintro ⟨a, ha⟩; exact ⟨a, by simp [κO, ha]⟩
    rw [this, rangeO]
    refine forall_congr' fun σ => ?_
    rw [← Ψ.injective.eq_iff, hΨσ, Ψ.apply_symm_apply]
  have hrange : κO.range = κC.range := by ext y; exact hr y
  have injκO : Function.Injective κO := Ψ.injective.comp injO
  let eO : AdicCompletion JO O ≃+* κO.range := RingEquiv.ofBijective κO.rangeRestrict
    ⟨fun a b h => injκO (congrArg Subtype.val h), κO.rangeRestrict_surjective⟩
  let eC : AdicCompletion JC C ≃+* κC.range := RingEquiv.ofBijective κC.rangeRestrict
    ⟨fun a b h => injC (congrArg Subtype.val h), κC.rangeRestrict_surjective⟩
  let Θ : AdicCompletion JO O ≃+* AdicCompletion JC C := (eO.trans (RingEquiv.subringCongr hrange)).trans eC.symm
  have hΘ : ∀ a, κC (Θ a) = κO a := fun a =>
    congrArg Subtype.val (eC.apply_symm_apply ((RingEquiv.subringCongr hrange) (eO a)))

  have hΘR : ∀ r : R, Θ (algebraMap R _ r) = algebraMap R _ r := by
    intro r
    apply injC
    rw [hΘ]
    show Ψ (κO1 (algebraMap R (AdicCompletion JO O) r)) = κC (algebraMap R (AdicCompletion JC C) r)
    rw [AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply, cmap_of, cmap_of,
      ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      ← AdicCompletion.algebraMap_apply IT r, ← AdicCompletion.algebraMap_apply IC r]
    exact Ψ.commutes r
  have hOm : ∀ k, (JO ^ k).map (algebraMap O (AdicCompletion JO O)) =
      ((maximalIdeal R) ^ k).map (algebraMap R (AdicCompletion JO O)) := by
    intro k; simp only [JO, Ideal.map_pow, Ideal.map_map]; rfl
  have hCm : ∀ k, (JC ^ k).map (algebraMap C (AdicCompletion JC C)) =
      ((maximalIdeal R) ^ k).map (algebraMap R (AdicCompletion JC C)) := by
    intro k; simp only [JC, Ideal.map_pow, Ideal.map_map]; rfl
  have key : ∀ a, AdicCompletion.evalₐ JC (e + 1) (Θ a) = 0 ↔ AdicCompletion.evalₐ JO (e + 1) a = 0 := by
    intro a
    rw [← RingHom.mem_ker, ← RingHom.mem_ker, ker_evalₐ, ker_evalₐ, hOm, hCm]
    have hmap : ((maximalIdeal R ^ (e + 1)).map (algebraMap R (AdicCompletion JC C))) =
        ((maximalIdeal R ^ (e + 1)).map (algebraMap R (AdicCompletion JO O))).map (Θ : _ →+* _) := by
      rw [Ideal.map_map]; congr 1; exact RingHom.ext fun r => (hΘR r).symm
    rw [hmap, Ideal.map_comap_of_equiv, Ideal.mem_comap, RingEquiv.symm_apply_apply]
  have hJC : JC ^ (e + 1) = ((maximalIdeal R) ^ (e + 1)).map (algebraMap R C) := (Ideal.map_pow _ _ _).symm
  let ψ0 : O →+* C ⧸ JC ^ (e + 1) :=
    (AdicCompletion.evalₐ JC (e + 1) : AdicCompletion JC C →+* C ⧸ JC ^ (e + 1)).comp
      ((Θ : _ →+* _).comp (algebraMap O (AdicCompletion JO O)))
  have hψ0 : ∀ x, ψ0 x = AdicCompletion.evalₐ JC (e + 1) (Θ (AdicCompletion.of JO O x)) := fun x => rfl
  have hsurj : Function.Surjective ψ0 := by
    intro z
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective
      (AdicCompletion.evalₐ JO (e + 1) (Θ.symm (AdicCompletion.of JC C c)))
    refine ⟨x, ?_⟩
    have h0 : AdicCompletion.evalₐ JO (e + 1)
        (AdicCompletion.of JO O x - Θ.symm (AdicCompletion.of JC C c)) = 0 := by
      rw [map_sub, AdicCompletion.evalₐ_of, hx, sub_self]
    have h1 := (key _).2 h0
    rw [map_sub, map_sub, RingEquiv.apply_symm_apply, AdicCompletion.evalₐ_of, sub_eq_zero] at h1
    rw [hψ0, h1]
  have hker : RingHom.ker ψ0 = ((maximalIdeal R) ^ (e + 1)).map (algebraMap R O) := by
    ext x
    rw [RingHom.mem_ker, hψ0, key, AdicCompletion.evalₐ_of, Ideal.Quotient.eq_zero_iff_mem]
    simp only [JO, Ideal.map_pow]
  let gR : (O ⧸ ((maximalIdeal R) ^ (e + 1)).map (algebraMap R O)) ≃+*
      (C ⧸ ((maximalIdeal R) ^ (e + 1)).map (algebraMap R C)) :=
    ((Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)).trans
      (Ideal.quotEquivOfEq hJC)
  have hgR : ∀ x, gR (Ideal.Quotient.mk _ x) = Ideal.quotEquivOfEq hJC (ψ0 x) := fun x => rfl
  let gm : (O ⧸ ((maximalIdeal R) ^ (e + 1)).map (algebraMap R O)) ≃ₐ[R]
      (C ⧸ ((maximalIdeal R) ^ (e + 1)).map (algebraMap R C)) :=
    AlgEquiv.ofRingEquiv (f := gR) (fun r => by
      change gR (Ideal.Quotient.mk _ (algebraMap R O r)) = Ideal.Quotient.mk _ (algebraMap R C r)
      rw [hgR, hψ0, ← AdicCompletion.algebraMap_apply JO r, hΘR, AdicCompletion.algebraMap_apply,
        AdicCompletion.evalₐ_of, Ideal.quotEquivOfEq_mk])
  refine ⟨gm, fun x c hxc => ?_⟩
  have h1' : ψ0 x = Ideal.Quotient.mk (JC ^ (e + 1)) c := by
    apply (Ideal.quotEquivOfEq hJC).injective
    rw [Ideal.quotEquivOfEq_mk]; exact (hgR x).symm.trans hxc
  have h2' : AdicCompletion.evalₐ IC (e + 1) (Ψ (AdicCompletion.of IT T (x ⊗ₜ[R] (1 : R')))) =
      Ideal.Quotient.mk (IC ^ (e + 1)) (c : C') := by
    have := congrArg (Ideal.quotientMap (IC ^ (e + 1)) (algebraMap C C')
      (pow_le_comap (algebraMap C C') (le_rfl : JC.map (algebraMap C C') ≤ IC) (e + 1))) h1'
    rw [hψ0, ← evalₐ_cmap] at this
    change AdicCompletion.evalₐ IC (e + 1) (κC (Θ _)) = _ at this
    rw [hΘ] at this
    rw [show κO (AdicCompletion.of JO O x) = Ψ (AdicCompletion.of IT T (x ⊗ₜ[R] (1 : R'))) from by
      show Ψ (κO1 _) = _
      rw [cmap_of]; rfl] at this
    rw [this, Ideal.quotientMap_mk]; rfl
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (i e x)
  have h3' := hΨi e x y hy
  rw [h2', Ideal.Quotient.eq] at h3'
  rw [← hy, Ideal.Quotient.eq]
  have hpow : IC ^ (e + 1) = ((maximalIdeal R) ^ (e + 1)).map (algebraMap R C') := by rw [hIC, Ideal.map_pow]
  rw [← hpow]; exact h3'

end GlobalTheory.InvAlg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletionGaloisInvariantsAgreeModMaxIdealPowStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completion_galoisInvariants_agree_mod_maxIdeal_pow : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] [Module.Finite R R'], Function.Injective (algebraMap R R') → IsGal (algebraMap R R') → ∀ (C' : Type) [CommRing C'] [Algebra R C'] [Algebra R' C'] [IsScalarTower R R' C'] [Algebra.FiniteType R' C'] (act : Gal (algebraMap R R') →* (C' ≃ₐ[R] C')), (∀ σ r, act σ (algebraMap R' C' r) = algebraMap R' C' (σ.1 r)) → ∀ (O : Type) [CommRing O] [Algebra R O] [Module.Flat R O] [Algebra.FiniteType R O] (i : ∀ e : ℕ, O →ₐ[R] C' ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R C')), (∀ e x y, Ideal.Quotient.mk _ y = i (e + 1) x → Ideal.Quotient.mk _ y = i e x) → (∀ e σ x y, Ideal.Quotient.mk _ y = i e x → Ideal.Quotient.mk _ (act σ y) = i e x) → (∀ e, Function.Surjective (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) ∧ RingHom.ker (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) = (maximalIdeal R ^ (e + 1)).map (algebraMap R (TensorProduct R O R'))) → ∀ C : Subalgebra R C', (∀ x, x ∈ C ↔ ∀ σ, act σ x = x) → Algebra.FiniteType R C → Module.Finite C C' → ∀ e : ℕ, ∃ gm : (O ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R O)) ≃ₐ[R] (C ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R C)), ∀ (x : O) (c : C), gm (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ c → Ideal.Quotient.mk ((maximalIdeal R ^ (e + 1)).map (algebraMap R C')) (c : C') = i e x := by
  first | exact @GlobalTheory.InvAlg.completion_invariants_agree | exact GlobalTheory.InvAlg.completion_invariants_agree | (intros; apply GlobalTheory.InvAlg.completion_invariants_agree <;> assumption)
end

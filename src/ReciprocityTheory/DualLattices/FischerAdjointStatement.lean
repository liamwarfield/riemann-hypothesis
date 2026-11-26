module

public import Mathlib

@[expose] public section

section -- merged from ReciprocityTheory.DualLattices.FischerAdjointStatement
noncomputable section

open MvPolynomial Matrix Finset

namespace ReciprocityTheory.PGsh

section Cayley

variable (n : ℕ) (R : Type*) [CommRing R]

abbrev cayDet : MvPolynomial (Fin n × Fin n) R :=
  (Matrix.mvPolynomialX (Fin n) (Fin n) R).det

def cayMono (σ : Equiv.Perm (Fin n)) : Module.End R (MvPolynomial (Fin n × Fin n) R) :=
  ((List.finRange n).map fun j => ((pderiv (σ j, j) : Derivation R _ _) :
    MvPolynomial (Fin n × Fin n) R →ₗ[R] MvPolynomial (Fin n × Fin n) R)).prod

def cayOp : Module.End R (MvPolynomial (Fin n × Fin n) R) :=
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ)) • cayMono n R σ

def CayleyStatement : Prop :=
  ∀ (n : ℕ) (R : Type) [CommRing R] (s : ℕ),
    cayOp n R (cayDet n R ^ s) = (∏ k ∈ range n, (s + k)) • cayDet n R ^ (s - 1)

end Cayley

section Tests

variable (R : Type*) [CommRing R]

end Tests

section HW

variable {ν : ℕ} {ι : Type*}

def rowSubst (g : Matrix (Fin ν) (Fin ν) ℂ) :
    MvPolynomial (Fin ν × ι) ℂ →ₐ[ℂ] MvPolynomial (Fin ν × ι) ℂ :=
  aeval fun p => ∑ l, C (g l p.1) * X (l, p.2)


open scoped Classical in
def fischer (P Q : MvPolynomial (Fin ν × ι) ℂ) : ℂ := by
  classical
  exact ∑ A ∈ P.support ∪ Q.support,
    AddMonoidAlgebra.coeff P A * starRingEnd ℂ (AddMonoidAlgebra.coeff Q A) * ((A.prod fun _ e => e.factorial : ℕ) : ℂ)

def IsUpperUnitri (g : Matrix (Fin ν) (Fin ν) ℂ) : Prop :=
  (∀ i, g i i = 1) ∧ ∀ i j, j < i → g i j = 0

end HW

end ReciprocityTheory.PGsh
end
end

section -- merged from ReciprocityTheory.DualLattices.SqZeroOfSpan
noncomputable section

open IsLocalRing TensorProduct

namespace ReciprocityTheory.PGsh

universe u

structure LAlg (R₀ : Type u) [CommRing R₀] where
  carrier : Type u
  [cr : CommRing carrier]
  [alg : Algebra R₀ carrier]
  [loc : IsLocalRing carrier]

attribute [instance] LAlg.cr LAlg.alg LAlg.loc

variable {R₀ : Type u} [CommRing R₀]

instance : CoeSort (LAlg R₀) (Type u) := ⟨LAlg.carrier⟩

def LHom (R S : LAlg R₀) : Type u := {f : R →ₐ[R₀] S // IsLocalHom (f : R →+* S)}

def LHom.id (R : LAlg R₀) : LHom R R := ⟨AlgHom.id R₀ R, ⟨fun _ h => h⟩⟩

def LHom.comp {R S T : LAlg R₀} (g : LHom S T) (f : LHom R S) : LHom R T :=
  ⟨g.1.comp f.1, ⟨fun a h => f.2.map_nonunit a (g.2.map_nonunit (f.1 a) h)⟩⟩

abbrev LHom.ker {R S : LAlg R₀} (π : LHom R S) : Submodule R₀ R :=
  (RingHom.ker π.1).restrictScalars R₀

def LHom.SqZero {R S : LAlg R₀} (π : LHom R S) : Prop :=
  Function.Surjective π.1 ∧ RingHom.ker π.1 ^ 2 = ⊥

lemma LHom.sqZero_of_span {R S : LAlg R₀} (π : LHom R S) (ξ : (R : Type u))
    (hs : Function.Surjective π.1) (hk : RingHom.ker π.1 = Ideal.span {ξ}) (hξ : ξ * ξ = 0) :
    π.SqZero := by
  unfold ReciprocityTheory.PGsh.LHom.SqZero
  refine ⟨hs, ?_⟩
  rw [hk, Ideal.span_singleton_pow, pow_two, hξ]
  exact Ideal.span_singleton_eq_bot.mpr rfl

def LHom.NilSurj {R S : LAlg R₀} (π : LHom R S) : Prop :=
  Function.Surjective π.1 ∧ ∃ n : ℕ, RingHom.ker π.1 ^ n = ⊥

def IsFibreSq {F R₁ R₂ R : LAlg R₀} (p₁ : LHom F R₁) (p₂ : LHom F R₂) (f₁ : LHom R₁ R)
    (f₂ : LHom R₂ R) : Prop :=
  f₁.1.comp p₁.1 = f₂.1.comp p₂.1 ∧ f₁.NilSurj ∧ f₂.NilSurj ∧
    ∀ a b, f₁.1 a = f₂.1 b → ∃! c, p₁.1 c = a ∧ p₂.1 c = b

def CarriesFibre {X₁ X₂ X Y : Type*} (q₁ : Y → X₁) (q₂ : Y → X₂) (g₁ : X₁ → X) (g₂ : X₂ → X) :
    Prop :=
  ∀ a b, g₁ a = g₂ b → ∃! c, q₁ c = a ∧ q₂ c = b

structure BX (R₀ : Type u) [CommRing R₀] where
  G : LAlg R₀ → Type u
  [grp : ∀ R, AddCommGroup (G R)]
  map : ∀ {R S : LAlg R₀}, LHom R S → G R →+ G S
  map_id : ∀ (R : LAlg R₀) (x : G R), map (LHom.id R) x = x
  map_comp : ∀ {R S T : LAlg R₀} (f : LHom R S) (g : LHom S T) (x : G R),
    map (g.comp f) x = map g (map f x)
  gg : Type u
  [ggg : AddCommGroup gg]
  [ggm : Module R₀ gg]
  [ggfree : Module.Free R₀ gg]
  [ggfin : Module.Finite R₀ gg]
  tg : ∀ {R S : LAlg R₀} (π : LHom R S), π.SqZero → gg ⊗[R₀] π.ker →+ G R
  tg_nat : ∀ {R S R' S' : LAlg R₀} (π : LHom R S) (π' : LHom R' S') (hπ : π.SqZero)
    (hπ' : π'.SqZero) (f : LHom R R') (hf : ∀ a ∈ π.ker, f.1.toLinearMap a ∈ π'.ker)
    (v : gg ⊗[R₀] π.ker),
    tg π' hπ' (LinearMap.lTensor gg (f.1.toLinearMap.restrict hf) v) = map f (tg π hπ v)
  surj : ∀ {R S : LAlg R₀} (π : LHom R S), π.SqZero → Function.Surjective (map π)
  tg_inj : ∀ {R S : LAlg R₀} (π : LHom R S) (hπ : π.SqZero), Function.Injective (tg π hπ)
  tg_ker : ∀ {R S : LAlg R₀} (π : LHom R S) (hπ : π.SqZero) (x : G R),
    map π x = 0 ↔ ∃ v, tg π hπ v = x
  P : ∀ R : LAlg R₀, G R → G R → Type u
  smul : ∀ {R : LAlg R₀} {x y : G R}, (R : Type u)ˣ → P R x y → P R x y
  one_smul : ∀ {R : LAlg R₀} {x y : G R} (u : P R x y), smul 1 u = u
  mul_smul : ∀ {R : LAlg R₀} {x y : G R} (l l' : (R : Type u)ˣ) (u : P R x y),
    smul (l * l') u = smul l (smul l' u)
  nonempty : ∀ (R : LAlg R₀) (x y : G R), Nonempty (P R x y)
  trans : ∀ {R : LAlg R₀} {x y : G R} (u w : P R x y), ∃! l : (R : Type u)ˣ, smul l u = w
  pmap : ∀ {R S : LAlg R₀} (f : LHom R S) {x y : G R}, P R x y → P S (map f x) (map f y)
  pmap_smul : ∀ {R S : LAlg R₀} (f : LHom R S) {x y : G R} (l : (R : Type u)ˣ) (u : P R x y),
    pmap f (smul l u) = smul (Units.map (f.1 : R →* S) l) (pmap f u)
  pmap_id : ∀ {R : LAlg R₀} {x y : G R} (u : P R x y), HEq (pmap (LHom.id R) u) u
  pmap_comp : ∀ {R S T : LAlg R₀} (f : LHom R S) (g : LHom S T) {x y : G R} (u : P R x y),
    HEq (pmap (g.comp f) u) (pmap g (pmap f u))
  add1 : ∀ {R : LAlg R₀} {x x' y : G R}, P R x y → P R x' y → P R (x + x') y
  add2 : ∀ {R : LAlg R₀} {x y y' : G R}, P R x y → P R x y' → P R x (y + y')
  zero1 : ∀ {R : LAlg R₀} (y : G R), P R 0 y
  zero2 : ∀ {R : LAlg R₀} (x : G R), P R x 0
  addFst_assoc : ∀ {R : LAlg R₀} {x x' x'' y : G R} (u : P R x y) (u' : P R x' y)
    (u'' : P R x'' y), HEq (add1 (add1 u u') u'') (add1 u (add1 u' u''))
  addSnd_assoc : ∀ {R : LAlg R₀} {x y y' y'' : G R} (u : P R x y) (u' : P R x y')
    (u'' : P R x y''), HEq (add2 (add2 u u') u'') (add2 u (add2 u' u''))
  addFst_comm : ∀ {R : LAlg R₀} {x x' y : G R} (u : P R x y) (u' : P R x' y),
    HEq (add1 u u') (add1 u' u)
  addSnd_comm : ∀ {R : LAlg R₀} {x y y' : G R} (u : P R x y) (u' : P R x y'),
    HEq (add2 u u') (add2 u' u)
  zeroFst_add : ∀ {R : LAlg R₀} {x y : G R} (u : P R x y), HEq (add1 (zero1 y) u) u
  zeroSnd_add : ∀ {R : LAlg R₀} {x y : G R} (u : P R x y), HEq (add2 (zero2 x) u) u
  addFst_smul : ∀ {R : LAlg R₀} {x x' y : G R} (l l' : (R : Type u)ˣ) (u : P R x y)
    (u' : P R x' y), add1 (smul l u) (smul l' u') = smul (l * l') (add1 u u')
  addSnd_smul : ∀ {R : LAlg R₀} {x y y' : G R} (l l' : (R : Type u)ˣ) (u : P R x y)
    (u' : P R x y'), add2 (smul l u) (smul l' u') = smul (l * l') (add2 u u')
  interchange : ∀ {R : LAlg R₀} {x x' y y' : G R} (u : P R x y) (u' : P R x' y)
    (w : P R x y') (w' : P R x' y'),
    add2 (add1 u u') (add1 w w') = add1 (add2 u w) (add2 u' w')
  addFst_nat : ∀ {R S : LAlg R₀} (f : LHom R S) {x x' y : G R} (u : P R x y) (u' : P R x' y),
    HEq (pmap f (add1 u u')) (add1 (pmap f u) (pmap f u'))
  addSnd_nat : ∀ {R S : LAlg R₀} (f : LHom R S) {x y y' : G R} (u : P R x y) (u' : P R x y'),
    HEq (pmap f (add2 u u')) (add2 (pmap f u) (pmap f u'))
  zeroFst_nat : ∀ {R S : LAlg R₀} (f : LHom R S) (y : G R),
    HEq (pmap f (zero1 y)) (zero1 (map f y))
  zeroSnd_nat : ∀ {R S : LAlg R₀} (f : LHom R S) (x : G R),
    HEq (pmap f (zero2 x)) (zero2 (map f x))
  sw : ∀ {R : LAlg R₀} {x y : G R}, P R x y → P R y x
  sw_smul : ∀ {R : LAlg R₀} {x y : G R} (l : (R : Type u)ˣ) (u : P R x y),
    sw (smul l u) = smul l (sw u)
  sw_nat : ∀ {R S : LAlg R₀} (f : LHom R S) {x y : G R} (u : P R x y),
    sw (pmap f u) = pmap f (sw u)
  swap_addFst : ∀ {R : LAlg R₀} {x x' y : G R} (u : P R x y) (u' : P R x' y),
    sw (add1 u u') = add2 (sw u) (sw u')
  sw_sw : ∀ {R : LAlg R₀} {x y : G R} (u : P R x y), sw (sw u) = u
  fibre_G : ∀ {F R₁ R₂ R : LAlg R₀} (p₁ : LHom F R₁) (p₂ : LHom F R₂) (f₁ : LHom R₁ R)
    (f₂ : LHom R₂ R), IsFibreSq p₁ p₂ f₁ f₂ → CarriesFibre (map p₁) (map p₂) (map f₁) (map f₂)
  fibre_P : ∀ {F R₁ R₂ R : LAlg R₀} (p₁ : LHom F R₁) (p₂ : LHom F R₂) (f₁ : LHom R₁ R)
    (f₂ : LHom R₂ R), IsFibreSq p₁ p₂ f₁ f₂ →
    CarriesFibre
      (fun t : (Σ x y : G F, P F x y) =>
        (⟨map p₁ t.1, map p₁ t.2.1, pmap p₁ t.2.2⟩ : Σ x y : G R₁, P R₁ x y))
      (fun t : (Σ x y : G F, P F x y) =>
        (⟨map p₂ t.1, map p₂ t.2.1, pmap p₂ t.2.2⟩ : Σ x y : G R₂, P R₂ x y))
      (fun t : (Σ x y : G R₁, P R₁ x y) =>
        (⟨map f₁ t.1, map f₁ t.2.1, pmap f₁ t.2.2⟩ : Σ x y : G R, P R x y))
      (fun t : (Σ x y : G R₂, P R₂ x y) =>
        (⟨map f₂ t.1, map f₂ t.2.1, pmap f₂ t.2.2⟩ : Σ x y : G R, P R x y))

attribute [instance] BX.grp BX.ggg BX.ggm BX.ggfree BX.ggfin

namespace BX

variable (B : BX R₀) {R : LAlg R₀}

def tr1 {x x' y : B.G R} (h : x = x') (u : B.P R x y) : B.P R x' y := h ▸ u

def tr2 {x y y' : B.G R} (h : y = y') (u : B.P R x y) : B.P R x y' := h ▸ u

def nsmul1 {x y : B.G R} (u : B.P R x y) : (n : ℕ) → B.P R (n • x) y
  | 0 => B.tr1 (zero_nsmul x).symm (B.zero1 y)
  | n + 1 => B.tr1 (succ_nsmul x n).symm (B.add1 (nsmul1 u n) u)

def nsmul2 {x y : B.G R} (u : B.P R x y) : (n : ℕ) → B.P R x (n • y)
  | 0 => B.tr2 (zero_nsmul y).symm (B.zero2 x)
  | n + 1 => B.tr2 (succ_nsmul y n).symm (B.add2 (nsmul2 u n) u)

def IsPairing (N : ℕ) (x y : B.G R) (z : (R : Type u)ˣ) : Prop :=
  ∃ (hx : N • x = 0) (hy : N • y = 0) (u : B.P R x y) (l₁ l₂ : (R : Type u)ˣ),
    B.tr1 hx (B.nsmul1 u N) = B.smul l₁ (B.zero1 y) ∧
      B.tr2 hy (B.nsmul2 u N) = B.smul l₂ (B.zero2 x) ∧ z = l₁ / l₂

end BX

end ReciprocityTheory.PGsh
end
end

section -- merged from ReciprocityTheory.DualLattices.ProdEraseUpdate
noncomputable section

open Finset

namespace ReciprocityTheory.PGsh.Up

variable {p : ℕ} [hp : Fact p.Prime] {k : Type} [Field k] [CharP k p] {ι : Type} [Fintype ι]
  [DecidableEq ι]

def xc (k : Type) [Field k] [CharP k p] (i : ι) (x : ι → ZMod p) : k :=
  ZMod.castHom (dvd_refl p) k (x i)

def lam (Cm : Matrix ι ι k) (j : ι) (x : ι → ZMod p) : k := ∑ i, Cm j i * xc k i x

def monF (Cm : Matrix ι ι k) (α : ι → ZMod p) (x : ι → ZMod p) : k :=
  ∏ j, lam Cm j x ^ (α j).val

theorem xc_pow (i : ι) (x : ι → ZMod p) : xc k i x ^ p = xc k i x := by
  simp only [xc, ← map_pow, ZMod.pow_card]

theorem lam_pow (Cm : Matrix ι ι k) (j : ι) (x : ι → ZMod p) :
    lam Cm j x ^ p = ∑ i, Cm j i ^ p * xc k i x := by
  simp only [lam, sum_pow_char, mul_pow, xc_pow]

theorem xc_eq (Cm Cinv : Matrix ι ι k) (h : Cinv * Cm = 1) (i : ι) (x : ι → ZMod p) :
    xc k i x = ∑ m, Cinv i m * lam Cm m x := by
  have e : ∀ i', ∑ m, Cinv i m * Cm m i' = (1 : Matrix ι ι k) i i' := by
    intro i'; rw [← h, Matrix.mul_apply]
  simp only [lam, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, e, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

def MulStable (S : Submodule k ((ι → ZMod p) → k)) (h : (ι → ZMod p) → k) : Prop :=
  ∀ f ∈ S, h * f ∈ S

theorem monF_split (Cm : Matrix ι ι k) (α : ι → ZMod p) (l : ι) (x : ι → ZMod p) :
    monF Cm α x = lam Cm l x ^ (α l).val * ∏ j ∈ univ.erase l, lam Cm j x ^ (α j).val := by
  unfold monF
  exact (Finset.mul_prod_erase _ _ (Finset.mem_univ l)).symm

theorem prod_erase_update (Cm : Matrix ι ι k) (α : ι → ZMod p) (l : ι) (a : ZMod p)
    (x : ι → ZMod p) :
    ∏ j ∈ univ.erase l, lam Cm j x ^ (Function.update α l a j).val =
      ∏ j ∈ univ.erase l, lam Cm j x ^ (α j).val := by
  refine Finset.prod_congr rfl (fun j hj => ?_)
  rw [Function.update_apply, if_neg (Finset.ne_of_mem_erase hj)]

theorem sum_erase_update (α : ι → ZMod p) (l : ι) (a : ZMod p) :
    ∑ j ∈ univ.erase l, (Function.update α l a j).val = ∑ j ∈ univ.erase l, (α j).val := by
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [Function.update_apply, if_neg (Finset.ne_of_mem_erase hj)]

theorem key_step (Cm Cinv : Matrix ι ι k) (h : Cinv * Cm = 1) :
    ∀ (N : ℕ) (α : ι → ZMod p), ∑ j, (α j).val = N → ∀ l,
      (fun x => lam Cm l x * monF Cm α x) ∈
        Submodule.span k (Set.range (monF (p := p) Cm)) := by
  have hp2 : 2 ≤ p := hp.out.two_le
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro α hα l
  have hlt : (α l).val < p := ZMod.val_lt (α l)
  by_cases hcase : (α l).val + 1 < p
  ·
    have hv : (α l + 1).val = (α l).val + 1 := by
      rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega : 1 < p),
        Nat.mod_eq_of_lt hcase]
    have hfun : (fun x => lam Cm l x * monF Cm α x) =
        monF Cm (Function.update α l (α l + 1)) := by
      funext x
      rw [monF_split Cm α l x, monF_split Cm (Function.update α l (α l + 1)) l x,
        prod_erase_update, Function.update_self, hv, pow_succ]
      ring
    rw [hfun]
    exact Submodule.subset_span ⟨_, rfl⟩
  ·
    have hval : (α l).val = p - 1 := by omega
    have hsplit : (α l).val + ∑ j ∈ univ.erase l, (α j).val = ∑ j, (α j).val :=
      Finset.add_sum_erase univ (fun j => (α j).val) (Finset.mem_univ l)
    have hsplitγ : (Function.update α l 0 l).val +
        ∑ j ∈ univ.erase l, (Function.update α l 0 j).val =
        ∑ j, (Function.update α l 0 j).val :=
      Finset.add_sum_erase univ (fun j => (Function.update α l 0 j).val) (Finset.mem_univ l)
    have hγl : (Function.update α l 0 l).val = 0 := by simp
    have hse := sum_erase_update α l 0
    have hlow : ∑ j, (Function.update α l 0 j).val < N := by omega
    have hfun : (fun x => lam Cm l x * monF Cm α x) =
        ∑ i, ∑ m, (Cm l i ^ p * Cinv i m) •
          (fun x => lam Cm m x * monF Cm (Function.update α l 0) x) := by
      funext x
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have e1 : monF Cm α x = lam Cm l x ^ (p - 1) * monF Cm (Function.update α l 0) x := by
        rw [monF_split Cm α l x, monF_split Cm (Function.update α l 0) l x, prod_erase_update,
          Function.update_self, ZMod.val_zero, pow_zero, one_mul, hval]
      have e2 : lam Cm l x * lam Cm l x ^ (p - 1) = lam Cm l x ^ p := by
        rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ p)]
      rw [e1, ← mul_assoc, e2, lam_pow, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [xc_eq Cm Cinv h i x, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      ring
    rw [hfun]
    refine Submodule.sum_mem _ (fun i _ => Submodule.sum_mem _ (fun m _ => Submodule.smul_mem _ _ ?_))
    exact ih _ hlow _ rfl m

theorem monF_zero (Cm : Matrix ι ι k) : monF Cm (0 : ι → ZMod p) = 1 := by
  funext x
  simp [monF]

theorem mulStable_lam (Cm Cinv : Matrix ι ι k) (h : Cinv * Cm = 1) (l : ι) :
    MulStable (Submodule.span k (Set.range (monF (p := p) Cm))) (lam Cm l) := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨α, rfl⟩ := hg
    exact key_step Cm Cinv h _ α rfl l
  | zero => simpa using Submodule.zero_mem _
  | add f g _ _ hf hg => rw [mul_add]; exact Submodule.add_mem _ hf hg
  | smul a f _ hf => rw [mul_smul_comm]; exact Submodule.smul_mem _ a hf

theorem MulStable.add {S : Submodule k ((ι → ZMod p) → k)} {h₁ h₂ : (ι → ZMod p) → k}
    (a : MulStable S h₁) (b : MulStable S h₂) : MulStable S (h₁ + h₂) := by
  intro f hf
  rw [add_mul]
  exact S.add_mem (a f hf) (b f hf)

theorem MulStable.mul {S : Submodule k ((ι → ZMod p) → k)} {h₁ h₂ : (ι → ZMod p) → k}
    (a : MulStable S h₁) (b : MulStable S h₂) : MulStable S (h₁ * h₂) := by
  intro f hf
  rw [mul_assoc]
  exact a _ (b f hf)

theorem MulStable.const (S : Submodule k ((ι → ZMod p) → k)) (c : k) :
    MulStable S (fun _ => c) := by
  intro f hf
  have e : (fun _ => c) * f = c • f := by funext x; simp
  rw [e]
  exact S.smul_mem c hf

theorem MulStable.sum {S : Submodule k ((ι → ZMod p) → k)} {s : Finset ι}
    {h : ι → (ι → ZMod p) → k} (a : ∀ i ∈ s, MulStable S (h i)) :
    MulStable S (∑ i ∈ s, h i) := by
  revert a
  refine Finset.induction_on s ?_ ?_
  · intro _ f _
    simp
  · intro j s hj ih a
    rw [Finset.sum_insert hj]
    exact (a j (Finset.mem_insert_self j s)).add (ih fun i hi => a i (Finset.mem_insert_of_mem hi))

theorem MulStable.prod {S : Submodule k ((ι → ZMod p) → k)} {s : Finset ι}
    {h : ι → (ι → ZMod p) → k} (a : ∀ i ∈ s, MulStable S (h i)) :
    MulStable S (∏ i ∈ s, h i) := by
  revert a
  refine Finset.induction_on s ?_ ?_
  · intro _ f hf
    simpa using hf
  · intro j s hj ih a
    rw [Finset.prod_insert hj]
    exact (a j (Finset.mem_insert_self j s)).mul (ih fun i hi => a i (Finset.mem_insert_of_mem hi))

theorem MulStable.pow {S : Submodule k ((ι → ZMod p) → k)} {h : (ι → ZMod p) → k}
    (a : MulStable S h) (n : ℕ) : MulStable S (h ^ n) := by
  induction n with
  | zero => intro f hf; simpa using hf
  | succ n ih => rw [pow_succ]; exact ih.mul a

def delta (k : Type) [Field k] [CharP k p] (y : ι → ZMod p) : (ι → ZMod p) → k :=
  ∏ i, ((fun _ => (1 : k)) + (fun _ => (-1 : k)) *
    ((fun x => xc k i x) + (fun _ => -ZMod.castHom (dvd_refl p) k (y i))) ^ (p - 1))

theorem delta_apply (y x : ι → ZMod p) : delta k y x = if x = y then 1 else 0 := by
  have hp1 : p - 1 ≠ 0 := by have := hp.out.two_le; omega
  have hfac : ∀ i, (1 : k) + -1 * (xc k i x + -ZMod.castHom (dvd_refl p) k (y i)) ^ (p - 1) =
      if x i = y i then 1 else 0 := by
    intro i
    have e : xc k i x + -ZMod.castHom (dvd_refl p) k (y i) =
        ZMod.castHom (dvd_refl p) k (x i - y i) := by
      simp [xc, sub_eq_add_neg]
    rw [e, ← map_pow]
    by_cases hxy : x i = y i
    · simp [hxy, zero_pow hp1]
    · rw [ZMod.pow_card_sub_one_eq_one (sub_ne_zero.mpr hxy)]
      simp [hxy]
  simp only [delta, Finset.prod_apply, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, hfac]
  rw [Finset.prod_boole]
  by_cases hxy : x = y
  · subst hxy; simp
  · have hn : ¬ ∀ i ∈ (univ : Finset ι), x i = y i := fun hall => hxy (funext fun i => hall i (mem_univ i))
    rw [if_neg hn, if_neg hxy]

theorem span_monF_eq_top (Cm Cinv : Matrix ι ι k) (h : Cinv * Cm = 1) :
    Submodule.span k (Set.range (monF (p := p) Cm)) = ⊤ := by
  have hxc : ∀ i, MulStable (Submodule.span k (Set.range (monF (p := p) Cm))) (fun x => xc k i x) := by
    intro i
    have e : (fun x => xc k i x) = ∑ m, (fun _ => Cinv i m) * lam Cm m := by
      funext x
      rw [xc_eq Cm Cinv h i x]
      simp [Finset.sum_apply]
    rw [e]
    exact MulStable.sum (fun m _ => (MulStable.const _ _).mul (mulStable_lam Cm Cinv h m))
  have hdelta : ∀ y, MulStable (Submodule.span k (Set.range (monF (p := p) Cm))) (delta k y) := by
    intro y
    unfold delta
    exact MulStable.prod (fun i _ => (MulStable.const _ 1).add
      ((MulStable.const _ (-1)).mul (((hxc i).add (MulStable.const _ _)).pow _)))
  have h1 : (1 : (ι → ZMod p) → k) ∈ Submodule.span k (Set.range (monF (p := p) Cm)) := by
    rw [← monF_zero Cm]
    exact Submodule.subset_span ⟨0, rfl⟩
  have hmem : ∀ y, delta k y ∈ Submodule.span k (Set.range (monF (p := p) Cm)) := fun y => by
    simpa using hdelta y 1 h1
  rw [eq_top_iff]
  intro f _
  have e : f = ∑ y, f y • delta k y := by
    funext x
    simp [Finset.sum_apply, delta_apply]
  rw [e]
  exact Submodule.sum_mem _ (fun y _ => Submodule.smul_mem _ _ (hmem y))

theorem det_monF_ne_zero (Cm : Matrix ι ι k) (hC : IsUnit Cm.det) :
    (Matrix.of fun (x α : ι → ZMod p) => monF Cm α x).det ≠ 0 := by
  have hspan := span_monF_eq_top (p := p) Cm Cm⁻¹ (Matrix.nonsing_inv_mul Cm hC)
  have hli : LinearIndependent k
      (fun α => Matrix.transpose (Matrix.of fun (x α : ι → ZMod p) => monF Cm α x) α) := by
    have hcols : (fun α => Matrix.transpose (Matrix.of fun (x α : ι → ZMod p) => monF Cm α x) α) =
        monF (p := p) Cm := by
      funext α x
      simp [Matrix.transpose_apply]
    rw [hcols]
    apply linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge
    simp
  have hu := Matrix.linearIndependent_cols_iff_isUnit.mp hli
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero

end ReciprocityTheory.PGsh.Up
end
end

section -- merged from ReciprocityTheory.DualLattices.QExpansionMonoWCoeffZero
section -- merged from ReciprocityTheory.DualLattices.Eisenstein4CoeffBound
namespace ReciprocityTheory.PGsh

open ModularForm EisensteinSeries ArithmeticFunction PowerSeries UpperHalfPlane
open scoped ArithmeticFunction.sigma

def e4Z : PowerSeries ℤ := PowerSeries.mk fun n => if n = 0 then 1 else 240 * (σ 3 n : ℤ)

def e6Z : PowerSeries ℤ := PowerSeries.mk fun n => if n = 0 then 1 else -504 * (σ 5 n : ℤ)

theorem qExpansion_E₄_eq : qExpansion 1 E₄ = PowerSeries.map (Int.castRingHom ℂ) e4Z := by
  ext n
  rw [coeff_map, e4Z, coeff_mk]
  by_cases hn : n = 0
  · subst hn; norm_num [E_qExpansion_coeff _ ⟨2, rfl⟩]
  · norm_num [E_qExpansion_coeff _ ⟨2, rfl⟩, hn, show bernoulli 4 = -1 / 30 by decide +kernel]

theorem qExpansion_E₆_eq : qExpansion 1 E₆ = PowerSeries.map (Int.castRingHom ℂ) e6Z := by
  ext n
  rw [coeff_map, e6Z, coeff_mk]
  by_cases hn : n = 0
  · subst hn; norm_num [E_qExpansion_coeff _ ⟨3, rfl⟩]
  · norm_num [E_qExpansion_coeff _ ⟨3, rfl⟩, hn, show bernoulli 6 = 1 / 42 by decide +kernel]

end ReciprocityTheory.PGsh
end

namespace ReciprocityTheory.PGsh

open UpperHalfPlane hiding I
open Complex ModularForm ModularFormClass MatrixGroups EisensteinSeries

def monoIdx (w : ℕ) : Finset ℕ :=
  (Finset.range (w + 1)).filter fun a => 4 * a ≤ w ∧ 6 ∣ w - 4 * a

def monoB (w a : ℕ) : ℕ := (w - 4 * a) / 6

theorem monoIdx_wt {w a : ℕ} (h : a ∈ monoIdx w) : 4 * a + 6 * monoB w a = w := by
  simp only [monoIdx, Finset.mem_filter, Finset.mem_range] at h
  obtain ⟨_, h1, h2⟩ := h
  unfold monoB
  omega

noncomputable def monoW (w a : ℕ) : ModularForm 𝒮ℒ (w : ℤ) :=
  if h : 4 * a + 6 * monoB w a = w then
    ModularForm.mcast (by omega) ((E₄.pow a).mul (E₆.pow (monoB w a)))
  else 0

theorem coe_monoW {w a : ℕ} (h : a ∈ monoIdx w) :
    (⇑(monoW w a) : ℍ → ℂ) = (⇑E₄) ^ a * (⇑E₆) ^ monoB w a := by
  simp [monoW, monoIdx_wt h]

theorem qExpansion_monoW {w a : ℕ} (h : a ∈ monoIdx w) :
    qExpansion 1 (monoW w a) =
      PowerSeries.map (Int.castRingHom ℂ) (e4Z ^ a * e6Z ^ monoB w a) := by
  simp only [monoW, monoIdx_wt h, dite_true, ModularForm.qExpansion_mcast]
  rw [ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL, qExpansion_E₄_eq,
    qExpansion_E₆_eq, map_mul, map_pow, map_pow]

theorem qExpansion_monoW_coeff_zero {w a : ℕ} (h : a ∈ monoIdx w) :
    (qExpansion 1 (monoW w a)).coeff 0 = 1 := by
  have h4 : PowerSeries.constantCoeff e4Z = 1 := by simp [e4Z]
  have h6 : PowerSeries.constantCoeff e6Z = 1 := by simp [e6Z]
  rw [qExpansion_monoW h, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    map_mul, map_pow, map_pow, h4, h6]
  simp

theorem monoIdx_nonempty {w : ℕ} (he : Even w) (h2 : w ≠ 2) : ∃ a, a ∈ monoIdx w := by
  obtain ⟨m, rfl⟩ := he
  simp only [monoIdx, Finset.mem_filter, Finset.mem_range]
  by_cases h : m % 2 = 0
  · exact ⟨(m + m) / 4, by omega, by omega, ⟨0, by omega⟩⟩
  · exact ⟨(m + m - 6) / 4, by omega, by omega, ⟨1, by omega⟩⟩

noncomputable def monoSpanF (w : ℕ) : Submodule ℂ (ℍ → ℂ) :=
  Submodule.span ℂ (Set.range fun a : monoIdx w => (⇑(monoW w a) : ℍ → ℂ))

theorem mono_mem_monoSpanF {w a : ℕ} (h : a ∈ monoIdx w) : (⇑(monoW w a) : ℍ → ℂ) ∈ monoSpanF w :=
  Submodule.subset_span ⟨⟨a, h⟩, rfl⟩

theorem mulDisc_mem {w : ℕ} (hw : 12 ≤ w) {φ : ℍ → ℂ} (hφ : φ ∈ monoSpanF (w - 12)) :
    (ModularForm.discriminant : ℍ → ℂ) * φ ∈ monoSpanF w := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨a, ha⟩, rfl⟩ := hx
    have hwt := monoIdx_wt ha
    have ha3 : a + 3 ∈ monoIdx w := by
      simp only [monoIdx, Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, by omega, ⟨monoB (w - 12) a, by omega⟩⟩
    have ha0 : a ∈ monoIdx w := by
      simp only [monoIdx, Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, by omega, ⟨monoB (w - 12) a + 2, by omega⟩⟩
    have hb3 : monoB w (a + 3) = monoB (w - 12) a := by
      have := monoIdx_wt ha3; omega
    have hb0 : monoB w a = monoB (w - 12) a + 2 := by
      have := monoIdx_wt ha0; omega
    have heq : (ModularForm.discriminant : ℍ → ℂ) * ⇑(monoW (w - 12) a) =
        (1728 : ℂ)⁻¹ • ((⇑(monoW w (a + 3)) : ℍ → ℂ) - ⇑(monoW w a)) := by
      rw [coe_monoW ha, coe_monoW ha3, coe_monoW ha0, hb3, hb0]
      funext z
      simp only [Pi.mul_apply, Pi.pow_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
        ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq]
      ring
    rw [heq]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (mono_mem_monoSpanF ha3)
      (mono_mem_monoSpanF ha0))
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx

theorem coe_mem_monoSpanF (w : ℕ) (f : ModularForm 𝒮ℒ (w : ℤ)) : (⇑f : ℍ → ℂ) ∈ monoSpanF w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  rcases Nat.even_or_odd w with he | ho
  · by_cases h2 : w = 2
    · subst h2
      have : f = 0 := rank_zero_iff_forall_zero.mp ModularForm.levelOne_weight_two_rank_zero f
      subst this
      simp
    obtain ⟨a, ha⟩ := monoIdx_nonempty he h2
    set g := f - (qExpansion 1 f).coeff 0 • monoW w a with hg
    have hgc : (qExpansion 1 g).coeff 0 = 0 :=
      (ModularForm.isCuspForm_iff_coeffZero_eq_zero g).mp
        (ModularForm.sub_smul_isCuspForm f _ (qExpansion_monoW_coeff_zero ha))
    have hfg : (⇑f : ℍ → ℂ) = ⇑g + (qExpansion 1 f).coeff 0 • ⇑(monoW w a) := by
      rw [hg]; simp
    rw [hfg]
    refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ (mono_mem_monoSpanF ha))
    by_cases h12 : w < 12
    · have h0 : ModularForm.toCuspForm g hgc = 0 :=
        rank_zero_iff_forall_zero.mp (CuspForm.rank_eq_zero_of_weight_lt_twelve (by omega)) _
      have : (⇑g : ℍ → ℂ) = 0 := by
        funext z
        have := congrArg (fun F : CuspForm 𝒮ℒ (w : ℤ) => F z) h0
        simpa using this
      rw [this]; exact Submodule.zero_mem _
    · replace h12 : 12 ≤ w := by omega
      set h := CuspForm.discriminantEquiv (ModularForm.toCuspForm g hgc) with hh
      have hmem := ih (w - 12) (by omega) (ModularForm.mcast (by omega) h)
      have hgd : (⇑g : ℍ → ℂ) = (ModularForm.discriminant : ℍ → ℂ) * ⇑h := by
        have := ModularForm.discriminant_mul_discriminantEquiv (ModularForm.toCuspForm g hgc)
        rw [hh, this]; rfl
      rw [hgd]
      exact mulDisc_mem h12 hmem
  · have : f = 0 := ModularForm.levelOne_odd_weight_eq_zero (by exact_mod_cast ho.natCast) f
    subst this
    simp

end ReciprocityTheory.PGsh
end

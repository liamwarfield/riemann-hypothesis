module

public import Development.AbelianVarietyTheory.Definitions.Foundations.CobOn
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrameLats
noncomputable section

open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors

namespace GlobalTheory.SgGlob

variable {E : Type} [Field E] [NumberField E]

def dInv (E : Type) [Field E] [NumberField E] (j : ℕ) : FractionalIdeal (𝓞 E)⁰ E :=
  ((differentIdeal ℤ (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E)⁻¹) ^ j

def SelfDual (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (Λ : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  Λ.FG ∧ ∀ v, v ∈ Λ ↔ ∀ w ∈ Λ, form σ J v w ∈ (algebraMap (𝓞 E) E).range

def frameLat {n r : ℕ} (P : Matrix (Fin n) (Fin (r + 1)) E) : Submodule (𝓞 E) (Fin n → E) :=
  Submodule.span (𝓞 E) {v | ∃ (b : Fin (r + 1)) (a : E), a ∈ dInv E (r - (b : ℕ)) ∧ v = a • fun i => P i b}

def PrimIn {n : ℕ} (M Λ : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  M ≤ Λ ∧ ∀ v ∈ Λ, v ∈ Submodule.span E (M : Set (Fin n → E)) → v ∈ M

def pairLat {n r : ℕ} (g : ℕ) (P P' : Matrix (Fin n) (Fin (r + 1)) E) :
    Submodule (𝓞 E) (Fin n → E) :=
  frameLat P ⊔ frameLat (((g : E)⁻¹) • (P' - P))

def latMap {n : ℕ} (γ : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E)) :
    Submodule (𝓞 E) (Fin n → E) := Λ.map (γ.mulVecLin.restrictScalars (𝓞 E))

abbrev Tri (E : Type) [Field E] [NumberField E] (n r : ℕ) : Type :=
  Submodule (𝓞 E) (Fin n → E) × Matrix (Fin n) (Fin (r + 1)) E × Matrix (Fin n) (Fin (r + 1)) E

def GenConf (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (T T' : E) (g : ℕ)
    (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Set (Tri E n r) :=
  {x | SelfDual σ J x.1 ∧ (x.2.1, x.2.2) ∈ XZ σ J T T' Z ∧ PrimIn (pairLat g x.2.1 x.2.2) x.1}

def FrameLats (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (P : Matrix (Fin n) (Fin (r + 1)) E) : Set (Submodule (𝓞 E) (Fin n → E)) :=
  {Λ | SelfDual σ J Λ ∧ PrimIn (frameLat P) Λ}

end GlobalTheory.SgGlob
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.CintTranslate
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumRefine
namespace GlobalTheory.SumRefinement

theorem finsum_fst {X F : Type} [Finite F] (g : X → ℂ) (hg : (Function.support g).Finite) :
    ∑ᶠ p : X × F, g p.1 = (Nat.card F : ℂ) * ∑ᶠ x, g x := by
  classical
  let _ : Fintype F := Fintype.ofFinite F
  rw [finsum_eq_sum_of_support_subset (s := hg.toFinset ×ˢ Finset.univ) _ ?_,
    finsum_eq_sum_of_support_subset (s := hg.toFinset) _ (by simp),
    Finset.sum_product, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  · intro p hp
    simp only [Function.mem_support] at hp
    simp [hp]

theorem sum_refine {W : Type} [AddCommGroup W] {A B C : AddSubgroup W} {φ : W → ℂ}
    (h : GlobalTheory.IdxInt.Fine A φ B) (hCB : C ≤ B) (hi : AddSubgroup.relIndex C B ≠ 0) :
    ∑ᶠ (c : W ⧸ C), φ (Quotient.out c) =
      (AddSubgroup.relIndex C B : ℂ) * ∑ᶠ (c : W ⧸ B), φ (Quotient.out c) := by
  classical
  obtain ⟨-, -, hinv, hfin⟩ := h
  set e := AddSubgroup.quotientEquivProdOfLE hCB with he
  have hfst : ∀ x : W ⧸ C, (e x).1 = (QuotientAddGroup.mk (Quotient.out x) : W ⧸ B) := by
    intro x
    conv_lhs => rw [← Quotient.out_eq' x]
    rfl
  have hcong : ∀ u v : W, (QuotientAddGroup.mk u : W ⧸ B) = QuotientAddGroup.mk v → φ u = φ v := by
    intro u v huv
    have hb : -u + v ∈ B := QuotientAddGroup.eq.1 huv
    have h1 := hinv u (-u + v) hb
    rw [add_neg_cancel_left] at h1
    exact h1.symm
  have hval : ∀ x : W ⧸ C, φ (Quotient.out x) = φ (Quotient.out (e x).1) := by
    intro x
    rw [hfst]
    exact hcong _ _ (QuotientAddGroup.out_eq' _).symm
  have : Finite (↥B ⧸ C.addSubgroupOf B) := Nat.finite_of_card_ne_zero hi
  have hg : (Function.support fun b : W ⧸ B => φ (Quotient.out b)).Finite := by
    refine hfin.subset ?_
    intro b hb
    exact ⟨Quotient.out b, hb, QuotientAddGroup.out_eq' b⟩
  rw [← finsum_comp_equiv e.symm]
  simp_rw [hval, Equiv.apply_symm_apply]
  rw [finsum_fst (fun b : W ⧸ B => φ (Quotient.out b)) hg]
  rfl

end GlobalTheory.SumRefinement
end

noncomputable section
open scoped Classical

namespace GlobalTheory.IdxInt.Model
open GlobalTheory.IdxInt

variable {W : Type} [AddCommGroup W]

lemma out_mk {φ : W → ℂ} {B : AddSubgroup W} (h : ∀ w, ∀ b ∈ B, φ (w + b) = φ w) (w : W) :
    φ (QuotientAddGroup.mk w : W ⧸ B).out = φ w := by
  obtain ⟨b, hb⟩ := QuotientAddGroup.mk_out_eq_add B w
  rw [hb]; exact h w b b.2

lemma sum_refine {A B C : AddSubgroup W} {φ : W → ℂ} (h : Fine A φ B) (hC : C ≤ B)
    (hi : C.relIndex B ≠ 0) :
    (∑ᶠ c : W ⧸ C, φ c.out) = (C.relIndex B : ℂ) * ∑ᶠ c : W ⧸ B, φ c.out := by
  apply _root_.GlobalTheory.SumRefinement.sum_refine <;> assumption

lemma ratio_eq {A B B' : AddSubgroup W} {φ : W → ℂ} (h : Fine A φ B) (h' : Fine A φ B') :
    (∑ᶠ c : W ⧸ B, φ c.out) / (B.relIndex A : ℂ) = (∑ᶠ c : W ⧸ B', φ c.out) / (B'.relIndex A : ℂ) := by
  have hC : (B ⊓ B').relIndex A ≠ 0 := AddSubgroup.relIndex_inf_ne_zero h.2.1 h'.2.1
  have m1 := AddSubgroup.relIndex_mul_relIndex (B ⊓ B') B A inf_le_left h.1
  have m2 := AddSubgroup.relIndex_mul_relIndex (B ⊓ B') B' A inf_le_right h'.1
  have i1 : (B ⊓ B').relIndex B ≠ 0 := fun z => hC (by rw [← m1, z, zero_mul])
  have i2 : (B ⊓ B').relIndex B' ≠ 0 := fun z => hC (by rw [← m2, z, zero_mul])
  have s1 := sum_refine h inf_le_left i1
  have s2 := sum_refine h' inf_le_right i2
  have c1 : (B.relIndex A : ℂ) ≠ 0 := by exact_mod_cast h.2.1
  have c2 : (B'.relIndex A : ℂ) ≠ 0 := by exact_mod_cast h'.2.1
  have c3 : (((B ⊓ B').relIndex B : ℕ) : ℂ) ≠ 0 := by exact_mod_cast i1
  have c4 : (((B ⊓ B').relIndex B' : ℕ) : ℂ) ≠ 0 := by exact_mod_cast i2
  have m : (((B ⊓ B').relIndex B : ℕ) : ℂ) * (B.relIndex A : ℂ) = (((B ⊓ B').relIndex B' : ℕ) : ℂ) * (B'.relIndex A : ℂ) := by
    exact_mod_cast m1.trans m2.symm
  rw [← mul_div_mul_left _ _ c3, ← s1, ← mul_div_mul_left (∑ᶠ c : W ⧸ B', φ c.out) _ c4, ← s2, m]

theorem cint_eq {A B : AddSubgroup W} {φ : W → ℂ} (h : Fine A φ B) :
    cint A φ = (∑ᶠ c : W ⧸ B, φ c.out) / (B.relIndex A : ℂ) := by
  have hn : Nice A φ := ⟨B, h⟩
  rw [cint, dite_eq_left hn]
  exact ratio_eq hn.choose_spec h

lemma fine_refine {A B C : AddSubgroup W} {φ : W → ℂ} (h : Fine A φ B) (hC : C ≤ B)
    (hi : C.relIndex A ≠ 0) : Fine A φ C := by
  have m1 := AddSubgroup.relIndex_mul_relIndex C B A hC h.1
  have i1 : C.relIndex B ≠ 0 := fun z => hi (by rw [← m1, z, zero_mul])
  haveI : Finite (B ⧸ C.addSubgroupOf B) := Nat.finite_of_card_ne_zero i1
  refine ⟨hC.trans h.1, hi, fun w b hb => h.2.2.1 w b (hC hb), ?_⟩
  let e := AddSubgroup.quotientEquivProdOfLE hC
  refine ((h.2.2.2.prod (Set.finite_univ (α := B ⧸ C.addSubgroupOf B))).preimage
    e.injective.injOn).subset ?_
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨⟨w, hw, rfl⟩, trivial⟩

end GlobalTheory.IdxInt.Model
end
end

module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.QuotientHighestWeightTensorStandard
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDiagExists

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.RealSmulCj
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.OfDInjective
noncomputable section

open Finset Matrix ComplexConjugate
open ReciprocityTheory.ChartRestriction.DS.Mult1.ConjugateHilbertSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK.DualRepresentationReversal

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def sub (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := A.submatrix Fin.revPerm Fin.revPerm

theorem sub_apply (A : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) : sub A a b = A (Fin.rev a) (Fin.rev b) := rfl

theorem sub_mul (A B : Matrix (Fin n) (Fin n) ℂ) : sub (A * B) = sub A * sub B := by
  simp only [sub]
  exact (Matrix.submatrix_mul_equiv _ _ _ _ _).symm

theorem sub_one : sub (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  simp only [sub]
  exact Matrix.submatrix_one_equiv _

theorem sub_H (A : Matrix (Fin n) (Fin n) ℂ) : (sub A)ᴴ = sub Aᴴ := by
  simp [sub, Matrix.conjTranspose_submatrix]

theorem sub_add (A B : Matrix (Fin n) (Fin n) ℂ) : sub (A + B) = sub A + sub B := rfl

theorem sub_smul (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ) : sub (c • A) = c • sub A := rfl

theorem sub_zero : sub (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := rfl

def Pr (n : ℕ) : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => if i = Fin.rev j then 1 else 0

theorem Pr_mul (A : Matrix (Fin n) (Fin n) ℂ) : Pr n * A = A.submatrix Fin.rev id := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev i)]
  · simp [Pr]
  · intro k _ hk
    simp only [Pr, Matrix.of_apply]
    rw [if_neg (fun h => hk (by rw [h, Fin.rev_rev]))]
    ring
  · simp

theorem mul_Pr (A : Matrix (Fin n) (Fin n) ℂ) : A * Pr n = A.submatrix id Fin.rev := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev j)]
  · simp [Pr]
  · intro k _ hk
    simp only [Pr, Matrix.of_apply]
    rw [if_neg hk]
    ring
  · simp

theorem Pr_conj (A : Matrix (Fin n) (Fin n) ℂ) : Pr n * A * Pr n = sub A := by
  rw [Pr_mul, mul_Pr]
  ext i j
  simp [sub]

theorem Pr_Pr : Pr n * Pr n = 1 := by
  rw [Pr_mul]
  ext i j
  simp [Pr, Matrix.one_apply]

theorem Pr_inv : (Pr n)⁻¹ = Pr n := by
  exact Matrix.inv_eq_left_inv Pr_Pr

theorem exp_sub (A : Matrix (Fin n) (Fin n) ℂ) : NormedSpace.exp (sub A) = sub (NormedSpace.exp A) := by
  have hu : IsUnit (Pr n) := ⟨⟨Pr n, Pr n, Pr_Pr, Pr_Pr⟩, rfl⟩
  rw [← Pr_conj, ← Pr_conj (NormedSpace.exp A)]
  have h1 : Pr n * A * Pr n = Pr n * A * (Pr n)⁻¹ := by rw [Pr_inv]
  rw [h1, Matrix.exp_conj _ _ hu, Pr_inv]

theorem Jm_rev (ε : Fin n → Bool) : sub (Jm (ε ∘ Fin.rev)) = Jm ε := by
  ext a b
  simp [sub, Jm, Matrix.diagonal_apply]

theorem inUJ_sub {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset (ε ∘ Fin.rev)) :
    sub g ∈ UJset ε := by
  show (sub g)ᴴ * Jm ε * sub g = Jm ε
  have hg' : gᴴ * Jm (ε ∘ Fin.rev) * g = Jm (ε ∘ Fin.rev) := hg
  rw [← Jm_rev ε, sub_H, ← sub_mul, ← sub_mul, hg']

theorem inG_sub {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG (ε ∘ Fin.rev) X) :
    inG ε (sub X) := by
  unfold inG at *
  rw [← Jm_rev ε, sub_H, ← sub_mul, ← sub_mul, ← sub_add, hX, sub_zero]

theorem K_sub {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset (ε ∘ Fin.rev)) :
    sub k ∈ Kset ε := by
  simp only [Kset, Set.mem_setOf_eq] at hk ⊢
  obtain ⟨hu, hc⟩ := hk
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff] at hu ⊢
    rw [Matrix.star_eq_conjTranspose] at hu ⊢
    rw [sub_H, ← sub_mul, hu, sub_one]
  · rw [← Jm_rev ε, ← sub_mul, ← sub_mul, hc]

theorem inG_entry {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (a b : Fin n) :
    X b a = (if ε a = ε b then -1 else 1) * conj (X a b) := by
  have h := congrFun (congrFun hX b) a
  rw [Matrix.add_apply, Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
    Matrix.zero_apply] at h
  cases hεa : ε a <;> cases hεb : ε b <;> simp [hεa, hεb, Complex.star_def] at h ⊢ <;>
    first | linear_combination h | linear_combination -h

section Conj

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def cjSub (S : Submodule ℂ H) : Submodule ℂ (Cj H) where
  carrier := {x | ofCj x ∈ S}
  add_mem' hx hy := S.add_mem hx hy
  zero_mem' := S.zero_mem
  smul_mem' c _ hx := S.smul_mem (conj c) hx

variable {D : Submodule ℂ H}

def toD (x : cjSub D) : D := ⟨ofCj (x : Cj H), x.2⟩

def ofD (u : D) : cjSub D := ⟨toCj (u : H), u.2⟩

@[simp] theorem toD_ofD (u : D) : toD (ofD u) = u := rfl

@[simp] theorem ofD_toD (x : cjSub D) : ofD (toD x) = x := rfl

theorem ofD_add (u v : D) : ofD (u + v) = ofD u + ofD v := rfl

theorem ofD_sub (u v : D) : ofD (u - v) = ofD u - ofD v := rfl

theorem ofD_neg (u : D) : ofD (-u) = -ofD u := rfl

theorem ofD_zero : ofD (0 : D) = 0 := rfl

theorem toD_add (x y : cjSub D) : toD (x + y) = toD x + toD y := rfl

theorem toD_smul (c : ℂ) (x : cjSub D) : toD (c • x) = conj c • toD x := rfl

theorem ofD_smul (c : ℂ) (u : D) : ofD (c • u) = conj c • ofD u := by
  have h := toD_smul (conj c) (ofD u)
  rw [toD_ofD, Complex.conj_conj] at h
  rw [← h, ofD_toD]

theorem ofD_injective : Function.Injective (ofD : D → cjSub D) := by
  intro u v h
  have := congrArg toD h
  simpa using this

def ofDh : D →+ cjSub D where
  toFun := ofD
  map_zero' := rfl
  map_add' := ofD_add

theorem ofD_sum {ι : Type*} (s : Finset ι) (f : ι → D) : ofD (∑ i ∈ s, f i) = ∑ i ∈ s, ofD (f i) := by
  exact map_sum ofDh f s

def ofDL : D →ₛₗ[starRingEnd ℂ] cjSub D where
  toFun := ofD
  map_add' := ofD_add
  map_smul' := ofD_smul

def cjEnd (A : Module.End ℂ D) : Module.End ℂ (cjSub D) where
  toFun x := ofD (A (toD x))
  map_add' x y := by rw [toD_add, map_add (f := _), ofD_add]
  map_smul' c x := by
    show ofD (A (toD (c • x))) = c • ofD (A (toD x))
    rw [toD_smul, A.map_smul, ofD_smul]
    simp

def sg (ε : Fin n → Bool) (a : Fin n) : ℂ := if ε (Fin.rev a) then 1 else -1

theorem sg_sq (ε : Fin n → Bool) (a : Fin n) : sg ε a * sg ε a = 1 := by
  unfold sg
  split_ifs <;> norm_num

theorem conj_sg (ε : Fin n → Bool) (a : Fin n) : conj (sg ε a) = sg ε a := by
  unfold sg
  split_ifs <;> simp

theorem sg_ne (ε : Fin n → Bool) (a : Fin n) : sg ε a ≠ 0 := by
  unfold sg
  split_ifs <;> norm_num

def Edd (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ D) (a b : Fin n) : Module.End ℂ (cjSub D) :=
  cjEnd ((-(sg ε a * sg ε b)) • E (Fin.rev b) (Fin.rev a))

theorem Edd_ofD (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ D) (a b : Fin n) (u : D) :
    Edd ε E a b (ofD u) = ofD ((-(sg ε a * sg ε b)) • E (Fin.rev b) (Fin.rev a) u) := rfl

theorem glRep_Edd (ε : Fin n → Bool) {E : Fin n → Fin n → Module.End ℂ D} (hE : IsGlRep E) :
    IsGlRep (Edd ε E) := by
  intro a b c d
  apply LinearMap.ext
  intro x
  obtain ⟨u, rfl⟩ : ∃ u, x = ofD u := ⟨toD x, (ofD_toD x).symm⟩
  have key := congrArg (fun T : Module.End ℂ D => T u) (hE (Fin.rev b) (Fin.rev a) (Fin.rev d) (Fin.rev c))
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Fin.rev_inj] at key
  have lhs : (Edd ε E a b * Edd ε E c d - Edd ε E c d * Edd ε E a b) (ofD u) =
      ofD ((sg ε a * sg ε b * (sg ε c * sg ε d)) • (E (Fin.rev b) (Fin.rev a) (E (Fin.rev d) (Fin.rev c) u) -
        E (Fin.rev d) (Fin.rev c) (E (Fin.rev b) (Fin.rev a) u))) := by
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Edd_ofD, LinearMap.map_smul]
    rw [← ofD_sub]
    congr 1
    module
  rw [lhs, key, LinearMap.sub_apply]
  by_cases hbc : b = c <;> by_cases hda : d = a
  · subst c
    subst d
    simp only [eq_self_iff_true, if_true, Edd_ofD]
    rw [← ofD_sub]
    congr 1
    unfold sg
    split_ifs <;> module
  · subst c
    have hda' : ¬ Fin.rev a = Fin.rev d := fun h => hda (Fin.rev_injective h).symm
    simp only [eq_self_iff_true, if_true, if_neg hda, if_neg (Ne.symm hda), if_neg hda', LinearMap.zero_apply, Edd_ofD,
      sub_zero, zero_sub]
    first
    | (congr 1; unfold sg; split_ifs <;> module)
    | (rw [← ofD_neg]; congr 1; unfold sg; split_ifs <;> module)
    | (apply ofD_injective; unfold sg; split_ifs <;> module)
    | (simp only [← ofD_neg, ← ofD_sub, ← ofD_zero]; congr 1; unfold sg; split_ifs <;> module)
  · subst d
    have hbc' : ¬ Fin.rev c = Fin.rev b := fun h => hbc (Fin.rev_injective h).symm
    simp only [eq_self_iff_true, if_true, if_neg hbc, if_neg (Ne.symm hbc), if_neg hbc', LinearMap.zero_apply, Edd_ofD,
      sub_zero, zero_sub]
    simp only [sub_zero, zero_sub, LinearMap.zero_apply, ← ofD_neg, ← ofD_sub]
    congr 1
    unfold sg
    split_ifs <;> module
  · have hda' : ¬ Fin.rev a = Fin.rev d := fun h => hda (Fin.rev_injective h).symm
    have hbc' : ¬ Fin.rev c = Fin.rev b := fun h => hbc (Fin.rev_injective h).symm
    simp only [if_neg hbc, if_neg (Ne.symm hbc), if_neg hda, if_neg (Ne.symm hda), if_neg hda', if_neg hbc', LinearMap.zero_apply,
      sub_zero, smul_zero]
    simp [ofD_zero]

end Conj

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.DualRepresentationReversal
end
end

noncomputable section

open Finset Matrix ComplexConjugate
open ReciprocityTheory.ChartRestriction.DS.Mult1.ConjugateHilbertSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK.DualRepresentationReversal

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : Submodule ℂ H}
  {ε : Fin n → Bool}

def sdd (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (g : Matrix (Fin n) (Fin n) ℂ) : Cj H →L[ℂ] Cj H :=
  opCj (σ (sub g))

theorem urep_sdd {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) :
    IsURepOn (UJset (ε ∘ Fin.rev)) (sdd σ) := by
  obtain ⟨⟨h1, hm⟩, hn, hc⟩ := hσ
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · unfold sdd; rw [sub_one, h1]; rfl
  · intro a ha b hb; unfold sdd; rw [sub_mul, hm _ (inUJ_sub ha) _ (inUJ_sub hb)]; rfl
  · intro g hg v; exact hn _ (inUJ_sub hg) (ofCj v)
  · intro v
    have hcs : Continuous (sub : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) :=
      continuous_id.matrix_submatrix _ _
    exact (hc (ofCj v)).comp hcs.continuousOn (fun g hg => inUJ_sub hg)

theorem smul_ofD (c : ℂ) (u : D) : c • ofD u = ofD (conj c • u) := by
  rw [ofD_smul]; simp

theorem sum_rev_swap {M : Type*} [AddCommMonoid M] (F : Fin n → Fin n → M) :
    ∑ a, ∑ b, F a b = ∑ a, ∑ b, F (Fin.rev b) (Fin.rev a) := by
  rw [Finset.sum_comm, ← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Equiv.sum_comp Fin.revPerm]
  rfl

theorem actM_Edd {E : Fin n → Fin n → Module.End ℂ D} {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : inG (ε ∘ Fin.rev) X) (u : D) : actM (Edd ε E) X (ofD u) = ofD (actM E (sub X) u) := by
  unfold actM
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Edd_ofD, smul_ofD, ofD_sum]
  rw [sum_rev_swap]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Fin.rev_rev, sub_apply, smul_smul]
  congr 2
  have he := inG_entry hX (Fin.rev b) (Fin.rev a)
  simp only [Function.comp_apply, Fin.rev_rev] at he
  rw [he]
  unfold sg
  simp only [Fin.rev_rev]
  cases ε a <;> cases ε b <;> simp

theorem real_smul_cj (r : ℝ) (x : Cj H) : r • x = toCj (r • ofCj x) := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.real_smul_eq_coe_smul (K := ℂ) r (ofCj x),
    ReciprocityTheory.ChartRestriction.DS.Mult1.ConjugateHilbertSpace.smul_def, RCLike.conj_ofReal]

def toCjR : H →L[ℝ] Cj H where
  toFun := toCj
  map_add' _ _ := rfl
  map_smul' r x := (real_smul_cj r (toCj x)).symm
  cont := continuous_id

theorem derived_sdd {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {E : Fin n → Fin n → Module.End ℂ D}
    (hD : IsDerivedOn ε σ D E) : IsDerivedOn (ε ∘ Fin.rev) (sdd σ) (cjSub D) (Edd ε E) := by
  refine ⟨glRep_Edd ε hD.glRep, ?_, ?_⟩
  · intro k hk v hv
    exact hD.kStable (sub k) (K_sub hk) (ofCj v) hv
  · intro X hX v
    have h3 := hD.deriv (sub X) (inG_sub hX) (toD v)
    have h4 := (toCjR (H := H)).hasFDerivAt.comp_hasDerivAt (x := (0 : ℝ)) h3
    have hv : v = ofD (toD v) := rfl
    rw [hv, actM_Edd hX]
    convert (preTransparency := .reducible) h4 using 1
    · funext t
      simp only [sdd, Function.comp_apply, ← exp_sub, sub_smul]
      rfl
    · rfl

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.DualRepresentationReversal
end
end

noncomputable section

open Finset Matrix ComplexConjugate
open ReciprocityTheory.ChartRestriction.DS.Mult1.ConjugateHilbertSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK.DualRepresentationReversal

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def lamd (lam : Fin n → ℝ) : Fin n → ℝ := fun a => -lam (Fin.rev a)

theorem card_eq_of_rev (P Q : Fin n → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ b, P b ↔ Q (Fin.rev b)) : (univ.filter P).card = (univ.filter Q).card := by
  apply Finset.card_bij' (fun b _ => Fin.rev b) (fun b _ => Fin.rev b) <;> simp [h]

theorem rhoN_rev (ε : Fin n → Bool) (a : Fin n) : rhoN (ε ∘ Fin.rev) a = -rhoN ε (Fin.rev a) := by
  have h1 : (univ.filter fun b => a < b ∧ (ε ∘ Fin.rev) b ≠ (ε ∘ Fin.rev) a).card =
      (univ.filter fun b => b < Fin.rev a ∧ ε b ≠ ε (Fin.rev a)).card :=
    card_eq_of_rev _ _ fun b => by simp [Fin.rev_lt_rev]
  have h2 : (univ.filter fun b => b < a ∧ (ε ∘ Fin.rev) b ≠ (ε ∘ Fin.rev) a).card =
      (univ.filter fun b => Fin.rev a < b ∧ ε b ≠ ε (Fin.rev a)).card :=
    card_eq_of_rev _ _ fun b => by simp [Fin.rev_lt_rev]
  unfold rhoN
  rw [h1, h2]
  ring

theorem rhoC_rev (ε : Fin n → Bool) (a : Fin n) : rhoC (ε ∘ Fin.rev) a = -rhoC ε (Fin.rev a) := by
  have h1 : (univ.filter fun b => a < b ∧ (ε ∘ Fin.rev) b = (ε ∘ Fin.rev) a).card =
      (univ.filter fun b => b < Fin.rev a ∧ ε b = ε (Fin.rev a)).card :=
    card_eq_of_rev _ _ fun b => by simp [Fin.rev_lt_rev]
  have h2 : (univ.filter fun b => b < a ∧ (ε ∘ Fin.rev) b = (ε ∘ Fin.rev) a).card =
      (univ.filter fun b => Fin.rev a < b ∧ ε b = ε (Fin.rev a)).card :=
    card_eq_of_rev _ _ fun b => by simp [Fin.rev_lt_rev]
  unfold rhoC
  rw [h1, h2]
  ring

theorem lowK_rev (ε : Fin n → Bool) (lam : Fin n → ℝ) (a : Fin n) :
    lowK (ε ∘ Fin.rev) (lamd lam) a = -lowK ε lam (Fin.rev a) := by
  simp only [lowK, Pi.add_apply, Pi.sub_apply, lamd, rhoN_rev, rhoC_rev]
  ring

theorem casVal_rev (lam : Fin n → ℝ) : casVal (lamd lam) = casVal lam := by
  unfold casVal nsq dot
  simp only [lamd, neg_mul_neg]
  congr 1
  exact Equiv.sum_comp Fin.revPerm (fun a => lam a * lam a)

theorem pOf_rev (ε : Fin n → Bool) : pOf (ε ∘ Fin.rev) = pOf ε :=
  card_eq_of_rev _ _ fun b => by simp

theorem qOf_rev (ε : Fin n → Bool) : qOf (ε ∘ Fin.rev) = qOf ε :=
  card_eq_of_rev _ _ fun b => by simp

theorem hNeed_rev (ε : Fin n → Bool) : hNeed (ε ∘ Fin.rev) = hNeed ε := by
  unfold hNeed; rw [pOf_rev, qOf_rev]

theorem gapLap_rev {ε : Fin n → Bool} {lam : Fin n → ℝ} {h : ℝ} (hg : GapLap ε lam h) :
    GapLap (ε ∘ Fin.rev) (lamd lam) h := by
  obtain ⟨hanti, hgap, hh⟩ := hg
  refine ⟨fun a b hab => neg_lt_neg (hanti (Fin.rev_lt_rev.mpr hab)), fun a b hab => ?_, by rwa [hNeed_rev]⟩
  have := hgap (Fin.rev a) (Fin.rev b) hab
  rw [show lamd lam a - lamd lam b = -(lam (Fin.rev a) - lam (Fin.rev b)) by simp only [lamd]; ring, abs_neg]
  exact this

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : Submodule ℂ H}

def cjV (V : Submodule ℂ D) : Submodule ℂ (cjSub D) := V.map (ofDL (D := D))

theorem mem_cjV {V : Submodule ℂ D} (x : cjSub D) : x ∈ cjV V ↔ toD x ∈ V := by
  constructor
  · rintro ⟨u, hu, rfl⟩; exact hu
  · intro h; exact ⟨toD x, h, rfl⟩

theorem ofD_E (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ D) (a b : Fin n) (u : D) :
    ofD (E a b u) = (-(sg ε (Fin.rev b) * sg ε (Fin.rev a))) • Edd ε E (Fin.rev b) (Fin.rev a) (ofD u) := by
  rw [Edd_ofD, smul_ofD, Fin.rev_rev, Fin.rev_rev, smul_smul]
  have h1 : conj (-(sg ε (Fin.rev b) * sg ε (Fin.rev a))) * -(sg ε (Fin.rev b) * sg ε (Fin.rev a)) = 1 := by
    simp only [map_neg, map_mul, conj_sg]
    linear_combination (sg ε (Fin.rev a) * sg ε (Fin.rev a)) * sg_sq ε (Fin.rev b) + sg_sq ε (Fin.rev a)
  rw [h1, one_smul]

theorem kirr_cjV {ε : Fin n → Bool} {lam : Fin n → ℝ} {E : Fin n → Fin n → Module.End ℂ D}
    {V : Submodule ℂ D} (hV : IsKIrrHW ε E (lowK ε lam) V) :
    IsKIrrHW (ε ∘ Fin.rev) (Edd ε E) (lowK (ε ∘ Fin.rev) (lamd lam)) (cjV V) := by
  obtain ⟨hfin, hst, hirr, w, hwV, hw0, hwa, hwb⟩ := hV
  refine ⟨?_, ?_, ?_, ofD w, (mem_cjV _).2 hwV, ?_, ?_, ?_⟩
  · have hfg : V.FG := Module.Finite.iff_fg.mp hfin
    exact Module.Finite.iff_fg.mpr (hfg.map _)
  · intro a b hab v hv
    rw [mem_cjV] at hv ⊢
    exact V.smul_mem _ (hst (Fin.rev b) (Fin.rev a) hab.symm _ hv)
  · intro S' hle hS'
    have hSle : S'.comap (ofDL (D := D)) ≤ V := fun u hu => (mem_cjV (ofD u)).1 (hle hu)
    have hSst : IsKStableSub ε E (S'.comap (ofDL (D := D))) := by
      intro a b hab u hu
      show ofD (E a b u) ∈ S'
      rw [ofD_E ε E a b u]
      refine S'.smul_mem _ (hS' _ _ ?_ _ hu)
      simp [hab]
    rcases hirr _ hSle hSst with h0 | h1
    · left
      rw [eq_bot_iff]
      intro x hx
      have : toD x ∈ S'.comap (ofDL (D := D)) := hx
      rw [h0, Submodule.mem_bot] at this
      rw [Submodule.mem_bot, ← ofD_toD x, this]
      rfl
    · right
      refine le_antisymm hle fun x hx => ?_
      have : toD x ∈ S'.comap (ofDL (D := D)) := by rw [h1]; exact (mem_cjV x).1 hx
      exact this
  · intro h
    apply hw0
    apply ofD_injective
    rw [h]; rfl
  · intro a
    rw [Edd_ofD, hwa, smul_smul, sg_sq, smul_ofD, lowK_rev]
    congr 1
    push_cast
    simp
  · intro a b hab hε
    rw [Edd_ofD, hwb _ _ (Fin.rev_lt_rev.mpr hab) hε.symm, smul_zero]
    rfl

theorem casimir_Edd (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ D) (u : D) :
    casimir (Edd ε E) (ofD u) = ofD (casimir E u) := by
  unfold casimir
  simp only [LinearMap.sum_apply, Module.End.mul_apply, Edd_ofD, ofD_sum, LinearMap.map_smul, smul_smul]
  conv_lhs => rw [sum_rev_swap]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Fin.rev_rev]
  have h1 : -(sg ε (Fin.rev b) * sg ε (Fin.rev a)) * -(sg ε (Fin.rev a) * sg ε (Fin.rev b)) = 1 := by
    linear_combination (sg ε (Fin.rev a) * sg ε (Fin.rev a)) * sg_sq ε (Fin.rev b) + sg_sq ε (Fin.rev a)
  rw [h1, one_smul]

theorem le_genSub' {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (S : Submodule ℂ M) : S ≤ genSub E S := le_sInf fun _ hT => hT.1

theorem genSub_stable' {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (S : Submodule ℂ M) (a b : Fin n) {v : M} (hv : v ∈ genSub E S) : E a b v ∈ genSub E S := by
  unfold genSub at hv ⊢
  rw [Submodule.mem_sInf] at hv ⊢
  intro T hT
  exact hT.2 a b v (hv T hT)

theorem genSub_le' {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    {S T : Submodule ℂ M} (hS : S ≤ T) (hT : ∀ a b, ∀ v ∈ T, E a b v ∈ T) : genSub E S ≤ T :=
  sInf_le ⟨hS, hT⟩

theorem mem_genSub_Edd (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ D) (V : Submodule ℂ D) {u : D}
    (hu : u ∈ genSub E V) : ofD u ∈ genSub (Edd ε E) (cjV V) := by
  have hle : genSub E V ≤ (genSub (Edd ε E) (cjV V)).comap (ofDL (D := D)) := by
    refine genSub_le' E (fun v hv => (le_genSub' (Edd ε E) (cjV V) ((mem_cjV (ofD v)).2 hv) : ofD v ∈ genSub (Edd ε E) (cjV V))) fun a b v hv => ?_
    show ofD (E a b v) ∈ _
    rw [ofD_E ε E a b v]
    exact Submodule.smul_mem _ _ (genSub_stable' (Edd ε E) (cjV V) _ _ (hv : ofD v ∈ genSub (Edd ε E) (cjV V)))
  exact hle hu

def Tf (ε : Fin n → Bool) (f : Fin n → D) : Fin n → cjSub D := fun c => ofD (sg ε c • f (Fin.rev c))

def Tfh (ε : Fin n → Bool) : (Fin n → D) →+ (Fin n → cjSub D) where
  toFun := Tf ε
  map_zero' := by
    funext c
    show ofD (sg ε c • (0 : D)) = 0
    rw [smul_zero]; rfl
  map_add' f g := by
    funext c
    show ofD (sg ε c • (f (Fin.rev c) + g (Fin.rev c))) = ofD (sg ε c • f (Fin.rev c)) + ofD (sg ε c • g (Fin.rev c))
    rw [smul_add, ofD_add]

theorem Tf_smul (ε : Fin n → Bool) (z : ℂ) (f : Fin n → D) : Tfh ε (z • f) = conj z • Tfh ε f := by
  funext c
  show ofD (sg ε c • (z • f (Fin.rev c))) = conj z • ofD (sg ε c • f (Fin.rev c))
  rw [smul_ofD, Complex.conj_conj, smul_comm]

theorem Tf_inj (ε : Fin n → Bool) {g : Fin n → D} (h : Tf ε g = 0) : g = 0 := by
  funext c
  have h1 := congrFun h (Fin.rev c)
  simp only [Tf, Fin.rev_rev, Pi.zero_apply] at h1
  have h2 : sg ε (Fin.rev c) • g c = 0 := ofD_injective (h1.trans ofD_zero.symm)
  exact (smul_eq_zero.mp h2).resolve_left (sg_ne ε _)

theorem weightVector_tensor_eq_dual (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ D) (f : Fin n → D) :
    eeV (Edd ε E) (Tf ε f) = Tf ε (eeVd E f) := by
  funext d
  simp only [Tf, eeV, eeVd, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.neg_apply,
    LinearMap.comp_apply, prj, LinearMap.proj_apply, Edd_ofD, LinearMap.map_smul, smul_smul]
  rw [← ofD_sum]
  congr 1
  rw [smul_neg, Finset.smul_sum, ← Finset.sum_neg_distrib]
  conv_rhs => rw [← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [Fin.revPerm_apply]
  rw [← neg_smul]
  congr 1
  linear_combination (-sg ε d) * sg_sq ε c

theorem prodShift_eq {X : Type*} [AddCommGroup X] [Module ℂ X] (A : Module.End ℂ X) (θ : Fin n → ℝ) :
    prodShift A θ = ((List.ofFn θ).map fun r : ℝ => A - ((r : ℝ) : ℂ) • (1 : Module.End ℂ X)).prod := by
  unfold prodShift; rw [List.map_ofFn]; rfl

theorem prodShift_aeval {X : Type*} [AddCommGroup X] [Module ℂ X] (A : Module.End ℂ X) (θ : Fin n → ℝ) :
    prodShift A θ = Polynomial.aeval A (∏ t, (Polynomial.X - Polynomial.C ((θ t : ℝ) : ℂ))) := by
  rw [← List.prod_ofFn, map_list_prod, List.map_ofFn]
  unfold prodShift
  congr 2
  funext t
  simp [Algebra.algebraMap_eq_smul_one]

theorem prodShift_rev {X : Type*} [AddCommGroup X] [Module ℂ X] (A : Module.End ℂ X) (θ : Fin n → ℝ) :
    prodShift A (fun t => θ (Fin.rev t)) = prodShift A θ := by
  rw [prodShift_aeval, prodShift_aeval]
  congr 1
  exact Equiv.prod_comp Fin.revPerm (fun t => Polynomial.X - Polynomial.C ((θ t : ℝ) : ℂ))

theorem list_inter {X Y : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (T : X →+ Y) (hs : ∀ (z : ℂ) (x : X), T (z • x) = conj z • T x) (A : Module.End ℂ Y)
    (B : Module.End ℂ X) (hAB : ∀ x, T (B x) = A (T x)) (L : List ℝ) (x : X) :
    T ((L.map fun r : ℝ => B - ((r : ℝ) : ℂ) • (1 : Module.End ℂ X)).prod x) =
      (L.map fun r : ℝ => A - ((r : ℝ) : ℂ) • (1 : Module.End ℂ Y)).prod (T x) := by
  induction L with
  | nil => simp
  | cons r L ih =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, Module.End.one_apply]
    rw [map_sub, hAB, hs, Complex.conj_ofReal, ih]

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.DualRepresentationReversal

module

public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
public import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothVec

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MemFiltOfWords
open Finset

noncomputable section

namespace GlobalTheory.CompanionTheory.DSICKoszul

open CompanionTheory.D.DSIC

section Ring

variable {R : Type*} [Ring R] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem homotopy_ring (A D an cr : ι → R)
    (h1 : ∀ i j, Commute (an i) (D j)) (h2 : ∀ i j, Commute (cr i) (A j))
    (h3 : ∀ i j, D i * A j - A j * D i = if i = j then 1 else 0)
    (h4 : ∀ i j, an i * cr j + cr j * an i = if i = j then 1 else 0) :
    (∑ i, A i * an i) * (∑ j, D j * cr j) + (∑ j, D j * cr j) * (∑ i, A i * an i) =
      ∑ i, A i * D i + ∑ i, cr i * an i := by
  have key : ∀ i j, A i * an i * (D j * cr j) + D j * cr j * (A i * an i) =
      (if i = j then A i * D i else 0) + (if i = j then cr i * an i else 0) := by
    intro i j
    have e1 : A i * an i * (D j * cr j) = A i * D j * (an i * cr j) := by
      rw [mul_assoc, ← mul_assoc (an i), (h1 i j).eq, mul_assoc, mul_assoc]
    have e2 : D j * cr j * (A i * an i) = D j * A i * (cr j * an i) := by
      rw [mul_assoc, ← mul_assoc (cr j), (h2 j i).eq, mul_assoc, mul_assoc]
    have e3 : D j * A i = A i * D j + if j = i then 1 else 0 := by
      rw [← h3 j i]; abel
    rw [e1, e2, e3, add_mul, ← add_assoc, ← mul_add, h4]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm (s := univ) (t := univ)
    (f := fun j i => D j * cr j * (A i * an i)), ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  simp only [key, Finset.sum_add_distrib]
  simp


omit [DecidableEq ι] in
theorem sq_ring (A an : ι → R)
    (h1 : ∀ i j, Commute (an i) (A j)) (h2 : ∀ i j, Commute (A i) (A j))
    (h4 : ∀ i j, an i * an j + an j * an i = 0) :
    (∑ i, A i * an i) * (∑ j, A j * an j) + (∑ j, A j * an j) * (∑ i, A i * an i) = 0 := by
  have key : ∀ i j, A i * an i * (A j * an j) + A j * an j * (A i * an i) = 0 := by
    intro i j
    have e1 : A i * an i * (A j * an j) = A i * A j * (an i * an j) := by
      rw [mul_assoc, ← mul_assoc (an i), (h1 i j).eq, mul_assoc, mul_assoc]
    have e2 : A j * an j * (A i * an i) = A j * A i * (an j * an i) := by
      rw [mul_assoc, ← mul_assoc (an j), (h1 j i).eq, mul_assoc, mul_assoc]
    rw [e1, e2, (h2 j i).eq, ← mul_add, h4, mul_zero]
  conv_lhs => congr; rw [Finset.sum_mul_sum]; rfl; rw [Finset.sum_mul_sum, Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun j _ => key i j

theorem euler_ring (A D : ι → R) (h2 : ∀ i j, Commute (D i) (D j))
    (h3 : ∀ i j, D i * A j - A j * D i = if i = j then 1 else 0) (i : ι) :
    D i * (∑ j, A j * D j) = (∑ j, A j * D j) * D i + D i := by
  have key : ∀ j, D i * (A j * D j) = A j * D j * D i + if i = j then D i else 0 := by
    intro j
    have e3 : D i * A j = A j * D i + if i = j then 1 else 0 := by
      rw [← h3 i j]; abel
    rw [← mul_assoc, e3, add_mul, mul_assoc, (h2 i j).eq, ← mul_assoc]
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  rw [Finset.mul_sum, Finset.sum_mul]
  simp only [key, Finset.sum_add_distrib]
  simp

end Ring

section Filt

variable {Z : Type*} [AddCommGroup Z] [Module ℂ Z] {ι : Type*}

def filt (d : ι → Module.End ℂ Z) (m : ℕ) : Submodule ℂ Z :=
  Nat.rec (motive := fun _ => Submodule ℂ Z) ⊥ (fun _ S => ⨅ i, S.comap (d i)) m

theorem mem_filt_succ (d : ι → Module.End ℂ Z) (m : ℕ) (z : Z) :
    z ∈ filt d (m + 1) ↔ ∀ i, d i z ∈ filt d m := by
  show z ∈ (⨅ i, (filt d m).comap (d i)) ↔ _
  simp [Submodule.mem_iInf]

theorem filt_mono (d : ι → Module.End ℂ Z) : Monotone (filt d) := by
  refine monotone_nat_of_le_succ fun m => ?_
  induction m with
  | zero => exact bot_le
  | succ m ih =>
    intro z hz
    rw [mem_filt_succ] at hz ⊢
    exact fun i => ih (hz i)

theorem mem_filt_of_words (d : ι → Module.End ℂ Z) (m : ℕ) (z : Z)
    (h : ∀ l : List ι, l.length = m → (l.map d).prod z = 0) : z ∈ filt d m := by
  induction m generalizing z with
  | zero => simpa [filt] using h [] rfl
  | succ m ih =>
    rw [mem_filt_succ]
    intro i
    refine ih _ fun l hl => ?_
    have := h (l ++ [i]) (by simp [hl])
    simpa using this

theorem euler_filt [Fintype ι] [DecidableEq ι] (a d : ι → Module.End ℂ Z) (h2 : ∀ i j, Commute (d i) (d j))
    (h3 : ∀ i j, d i * a j - a j * d i = if i = j then 1 else 0) (m : ℕ) (z : Z)
    (hz : z ∈ filt d (m + 1)) : (∑ j, a j * d j) z - (m : ℂ) • z ∈ filt d m := by
  induction m generalizing z with
  | zero =>
    rw [mem_filt_succ] at hz
    have h0 : ∀ i, d i z = 0 := fun i => by simpa [filt] using hz i
    simp [filt, LinearMap.sum_apply, h0]
  | succ m ih =>
    rw [mem_filt_succ] at hz ⊢
    intro i
    have e := congrArg (fun T : Module.End ℂ Z => T z) (euler_ring a d h2 h3 i)
    simp only [Module.End.mul_apply, LinearMap.add_apply] at e
    have := ih _ (hz i)
    convert this using 1
    rw [map_sub, e, map_smul]
    push_cast
    rw [add_smul, one_smul]
    abel

end Filt

variable {n : ℕ} {ε : Fin n → Bool} {Z : Type} [AddCommGroup Z] [Module ℂ Z]

theorem lift_mul (S T : Module.End ℂ Z) :
    (lift ε (S * T) : Module.End ℂ (Ch ε Z)) = lift ε S * lift ε T := rfl

theorem ann_lift (i : NC ε) (T : Module.End ℂ Z) :
    Commute (ann i : Module.End ℂ (Ch ε Z)) (lift ε T) := by
  refine LinearMap.ext fun x => funext fun A => ?_
  by_cases h : i ∈ A <;> simp [ann, h]

theorem cre_lift (i : NC ε) (T : Module.End ℂ Z) :
    Commute (cre i : Module.End ℂ (Ch ε Z)) (lift ε T) := by
  refine LinearMap.ext fun x => funext fun A => ?_
  by_cases h : i ∈ A <;> simp [cre, h]

theorem cre_ann_apply (i : NC ε) (x : Ch ε Z) (A : Finset (NC ε)) :
    (cre i (ann i x)) A = if i ∈ A then x A else 0 := by
  by_cases h : i ∈ A
  · have e : sg i (A.erase i) = sg i A := by
      unfold sg
      congr 2
      ext j
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨_, h1⟩, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨fun hh => by rw [hh] at h2; exact lt_irrefl _ h2, h1⟩, h2⟩
    have e2 : sg i A * sg i A = 1 := by
      unfold sg
      rw [← mul_pow]; simp
    simp [cre, ann, h, e, Finset.insert_erase h, smul_smul, e2]
  · simp [cre, h]

theorem number_apply (x : Ch ε Z) (A : Finset (NC ε)) :
    ((∑ i : NC ε, (cre i * ann i : Module.End ℂ (Ch ε Z))) x) A = (A.card : ℂ) • x A := by
  rw [LinearMap.sum_apply, Finset.sum_apply]
  simp only [Module.End.mul_apply, cre_ann_apply]
  rw [← Finset.sum_filter]
  simp [Nat.cast_smul_eq_nsmul]

theorem deg_h (d : NC ε → Module.End ℂ Z) (j : ℕ) (x : Ch ε Z) (hx : Deg j x) :
    Deg (j + 1) ((∑ i : NC ε, ((lift ε (d i) : Module.End ℂ (Ch ε Z)) * cre i : Module.End ℂ (Ch ε Z))) x) := by
  intro A hA
  rw [LinearMap.sum_apply, Finset.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases h : i ∈ A
  · have : x (A.erase i) = 0 := hx _ (by
      have := Finset.card_erase_add_one h
      omega)
    simp [cre, h, this]
  · simp [cre, h]

theorem koszul : CAR → Koszul := by
  intro hC n ε Z _ _ a d ha hd hda hnil j x hx hcyc
  set H : Module.End ℂ (Ch ε Z) := ∑ i : NC ε, (lift ε (d i) : Module.End ℂ (Ch ε Z)) * cre i with hH
  have hom : bdA a * H + H * bdA a =
      ∑ i, (lift ε (a i) : Module.End ℂ (Ch ε Z)) * lift ε (d i) + ∑ i, cre i * ann i := by
    refine homotopy_ring (fun i => (lift ε (a i) : Module.End ℂ (Ch ε Z))) (fun i => lift ε (d i)) ann cre
      (fun i j => ann_lift _ _) (fun i j => cre_lift _ _) (fun i j => ?_) (fun i j => (hC n ε Z i j).2.2)
    refine LinearMap.ext fun y => funext fun A => ?_
    have e := congrArg (fun T : Module.End ℂ Z => T (y A)) (hda i j)
    by_cases h : i = j
    · simpa [h] using e
    · simpa [h] using e
  have hsq : ∀ y : Ch ε Z, bdA a (bdA a y) = 0 := by
    intro y
    have e : bdA a * bdA a + bdA a * bdA a = 0 :=
      sq_ring (fun i => (lift ε (a i) : Module.End ℂ (Ch ε Z))) ann (fun i j => ann_lift _ _)
        (fun i j => by
          show lift ε (a i) * lift ε (a j) = lift ε (a j) * lift ε (a i)
          rw [← lift_mul, ← lift_mul, (ha i j).eq]) (fun i j => (hC n ε Z i j).1)
    have e2 := congrArg (fun T : Module.End ℂ (Ch ε Z) => T y) e
    simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply] at e2
    rw [← two_smul ℂ] at e2
    exact (smul_eq_zero.mp e2).resolve_left two_ne_zero
  have main : ∀ (m : ℕ) (y : Ch ε Z), (∀ A, y A ∈ filt d m) → Deg (j + 1) y → bdA a y = 0 →
      ∃ t : Ch ε Z, Deg (j + 2) t ∧ bdA a t = y := by
    intro m
    induction m with
    | zero =>
      intro y hy _ _
      refine ⟨0, fun _ _ => rfl, ?_⟩
      rw [map_zero]
      funext A
      have hA : y A ∈ (⊥ : Submodule ℂ Z) := hy A
      have hA0 : y A = 0 := by simpa only [Submodule.mem_bot] using hA
      exact hA0.symm
    | succ m ih =>
      intro y hy hdeg hc
      have hne : ((m : ℂ) + (j + 1 : ℕ)) ≠ 0 := by
        exact_mod_cast (by omega : m + (j + 1) ≠ 0)
      have hw : ∀ A, (bdA a (H y) - ((m : ℂ) + (j + 1 : ℕ)) • y) A =
          (∑ i, a i * d i) (y A) - (m : ℂ) • y A := by
        intro A
        have e := congrArg (fun T : Module.End ℂ (Ch ε Z) => T y A) hom
        simp only [LinearMap.add_apply, Module.End.mul_apply, hc, map_zero, Pi.add_apply, Pi.zero_apply, add_zero,
          number_apply] at e
        have e2 : (A.card : ℂ) • y A = ((j + 1 : ℕ) : ℂ) • y A := by
          by_cases h : A.card = j + 1
          · rw [h]
          · rw [hdeg A h, smul_zero, smul_zero]
        have e3 : ((∑ i, (lift ε (a i) : Module.End ℂ (Ch ε Z)) * lift ε (d i)) y) A =
            (∑ i, a i * d i) (y A) := by
          rw [LinearMap.sum_apply, Finset.sum_apply, LinearMap.sum_apply]
          rfl
        rw [Pi.sub_apply, e, e2, e3, Pi.smul_apply, add_smul]
        abel
      obtain ⟨t, ht, hbt⟩ := ih (bdA a (H y) - ((m : ℂ) + (j + 1 : ℕ)) • y)
        (fun A => by rw [hw]; exact euler_filt a d hd hda m _ (hy A))
        (fun A hA => by rw [hw, hdeg A hA]; simp)
        (by rw [map_sub, hsq, map_smul, hc]; simp)
      refine ⟨((m : ℂ) + (j + 1 : ℕ))⁻¹ • (H y - t), fun A hA => ?_, ?_⟩
      · have := deg_h d (j + 1) y hdeg A hA
        rw [Pi.smul_apply, Pi.sub_apply, ht A hA, this]
        simp
      · rw [map_smul, map_sub, hbt, sub_sub_cancel, smul_smul, inv_mul_cancel₀ hne, one_smul]
  choose f hf using hnil
  refine main (univ.sup fun A => f (x A)) x (fun A => ?_) hx hcyc
  exact filt_mono d (Finset.le_sup (f := fun A => f (x A)) (mem_univ A)) (mem_filt_of_words d _ _ (hf _))

end GlobalTheory.CompanionTheory.DSICKoszul
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.WordMonomial
open scoped TensorProduct
open MvPolynomial

noncomputable section

namespace GlobalTheory.CompanionTheory.DSCover

open Formalism.REAL (GlRel)
open CompanionTheory.D.DSIC

theorem glRel_add {A : Type} [Ring A] {n : ℕ} {E F : Fin n → Fin n → A} (hE : GlRel E) (hF : GlRel F)
    (h : ∀ a b c d, E a b * F c d = F c d * E a b) : GlRel fun a b => E a b + F a b := by
  intro a b c d
  have h1 := hE a b c d
  have h2 := hF a b c d
  have h3 := h a b c d
  have h4 := h c d a b
  have e : (E a b + F a b) * (E c d + F c d) - (E c d + F c d) * (E a b + F a b) =
      (E a b * E c d - E c d * E a b) + (F a b * F c d - F c d * F a b) := by
    simp only [add_mul, mul_add, h3, h4]
    abel
  beta_reduce
  rw [e, h1, h2]
  split_ifs <;> abel

theorem glRel_map {A B : Type} [Ring A] [Ring B] (φ : A →+* B) {n : ℕ} {E : Fin n → Fin n → A} (hE : GlRel E) :
    GlRel fun a b => φ (E a b) := by
  intro a b c d
  have h := congrArg φ (hE a b c d)
  simp only [map_sub, map_mul] at h
  rw [h]
  split_ifs <;> simp

section Pol

variable {σ : Type}

def pd (i : σ) : Module.End ℂ (MvPolynomial σ ℂ) := (pderiv i : Derivation ℂ (MvPolynomial σ ℂ) _).toLinearMap

theorem pd_apply (i : σ) (f : MvPolynomial σ ℂ) : pd i f = pderiv i f := rfl

theorem pd_comm (i j : σ) : pd i * pd j = pd j * pd i := by
  classical
  apply LinearMap.ext
  intro f
  simp only [Module.End.mul_apply, pd_apply]
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p k hp =>
    simp only [Derivation.leibniz, map_add (f := _), smul_eq_mul, pderiv_X, hp]
    by_cases h1 : i = k <;> by_cases h2 : j = k <;> simp [h1, h2, add_comm]

theorem word_monomial (l : List σ) : ∀ (s : σ →₀ ℕ) (c : ℂ), s.degree < l.length →
    (l.map pd).prod (monomial s c) = 0 := by
  induction l using List.reverseRecOn with
  | nil => intro s c h; simp at h
  | append_singleton l i ih =>
    intro s c h
    rw [List.map_append, List.prod_append]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, Module.End.mul_apply, pd_apply,
      pderiv_monomial]
    by_cases hs : s i = 0
    · simp [hs]
    · apply ih
      have e : s = (s - Finsupp.single i 1) + Finsupp.single i 1 := by
        rw [tsub_add_cancel_of_le]
        rw [Finsupp.single_le_iff]
        omega
      have e2 := congrArg Finsupp.degree e
      rw [map_add (f := _), Finsupp.degree_single] at e2
      simp only [List.length_append, List.length_singleton] at h
      omega

theorem word_pol (f : MvPolynomial σ ℂ) : ∃ m : ℕ, ∀ l : List σ, m ≤ l.length → (l.map pd).prod f = 0 := by
  induction f using MvPolynomial.induction_on' with
  | monomial s c => exact ⟨s.degree + 1, fun l hl => word_monomial l s c (by omega)⟩
  | add p q hp hq =>
    obtain ⟨m, hm⟩ := hp
    obtain ⟨k, hk⟩ := hq
    exact ⟨max m k, fun l hl => by
      rw [map_add (f := _), hm l (le_trans (le_max_left _ _) hl), hk l (le_trans (le_max_right _ _) hl), add_zero]⟩

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem word_tmul (l : List σ) (v : V) (f : MvPolynomial σ ℂ) :
    (l.map fun i => ((pd i).lTensor V : Module.End ℂ (V ⊗[ℂ] MvPolynomial σ ℂ))).prod (v ⊗ₜ f) =
      v ⊗ₜ (l.map pd).prod f := by
  induction l with
  | nil => simp
  | cons i l ih => simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, ih, LinearMap.lTensor_tmul]

theorem word_tens (z : V ⊗[ℂ] MvPolynomial σ ℂ) : ∃ m : ℕ, ∀ l : List σ, m ≤ l.length →
    (l.map fun i => ((pd i).lTensor V : Module.End ℂ (V ⊗[ℂ] MvPolynomial σ ℂ))).prod z = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, fun l _ => map_zero _⟩
  | tmul v f =>
    obtain ⟨m, hm⟩ := word_pol f
    exact ⟨m, fun l hl => by rw [word_tmul, hm l hl, TensorProduct.tmul_zero]⟩
  | add p q hp hq =>
    obtain ⟨m, hm⟩ := hp
    obtain ⟨k, hk⟩ := hq
    exact ⟨max m k, fun l hl => by
      rw [map_add (f := _), hm l (le_trans (le_max_left _ _) hl), hk l (le_trans (le_max_right _ _) hl), add_zero]⟩

end Pol

theorem cover : Koszul → Verma → Cover := by
  intro hK hV n ε V _ _ E hE
  classical
  obtain ⟨M, hM, hX, h0⟩ := hV n ε
  let P := MvPolynomial (NC ε) ℂ
  let EY : Fin n → Fin n → Module.End ℂ (V ⊗[ℂ] P) := fun a b => (E a b).rTensor P + (M a b).lTensor V
  have hEY : GlRel EY := by
    refine glRel_add (E := fun a b => ((E a b).rTensor P : Module.End ℂ (V ⊗[ℂ] P)))
      (F := fun a b => ((M a b).lTensor V : Module.End ℂ (V ⊗[ℂ] P))) ?_ ?_ ?_
    · exact glRel_map (Module.End.rTensorAlgHom ℂ V P).toRingHom hE
    · exact glRel_map (Module.End.lTensorAlgHom ℂ P V).toRingHom hM
    · intro a b c d
      apply TensorProduct.ext'
      intro v f
      simp [Module.End.mul_apply]
  let cc : P →ₗ[ℂ] ℂ := (MvPolynomial.lcoeff ℂ (0 : NC ε →₀ ℕ))
  have hcc : ∀ f : P, cc f = constantCoeff f := fun f => rfl
  refine ⟨V ⊗[ℂ] P, inferInstance, inferInstance, EY, (TensorProduct.rid ℂ V).toLinearMap ∘ₗ cc.lTensor V,
    hEY, ?_, ?_, ?_⟩
  · intro v
    exact ⟨v ⊗ₜ 1, by simp [hcc]⟩
  · intro a b y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v f => simp [EY, hcc, h0]
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
  · refine hK n ε (V ⊗[ℂ] P) (fun i => EY i.1.1 i.1.2) (fun i => (pd i).lTensor V) ?_ ?_ ?_ ?_
    · intro i j
      have h := hEY i.1.1 i.1.2 j.1.1 j.1.2
      have h1 : i.1.2 ≠ j.1.1 := fun e => by
        have := i.2.2; rw [e, j.2.1] at this; exact Bool.noConfusion this
      have h2 : j.1.2 ≠ i.1.1 := fun e => by
        have := j.2.2; rw [e, i.2.1] at this; exact Bool.noConfusion this
      rw [if_neg h1, if_neg h2, sub_zero, sub_eq_zero] at h
      exact h
    · intro i j
      apply TensorProduct.ext'
      intro v f
      have := congrArg (fun T : Module.End ℂ P => T f) (pd_comm i j)
      simp only [Module.End.mul_apply] at this
      simp only [Module.End.mul_apply, LinearMap.lTensor_tmul, this]
    · intro i j
      apply TensorProduct.ext'
      intro v f
      simp only [EY, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply, LinearMap.lTensor_tmul,
        LinearMap.rTensor_tmul, map_add, hX, pd_apply, Derivation.leibniz, pderiv_X, smul_eq_mul,
        TensorProduct.tmul_add]
      by_cases h : i = j
      · subst h; simp
      · simp [h, Ne.symm h]
    · intro z
      obtain ⟨m, hm⟩ := word_tens z
      exact ⟨m, fun l hl => hm l hl.ge⟩

end GlobalTheory.CompanionTheory.DSCover
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.KummerLiftedCocycleImageEqPicardClass
open Finset

noncomputable section

namespace GlobalTheory.CompanionTheory.DSVerma

open CompanionTheory.D.DSIC Formalism.REAL

variable {n : ℕ} {ε : Fin n → Bool}

theorem sum_nc {R : Type} [AddCommMonoid R] (d b : Fin n) (g : Fin n → Fin n → R) :
    (∑ j : NC ε, if d = j.1.1 ∧ b = j.1.2 then g j.1.1 j.1.2 else 0) =
      if ε d = true ∧ ε b = false then g d b else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨(d, b), h⟩ : NC ε)]
    · simp
    · intro j _ hj
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact hj (Subtype.ext (Prod.ext h1.symm h2.symm))
    · simp
  · refine Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact h (by rw [h1, h2]; exact j.2)

section Abstract

variable {R : Type} [Ring R] (Y : NC ε → R) (u v : Fin n → Fin n → R)

theorem inner_sum
    (huY : ∀ a c j, u a c * Y j - Y j * u a c = -(if a = j.1.1 ∧ c = j.1.2 then 1 else 0))
    (hvY : ∀ a c j, v a c * Y j - Y j * v a c = if a = j.1.1 ∧ c = j.1.2 then 1 else 0)
    (i : NC ε) (c d e f : Fin n) :
    (∑ j : NC ε, ((u i.1.1 c * v d i.1.2) * Y j - Y j * (u i.1.1 c * v d i.1.2)) * (u j.1.1 e * v f j.1.2)) =
      u i.1.1 c * (if ε d = true then u d e else 0) * v f i.1.2 -
        v d i.1.2 * u i.1.1 e * (if ε c = false then v f c else 0) := by
  have h1 : ∀ j : NC ε, ((u i.1.1 c * v d i.1.2) * Y j - Y j * (u i.1.1 c * v d i.1.2)) * (u j.1.1 e * v f j.1.2) =
      (if d = j.1.1 ∧ i.1.2 = j.1.2 then u i.1.1 c * u j.1.1 e * v f j.1.2 else 0) -
        (if i.1.1 = j.1.1 ∧ c = j.1.2 then v d i.1.2 * u j.1.1 e * v f j.1.2 else 0) := by
    intro j
    have : (u i.1.1 c * v d i.1.2) * Y j - Y j * (u i.1.1 c * v d i.1.2) =
        u i.1.1 c * (v d i.1.2 * Y j - Y j * v d i.1.2) + (u i.1.1 c * Y j - Y j * u i.1.1 c) * v d i.1.2 := by
      noncomm_ring
    rw [this, huY, hvY]
    split_ifs <;> noncomm_ring
  simp only [h1, Finset.sum_sub_distrib]
  rw [sum_nc d i.1.2 (fun a b => u i.1.1 c * u a e * v f b),
    sum_nc i.1.1 c (fun a b => v d i.1.2 * u a e * v f b)]
  simp only [i.2.1, i.2.2, and_true, true_and]
  split_ifs <;> simp

theorem glRel_abstract (hYY : ∀ i j, Commute (Y i) (Y j))
    (huu : ∀ a b c d, Commute (u a b) (u c d)) (huv : ∀ a b c d, Commute (u a b) (v c d))
    (hvv : ∀ a b c d, Commute (v a b) (v c d))
    (huY : ∀ a c j, u a c * Y j - Y j * u a c = -(if a = j.1.1 ∧ c = j.1.2 then 1 else 0))
    (hvY : ∀ a c j, v a c * Y j - Y j * v a c = if a = j.1.1 ∧ c = j.1.2 then 1 else 0)
    (hs : ∀ d e, (if ε d = true then u d e else 0) + (if ε e = false then v d e else 0) =
      if d = e then 1 else 0) (c d e f : Fin n) :
    (∑ i : NC ε, Y i * (u i.1.1 c * v d i.1.2)) * (∑ i : NC ε, Y i * (u i.1.1 e * v f i.1.2)) -
      (∑ i : NC ε, Y i * (u i.1.1 e * v f i.1.2)) * (∑ i : NC ε, Y i * (u i.1.1 c * v d i.1.2)) =
      (if d = e then ∑ i : NC ε, Y i * (u i.1.1 c * v f i.1.2) else 0) -
        (if f = c then ∑ i : NC ε, Y i * (u i.1.1 e * v d i.1.2) else 0) := by
  have hprod : ∀ p q : NC ε → R, (∑ i, Y i * p i) * (∑ j, Y j * q j) =
      ∑ i, ∑ j, Y i * Y j * (p i * q j) + ∑ i, Y i * ∑ j, (p i * Y j - Y j * p i) * q j := by
    intro p q
    rw [Finset.sum_mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    noncomm_ring
  rw [hprod, hprod]
  have hsym : (∑ i : NC ε, ∑ j : NC ε, Y i * Y j * (u i.1.1 c * v d i.1.2 * (u j.1.1 e * v f j.1.2))) =
      ∑ i : NC ε, ∑ j : NC ε, Y i * Y j * (u i.1.1 e * v f i.1.2 * (u j.1.1 c * v d j.1.2)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [(hYY j i).eq, (((huu _ _ _ _).mul_right (huv _ _ _ _)).mul_left
      ((huv _ _ _ _).symm.mul_right (hvv _ _ _ _))).eq]
  rw [hsym, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  have key : ∀ i : NC ε,
      Y i * (∑ j : NC ε, ((u i.1.1 c * v d i.1.2) * Y j - Y j * (u i.1.1 c * v d i.1.2)) * (u j.1.1 e * v f j.1.2)) -
      Y i * (∑ j : NC ε, ((u i.1.1 e * v f i.1.2) * Y j - Y j * (u i.1.1 e * v f i.1.2)) * (u j.1.1 c * v d j.1.2)) =
      (if d = e then Y i * (u i.1.1 c * v f i.1.2) else 0) -
        (if f = c then Y i * (u i.1.1 e * v d i.1.2) else 0) := by
    intro i
    rw [inner_sum Y u v huY hvY, inner_sum Y u v huY hvY]
    have e1 : ∀ c d e f : Fin n, v d i.1.2 * u i.1.1 e * (if ε c = false then v f c else 0) =
        u i.1.1 e * (if ε c = false then v f c else 0) * v d i.1.2 := by
      intro c d e f
      split_ifs
      · rw [mul_assoc]
        exact ((huv _ _ _ _).symm.mul_right (hvv _ _ _ _)).eq
      · simp
    rw [e1, e1]
    have h1 := hs d e
    have h2 := hs f c
    generalize (if ε d = true then u d e else 0) = A at *
    generalize (if ε e = false then v d e else 0) = B at *
    generalize (if ε f = true then u f c else 0) = C at *
    generalize (if ε c = false then v f c else 0) = D at *
    calc _ = Y i * (u i.1.1 c * (A + B) * v f i.1.2) - Y i * (u i.1.1 e * (C + D) * v d i.1.2) := by noncomm_ring
      _ = _ := by rw [h1, h2]; split_ifs <;> simp
  simp only [key, Finset.sum_sub_distrib]
  split_ifs <;> simp

end Abstract

open MvPolynomial

def dd (ε : Fin n → Bool) (a b : Fin n) : Module.End ℂ (MvPolynomial (NC ε) ℂ) :=
  if h : ε a = true ∧ ε b = false then (pderiv (⟨(a, b), h⟩ : NC ε)).toLinearMap else 0

def yy (i : NC ε) : Module.End ℂ (MvPolynomial (NC ε) ℂ) := LinearMap.mulLeft ℂ (X i)

theorem pderiv_comm' {σ : Type} (i j : σ) (f : MvPolynomial σ ℂ) :
    pderiv i (pderiv j f) = pderiv j (pderiv i f) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p k hp =>
    simp only [Derivation.leibniz, map_add (f := _), smul_eq_mul, hp, pderiv_X, Pi.single_apply]
    split_ifs <;> simp <;> ring

theorem dd_comm (a b c d : Fin n) : Commute (dd ε a b) (dd ε c d) := by
  unfold dd
  split_ifs
  · refine LinearMap.ext fun f => ?_
    exact pderiv_comm' _ _ f
  all_goals simp

theorem dd_yy (a c : Fin n) (j : NC ε) :
    dd ε a c * yy j - yy j * dd ε a c = if a = j.1.1 ∧ c = j.1.2 then 1 else 0 := by
  classical
  unfold dd yy
  split_ifs with h1 h2 h2
  · refine LinearMap.ext fun f => ?_
    have : j = ⟨(a, c), h1⟩ := Subtype.ext (Prod.ext h2.1.symm h2.2.symm)
    subst this
    simp
  · refine LinearMap.ext fun f => ?_
    have : j ≠ ⟨(a, c), h1⟩ := by
      rintro rfl
      exact h2 ⟨rfl, rfl⟩
    simp [pderiv_X_of_ne this]
  · exact absurd (by rw [h2.1, h2.2]; exact j.2) h1
  · simp

theorem verma : CompanionTheory.D.DSIC.Verma := by
  intro n ε
  let u : Fin n → Fin n → Module.End ℂ (MvPolynomial (NC ε) ℂ) := fun a c => (if a = c then 1 else 0) - dd ε a c
  let v : Fin n → Fin n → Module.End ℂ (MvPolynomial (NC ε) ℂ) := fun a c => (if a = c then 1 else 0) + dd ε a c
  have hδ : ∀ (a c : Fin n) (T : Module.End ℂ (MvPolynomial (NC ε) ℂ)),
      Commute (if a = c then 1 else 0) T := by
    intro a c T
    split_ifs <;> simp
  refine ⟨fun c d => ∑ i : NC ε, yy i * (u i.1.1 c * v d i.1.2), ?_, ?_, ?_⟩
  · intro c d e f
    refine glRel_abstract yy u v ?_ ?_ ?_ ?_ ?_ ?_ ?_ c d e f
    · intro i j
      refine LinearMap.ext fun f => ?_
      simp [yy, mul_left_comm]
    · intro a b c d
      exact (hδ _ _ _).sub_left ((hδ _ _ _).symm.sub_right (dd_comm _ _ _ _))
    · intro a b c d
      exact (hδ _ _ _).sub_left ((hδ _ _ _).symm.add_right (dd_comm _ _ _ _))
    · intro a b c d
      exact (hδ _ _ _).add_left ((hδ _ _ _).symm.add_right (dd_comm _ _ _ _))
    · intro a c j
      rw [← dd_yy]
      simp only [u, sub_mul, mul_sub, (hδ a c (yy j)).eq]
      abel
    · intro a c j
      rw [← dd_yy]
      simp only [v, add_mul, mul_add, (hδ a c (yy j)).eq]
      abel
    · intro d e
      have h0 : ¬(ε d = true ∧ ε e = false) → dd ε d e = 0 := fun h => dif_neg h
      simp only [u, v]
      generalize dd ε d e = T at *
      by_cases hde : d = e
      · subst hde
        cases h : ε d <;> simp_all
      · cases h : ε d <;> cases h' : ε e <;> simp_all
  · intro i f
    have hu : ∀ j : NC ε, u j.1.1 i.1.1 = if j.1.1 = i.1.1 then 1 else 0 := by
      intro j
      simp [u, dd, i.2.1]
    have hv : ∀ j : NC ε, v i.1.2 j.1.2 = if i.1.2 = j.1.2 then 1 else 0 := by
      intro j
      simp [v, dd, i.2.2]
    simp only [hu, hv]
    rw [Finset.sum_eq_single i]
    · simp [yy]
    · intro j _ hj
      split_ifs with h1 h2
      · exact absurd (Subtype.ext (Prod.ext h1 h2.symm)) hj
      all_goals simp
    · simp
  · intro a b f
    set_option synthInstance.maxHeartbeats 100000 in
      simp [yy, LinearMap.sum_apply, map_sum]

end GlobalTheory.CompanionTheory.DSVerma
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MulMemUJset
open Matrix PI.UpqRep CompanionTheory.D.Upq.Sm

namespace GlobalTheory.CompanionTheory.DSSmLin

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem mul_mem_UJset {n : ℕ} (ε : Fin n → Bool) (a b : Matrix (Fin n) (Fin n) ℂ) (ha : a ∈ UJset ε)
    (hb : b ∈ UJset ε) : a * b ∈ UJset ε := by
  simp only [UJset, Set.mem_setOf_eq, inUJ, Matrix.conjTranspose_mul] at *
  calc bᴴ * aᴴ * Jm ε * (a * b) = bᴴ * (aᴴ * Jm ε * a) * b := by simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [ha, hb]

theorem ex_mem_UJset {n : ℕ} {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (t : ℝ) :
    ex X t ∈ UJset ε :=
  Formalism.REAL.exp_indefinite_unitary_holds n ε X hX t

theorem inG_add {n : ℕ} {ε : Fin n → Bool} {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (hY : inG ε Y) :
    inG ε (X + Y) := by
  unfold inG at *
  rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hX, hY, add_zero]

theorem inG_smul {n : ℕ} {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (s : ℝ) :
    inG ε ((s : ℂ) • X) := by
  unfold inG at *
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, Complex.star_def, Complex.conj_ofReal,
    ← smul_add, hX, smul_zero]

theorem smLin : CompanionTheory.D.DSIC.SmLin := by
  intro n ε H _ _ σ hσ
  obtain ⟨⟨h1, hm⟩, -, -⟩ := hσ
  have h : RepOn (UJset ε) σ := ⟨by simp [UJset, inUJ], fun a ha b hb => mul_mem_UJset ε a b ha hb, h1, hm⟩
  refine ⟨(IsSm.zero : IsSm (UJset ε) σ 0), fun v hv w hw => ?_, fun c v hv => ?_, fun g hg v hv => ?_,
    fun X hX v hv => ?_, fun X Y hX hY v hv => ?_⟩
  · exact IsSm.add (G := UJset ε) hv hw
  · exact IsSm.smul (G := UJset ε) hv c
  · exact IsSm.apply h hv hg
  · have hv' : IsSm (UJset ε) σ v := hv
    refine ⟨hv'.dsW h (W := [X]) fun Y hY t => ?_, (hv'.differentiableAt h (ex_mem_UJset hX)).hasDerivAt⟩
    rw [List.mem_singleton.1 hY]
    exact ex_mem_UJset hX t
  · have hv' : IsSm (UJset ε) σ v := hv
    obtain ⟨U, F, hU, h1U, hF, hfF⟩ := hv' 1 h.one_mem
    have key : ∀ Z, inG ε Z → PI.PhMeasCore.dsig σ Z v = fderiv ℝ F 1 Z := fun Z hZ => by
      have hd : HasDerivAt (fun t => ex Z t) Z 0 := by simpa using hasDerivAt_mul_ex 1 Z
      exact (hasDerivAt_local (f := fun g => σ g v) (ex_mem_UJset hZ) (ex_zero Z) hd hU h1U hF hfF).deriv
    refine ⟨?_, fun s => ?_⟩
    · rw [key _ (inG_add hX hY), key _ hX, key _ hY, map_add (f := _)]
    · rw [key _ (inG_smul hX s), key _ hX, Complex.coe_smul, Complex.coe_smul, map_smul]

end GlobalTheory.CompanionTheory.DSSmLin
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AlgCoreSubOfAlgCore
open Formalism.REAL CompanionTheory.D.DSIC

noncomputable section

namespace GlobalTheory.CompanionTheory.DSCoreSub

variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] {n : ℕ}

theorem ofFn_prod_intertwine (φ : V' →ₗ[ℂ] V) :
    ∀ {t : ℕ} (f' : Fin t → Module.End ℂ V') (f : Fin t → Module.End ℂ V),
      (∀ k x, φ (f' k x) = f k (φ x)) → ∀ x, φ ((List.ofFn f').prod x) = (List.ofFn f).prod (φ x)
  | 0, _, _, _, x => by simp
  | t + 1, f', f, h, x => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, Module.End.mul_apply,
      Module.End.mul_apply, h, ofFn_prod_intertwine φ _ (fun k => f k.succ) (fun k => h k.succ)]

theorem qdet_intertwine (φ : V' →ₗ[ℂ] V) (E' : Fin n → Fin n → Module.End ℂ V')
    (E : Fin n → Fin n → Module.End ℂ V) (h : ∀ a b x, φ (E' a b x) = E a b (φ x)) (u : ℂ) (x : V') :
    φ (qdet E' u x) = qdet E u (φ x) := by
  unfold qdet qminor
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.sum_apply, map_sum, Module.End.mul_apply, Module.End.intCast_apply, map_zsmul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  refine ofFn_prod_intertwine φ _ _ (fun k y => ?_) x
  unfold Tm
  split_ifs <;> simp [h, Module.algebraMap_end_apply]

theorem algCoreSub_of_algCore : AlgCore → AlgCoreSub := by
  intro hA n ε lam V _ _ E V₀ v S hlam hgl hun hst hS hv hfd hK hvS hmin Y
  let E' : Fin n → Fin n → Module.End ℂ V₀ := fun a b => (E a b).restrict (hst a b)
  have hE : ∀ a b (x : V₀), ((E' a b x : V₀) : V) = E a b x := fun a b x => rfl
  have hhi : ∀ (μ : Fin n → ℝ) (x : V₀), KHighest ε E' μ x ↔ KHighest ε E μ (x : V) := by
    intro μ x
    unfold KHighest IsWeight
    simp only [Subtype.ext_iff, hE, Submodule.coe_smul, Submodule.coe_zero]
  have hgl' : GlRel E' := by
    intro a b c d
    ext x
    have := LinearMap.congr_fun (hgl a b c d) (x : V)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, hE] at this ⊢
    rw [this]
    split_ifs <;> simp [hE]
  have hun' : IsUnitary ε E' := fun a b x y => hun a b x y
  haveI : FiniteDimensional ℂ (S.comap V₀.subtype) :=
    (Submodule.comapSubtypeEquivOfLe hS).symm.finiteDimensional
  have key := hA n ε lam V₀ E' ⟨v, hS hvS⟩ (S.comap V₀.subtype) hlam hgl' hun' ((hhi _ _).2 hv) inferInstance
    (fun a b hab x hx => hK a b hab x hx) hvS
    (fun μ x hx hμ => hmin μ x x.2 (fun h0 => hx (Subtype.ext h0)) ((hhi μ x).1 hμ)) Y
  have h2 := qdet_intertwine V₀.subtype E' E hE (Y + ((n : ℂ) - 1) / 2) ⟨v, hS hvS⟩
  rw [key] at h2
  simpa using h2.symm

end GlobalTheory.CompanionTheory.DSCoreSub
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.KsetSubsetUjset
open Matrix

namespace GlobalTheory.CompanionTheory.DSKType

open CompanionTheory.D.DSIC PI.UpqRep

theorem kset_subset_ujset {n : ℕ} {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) :
    g ∈ UJset ε := by
  obtain ⟨h1, h2⟩ := hg
  have h3 : gᴴ * g = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff'.1 h1)
  show inUJ ε g
  unfold inUJ
  rw [Matrix.mul_assoc, ← h2, ← Matrix.mul_assoc, h3, Matrix.one_mul]

theorem typeOfHW (hL : LowSpan) (hS : StabLink) (hW : WtLink) : TypeOfHW := by
  intro n ε H _ _ σ S E hσ hM μ x hx0 hfin hhw
  obtain ⟨S₀, hfd, hxS, hst⟩ := hfin
  have hinj : Function.Injective S.subtype := S.injective_subtype
  have := hfd
  have hU : FiniteDimensional ℂ (S₀.comap S.subtype) := by
    refine FiniteDimensional.of_injective
      (LinearMap.codRestrict S₀ (S.subtype ∘ₗ (S₀.comap S.subtype).subtype) (fun y => y.2)) ?_
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun y : S₀ => (y : H)) hab
  have hUst : KStab ε E (S₀.comap S.subtype) := by
    refine (hS n ε H σ S E hσ hM _ hU).2 ?_
    rintro g hg _ ⟨v, hv, rfl⟩
    exact ⟨⟨σ g v, hM.stab g (kset_subset_ujset hg) v v.2⟩, hst g hg v hv, rfl⟩
  have hrel : KRel ε E := fun a b c d _ _ => hM.gl a b c d
  have hun : KUnit ε E := by
    intro a b hab y z
    have := hM.unit a b y z
    simpa [Formalism.REAL.sgn, hab] using this
  obtain ⟨L, hLU, hxL, hLst, hirr, hdom, -⟩ := hL n ε S E μ x _ hrel hun hx0 hhw hU hUst hxS
  have hLfd : FiniteDimensional ℂ L := Submodule.finiteDimensional_of_le hLU
  refine ⟨L.map S.subtype, inferInstance, (hS n ε H σ S E hσ hM L hLfd).1 hLst, ?_, ?_, ?_⟩
  · intro S' hle hS'
    have hle' : S'.comap S.subtype ≤ L := by
      intro y hy
      obtain ⟨z, hz, hzy⟩ := hle hy
      rwa [← hinj hzy]
    have hmap : (S'.comap S.subtype).map S.subtype = S' := by
      apply Submodule.map_comap_eq_of_le
      exact hle.trans LinearMap.map_le_range
    have hst' : KStab ε E (S'.comap S.subtype) := by
      refine (hS n ε H σ S E hσ hM _ (Submodule.finiteDimensional_of_le hle')).2 ?_
      rwa [hmap]
    rcases hirr _ hle' hst' with h | h
    · left; rw [← hmap, h, Submodule.map_bot]
    · right; rw [← hmap, h]
  · exact ⟨x, ⟨x, hxL, rfl⟩, fun h => hx0 (Subtype.ext h), (hW n ε H σ S E hσ hM μ x).1 hhw.1⟩
  · rintro ν _ ⟨v, hv, rfl⟩ hv0 hwt
    exact hdom ν v hv (fun h => hv0 (by rw [h]; rfl)) ((hW n ε H σ S E hσ hM ν v).2 hwt)

end GlobalTheory.CompanionTheory.DSKType
end

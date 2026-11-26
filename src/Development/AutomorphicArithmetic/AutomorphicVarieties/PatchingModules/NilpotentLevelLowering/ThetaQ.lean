module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ActUVariableEqPow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwThetaEx
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwJqRec

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ThetaQ
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FixPiIff
namespace UpperTheory.Reformulated.B.Gr34

open ValuativeRel IsLocalRing UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools
  UpperTheory.V.Pa UpperTheory.V.Pa.Lev

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem fix_pi_iff {ι : Type} [Finite ι] [DecidableEq ι] {G : ι → Type} [∀ i, Group (G i)]
    {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A (∀ i, G i) M)
    (K : ∀ i, Subgroup (G i)) (m : M) :
    (∀ k ∈ Subgroup.pi Set.univ K, ρ k m = m) ↔
      ∀ j, ∀ k ∈ K j, ρ (Pi.mulSingle j k) m = m := by
  refine ⟨fun h j k hk => h _ fun i _ => ?_, fun h k hk => ?_⟩
  · rcases eq_or_ne i j with rfl | hij
    · simpa using hk
    · simp [Pi.mulSingle_eq_of_ne hij]
  · let H : Subgroup (∀ i, G i) :=
      { carrier := {g | ρ g m = m}
        one_mem' := by simp
        mul_mem' := fun {a b} (ha : ρ a m = m) (hb : ρ b m = m) =>
          show ρ (a * b) m = m by simp [ha, hb]
        inv_mem' := fun {a} (ha : ρ a m = m) => show ρ a⁻¹ m = m by
          conv_lhs => rw [← ha, Representation.inv_self_apply] }
    exact Subgroup.pi_mem_of_mulSingle_mem (H := H) k fun i => h i _ (hk i trivial)

theorem mem_UC {L : Type} [Field L] [NumberField L] {n q : ℕ} {w : Fin q → Plc L}
    {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (ρ : Representation A (GV n w) M)
    (C : ∀ j : Fin q, Subgroup 𝓀[(w j).adicCompletion L]ˣ) (m : M) :
    m ∈ fixd ρ (UC n w C) ↔ ∀ j, m ∈ fixd (ρ.comp (atJ n w j)) (iwC _ n (C j)) :=
  fix_pi_iff (G := fun j => GLw n (w j)) ρ _ m

end UpperTheory.Reformulated.B.Gr34
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem dom_gen {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    (t : Fin n → kˣ) : ∃ a b : Fin n → kˣ, Dom a ∧ Dom b ∧ t = a * b⁻¹ := by
  have key : ∃ c : kˣ, ∀ s : Fin n → kˣ, (s = 1 ∨ s = t) → ∀ i j : Fin n, i ≤ j →
      valuation k ((s i * c ^ (n - i) : kˣ) : k) ≤ valuation k ((s j * c ^ (n - j) : kˣ) : k) := by
    rcases isEmpty_or_nonempty (Fin n) with h | h
    · exact ⟨1, fun _ _ i => h.elim i⟩
    obtain ⟨p, hp⟩ := Finite.exists_min (fun p : Fin n × Fin n => valuation k ((t p.2 * (t p.1)⁻¹ : kˣ) : k))
    set c : kˣ := t p.2 * (t p.1)⁻¹ with hc
    have h1 : valuation k (c : k) ≤ 1 := by simpa using hp (p.1, p.1)
    refine ⟨c, fun s hs i j hij => ?_⟩
    rcases hij.eq_or_lt with rfl | hlt
    · exact le_rfl
    have h2 : valuation k (s i : k) * valuation k (c : k) ≤ valuation k (s j : k) := by
      rcases hs with rfl | rfl
      · simpa using h1
      · have := mul_le_mul_right (hp (i, j)) (valuation k (s i : k))
        refine this.trans (le_of_eq ?_)
        rw [← map_mul, ← Units.val_mul]
        congr 2
        simp
    have hj := j.2
    have hlt' : (i : ℕ) < j := hlt
    have e : n - (i : ℕ) = 1 + ((n - j) + (j - i - 1)) := by omega
    rw [e]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, pow_add, pow_one]
    rw [← mul_assoc]
    exact mul_le_mul' h2 (mul_le_of_le_one_right' (pow_le_one' h1 _))
  obtain ⟨c, hc⟩ := key
  refine ⟨t * (fun i : Fin n => c ^ (n - (i : ℕ))), (1 : Fin n → kˣ) * (fun i : Fin n => c ^ (n - (i : ℕ))),
    hc t (Or.inr rfl), hc 1 (Or.inl rfl), ?_⟩
  simp

private theorem comm_dc {A H M : Type} [CommRing A] [Group H] [AddCommGroup M] [Module A M]
    (ρ : Representation A H M) (K K' : Subgroup H) (x : H) (φ : Module.End A M) (h : ∀ g, Commute φ (ρ g)) :
    Commute φ (dc ρ K K' x) :=
  finsum_induction (fun e => Commute φ e) (Commute.zero_right φ) (fun _ _ h1 h2 => h1.add_right h2) fun _ => h _

section

variable {L : Type} [Field L] [NumberField L] {n q : ℕ} {w : Fin q → Plc L} {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
  (ρ : Representation A (GV n w) M) (C : ∀ j, Subgroup 𝓀[(w j).adicCompletion L]ˣ)

private theorem comm_at {j j' : Fin q} (h : j ≠ j') (g : GLw n (w j)) (g' : GLw n (w j')) :
    Commute (ρ (atJ n w j g)) (ρ (atJ n w j' g')) :=
  (Pi.mulSingle_commute (f := fun j => GLw n (w j)) h g g').map ρ

private theorem mem_UC (m : M) :
    m ∈ fixd ρ (UC n w C) ↔ ∀ j, m ∈ fixd (ρ.comp (atJ n w j)) (iwC _ n (C j)) :=
  by apply _root_.UpperTheory.Reformulated.B.Gr34.mem_UC <;> assumption

private theorem one_place (j : Fin q) (hq : IsUnit (qj w j : A)) :
    ∃ θ : (Fin n → ((w j).adicCompletion L)ˣ) →* (Module.End A (fixd ρ (UC n w C)))ˣ, ∀ t, Dom t →
      ∀ m : fixd ρ (UC n w C), ((θ t : Module.End A (fixd ρ (UC n w C))) m : M) =
        dc (ρ.comp (atJ n w j)) (iwC _ n (C j)) (iwC _ n (C j)) (diagT _ (Fin n) t) m := by
  obtain ⟨hmul, hunit, -⟩ := domMul _ n (C j) A M (ρ.comp (atJ n w j))
  have happ : ∀ x (v : fixd (ρ.comp (atJ n w j)) (iwC _ n (C j))),
      (hk (ρ.comp (atJ n w j)) (iwC _ n (C j)) x v : M) =
        dc (ρ.comp (atJ n w j)) (iwC _ n (C j)) (iwC _ n (C j)) x v := fun x =>
    (hkApply A _ M (ρ.comp (atJ n w j)) _ _ x ((heckePairIwC _ n (C j)).1 x)).1
  have hcomm : ∀ j', j' ≠ j → ∀ g x, Commute (ρ (atJ n w j' g))
      (dc (ρ.comp (atJ n w j)) (iwC _ n (C j)) (iwC _ n (C j)) x) := fun j' h g x =>
    comm_dc _ _ _ _ _ fun g' => comm_at ρ h g g'
  have hpres : ∀ x, ∀ m ∈ fixd ρ (UC n w C),
      dc (ρ.comp (atJ n w j)) (iwC _ n (C j)) (iwC _ n (C j)) x m ∈ fixd ρ (UC n w C) := by
    intro x m hm
    rw [mem_UC] at hm ⊢
    intro j'
    by_cases e : j' = j
    · subst e
      exact happ x ⟨m, hm _⟩ ▸ (hk (ρ.comp (atJ n w j')) (iwC _ n (C j')) x ⟨m, hm _⟩).2
    · intro u hu
      have h1 := LinearMap.congr_fun (hcomm j' e u x).eq m
      rw [Module.End.mul_apply, Module.End.mul_apply, show ρ (atJ n w j' u) m = m from hm j' u hu] at h1
      exact h1
  let f : (Fin n → ((w j).adicCompletion L)ˣ) → Module.End A (fixd ρ (UC n w C)) := fun t =>
    (dc (ρ.comp (atJ n w j)) (iwC _ n (C j)) (iwC _ n (C j)) (diagT _ (Fin n) t)).restrict (hpres _)
  have hf : ∀ t m, (f t m : M) =
    dc (ρ.comp (atJ n w j)) (iwC _ n (C j)) (iwC _ n (C j)) (diagT _ (Fin n) t) m := fun _ _ => rfl
  have fmul : ∀ a b, Dom a → Dom b → f (a * b) = f a * f b := by
    intro a b ha hb
    ext m
    have h1 := congrArg Subtype.val (LinearMap.congr_fun (hmul a b ha hb) ⟨m, (mem_UC ρ C _).1 m.2 j⟩)
    rw [Module.End.mul_apply, happ, happ, happ] at h1
    exact h1.symm
  have funit : ∀ a, Dom a → IsUnit (f a) := by
    intro a ha
    obtain ⟨hi, hs⟩ := (Module.End.isUnit_iff _).1 (hunit hq a ha)
    refine (Module.End.isUnit_iff _).2 ⟨fun m m' h => ?_, fun m => ?_⟩
    · have := @hi ⟨m, (mem_UC ρ C _).1 m.2 j⟩ ⟨m', (mem_UC ρ C _).1 m'.2 j⟩ (Subtype.ext (by
        rw [happ, happ]; exact congrArg Subtype.val h))
      have h2 := congrArg Subtype.val this
      exact Subtype.ext h2
    · obtain ⟨v, hv⟩ := hs ⟨m, (mem_UC ρ C _).1 m.2 j⟩
      have hv' := congrArg Subtype.val hv
      rw [happ] at hv'
      refine ⟨⟨v, (mem_UC ρ C _).2 fun j' => ?_⟩, Subtype.ext hv'⟩
      by_cases e : j' = j
      · subst e
        exact v.2
      · intro u hu
        have hm : ρ (atJ n w j' u) v ∈ fixd (ρ.comp (atJ n w j)) (iwC _ n (C j)) := by
          intro g hg
          have h1 := LinearMap.congr_fun (comm_at ρ e u g).eq v
          rw [Module.End.mul_apply, Module.End.mul_apply, show ρ (atJ n w j g) v = v from v.2 g hg] at h1
          exact h1.symm
        have := @hi ⟨_, hm⟩ v (Subtype.ext (by
          rw [happ, happ]
          have h1 := LinearMap.congr_fun (hcomm j' e u (diagT _ (Fin n) a)).eq v
          rw [Module.End.mul_apply, Module.End.mul_apply, hv'] at h1
          rw [hv']
          exact h1.symm.trans ((mem_UC ρ C _).1 m.2 j' u hu)))
        exact congrArg Subtype.val this
  let P : Submonoid (Fin n → ((w j).adicCompletion L)ˣ) :=
    { carrier := {t | Dom t}
      one_mem' := dom_one
      mul_mem' := fun {a b} ha hb i j hij => by
        simp only [Pi.mul_apply, Units.val_mul, map_mul]
        exact mul_le_mul' (ha i j hij) (hb i j hij) }
  obtain ⟨θ, hθ, -⟩ := monoidExt _ _ P f (fun t => by
      obtain ⟨a, b, ha, hb, h⟩ := dom_gen t
      exact ⟨a, ha, b, hb, h⟩)
    (by
      have h := fmul 1 1 dom_one dom_one
      rw [mul_one] at h
      exact (funit 1 dom_one).mul_left_cancel (h.symm.trans (mul_one _).symm))
    (fun a ha b hb => fmul a b ha hb) (fun a ha => funit a ha)
  exact ⟨θ, fun t ht m => by rw [hθ t ht, hf]⟩

end

theorem UpperTheory.V.Pa.Lev.thetaQ :
    ∀ (L : Type) [Field L] [NumberField L] (n q : ℕ) (w : Fin q → Plc L) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A (GV n w) M) (C : ∀ j, Subgroup 𝓀[(w j).adicCompletion L]ˣ), (∀ j, IsUnit (qj w j : A)) → ∃ Θ, IsThetaQ ρ C Θ := by
  intro L _ _ n q w A M _ _ _ ρ C hq
  choose Θ hΘ using fun j => one_place ρ C j (hq j)
  refine ⟨Θ, hΘ, fun j j' t t' => ?_⟩
  by_cases e : j = j'
  · subst e
    exact (Commute.all t t').map _
  have hd : ∀ a b, Dom a → Dom b → Commute (Θ j a) (Θ j' b) := by
    intro a b ha hb
    refine Units.ext (LinearMap.ext fun m => Subtype.ext ?_)
    rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply, hΘ j a ha, hΘ j' b hb,
      hΘ j' b hb, hΘ j a ha]
    exact LinearMap.congr_fun (comm_dc _ _ _ _ _ fun g' =>
      (comm_dc _ _ _ _ _ fun g => comm_at ρ (Ne.symm e) g' g).symm).eq (m : M)
  obtain ⟨a, b, ha, hb, rfl⟩ := dom_gen t
  obtain ⟨c, d, hc, hd', rfl⟩ := dom_gen t'
  rw [map_mul, map_mul, map_inv, map_inv]
  exact ((hd a c ha hc).mul_right (hd a d ha hd').inv_right).mul_left
    ((hd b c hb hc).mul_right (hd b d hb hd').inv_right).inv_left
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ThetaLoc
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem mul_prod_le_of_le_one_of_le_of_mul_le_one {G : Type} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {n : ℕ}
    (a b : Fin n → G) (hb1 : ∀ l, b l ≤ 1) (hba : ∀ l, b l ≤ a l) (hab : ∀ l, a l * b l ≤ 1) :
    ∀ i j : Fin n, i < j → a i * ∏ l, b l ≤ a j := by
  classical
  intro i j hij
  have hne : j ≠ i := ne_of_gt hij
  have hsplit : ∏ l, b l = b i * (b j * ∏ l ∈ (Finset.univ.erase i).erase j, b l) := by
    rw [Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ j⟩),
      Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  calc a i * ∏ l, b l = (a i * b i) * (b j * ∏ l ∈ (Finset.univ.erase i).erase j, b l) := by
        rw [hsplit, mul_assoc]
    _ ≤ 1 * (b j * 1) := mul_le_mul' (hab i) (mul_le_mul' le_rfl (Finset.prod_le_one' (fun l _ => hb1 l)))
    _ ≤ a j := by rw [one_mul, mul_one]; exact hba j

private theorem mul_pow_sub_le_of_mul_le_of_le_of_le_one {G : Type} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {n : ℕ}
    (a : Fin n → G) (c : G) (hc1 : c ≤ 1) (hc : ∀ i j : Fin n, i < j → a i * c ≤ a j) (i j : Fin n)
    (hij : i ≤ j) : a i * c ^ (n - (i : ℕ)) ≤ a j * c ^ (n - (j : ℕ)) := by
  rcases lt_or_eq_of_le hij with h | h
  · obtain ⟨d, hd⟩ : ∃ d, n - (i : ℕ) = (n - (j : ℕ)) + d + 1 :=
      ⟨(j : ℕ) - i - 1, by have := j.isLt; have := Fin.lt_iff_val_lt_val.mp h; omega⟩
    calc a i * c ^ (n - (i : ℕ)) = (a i * c) * c ^ d * c ^ (n - (j : ℕ)) := by
          rw [hd, pow_add, pow_add, pow_one]; ac_rfl
      _ ≤ a j * 1 * c ^ (n - (j : ℕ)) := mul_le_mul' (mul_le_mul' (hc i j h) (pow_le_one' hc1 d)) le_rfl
      _ = a j * c ^ (n - (j : ℕ)) := by rw [mul_one]
  · rw [h]

private theorem thetaLoc_split {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (t : Fin n → kˣ) : ∃ b : Fin n → kˣ, Dom b ∧ Dom (t * b) := by
  classical
  let φ : kˣ →* (ValueGroupWithZero k)ˣ := Units.map (valuation k).toMonoidWithZeroHom.toMonoidHom
  have hφ : ∀ u : kˣ, valuation k (u : k) = ((φ u : (ValueGroupWithZero k)ˣ) : ValueGroupWithZero k) :=
    fun u => rfl
  let w : Fin n → kˣ := fun l => if φ (t l) ≤ 1 then t l else (t l)⁻¹
  have hw1 : ∀ l, φ (w l) ≤ 1 := fun l => by
    simp only [w]
    split_ifs with h
    · exact h
    · rw [map_inv]; exact inv_le_one'.mpr (le_of_lt (not_le.mp h))
  have hwa : ∀ l, φ (w l) ≤ φ (t l) := fun l => by
    simp only [w]
    split_ifs with h
    · exact le_rfl
    · rw [map_inv]
      exact (inv_le_one'.mpr (le_of_lt (not_le.mp h))).trans (le_of_lt (not_le.mp h))
  have hwab : ∀ l, φ (t l) * φ (w l) ≤ 1 := fun l => by
    simp only [w]
    split_ifs with h
    · exact mul_le_one' h h
    · rw [map_inv, mul_inv_cancel]
  have hC : φ (∏ l, w l) = ∏ l, φ (w l) := map_prod φ _ _
  have hc1 : ∏ l, φ (w l) ≤ 1 := Finset.prod_le_one' (fun l _ => hw1 l)
  refine ⟨fun i => (∏ l, w l) ^ (n - (i : ℕ)), ?_, ?_⟩
  · intro i j hij
    dsimp only
    rw [hφ, hφ, Units.val_le_val, map_pow, map_pow, hC]
    simpa using mul_pow_sub_le_of_mul_le_of_le_of_le_one (fun _ => (1 : (ValueGroupWithZero k)ˣ)) _ hc1
      (fun _ _ _ => by rw [one_mul]; exact hc1) i j hij
  · intro i j hij
    rw [Pi.mul_apply, Pi.mul_apply]
    rw [hφ, hφ, Units.val_le_val, map_mul, map_mul, map_pow, map_pow, hC]
    exact mul_pow_sub_le_of_mul_le_of_le_of_le_one (fun l => φ (t l)) _ hc1
      (mul_prod_le_of_le_one_of_le_of_mul_le_one (fun l => φ (t l)) (fun l => φ (w l)) hw1 hwa hwab) i j hij

private theorem thetaLoc_ext {T A M₁ M₂ : Type} [CommGroup T] [CommRing A] [AddCommGroup M₁] [Module A M₁]
    [AddCommGroup M₂] [Module A M₂] (Θ : T →* (Module.End A M₁)ˣ) (θ : T →* (Module.End A M₂)ˣ) (ι : M₁ → M₂)
    (t b : T) (hb : ∀ m, (θ b).val (ι m) = ι ((Θ b).val m))
    (htb : ∀ m, (θ (t * b)).val (ι m) = ι ((Θ (t * b)).val m)) (m : M₁) :
    (θ t).val (ι m) = ι ((Θ t).val m) := by
  have key : ∀ y, ((θ b)⁻¹).val ((θ b).val y) = y := fun y => by
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one, Module.End.one_apply]
  have h1 := htb m
  rw [mul_comm t b] at h1
  simp only [map_mul, Units.val_mul, Module.End.mul_apply] at h1
  rw [← hb] at h1
  rw [← key ((θ t).val (ι m)), h1, key]

theorem UpperTheory.V.Pa.Lev.thetaLoc :
    ∀ (L : Type) [Field L] [NumberField L] (n q : ℕ) (w : Fin q → Plc L) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A (GV n w) M) (C : ∀ j, Subgroup 𝓀[(w j).adicCompletion L]ˣ) (Θ), IsThetaQ ρ C Θ → ∀ j θ, IsTheta (ρ.comp (atJ n w j)) (C j) θ → ∀ t (m : fixd ρ (UC n w C)) (m' : fixd (ρ.comp (atJ n w j)) (iwC _ n (C j))), (m' : M) = m → ((θ t).val m').val = ((Θ j t).val m).val := by
  intro L _ _ n q w A M _ _ _ ρ C Θ hΘ j θ hθ t m m' hm
  have hmem : ∀ u ∈ iwC _ n (C j), atJ n w j u ∈ UC n w C := by
    intro u hu
    simp only [UC, Subgroup.mem_pi]
    intro i _
    by_cases h : i = j
    · subst h
      simpa [atJ] using hu
    · simp [atJ, Pi.mulSingle_eq_of_ne h, Subgroup.one_mem]
  let ι : fixd ρ (UC n w C) → fixd (ρ.comp (atJ n w j)) (iwC _ n (C j)) := fun x =>
    ⟨x, show ∀ u ∈ iwC _ n (C j), (ρ.comp (atJ n w j)) u x = x from fun u hu =>
      (show ∀ u ∈ UC n w C, ρ u x = x from x.2) _ (hmem u hu)⟩
  have hdom : ∀ s, Dom s → ∀ x, (θ s).val (ι x) = ι ((Θ j s).val x) := by
    intro s hs x
    apply Subtype.ext
    rw [hθ s hs]
    unfold hk
    rw [(hkApply _ _ _ _ _ _ _ ((heckePairIwC _ n (C j)).1 _)).1]
    exact (hΘ.1 j s hs x).symm
  obtain ⟨b, hb, htb⟩ := thetaLoc_split t
  have key := thetaLoc_ext (Θ j) θ ι t b (hdom b hb) (hdom (t * b) htb) m
  have hm' : m' = ι m := Subtype.ext hm
  rw [hm', key]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ThetaMap
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem lt_imp_mul_prod_le_of_b_le_one_le_a_mul_le {G : Type} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {n : ℕ}
    (a b : Fin n → G) (hb1 : ∀ l, b l ≤ 1) (hba : ∀ l, b l ≤ a l) (hab : ∀ l, a l * b l ≤ 1) :
    ∀ i j : Fin n, i < j → a i * ∏ l, b l ≤ a j := by
  classical
  intro i j hij
  have hne : j ≠ i := ne_of_gt hij
  have hsplit : ∏ l, b l = b i * (b j * ∏ l ∈ (Finset.univ.erase i).erase j, b l) := by
    rw [Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ j⟩),
      Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  calc a i * ∏ l, b l = (a i * b i) * (b j * ∏ l ∈ (Finset.univ.erase i).erase j, b l) := by
        rw [hsplit, mul_assoc]
    _ ≤ 1 * (b j * 1) := mul_le_mul' (hab i) (mul_le_mul' le_rfl (Finset.prod_le_one' (fun l _ => hb1 l)))
    _ ≤ a j := by rw [one_mul, mul_one]; exact hba j

private theorem le_imp_mul_pow_sub_le_of_c_le_one_mul_le {G : Type} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {n : ℕ}
    (a : Fin n → G) (c : G) (hc1 : c ≤ 1) (hc : ∀ i j : Fin n, i < j → a i * c ≤ a j) (i j : Fin n)
    (hij : i ≤ j) : a i * c ^ (n - (i : ℕ)) ≤ a j * c ^ (n - (j : ℕ)) := by
  rcases lt_or_eq_of_le hij with h | h
  · obtain ⟨d, hd⟩ : ∃ d, n - (i : ℕ) = (n - (j : ℕ)) + d + 1 :=
      ⟨(j : ℕ) - i - 1, by have := j.isLt; have := Fin.lt_iff_val_lt_val.mp h; omega⟩
    calc a i * c ^ (n - (i : ℕ)) = (a i * c) * c ^ d * c ^ (n - (j : ℕ)) := by
          rw [hd, pow_add, pow_add, pow_one]; ac_rfl
      _ ≤ a j * 1 * c ^ (n - (j : ℕ)) := mul_le_mul' (mul_le_mul' (hc i j h) (pow_le_one' hc1 d)) le_rfl
      _ = a j * c ^ (n - (j : ℕ)) := by rw [mul_one]
  · rw [h]

private theorem thetaMap_split {k : Type} [Field k] [ValuativeRel k] {n : ℕ} (t : Fin n → kˣ) :
    ∃ c : kˣ, ∀ s : Fin n → kˣ, (s = 1 ∨ s = t) → ∀ i j : Fin n, i ≤ j →
      valuation k ((s i * c ^ (n - i) : kˣ) : k) ≤ valuation k ((s j * c ^ (n - j) : kˣ) : k) := by
  classical
  let φ : kˣ →* (ValueGroupWithZero k)ˣ := Units.map (valuation k).toMonoidWithZeroHom.toMonoidHom
  have hφ : ∀ u : kˣ, valuation k (u : k) = ((φ u : (ValueGroupWithZero k)ˣ) : ValueGroupWithZero k) :=
    fun u => rfl
  let w : Fin n → kˣ := fun l => if φ (t l) ≤ 1 then t l else (t l)⁻¹
  have hw1 : ∀ l, φ (w l) ≤ 1 := fun l => by
    simp only [w]
    split_ifs with h
    · exact h
    · rw [map_inv]; exact inv_le_one'.mpr (le_of_lt (not_le.mp h))
  have hwa : ∀ l, φ (w l) ≤ φ (t l) := fun l => by
    simp only [w]
    split_ifs with h
    · exact le_rfl
    · rw [map_inv]
      exact (inv_le_one'.mpr (le_of_lt (not_le.mp h))).trans (le_of_lt (not_le.mp h))
  have hwab : ∀ l, φ (t l) * φ (w l) ≤ 1 := fun l => by
    simp only [w]
    split_ifs with h
    · exact mul_le_one' h h
    · rw [map_inv, mul_inv_cancel]
  refine ⟨∏ l, w l, ?_⟩
  have hC : φ (∏ l, w l) = ∏ l, φ (w l) := map_prod φ _ _
  have hc1 : ∏ l, φ (w l) ≤ 1 := Finset.prod_le_one' (fun l _ => hw1 l)
  intro s hs i j hij
  rw [hφ, hφ, Units.val_le_val, map_mul, map_mul, map_pow, map_pow, hC]
  rcases hs with h | h
  · rw [h]
    simpa using le_imp_mul_pow_sub_le_of_c_le_one_mul_le (fun _ => (1 : (ValueGroupWithZero k)ˣ)) _ hc1
      (fun _ _ _ => by rw [one_mul]; exact hc1) i j hij
  · rw [h]
    exact le_imp_mul_pow_sub_le_of_c_le_one_mul_le (fun l => φ (t l)) _ hc1
      (lt_imp_mul_prod_le_of_b_le_one_le_a_mul_le (fun l => φ (t l)) (fun l => φ (w l)) hw1 hwa hwab) i j hij

private theorem thetaMap_dc {A M A' M' G : Type} [CommRing A] [AddCommGroup M] [Module A M] [CommRing A'] [AddCommGroup M']
    [Module A' M'] [Group G] (ρ : Representation A G M) (ρ' : Representation A' G M') (K K' : Subgroup G) (x : G)
    (hx : FinOrb K K' x) (f : M →+ M') (hf : ∀ g m, f (ρ g m) = ρ' g (f m)) (m : M) :
    dc ρ' K K' x (f m) = f (dc ρ K K' x m) := by
  haveI := hx.fintype
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dc, finsum_eq_sum_of_fintype, LinearMap.sum_apply, map_sum, hf]

private theorem thetaMap_ext {A N A' N' T : Type} [CommRing A] [AddCommGroup N] [Module A N] [CommRing A'] [AddCommGroup N']
    [Module A' N'] [Group T] (θ : T →* (Module.End A N)ˣ) (θ' : T →* (Module.End A' N')ˣ) (g : N → N') (t b : T)
    (hb : ∀ m, (θ' b).val (g m) = g ((θ b).val m)) (ha : ∀ m, (θ' (b * t)).val (g m) = g ((θ (b * t)).val m)) (m : N) :
    (θ' t).val (g m) = g ((θ t).val m) := by
  have key : ∀ y, ((θ' b)⁻¹).val ((θ' b).val y) = y := fun y => by
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one, Module.End.one_apply]
  have h1 := ha m
  simp only [map_mul, Units.val_mul, Module.End.mul_apply] at h1
  rw [← hb] at h1
  rw [← key ((θ' t).val (g m)), h1, key]

theorem UpperTheory.V.Pa.Lev.thetaMap :
    ∀ (L : Type) [Field L] [NumberField L] (n q : ℕ) (w : Fin q → Plc L) (A M A' M' : Type) [CommRing A] [AddCommGroup M] [Module A M] [CommRing A'] [AddCommGroup M'] [Module A' M'] (ρ : Representation A (GV n w) M) (ρ' : Representation A' (GV n w) M') (C : ∀ j, Subgroup 𝓀[(w j).adicCompletion L]ˣ) (Θ) (Θ'), IsThetaQ ρ C Θ → IsThetaQ ρ' C Θ' → ∀ f : M →+ M', (∀ g m, f (ρ g m) = ρ' g (f m)) → ∀ j t (m : fixd ρ (UC n w C)) (m' : fixd ρ' (UC n w C)), (m' : M') = f m → ((Θ' j t).val m').val = f ((Θ j t).val m).val := by
  intro L _ _ n q w A M A' M' _ _ _ _ _ _ ρ ρ' C Θ Θ' hΘ hΘ' f hf j t m m' hm
  let g : fixd ρ (UC n w C) → fixd ρ' (UC n w C) := fun x =>
    ⟨f x, show ∀ u ∈ UC n w C, ρ' u (f x) = f x from fun u hu => by
      rw [← hf]
      exact congrArg f ((show ∀ u ∈ UC n w C, ρ u x = x from x.2) u hu)⟩
  have hdom : ∀ s, Dom s → ∀ x, (Θ' j s).val (g x) = g ((Θ j s).val x) := by
    intro s hs x
    apply Subtype.ext
    rw [hΘ'.1 j s hs (g x)]
    change _ = f (((Θ j s).val x : M))
    rw [hΘ.1 j s hs x]
    exact thetaMap_dc _ _ _ _ _ ((heckePairIwC _ n (C j)).1 _) f (fun g' y => hf _ y) x
  obtain ⟨c, hc⟩ := thetaMap_split t
  let b : Fin n → (HeightOneSpectrum.adicCompletion L (w j))ˣ := fun i => c ^ (n - (i : ℕ))
  have hb : Dom b := fun i i' h => by simpa [b] using hc 1 (Or.inl rfl) i i' h
  have hbt : Dom (b * t) := fun i i' h => by
    have := hc t (Or.inr rfl) i i' h
    simpa [b, Pi.mul_apply, mul_comm] using this
  have key := thetaMap_ext (Θ j) (Θ' j) g t b (hdom b hb) (hdom (b * t) hbt) m
  have hm' : m' = g m := Subtype.ext hm
  rw [hm', key]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.IsoFix
section -- merged from Development.AutomorphicArithmetic.LocalEmbeddings.CoinvFin
noncomputable section

open GlobalTheory.PRep Topology Filter

namespace UpperTheory.Dv.CoinvFin

section Alg

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def stab (ρ : Representation ℂ G V) (v : V) : Subgroup G where
  carrier := {g | ρ g v = v}
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
    rw [hy, hx]
  one_mem' := by simp
  inv_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← hx]
    rw [← Module.End.mul_apply, ← map_mul]
    simp

def av (ρ : Representation ℂ G V) (K K' : Subgroup G) [Fintype (K ⧸ K'.subgroupOf K)] (v : V) : V :=
  ∑ q : K ⧸ K'.subgroupOf K, ρ (q.out : K) v

theorem av_fixed (ρ : Representation ℂ G V) (K K' : Subgroup G) [Fintype (K ⧸ K'.subgroupOf K)] {v : V}
    (hv : K' ≤ stab ρ v) : ∀ k ∈ K, ρ k (av ρ K K' v) = av ρ K K' v := by
  intro k hk
  unfold av
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Fintype.sum_equiv (MulAction.toPerm (⟨k, hk⟩ : K)) _ _ fun q => ?_
  have h1 : ((((⟨k, hk⟩ : K) • q).out : K) : K ⧸ K'.subgroupOf K) = ((⟨k, hk⟩ * q.out : K) : K ⧸ K'.subgroupOf K) := by
    rw [QuotientGroup.out_eq', ← smul_eq_mul, MulAction.Quotient.mk_smul_out]
  have h2 : ρ _ v = v := hv (Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 h1))
  rw [MulAction.toPerm_apply]
  conv_rhs => rw [← h2]
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  simp

theorem av_of_fixed (ρ : Representation ℂ G V) (K K' : Subgroup G) [Fintype (K ⧸ K'.subgroupOf K)] {v : V}
    (hv : ∀ k ∈ K, ρ k v = v) : av ρ K K' v = (Fintype.card (K ⧸ K'.subgroupOf K) : ℂ) • v := by
  unfold av
  rw [Finset.sum_congr rfl fun q _ => hv _ (q.out).2, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]

end Alg

section Top

variable {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

theorem finite_quot {K K' : Subgroup G} (c : IsCompact (K : Set G)) (o : IsOpen (K' : Set G)) :
    Finite (K ⧸ K'.subgroupOf K) := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 c
  exact Subgroup.quotient_finite_of_isOpen _ (Subgroup.subgroupOf_isOpen K K' o)

theorem mem_of_span (ρ : Representation ℂ G V) {K : Subgroup G} (c : IsCompact (K : Set G)) (S : Set V) (W₀ : Submodule ℂ V)
    (hS : ∀ s ∈ S, ∃ K₀ : Subgroup G, IsOpen (K₀ : Set G) ∧ ∀ K' ≤ K₀, ∀ [Fintype (K ⧸ K'.subgroupOf K)], av ρ K K' s ∈ W₀)
    {w : V} (hw : w ∈ Submodule.span ℂ S) (hfix : ∀ k ∈ K, ρ k w = w) : w ∈ W₀ := by
  have key : ∀ w ∈ Submodule.span ℂ S, ∃ K₀ : Subgroup G, IsOpen (K₀ : Set G) ∧
      ∀ K' ≤ K₀, ∀ [Fintype (K ⧸ K'.subgroupOf K)], av ρ K K' w ∈ W₀ := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem s hs => exact hS s hs
    | zero => exact ⟨⊤, isOpen_univ, fun K' _ _ => by simp [av]⟩
    | add x y _ _ hx hy =>
      obtain ⟨K₁, o₁, h₁⟩ := hx
      obtain ⟨K₂, o₂, h₂⟩ := hy
      refine ⟨K₁ ⊓ K₂, o₁.inter o₂, fun K' h _ => ?_⟩
      have := add_mem (h₁ K' (h.trans inf_le_left)) (h₂ K' (h.trans inf_le_right))
      simpa [av, Finset.sum_add_distrib] using this
    | smul a x _ hx =>
      obtain ⟨K₁, o₁, h₁⟩ := hx
      refine ⟨K₁, o₁, fun K' h _ => ?_⟩
      have := W₀.smul_mem a (h₁ K' h)
      simpa [av, Finset.smul_sum] using this
  obtain ⟨K₀, o, h⟩ := key w hw
  haveI := finite_quot c o
  letI := Fintype.ofFinite (K ⧸ K₀.subgroupOf K)
  have h1 := h K₀ le_rfl
  rw [av_of_fixed ρ K K₀ hfix] at h1
  exact (Submodule.smul_mem_iff _ (Nat.cast_ne_zero.2 Fintype.card_ne_zero)).1 h1

end Top

end UpperTheory.Dv.CoinvFin

end
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Pa.Lev.isoFix :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (Y : Type) [AddCommGroup Y] [Module ℂ Y] (π : Representation ℂ (GL (Fin n) k) Y) (σ : SmIrr (GL (Fin n) k)) (I : Subgroup (GL (Fin n) k)), IsCompact (I : Set (GL (Fin n) k)) → IsoSum π ⊤ σ → ∀ y ∈ fixd π I, y ∈ ⨆ f : {f : σ.V →ₗ[ℂ] Y // ∀ g v, f (σ.ρ g v) = π g (f v)}, (fixd σ.ρ I).map f.1 := by
  intro k _ _ _ _ n Y _ _ π σ I hI hs y hy
  refine UpperTheory.Dv.CoinvFin.mem_of_span π hI
    {w | ∃ f : σ.V →ₗ[ℂ] Y, (∀ g v, f (σ.ρ g v) = π g (f v)) ∧ ∃ v, w = f v} _ ?_ ?_ hy
  · rintro _ ⟨f, hf, v, rfl⟩
    refine ⟨UpperTheory.Dv.CoinvFin.stab σ.ρ v, σ.smooth v, fun K' hK' _ => ?_⟩
    refine Submodule.mem_iSup_of_mem ⟨f, hf⟩ ⟨UpperTheory.Dv.CoinvFin.av σ.ρ I K' v, UpperTheory.Dv.CoinvFin.av_fixed σ.ρ I K' hK', ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [UpperTheory.Dv.CoinvFin.av, map_sum, hf]
  · refine (iSup_le fun f => ?_ : _ ≤ Submodule.span ℂ _) (hs Submodule.mem_top)
    rintro _ ⟨v, rfl⟩
    exact Submodule.subset_span ⟨f.1, f.2.1, v, rfl⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.WdChar
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem unip_eq_one {n d : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hd : d ≠ 0) (h1 : M ^ d = 1)
    (hc : M.charpoly = (Polynomial.X - 1) ^ n) : M = 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Subsingleton.elim _ _
  have hsep : (Polynomial.X ^ d - Polynomial.C (1 : ℂ)).Separable :=
    Polynomial.separable_X_pow_sub_C 1 (Nat.cast_ne_zero.mpr hd) one_ne_zero
  have h1' : minpoly ℂ M ∣ Polynomial.X ^ d - Polynomial.C 1 := minpoly.dvd ℂ M (by simp [h1])
  have hsq : Squarefree (minpoly ℂ M) := hsep.squarefree.squarefree_of_dvd h1'
  have h2 : minpoly ℂ M ∣ (Polynomial.X - 1) ^ n := hc ▸ Matrix.minpoly_dvd_charpoly M
  have h3 : minpoly ℂ M ∣ Polynomial.X - 1 := (hsq.dvd_pow_iff_dvd hn.ne').mp h2
  have h4 := (minpoly.dvd_iff).mp h3
  simpa [sub_eq_zero] using h4

theorem UpperTheory.V.Pa.Lev.wdChar :
    ∀ (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (Bq : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (hB : IsPlaceOver Bq w), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (n : ℕ) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin n) (Qbar l)) (x : WD hB), IsWDOf ι r x → (∀ σ : Weil hB, ((r σ : Matrix (Fin n) (Fin n) (Qbar l)).map ι).charpoly = x.charPol σ) ∧ ∀ σ ∈ GlobalTheory.TameQuot.ineKer E Bq l, ((r σ : Matrix (Fin n) (Fin n) (Qbar l)).map ι).charpoly = (Polynomial.X - 1) ^ n → r σ = 1 := by
  intro l _ E Ω _ _ _ _ _ Bq w hB hl n ι r x hx
  have hxe : wdOf (h := hB) hl ι r = x := IsWDOf.wdOf_eq hl hx
  obtain ⟨t, ht, φ, hφ, N, a, hmon, -, -⟩ := hx
  constructor
  · intro σ
    rw [← hxe, IsMonodromy.charPol_wdOf hl ht hmon ι σ]
    exact Matrix.charpoly_map _ ι.toRingHom
  · intro σ hσ hc
    have hσI : σ ∈ Ine Bq := GlobalTheory.TameQuot.ineKer_le_Ine Bq l hσ
    let τ : Ine Bq := ⟨σ, hσI⟩
    have htτ : t τ = 1 := (GlobalTheory.TameQuot.eq_one_iff_mem_ineKer E Ω l Bq w hB hl t ht.1 ht.2 τ).mpr hσ
    have hval : tval t τ = 0 := by simp [tval, htτ]
    obtain ⟨-, U, hU, hUr⟩ := hmon
    haveI := compactSpace_Ine (E := E) Bq
    haveI : Finite (Ine Bq ⧸ U) := Subgroup.quotient_finite_of_isOpen U hU
    haveI : U.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    have hd : U.normalCore.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
    have hpow : τ ^ U.normalCore.index ∈ U := U.normalCore_le (U.normalCore.pow_index_mem τ)
    have hr : (r σ : Matrix (Fin n) (Fin n) (Qbar l)) ^ U.normalCore.index = 1 := by
      have := hUr _ hpow
      rw [tval_pow, hval, mul_zero, zero_smul, IsNilpotent.exp_zero, Subgroup.coe_pow, map_pow,
        Units.val_pow_eq_pow_val] at this
      exact this
    have hM : (r σ : Matrix (Fin n) (Fin n) (Qbar l)).map ι = 1 := by
      apply unip_eq_one _ hd _ hc
      have e : (r σ : Matrix (Fin n) (Fin n) (Qbar l)).map ι = ι.toRingHom.mapMatrix (r σ : Matrix (Fin n) (Fin n) (Qbar l)) := rfl
      rw [e, ← map_pow, hr, map_one]
    apply Units.ext
    refine Matrix.map_injective ι.injective ?_
    show (r σ : Matrix (Fin n) (Fin n) (Qbar l)).map ι = (1 : Matrix (Fin n) (Fin n) (Qbar l)).map ι
    rw [hM, Matrix.map_one _ (map_zero ι) (map_one ι)]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ProjNorm
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem coeffSum (Λ G : Type) [CommRing Λ] [Group G] [Fintype G] (x : MonoidAlgebra Λ G) :
    ∑ g : G, (MonoidAlgebra.single g (1:Λ)) * MonoidAlgebra.single (1:G) (((MonoidAlgebra.single g⁻¹ (1:Λ)) * x).coeff 1) = x := by
  classical
  ext h
  simp [MonoidAlgebra.single_mul_single, Finsupp.single_apply]

private theorem higman (Λ G N : Type) [CommRing Λ] [Group G] [Fintype G] [AddCommGroup N]
    [Module (MonoidAlgebra Λ G) N] (h : Module.Projective (MonoidAlgebra Λ G) N) :
    ∃ φ : N →+ N, ∀ m, ∑ g : G, MonoidAlgebra.single g (1:Λ) • φ (MonoidAlgebra.single g⁻¹ (1:Λ) • m) = m := by
  classical
  obtain ⟨s, hs⟩ := Module.projective_def.1 h
  let e : MonoidAlgebra Λ G →+ MonoidAlgebra Λ G :=
    { toFun := fun x => MonoidAlgebra.single (1:G) (x.coeff 1)
      map_zero' := by simp
      map_add' := by intro x y; simp [MonoidAlgebra.single_add] }
  refine ⟨(Finsupp.linearCombination (MonoidAlgebra Λ G) (id : N → N)).toAddMonoidHom.comp
    ((Finsupp.mapRange.addMonoidHom e).comp s.toAddMonoidHom), fun m => ?_⟩
  conv_rhs => rw [← hs m]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, ← map_smul, ← map_sum]
  congr 1
  ext1 n
  rw [Finsupp.finsetSum_apply]
  simp only [map_smul, Finsupp.smul_apply, Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_apply, smul_eq_mul]
  exact coeffSum Λ G (s m n)

theorem UpperTheory.V.Pa.Lev.projNorm :
    ∀ (Λ G M : Type) [CommRing Λ] [Group G] [Fintype G] [AddCommGroup M] [Module Λ M] (ρ : Representation Λ G M), Module.Projective (MonoidAlgebra Λ G) ρ.asModule → (∀ m, (∀ g, ρ g m = m) → ∃ m', ∑ g, ρ g m' = m) ∧ ∀ S : Set G, Subgroup.closure S = ⊤ → ∀ m, ∑ g, ρ g m = 0 → m ∈ ⨆ g ∈ S, LinearMap.range (ρ g - 1) := by
  intro Λ G M _ _ _ _ _ ρ hP
  obtain ⟨φ₀, hφ₀⟩ := higman Λ G ρ.asModule hP
  obtain ⟨φ, hφ⟩ : ∃ φ : M →+ M, ∀ m, ∑ g : G, ρ g (φ (ρ g⁻¹ m)) = m := by
    refine ⟨ρ.asModuleEquiv.toLinearMap.toAddMonoidHom.comp (φ₀.comp ρ.asModuleEquiv.symm.toLinearMap.toAddMonoidHom), fun m => ?_⟩
    have := congrArg ρ.asModuleEquiv (hφ₀ (ρ.asModuleEquiv.symm m))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, LinearEquiv.apply_symm_apply] at this
    rw [← this]
    conv_lhs => rw [this]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp [Representation.asModuleEquiv_map_smul, Representation.asModuleEquiv_symm_map_rho]
    rfl
  refine ⟨fun m hm => ⟨φ m, ?_⟩, fun S hS m hm => ?_⟩
  · simpa only [hm] using hφ m
  · set I : Submodule Λ M := ⨆ g ∈ S, LinearMap.range (ρ g - 1) with hI
    have key : ∀ g : G, ∀ x, ρ g x - x ∈ I := by
      intro g
      have hg : g ∈ Subgroup.closure S := hS ▸ Subgroup.mem_top g
      induction hg using Subgroup.closure_induction with
      | mem g hg =>
        intro x
        exact Submodule.mem_iSup_of_mem g (Submodule.mem_iSup_of_mem hg ⟨x, rfl⟩)
      | one => intro x; simp
      | mul a b _ _ ha hb =>
        intro x
        have := I.add_mem (ha (ρ b x)) (hb x)
        simpa using this
      | inv a _ ha =>
        intro x
        have := I.neg_mem (ha (ρ a⁻¹ x))
        simpa using this
    have h0 : ∑ g : G, φ (ρ g⁻¹ m) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum, ← map_zero φ, ← hm]
      congr 1
      exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun _ => rfl)
    have : m = ∑ g : G, (ρ g (φ (ρ g⁻¹ m)) - φ (ρ g⁻¹ m)) := by
      rw [Finset.sum_sub_distrib, hφ, h0, sub_zero]
    rw [this]
    exact I.sum_mem fun g _ => key g _
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.NuChar
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep

open Polynomial in
private theorem roots_smul_matrix {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (u : ℂ) (hu : u ≠ 0) :
    (u • M).charpoly = ((M.charpoly.roots.map (· * u)).map fun α => X - C α).prod := by
  have hM := (IsAlgClosed.splits M.charpoly).eq_prod_roots_of_monic (Matrix.charpoly_monic M)
  have hc : Multiset.card M.charpoly.roots = Fintype.card ι := by
    rw [← (IsAlgClosed.splits M.charpoly).natDegree_eq_card_roots, Matrix.charpoly_natDegree_eq_dim]
  refine Polynomial.funext fun x => ?_
  have h1 := congrArg (eval (x / u)) hM
  rw [Matrix.eval_charpoly, eval_multiset_prod, Multiset.map_map] at h1
  have e : Matrix.scalar ι x - u • M = u • (Matrix.scalar ι (x / u) - M) := by
    ext a b
    by_cases hab : a = b
    · subst hab
      simp
      field_simp
    · simp [Matrix.diagonal_apply_ne _ hab]
  rw [Matrix.eval_charpoly, e, Matrix.det_smul, h1, eval_multiset_prod, Multiset.map_map,
    Multiset.map_map, ← hc, ← Multiset.prod_replicate, ← Multiset.map_const, ← Multiset.prod_map_mul]
  refine congrArg _ (Multiset.map_congr rfl fun α _ => ?_)
  simp
  field_simp

open Polynomial in
private theorem charpoly_smul_prod {V ι : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Fintype ι]
    (f : Module.End ℂ V) (u : ℂ) (hu : u ≠ 0) (c : ι → ℂ) (h : f.charpoly = ∏ i, (X - C (c i))) :
    (u • f).charpoly = ∏ i, (X - C (c i * u)) := by
  have hr : f.charpoly.roots = Finset.univ.val.map c := by
    rw [h, Finset.prod_eq_multiset_prod, ← roots_multiset_prod_X_sub_C (Finset.univ.val.map c), Multiset.map_map]
    rfl
  rw [← LinearMap.charpoly_toMatrix (u • f) (Module.finBasis ℂ V), map_smul, roots_smul_matrix _ _ hu,
    LinearMap.charpoly_toMatrix, hr, Multiset.map_map, Multiset.map_map, Finset.prod_eq_multiset_prod]
  rfl

private theorem absPow_neg_nat (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (i : ℕ) (x : kˣ) : (absPow k (-(i : ℂ)) x : ℂ) = (resCard k : ℂ) ^ ((i : ℤ) * ord k x) := by
  rw [val_absPow, GlobalTheory.LGrp.nabs_eq_zpow, Complex.cpow_neg, Complex.cpow_natCast]
  push_cast
  rw [← zpow_natCast, ← zpow_mul, ← zpow_neg]
  congr 1
  ring

theorem UpperTheory.V.Pa.Lev.nuChar :
    ∀ (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (Bq : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (hB : IsPlaceOver Bq w), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (a : Weil hB →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin hB a) (ε : EpsFamily Bq) (rc : IrrGL (k := w.adicCompletion E) → WD hB), Laws a ha ε rc → ∀ (n : ℕ) (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (ψ : Fin n → (w.adicCompletion E)ˣ →* ℂˣ) (χ : (Fin n → (w.adicCompletion E)ˣ) →* ℂˣ), (∀ i, IsSmoothChar (ψ i)) → torusChar ψ = χ * ((deltaHalf (w.adicCompletion E) fun _ : Fin n => Unit).comp (leviTorus (w.adicCompletion E) (Fin n)).toMonoidHom) → IsSubquotient σ.ρ (prinSeries ψ) → ∀ g : Weil hB, (rc (algNorm σ)).charPol g = ∏ i : Fin n, (Polynomial.X - Polynomial.C ((resCard (w.adicCompletion E) : ℂ) ^ (((i : ℕ) : ℤ) * ord (w.adicCompletion E) (a g)) * (χ (Pi.mulSingle i (a g)) : ℂ))) := by
  intro l _ E Ω _ _ _ _ _ Bq w hB _ a ha ε rc L n σ ψ χ hψ hχ hs g
  have H := UpperTheory.V.AlgebraTools.jqRec E Ω Bq w hB a ha ε rc L n ⟨σ.V, σ.ρ, σ.smooth, σ.irred⟩ ψ hψ hs g
  rw [algNorm, IrrGL.nu, L.tw_eq]
  change (rc (IrrGL.of σ.ρ σ.smooth σ.irred)).charPol g = _ at H
  generalize rc (IrrGL.of σ.ρ σ.smooth σ.irred) = x at H ⊢
  obtain ⟨m, b, rfl⟩ := x.exists_rep
  rw [WD.charPol_mk] at H
  rw [WD.lpTwist_mk, WD.charPol_mk, WDRep.twist_ρ, charpoly_smul_prod _ _ (Units.ne_zero _) _ H]
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 2
  have h1 : torusChar ψ (Pi.mulSingle i (a g)) = ψ i (a g) := by
    rw [torusChar_apply, Finset.prod_eq_single i, Pi.mulSingle_eq_same]
    · intro j _ hj
      rw [Pi.mulSingle_eq_of_ne hj, map_one]
    · simp
  have hd : ∀ (t : Fin n → (w.adicCompletion E)ˣ) j,
      Matrix.GeneralLinearGroup.det (leviTorus (w.adicCompletion E) (Fin n) t j) = t j := fun t =>
    congrFun ((leviTorus (w.adicCompletion E) (Fin n)).left_inv t)
  have h2 : deltaHalf (w.adicCompletion E) (fun _ : Fin n => Unit)
      (leviTorus (w.adicCompletion E) (Fin n) (Pi.mulSingle i (a g))) =
      absPow (w.adicCompletion E) ((modExp (fun _ : Fin n => Unit) i : ℂ) / 2) (a g) := by
    rw [deltaHalf_apply, Finset.prod_eq_single i, hd, Pi.mulSingle_eq_same]
    · intro j _ hj
      rw [hd, Pi.mulSingle_eq_of_ne hj, map_one]
    · simp
  rw [← h1, hχ, ← absPow_neg_nat]
  have h3 : -((i : ℕ) : ℂ) = (modExp (fun _ : Fin n => Unit) i : ℂ) / 2 + (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) := by
    rw [modExp_fin _ (fun _ => by simp)]
    push_cast
    ring
  rw [h3, absPow_add]
  simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul]
  erw [h2]
  ring
end

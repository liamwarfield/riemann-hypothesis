module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HaarExistence
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LeviActionCommutesWithBoundary

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CreationProductSupportDegree
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CreationProductSupportDegree
open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.RgExh

theorem suppIn_deg_cre_prod : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (P : Pos n → Prop) (l : List (Pos n)) (x : Cn n V) (j : ℕ),
    (∀ i ∈ l, P i) → SuppIn P x → Deg j x →
      SuppIn P (((l.map cre).prod : Module.End ℂ (Cn n V)) x) ∧
        Deg (j + l.length) (((l.map cre).prod : Module.End ℂ (Cn n V)) x) := by
  intro n V _ _ P l x j hl hx hd
  induction l with
  | nil => simpa using And.intro hx hd
  | cons i l ih =>
    obtain ⟨ih1, ih2⟩ := ih fun k hk => hl k (List.mem_cons_of_mem i hk)
    have hi : P i := hl i List.mem_cons_self
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, List.length_cons]
    constructor
    · intro A hA k hk
      obtain ⟨h1, h2⟩ := CompanionTheory.D.LK.cre_ne hA
      by_cases hki : k = i
      · exact hki ▸ hi
      · exact ih1 _ h2 k (Finset.mem_erase.2 ⟨hki, hk⟩)
    · intro A hA
      obtain ⟨h1, h2⟩ := CompanionTheory.D.LK.cre_ne hA
      have h3 := ih2 _ h2
      have h4 := Finset.card_erase_add_one h1
      omega

end GlobalTheory.CompanionTheory.RgExh
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CreationProductSupportDegreeStatement
open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.creation_product_support_degree : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (P : Pos n → Prop) (l : List (Pos n)) (x : Cn n V) (j : ℕ),
    (∀ i ∈ l, P i) → SuppIn P x → Deg j x →
      SuppIn P (((l.map cre).prod : Module.End ℂ (Cn n V)) x) ∧
        Deg (j + l.length) (((l.map cre).prod : Module.End ℂ (Cn n V)) x) := by
  first | exact @GlobalTheory.CompanionTheory.RgExh.suppIn_deg_cre_prod | exact GlobalTheory.CompanionTheory.RgExh.suppIn_deg_cre_prod | (intros; apply GlobalTheory.CompanionTheory.RgExh.suppIn_deg_cre_prod <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LeviActionUnitaryAdjoint
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LeviActionUnitaryAdjoint
open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin sg)
open CompanionTheory.D.LK.Car (ann_apply cre_apply sg_erase tw_self)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.RgExhFarReg.ChainAdj

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def ip (x z : Cn n V) : ℂ := ∑ A, ⟪x A, z A⟫_ℂ

theorem sg_conj (i : Pos n) (A : Finset (Pos n)) : (starRingEnd ℂ) (sg i A) = sg i A := by
  unfold sg
  simp

theorem sg_erase_self (i : Pos n) {A : Finset (Pos n)} (h : i ∈ A) : sg i (A.erase i) = sg i A := by
  rw [sg_erase i h, tw_self, one_mul]

theorem ip_cre (i : Pos n) (x z : Cn n V) : ip (cre i x) z = ip x (ann i z) := by
  unfold ip
  have h1 : ∀ A : Finset (Pos n), ⟪cre i x A, z A⟫_ℂ =
      if i ∈ A then sg i A * ⟪x (A.erase i), z A⟫_ℂ else 0 := fun A => by
    rw [cre_apply]
    split_ifs
    · rw [inner_smul_left, sg_conj]
    · simp
  have h2 : ∀ A : Finset (Pos n), ⟪x A, ann i z A⟫_ℂ =
      if i ∈ A then 0 else sg i A * ⟪x A, z (insert i A)⟫_ℂ := fun A => by
    rw [ann_apply]
    split_ifs
    · simp
    · rw [inner_smul_right]
  simp only [h1, h2]
  rw [← Finset.sum_filter, Finset.sum_ite, Finset.sum_const_zero, zero_add]
  refine Finset.sum_bij' (fun A _ => A.erase i) (fun A _ => insert i A) ?_ ?_ ?_ ?_ ?_
  · intro A hA
    simp
  · intro A hA
    simp
  · intro A hA
    exact Finset.insert_erase (by simpa using hA)
  · intro A hA
    exact Finset.erase_insert (by simpa using hA)
  · intro A hA
    have hA' : i ∈ A := by simpa using hA
    rw [sg_erase_self i hA', Finset.insert_erase hA']

theorem ip_conj (x z : Cn n V) : (starRingEnd ℂ) (ip x z) = ip z x := by
  unfold ip
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun A _ => inner_conj_symm _ _

theorem ip_ann (i : Pos n) (x z : Cn n V) : ip (ann i x) z = ip x (cre i z) := by
  rw [← ip_conj, ← ip_cre, ip_conj]

theorem ip_cre_ann (i k : Pos n) (x z : Cn n V) :
    ip ((cre k * ann i : Module.End ℂ (Cn n V)) x) z = ip x ((cre i * ann k : Module.End ℂ (Cn n V)) z) := by
  simp only [Module.End.mul_apply]
  rw [ip_cre, ip_ann]

theorem ip_add_left (x y z : Cn n V) : ip (x + y) z = ip x z + ip y z := by
  simp only [ip, Pi.add_apply, inner_add_left, Finset.sum_add_distrib]

theorem ip_add_right (x y z : Cn n V) : ip x (y + z) = ip x y + ip x z := by
  simp only [ip, Pi.add_apply, inner_add_right, Finset.sum_add_distrib]

theorem ip_smul_left (c : ℂ) (x z : Cn n V) : ip (c • x) z = (starRingEnd ℂ) c * ip x z := by
  simp only [ip, Pi.smul_apply, inner_smul_left, Finset.mul_sum]

theorem ip_smul_right (c : ℂ) (x z : Cn n V) : ip x (c • z) = c * ip x z := by
  simp only [ip, Pi.smul_apply, inner_smul_right, Finset.mul_sum]

theorem ip_sum_left {ι : Type} (s : Finset ι) (f : ι → Cn n V) (z : Cn n V) :
    ip (∑ a ∈ s, f a) z = ∑ a ∈ s, ip (f a) z := by
  simp only [ip, Finset.sum_apply, sum_inner]
  exact Finset.sum_comm

theorem ip_sum_right {ι : Type} (s : Finset ι) (x : Cn n V) (f : ι → Cn n V) :
    ip x (∑ a ∈ s, f a) = ∑ a ∈ s, ip x (f a) := by
  simp only [ip, Finset.sum_apply, inner_sum]
  exact Finset.sum_comm

theorem adC_conj (p q : Fin n) (i k : Pos n) : (starRingEnd ℂ) (adC p q i k) = adC p q i k := by
  unfold adC
  split_ifs <;> simp

theorem adC_swap (p q : Fin n) (i k : Pos n) : adC p q i k = adC q p k i := by
  have e1 : (q = i.1.1 ∧ k.1 = (p, i.1.2)) ↔ (p = k.1.1 ∧ i.1 = (q, k.1.2)) := by
    obtain ⟨⟨a, b⟩, hi⟩ := i
    obtain ⟨⟨c, d⟩, hk⟩ := k
    simp only [Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl, rfl⟩; exact ⟨rfl, rfl, rfl⟩
    · rintro ⟨rfl, rfl, rfl⟩; exact ⟨rfl, rfl, rfl⟩
  have e2 : (i.1.2 = p ∧ k.1 = (i.1.1, q)) ↔ (k.1.2 = q ∧ i.1 = (k.1.1, p)) := by
    obtain ⟨⟨a, b⟩, hi⟩ := i
    obtain ⟨⟨c, d⟩, hk⟩ := k
    simp only [Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl, rfl⟩; exact ⟨rfl, rfl, rfl⟩
    · rintro ⟨rfl, rfl, rfl⟩; exact ⟨rfl, rfl, rfl⟩
  unfold adC
  simp only [e1, e2]

theorem ip_adL (p q : Fin n) (x z : Cn n V) : ip (adL p q x) z = ip x (adL q p z) := by
  simp only [adL, LinearMap.sum_apply, LinearMap.smul_apply, ip_sum_left, ip_sum_right, ip_smul_left,
    ip_smul_right, adC_conj, ip_cre_ann]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  rw [adC_swap]

theorem ip_lift {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} (hU : KUnit ε E) {p q : Fin n}
    (h : ε p = ε q) (x z : Cn n V) : ip (lift n (E p q) x) z = ip x (lift n (E q p) z) :=
  Finset.sum_congr rfl fun A _ => hU p q h (x A) (z A)

theorem lF_adjoint : ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V), KUnit ε E → ∀ p q : Fin n, ε p = ε q → ∀ x z : Cn n V,
      ∑ A, ⟪lF E p q x A, z A⟫_ℂ = ∑ A, ⟪x A, lF E q p z A⟫_ℂ := by
  intro n ε V _ _ E hU p q h x z
  change ip (lF E p q x) z = ip x (lF E q p z)
  simp only [lF, LinearMap.add_apply, ip_add_left, ip_add_right]
  rw [ip_lift hU h, ip_adL]

end GlobalTheory.CompanionTheory.RgExhFarReg.ChainAdj
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LeviActionUnitaryAdjointStatement
open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_action_unitary_adjoint : ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V), KUnit ε E → ∀ p q : Fin n, ε p = ε q → ∀ x z : Cn n V,
      ∑ A, ⟪lF E p q x A, z A⟫_ℂ = ∑ A, ⟪x A, lF E q p z A⟫_ℂ := by
  first | exact @GlobalTheory.CompanionTheory.RgExhFarReg.ChainAdj.lF_adjoint | exact GlobalTheory.CompanionTheory.RgExhFarReg.ChainAdj.lF_adjoint | (intros; apply GlobalTheory.CompanionTheory.RgExhFarReg.ChainAdj.lF_adjoint <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CreationProductSingleBasis
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CreationProductSingleBasis
open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.Chains

theorem cre_single {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (f : Pos n) (S : Finset (Pos n)) (w : V)
    (h : f ∉ S) :
    (cre f : Module.End ℂ (Cn n V)) (Pi.single S w : Cn n V) =
      CompanionTheory.D.LK.sg f (insert f S) • (Pi.single (insert f S) w : Cn n V) := by
  funext A
  show (if f ∈ A then CompanionTheory.D.LK.sg f A • (Pi.single S w : Cn n V) (A.erase f) else 0) = _
  by_cases hA : A = insert f S
  · subst hA
    rw [if_pos (Finset.mem_insert_self f S), Finset.erase_insert h]
    simp [Pi.single_apply]
  · have hr : (CompanionTheory.D.LK.sg f (insert f S) • (Pi.single (insert f S) w : Cn n V)) A = 0 := by
      simp [Pi.single_apply, hA]
    rw [hr]
    split_ifs with hf
    · have hne : A.erase f ≠ S := fun he => hA (by rw [← he, Finset.insert_erase hf])
      simp [Pi.single_apply, hne]
    · rfl

theorem sg_ne_zero {n : ℕ} (f : Pos n) (A : Finset (Pos n)) : CompanionTheory.D.LK.sg f A ≠ 0 := by
  delta CompanionTheory.D.LK.sg
  exact pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)

theorem prod_cre_single : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (l : List (Pos n)) (S : Finset (Pos n)) (w : V),
    l.Nodup → (∀ i ∈ l, i ∉ S) → ∃ c : ℂ, c ≠ 0 ∧
      ((l.map cre).prod : Module.End ℂ (Cn n V)) (Pi.single S w : Cn n V) = c • (Pi.single (S ∪ l.toFinset) w : Cn n V) := by
  intro n V _ _ l S w
  induction l with
  | nil =>
    intro _ _
    refine ⟨1, one_ne_zero, ?_⟩
    simp
  | cons a l ih =>
    intro hnd hS
    obtain ⟨c, hc, hcl⟩ := ih hnd.of_cons (fun i hi => hS i (by simp [hi]))
    have ha : a ∉ S ∪ l.toFinset := by
      rw [Finset.mem_union, not_or, List.mem_toFinset]
      exact ⟨hS a (by simp), (List.nodup_cons.1 hnd).1⟩
    refine ⟨c * CompanionTheory.D.LK.sg a (insert a (S ∪ l.toFinset)), mul_ne_zero hc (sg_ne_zero _ _), ?_⟩
    rw [List.map_cons, List.prod_cons]
    show cre a (((l.map cre).prod : Module.End ℂ (Cn n V)) (Pi.single S w : Cn n V)) = _
    rw [hcl, map_smul, cre_single a _ w ha, smul_smul, List.toFinset_cons, Finset.union_insert]

end GlobalTheory.CompanionTheory.Chains
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CreationProductSingleBasisStatement
open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.creation_product_single_basis : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (l : List (Pos n)) (S : Finset (Pos n)) (w : V),
    l.Nodup → (∀ i ∈ l, i ∉ S) → ∃ c : ℂ, c ≠ 0 ∧
      ((l.map cre).prod : Module.End ℂ (Cn n V)) (Pi.single S w : Cn n V) = c • (Pi.single (S ∪ l.toFinset) w : Cn n V) := by
  first | exact @GlobalTheory.CompanionTheory.Chains.prod_cre_single | exact GlobalTheory.CompanionTheory.Chains.prod_cre_single | (intros; apply GlobalTheory.CompanionTheory.Chains.prod_cre_single <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LocallyFiniteLeviInvariantSubspace
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LocallyFiniteLeviInvariantSubspace
open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit KStab)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.RgExhStableChains

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def chainsIn (lev : Fin n → ℕ) (d : ℕ) (S : Submodule ℂ V) : Submodule ℂ (Cn n V) where
  carrier := {x | SuppIn (inU lev) x ∧ Deg d x ∧ ∀ A, x A ∈ S}
  add_mem' := by
    rintro x y ⟨hx1, hx2, hx3⟩ ⟨hy1, hy2, hy3⟩
    have key : ∀ A, (x + y) A ≠ 0 → x A ≠ 0 ∨ y A ≠ 0 := fun A h => by
      by_contra hc
      push Not at hc
      exact h (by simp [hc.1, hc.2])
    refine ⟨fun A h => ?_, fun A h => ?_, fun A => S.add_mem (hx3 A) (hy3 A)⟩
    · rcases key A h with h' | h'
      · exact hx1 A h'
      · exact hy1 A h'
    · rcases key A h with h' | h'
      · exact hx2 A h'
      · exact hy2 A h'
  zero_mem' := ⟨fun A h => absurd rfl h, fun A h => absurd rfl h, fun A => S.zero_mem⟩
  smul_mem' := by
    rintro c x ⟨hx1, hx2, hx3⟩
    have key : ∀ A, (c • x) A ≠ 0 → x A ≠ 0 := fun A h h0 => h (by simp [h0])
    exact ⟨fun A h => hx1 A (key A h), fun A h => hx2 A (key A h), fun A => S.smul_mem c (hx3 A)⟩

theorem finiteDimensional_chainsIn (lev : Fin n → ℕ) (d : ℕ) (S : Submodule ℂ V) [FiniteDimensional ℂ S] :
    FiniteDimensional ℂ (chainsIn lev d S) := by
  let L : chainsIn lev d S →ₗ[ℂ] (Finset (Pos n) → S) :=
    LinearMap.pi fun A => LinearMap.codRestrict S ((LinearMap.proj A).comp (chainsIn lev d S).subtype)
      fun x => x.2.2.2 A
  refine Module.Finite.of_injective L fun x y h => Subtype.ext (funext fun A => ?_)
  exact congrArg Subtype.val (congrFun h A)

theorem lF_apply (E : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) (x : Cn n V) (A : Finset (Pos n)) :
    lF E p q x A = E p q (x A) + ∑ i : Pos n, ∑ k : Pos n, adC p q i k • cre k (ann i x) A := by
  simp [lF, adL, LinearMap.add_apply, LinearMap.sum_apply, Finset.sum_apply, Module.End.mul_apply]

theorem cre_ann_mem {S : Submodule ℂ V} {x : Cn n V} (hx : ∀ A, x A ∈ S) (i k : Pos n) (A : Finset (Pos n)) :
    cre k (ann i x) A ∈ S := by
  rw [CompanionTheory.D.LK.Car.cre_apply]
  split_ifs
  · refine S.smul_mem _ ?_
    rw [CompanionTheory.D.LK.Car.ann_apply]
    split_ifs
    · exact S.zero_mem
    · exact S.smul_mem _ (hx _)
  · exact S.zero_mem

theorem inU_of_adC {lev : Fin n → ℕ} {p q : Fin n} (hpq : lev p = lev q) {i k : Pos n}
    (h : adC p q i k ≠ 0) (hi : inU lev i) : inU lev k := by
  by_cases c1 : q = i.1.1 ∧ k.1 = (p, i.1.2)
  · show lev k.1.1 < lev k.1.2
    rw [c1.2]
    show lev p < lev i.1.2
    rw [hpq, c1.1]
    exact hi
  by_cases c2 : i.1.2 = p ∧ k.1 = (i.1.1, q)
  · show lev k.1.1 < lev k.1.2
    rw [c2.2]
    show lev i.1.1 < lev q
    rw [← hpq, ← c2.1]
    exact hi
  · exact absurd (by simp [adC, c1, c2]) h

theorem lF_ne {E : Fin n → Fin n → Module.End ℂ V} {p q : Fin n} {x : Cn n V} {A : Finset (Pos n)}
    (h : lF E p q x A ≠ 0) : x A ≠ 0 ∨ ∃ i k, adC p q i k ≠ 0 ∧ cre k (ann i x) A ≠ 0 := by
  by_contra hc
  push Not at hc
  apply h
  rw [lF_apply, hc.1, map_zero, zero_add]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun k _ => ?_
  by_cases h0 : adC p q i k = 0
  · rw [h0, zero_smul]
  · rw [hc.2 i k h0, smul_zero]

theorem term_supp {lev : Fin n → ℕ} {d : ℕ} {p q : Fin n} (hpq : lev p = lev q) {x : Cn n V}
    (hx : SuppIn (inU lev) x) (hd : Deg d x) {A : Finset (Pos n)} {i k : Pos n} (h0 : adC p q i k ≠ 0)
    (h : cre k (ann i x) A ≠ 0) : (∀ j ∈ A, inU lev j) ∧ A.card = d := by
  obtain ⟨hk, h1⟩ := CompanionTheory.D.LK.cre_ne h
  obtain ⟨h2, h3⟩ := CompanionTheory.D.LK.ann_ne h1
  have hs := hx _ h3
  have hi : inU lev i := hs i (mem_insert_self _ _)
  refine ⟨fun j hj => ?_, ?_⟩
  · by_cases e : j = k
    · exact e ▸ inU_of_adC hpq h0 hi
    · exact hs j (mem_insert_of_mem (mem_erase.2 ⟨e, hj⟩))
  · have e1 := hd _ h3
    rw [card_insert_of_notMem h2] at e1
    have e2 := card_erase_add_one hk
    omega

theorem lF_mem_chainsIn {ε : Fin n → Bool} {lev : Fin n → ℕ} {d : ℕ} {E : Fin n → Fin n → Module.End ℂ V}
    {S : Submodule ℂ V} (hS : KStab ε E S) {p q : Fin n} (hε : ε p = ε q) (hpq : lev p = lev q) {x : Cn n V}
    (hx : x ∈ chainsIn lev d S) : lF E p q x ∈ chainsIn lev d S := by
  obtain ⟨hx1, hx2, hx3⟩ := hx
  refine ⟨fun A h => ?_, fun A h => ?_, fun A => ?_⟩
  · rcases lF_ne h with h' | ⟨i, k, h0, h'⟩
    · exact hx1 A h'
    · exact (term_supp hpq hx1 hx2 h0 h').1
  · rcases lF_ne h with h' | ⟨i, k, h0, h'⟩
    · exact hx2 A h'
    · exact (term_supp hpq hx1 hx2 h0 h').2
  · rw [lF_apply]
    exact S.add_mem (hS p q hε _ (hx3 A)) (S.sum_mem fun i _ => S.sum_mem fun k _ =>
      S.smul_mem _ (cre_ann_mem hx3 i k A))

theorem exists_stable : ∀ (n : ℕ) (ε : Fin n → Bool) (lev : Fin n → ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (d : ℕ) (y : Cn n V), LocFin ε E → SuppIn (inU lev) y → Deg d y →
    ∃ T : Submodule ℂ (Cn n V), FiniteDimensional ℂ T ∧ y ∈ T ∧ (∀ x ∈ T, SuppIn (inU lev) x ∧ Deg d x) ∧
      ∀ p q : Fin n, ε p = ε q → lev p = lev q → ∀ x ∈ T, lF E p q x ∈ T := by
  intro n ε lev V _ _ E d y hF hy hd
  choose Sf hfd hSt hmem using hF
  let S : Submodule ℂ V := ⨆ A, Sf (y A)
  haveI : ∀ A, FiniteDimensional ℂ (Sf (y A)) := fun A => hfd _
  haveI : FiniteDimensional ℂ S := Submodule.finiteDimensional_iSup _
  have hSs : KStab ε E S := fun a b h v hv =>
    (iSup_le fun A z hz => Submodule.mem_iSup_of_mem A (hSt _ a b h z hz) : S ≤ S.comap (E a b)) hv
  refine ⟨chainsIn lev d S, finiteDimensional_chainsIn lev d S,
    ⟨hy, hd, fun A => Submodule.mem_iSup_of_mem A (hmem _)⟩, fun x hx => ⟨hx.1, hx.2.1⟩,
    fun p q hε hpq x hx => lF_mem_chainsIn hSs hε hpq hx⟩

end GlobalTheory.CompanionTheory.RgExhStableChains
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LocallyFiniteLeviInvariantSubspaceStatement
open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locally_finite_levi_invariant_subspace : ∀ (n : ℕ) (ε : Fin n → Bool) (lev : Fin n → ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (d : ℕ) (y : Cn n V), LocFin ε E → SuppIn (inU lev) y → Deg d y →
    ∃ T : Submodule ℂ (Cn n V), FiniteDimensional ℂ T ∧ y ∈ T ∧ (∀ x ∈ T, SuppIn (inU lev) x ∧ Deg d x) ∧
      ∀ p q : Fin n, ε p = ε q → lev p = lev q → ∀ x ∈ T, lF E p q x ∈ T := by
  first | exact @GlobalTheory.CompanionTheory.RgExhStableChains.exists_stable | exact GlobalTheory.CompanionTheory.RgExhStableChains.exists_stable | (intros; apply GlobalTheory.CompanionTheory.RgExhStableChains.exists_stable <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HighestWeightVectorKilledByRaising
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HighestWeightVectorKilledByRaising
open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.RgExh

theorem adC_mem_omU {n : ℕ} {ε : Fin n → Bool} {lev : Fin n → ℕ} {p q : Fin n} (hpq : p < q) (hε : ε p = ε q)
    (hl : lev p = lev q) {i k : Pos n} (hc : adC p q i k ≠ 0) (hi : i ∈ omU ε lev) :
    k ∈ omU ε lev ∧ k ≠ i := by
  have hcase : (q = i.1.1 ∧ k.1 = (p, i.1.2)) ∨ (i.1.2 = p ∧ k.1 = (i.1.1, q)) := by
    by_contra hn
    rw [not_or] at hn
    exact hc (by simp only [adC, if_neg hn.1, if_neg hn.2, sub_self])
  obtain ⟨h1, h2⟩ : ε i.1.1 = ε i.1.2 ∧ lev i.1.1 < lev i.1.2 := (mem_filter.1 hi).2
  have hne : p ≠ q := ne_of_lt hpq
  rcases hcase with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · refine ⟨mem_filter.2 ⟨mem_univ _, ?_, ?_⟩, fun e => ?_⟩
    · rw [e2]; show ε p = ε i.1.2; rw [hε, e1, h1]
    · rw [e2]; show lev p < lev i.1.2; rw [hl, e1]; exact h2
    · rw [e] at e2; exact hne (e1.trans (congrArg Prod.fst e2)).symm
  · refine ⟨mem_filter.2 ⟨mem_univ _, ?_, ?_⟩, fun e => ?_⟩
    · rw [e2]; show ε i.1.1 = ε q; rw [h1, e1, hε]
    · rw [e2]; show lev i.1.1 < lev q; rw [← hl, ← e1]; exact h2
    · rw [e] at e2; exact hne (e1.symm.trans (congrArg Prod.snd e2))

theorem lF_single_omU : ∀ (n : ℕ) (ε : Fin n → Bool) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (γ : Fin n → ℝ) (u : V), KHighest ε E γ u →
    ∀ p q : Fin n, p < q → ε p = ε q → lev p = lev q →
      lF E p q (Pi.single (omU ε lev) u : Cn n V) = 0 := by
  intro n ε lev V _ _ E γ u hu p q hpq hε hl
  have hE : E p q u = 0 := hu.2 p q hpq hε
  have h1 : lift n (E p q) (Pi.single (omU ε lev) u : Cn n V) = 0 := by
    funext A
    rw [CompanionTheory.D.LK.lift_apply]
    by_cases e : A = omU ε lev
    · subst e
      rw [Pi.single_eq_same]
      exact hE
    · rw [Pi.single_eq_of_ne e, map_zero]
      rfl
  have h2 : adL p q (Pi.single (omU ε lev) u : Cn n V) = 0 := by
    simp only [adL, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun k _ => ?_
    by_cases hc : adC p q i k = 0
    · rw [hc, zero_smul]
    suffices h : cre k (ann i (Pi.single (omU ε lev) u : Cn n V)) = 0 by rw [h, smul_zero]
    funext B
    by_contra h
    obtain ⟨-, h3⟩ := CompanionTheory.D.LK.cre_ne h
    obtain ⟨-, h4⟩ := CompanionTheory.D.LK.ann_ne h3
    have e : insert i (B.erase k) = omU ε lev := by
      by_contra h'
      exact h4 (Pi.single_eq_of_ne h' _)
    have hi : i ∈ omU ε lev := e ▸ mem_insert_self _ _
    obtain ⟨hk, hki⟩ := adC_mem_omU hpq hε hl hc hi
    rw [← e] at hk
    rcases mem_insert.1 hk with h5 | h5
    · exact hki h5
    · exact notMem_erase _ _ h5
  show lift n (E p q) _ + adL p q _ = 0
  rw [h1, h2, add_zero]

end GlobalTheory.CompanionTheory.RgExh
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HighestWeightVectorKilledByRaisingStatement
open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.highest_weight_vector_killed_by_raising : ∀ (n : ℕ) (ε : Fin n → Bool) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (γ : Fin n → ℝ) (u : V), KHighest ε E γ u →
    ∀ p q : Fin n, p < q → ε p = ε q → lev p = lev q →
      lF E p q (Pi.single (omU ε lev) u : Cn n V) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.RgExh.lF_single_omU | exact GlobalTheory.CompanionTheory.RgExh.lF_single_omU | (intros; apply GlobalTheory.CompanionTheory.RgExh.lF_single_omU <;> assumption)
end
end

noncomputable section

open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.RgExh

theorem injU_of_injR : CompanionTheory.RgExh.U.InjR → CompanionTheory.RgExh.U.InjU := by
  intro hR n ε γ lev V _ _ E hG hE hU hL hM u y hu hy hd hb
  have hmono := hG.2.1
  have hsingle := GlobalTheory.T.highest_weight_vector_killed_by_raising n ε lev V E γ u hu
  obtain ⟨T, hTf, hyT, hTS, hTs⟩ := GlobalTheory.T.locally_finite_levi_invariant_subspace n ε lev V E _ y hL hy hd
  obtain ⟨y', hy'T, hy'0, hy'b⟩ := GlobalTheory.T.finite_dim_invariant_subspace_adjoint_pair n V
    {pq : Fin n × Fin n // pq.1 < pq.2 ∧ ε pq.1 = ε pq.2 ∧ lev pq.1 = lev pq.2} T
    (fun i => lF E i.1.1 i.1.2) (fun i => lF E i.1.2 i.1.1) (bd (allT n) E) y hTf
    (fun i x z => GlobalTheory.T.levi_action_unitary_adjoint n ε V E hU _ _ i.2.2.1 x z)
    (fun i t ht => hTs _ _ i.2.2.1 i.2.2.2 t ht)
    (fun i t ht => hTs _ _ i.2.2.1.symm i.2.2.2.symm t ht)
    (fun i t ht => GlobalTheory.T.levi_action_commutes_with_boundary n lev V E hmono hE _ _ i.2.2.2 t (hTS t ht).1)
    (fun i t ht => GlobalTheory.T.levi_action_commutes_with_boundary n lev V E hmono hE _ _ i.2.2.2.symm t (hTS t ht).1) hyT
    (fun i => by rw [hb]; exact hsingle _ _ i.2.1 i.2.2.1 i.2.2.2)
  obtain ⟨hy's, hy'd⟩ := hTS y' hy'T
  obtain ⟨l, hnd, hmem, hcl⟩ := GlobalTheory.T.exists_ordered_creation_list n ε lev hmono
  have hlc : ∀ e ∈ l, e.1.1 < e.1.2 ∧ ε e.1.1 = ε e.1.2 ∧ lev e.1.1 = lev e.1.2 := fun e he => by
    obtain ⟨h1, h2⟩ := (hmem e).1 he
    have hc : ε e.1.1 = ε e.1.2 := (Finset.mem_filter.1 h1).2
    refine ⟨e.2, hc, le_antisymm (hmono e.2.le) ?_⟩
    by_contra h3
    exact h2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, hc, not_le.1 h3⟩)
  have hbd := GlobalTheory.T.ordered_creation_commutes_past_levi n V E (GlobalTheory.T.boundary_creation_anticommutator n V E) l y' hcl
    (fun e he => hy'0 ⟨e.1, hlc e he⟩)
  obtain ⟨c, hc0, hcw⟩ := GlobalTheory.T.creation_product_single_basis n V l (omU ε lev) u hnd (fun i hi => ((hmem i).1 hi).2)
  have hun : omU ε lev ∪ l.toFinset = om ε := by
    ext i
    simp only [Finset.mem_union, List.mem_toFinset, hmem]
    constructor
    · rintro (h | h)
      · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 h).2.1⟩
      · exact h.1
    · intro h
      by_cases h2 : i ∈ omU ε lev
      · exact Or.inl h2
      · exact Or.inr ⟨h, h2⟩
  have hcard : (om ε).card = (omU ε lev).card + l.length := by
    rw [← hun, Finset.card_union_of_disjoint, List.toFinset_card_of_nodup hnd]
    exact Finset.disjoint_left.2 fun i h1 h2 => ((hmem i).1 (List.mem_toFinset.1 h2)).2 h1
  obtain ⟨hs1, hs2⟩ := GlobalTheory.T.creation_product_support_degree n V (inR ε lev) l y' _ (fun i hi => Or.inl (hlc i hi).2.1)
    (fun A hA i hi => Or.inr (hy's A hA i hi)) hy'd
  set C : Cn n V := ((l.map cre).prod : Module.End ℂ (Cn n V)) y' with hC
  have hsm : ∀ (s : ℂ) (x : Cn n V) (A : Finset (Pos n)), s • x A ≠ 0 → x A ≠ 0 := fun s x A h h0 => h (by rw [h0, smul_zero])
  refine hR n ε γ lev V E hG hE hU hL hM u ((c⁻¹ * (-1 : ℂ) ^ l.length) • C) hu.1 ?_ ?_ ?_
  · exact fun A hA => hs1 A (hsm _ C A hA)
  · intro A hA
    have h3 := hs2 A (hsm _ C A hA)
    refine ⟨Finset.filter_false_of_mem fun _ _ h => h rfl, ?_⟩
    rw [Finset.filter_true_of_mem (fun _ _ => rfl), h3, hcard]
    omega
  · rw [map_smul, hC, hbd, hy'b, hb, hcw, hun, smul_smul, smul_smul]
    have h1 : ((-1 : ℂ) ^ l.length) * ((-1 : ℂ) ^ l.length) = 1 := by
      rw [← mul_pow]; simp
    have h2 : c⁻¹ * (-1 : ℂ) ^ l.length * (-1 : ℂ) ^ l.length * c = 1 := by
      rw [mul_assoc c⁻¹, h1, mul_one, inv_mul_cancel₀ hc0]
    rw [h2, one_smul]

end GlobalTheory.CompanionTheory.RgExh
